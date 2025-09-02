/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 * Copyright (C) 2016 Kangjie Lu
 * Copyrigth (C) 2024 Chengyu Song
 *
 * For licensing details see LICENSE
 */


#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>

#include <vector>
#include <algorithm>

#include "CallGraph.h"
#include "Annotation.h"
#include "PointTo.h"

#include "gracfl/include/solvers/Solver.hpp"

#define CG_LOG(stmt) KA_LOG(2, "CallGraph: " << stmt)
#define CG_DEBUG(stmt) KA_LOG(3, "CallGraph: " << stmt)

using namespace llvm;

Function* CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

bool CallGraphPass::isCompatibleType(Type *T1, Type *T2) {
  if (T1 == T2) {
      return true;
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
  } else if (T1->isIntegerTy()) {
    // assume pointer can be cased to the address space size
    if (T2->isPointerTy() && T1->getIntegerBitWidth() == T2->getPointerAddressSpace())
      return true;

    // assume all integer type are compatible
    if (T2->isIntegerTy())
      return true;
    else
      return false;
  } else if (T1->isPointerTy()) {
    if (!T2->isPointerTy())
      return false;

#if LLVM_VERSION_MAJOR > 12
    return true;
#else
    Type *ElT1 = T1->getPointerElementType();
    Type *ElT2 = T2->getPointerElementType();
    // assume "void *" and "char *" are equivalent to any pointer type
    if (ElT1->isIntegerTy(8) || ElT2->isIntegerTy(8))
      return true;

    return isCompatibleType(ElT1, ElT2);
#endif
  } else if (T1->isArrayTy()) {
    if (!T2->isArrayTy())
      return false;

    Type *ElT1 = T1->getArrayElementType();
    Type *ElT2 = T2->getArrayElementType();
    return isCompatibleType(ElT1, ElT2);
  } else if (T1->isStructTy()) {
    StructType *ST1 = cast<StructType>(T1);
    StructType *ST2 = dyn_cast<StructType>(T2);
    if (!ST2)
      return false;

    // literal has to be equal
    if (ST1->isLiteral() != ST2->isLiteral())
      return false;

    // literal, compare content
    if (ST1->isLiteral()) {
      unsigned numEl1 = ST1->getNumElements();
      if (numEl1 != ST2->getNumElements())
        return false;

      for (unsigned i = 0; i < numEl1; ++i) {
        if (!isCompatibleType(ST1->getElementType(i), ST2->getElementType(i)))
          return false;
      }
      return true;
    }

    // not literal, use name?
    return ST1->getStructName().equals(ST2->getStructName());
  } else if (T1->isFunctionTy()) {
    FunctionType *FT1 = cast<FunctionType>(T1);
    FunctionType *FT2 = dyn_cast<FunctionType>(T2);
    if (!FT2)
      return false;

    if (!isCompatibleType(FT1->getReturnType(), FT2->getReturnType()))
      return false;

    // assume varg is always compatible with varg?
    if (FT1->isVarArg()) {
      if (FT2->isVarArg())
        return true;
      else
        return false;
    }

    // compare args, again ...
    unsigned numParam1 = FT1->getNumParams();
    if (numParam1 != FT2->getNumParams())
      return false;

    for (unsigned i = 0; i < numParam1; ++i) {
      if (!isCompatibleType(FT1->getParamType(i), FT2->getParamType(i)))
        return false;
    }
    return true;
  } else if (T1->getTypeID() <= Type::FP128TyID) {
    return T1->getTypeID() == T2->getTypeID();
  } else {
    errs() << "Unhandled Types:" << *T1 << " :: " << *T2 << "\n";
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool CallGraphPass::isCompatible(const CallBase *CS, const Function *F) {
  // just compare known args
  if (F->getFunctionType()->isVarArg()) {
    //errs() << "VarArg: " << F->getName() << "\n";
    //report_fatal_error("VarArg address taken function\n");
  } else if (F->arg_size() != CS->arg_size()) {
    //errs() << "ArgNum mismatch: " << F.getName() << "\n";
    return false;
  } else if (!isCompatibleType(F->getReturnType(), CS->getType())) {
    return false;
  }

  if (F->isIntrinsic()) {
    //errs() << "Intrinsic: " << F.getName() << "\n";
    return false;
  }

  // type matching on args
  bool Matched = true;
  auto AI = CS->arg_begin();
  for (auto FI = F->arg_begin(), FE = F->arg_end();
       FI != FE; ++FI, ++AI) {
    // check type mis-match
    Type *FormalTy = FI->getType();
    Type *ActualTy = (*AI)->getType();

    if (isCompatibleType(FormalTy, ActualTy))
      continue;
    else {
      Matched = false;
      break;
    }
  }

  return Matched;
}

bool CallGraphPass::findCalleesByType(const CallBase *CS, FuncSet &FS) {
  //errs() << *CS << "\n";
  for (const Function *F : Ctx->AddressTakenFuncs) {
    if (isCompatible(CS, const_cast<Function*>(F)))
      FS.insert(F);
  }

  return false;
}

bool CallGraphPass::handleMemcpy(const CallBase *CS) {
  Value *dst = CS->getArgOperand(0);
  Value *src = CS->getArgOperand(1);
  CG_LOG("Memcpy: " << *dst << " = " << *src << "\n");
  // field insensitive
  NodeIndex dstNode = NF.getValueNodeFor(dst);
  NodeIndex srcNode = NF.getValueNodeFor(src);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Memcpy dst node not found!");
  assert(srcNode != AndersNodeFactory::InvalidIndex && "Memcpy src node not found!");
  NodeIndex derefDst = NF.getDereferenceNodeFor(dst);
  if (derefDst == AndersNodeFactory::InvalidIndex) {
    CG_DEBUG("Create deref node " << derefDst << " for " << *dst << "\n");
    derefDst = NF.createDereferenceNode(dst);
    EB.addDereferenceEdges(dstNode, derefDst);
  }
  NodeIndex derefSrc = NF.getDereferenceNodeFor(src);
  if (derefSrc == AndersNodeFactory::InvalidIndex) {
    CG_DEBUG("Create deref node " << derefSrc << " for " << *src << "\n");
    derefSrc = NF.createDereferenceNode(src);
    EB.addDereferenceEdges(srcNode, derefSrc);
  }
  EB.addAssignmentEdges(derefSrc, derefDst);

  return false;
}

bool CallGraphPass::handleCall(const CallBase *CS, const Function *CF) {
  if (CF->isIntrinsic()) {
    // handle intrinsic functions
    return false;
  }

  // assumes CF is the function definition
  if (CF->empty()) {
    // external function, nothing to do
    WARNING("Call: " << CF->getName() << " is empty!\n");
    if (CF->getName() == "memcpy" || CF->getName() == "memmove")
      handleMemcpy(CS);
    return false;
  }

  // handle args
  unsigned numArgs = CS->arg_size();
  if (CF->isVarArg()) {
    NodeIndex formalNode = NF.getVarargNodeFor(CF);
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      NodeIndex argNode = NF.getValueNodeFor(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      EB.addAssignmentEdges(argNode, formalNode);
    }
  } else {
    if (numArgs != CF->arg_size()) {
      WARNING("Call argument number mismatch! " << *CS << " -> " << CF->getName() << "\n");
      return false;
    }
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      NodeIndex argNode = NF.getValueNodeFor(arg);
      assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = NF.getValueNodeFor(farg);
      assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
      EB.addAssignmentEdges(argNode, formalNode);
    }
  }

  // handle return
  if (!CF->getReturnType()->isVoidTy()) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = NF.getValueNodeFor(CS);
    assert(callNode != AndersNodeFactory::InvalidIndex && "Call node not found!");
    EB.addAssignmentEdges(retNode, callNode);
  }

  return false;
}

static inline Type *getElementTy(Type *T) {
  while (T) {
    if (ArrayType *AT = dyn_cast<ArrayType>(T))
      T = AT->getElementType();
    else if (VectorType *VT = dyn_cast<VectorType>(T))
      T = VT->getElementType();
    else
      break;
  }

  return T;
}

bool CallGraphPass::runOnFunction(Function *F) {

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

  // Use InstVisitor to handle instructions
  InstHandler visitor(*this, F);
  visitor.visit(F);

  return false;
}

// Implementation of InstHandler visitor methods
void CallGraphPass::InstHandler::visitReturnInst(ReturnInst &I) {
  if (I.getNumOperands() > 0) {
    Value *rv = I.getOperand(0);
    NodeIndex rvNode = CGP.NF.getValueNodeFor(rv);
    assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
    NodeIndex RT = CGP.NF.getReturnNodeFor(F);
    assert(RT != AndersNodeFactory::InvalidIndex && "Return node not found!");
    CGP.EB.addAssignmentEdges(rvNode, RT);
  }
}

void CallGraphPass::InstHandler::visitCallBase(CallBase &CS) {
  if (CS.isInlineAsm()) return;

  if (Function *CF = CS.getCalledFunction()) {
    // direct call
    auto RCF = CGP.getFuncDef(CF);
    CGP.Ctx->Callees[&CS].insert(RCF);
    CGP.handleCall(&CS, RCF);
  } else {
    // indirect call
    Value *CO = CS.getCalledOperand()->stripPointerCasts();
    // resolve constant expr
    if (auto *CE = dyn_cast<ConstantExpr>(CO)) {
      switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: {
          GEPOperator* GEP = dyn_cast<GEPOperator>(CE);
          CO = GEP->getPointerOperand()->stripPointerCasts();
          break;
        }
        case Instruction::BitCast: {
          CO = CE->getOperand(0);
          break;
        }
        default:
          WARNING("Unhandled constant expression call target: " << *CE << "\n");
      }
    }
    if (Function *CF = dyn_cast<Function>(CO)) {
      // direct call through bitcast
      auto RCF = CGP.getFuncDef(CF);
      CGP.Ctx->Callees[&CS].insert(RCF);
      CGP.handleCall(&CS, RCF);
    } else {
      CGP.funcPts.insert(CO);
      CGP.Ctx->IndirectCallInsts.insert(&CS);
    }
  }
}

void CallGraphPass::InstHandler::visitAllocaInst(AllocaInst &I) {
  // flow insensitive, create derference node for all following loads/stores
  NodeIndex derefNode = CGP.NF.createDereferenceNode(&I);
  CGP.EB.addDereferenceEdges(CGP.NF.getValueNodeFor(&I), derefNode);
}

void CallGraphPass::InstHandler::visitLoadInst(LoadInst &I) {
  NodeIndex valNode = CGP.NF.getValueNodeFor(&I);
  Value *ptr = I.getOperand(0);
  NodeIndex derefNode = CGP.NF.getDereferenceNodeFor(ptr);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    CG_DEBUG("Create deref node for " << *ptr << "\n");
    derefNode = CGP.NF.createDereferenceNode(ptr);
    NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
    assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find load ptr node");
    CGP.EB.addDereferenceEdges(ptrNode, derefNode);
  }
  CGP.EB.addAssignmentEdges(derefNode, valNode);
}

void CallGraphPass::InstHandler::visitStoreInst(StoreInst &I) {
  Value *val = I.getOperand(0);
  if (!val->getType()->isPointerTy()) {
    // XXX only consider pointer type
    return;
  }
  Value *ptr = I.getOperand(1);
  NodeIndex valNode = CGP.NF.getValueNodeFor(val);
  NodeIndex derefNode = CGP.NF.getDereferenceNodeFor(ptr);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    CG_DEBUG("Create deref node for " << *ptr << "\n");
    derefNode = CGP.NF.createDereferenceNode(ptr);
    NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
    assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find store ptr node");
    CGP.EB.addDereferenceEdges(ptrNode, derefNode);
  }
  CGP.EB.addAssignmentEdges(valNode, derefNode);
}

void CallGraphPass::InstHandler::visitGetElementPtrInst(GetElementPtrInst &GEP) {
  Value *ptr = GEP.getPointerOperand();
  NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
  NodeIndex valNode = CGP.NF.getValueNodeFor(&GEP);

#ifndef FILED_SENSITIVE
  CGP.EB.addAssignmentEdges(ptrNode, valNode);
#else
  Type *ptrTy = getElementTy(GEP.getSourceElementType());
  auto itr = CGP.funcPtsGraph.find(ptrNode);
  if (itr != CGP.funcPtsGraph.end()) {
    // if the point2 set of the source ptr is not empty
    for (auto idx = itr->second.find_first(), end = itr->second.getSize();
         idx < end; idx = itr->second.find_next(idx)) {

      CG_LOG("GEP source obj " << idx << ", end = " << end << "\n");
      if (CGP.NF.isSpecialNode(idx)) {
        // special object, e.g., null or univeral
        CGP.funcPtsGraph[valNode].insert(idx);
        continue;
      }

      // check if we need to resize the obj of the ptr
      // get allocated size
      unsigned allocSize = CGP.NF.getObjectSize(idx);
      if (StructType *STy = dyn_cast<StructType>(ptrTy)) {
        const StructInfo* stInfo = CGP.SA.getStructInfo(STy, F->getParent());
        assert(stInfo != NULL && "Struct info not found!");
        unsigned ptrSize = stInfo->getExpandedSize();
        if (ptrSize > allocSize) {
          if (CGP.NF.isOpaqueObject(idx)) {
            // we don't know the allocation size for opaque objects
            CG_LOG("GEP resize obj: " << idx << " to type " << STy->getName() << "\n");
            assert(CGP.NF.isHeapObject(idx) && "GEP: non-heap obj needs to be resized!");
            // resize the obj
            idx = extendObjectSize(idx, STy, CGP.NF, CGP.SA, CGP.funcPtsGraph);
          } else {
            // XXX: this is likely due to passing data as void*
            // lacking context sensitivity, we cannot distinguish them
            // so remove them from the resulting point2 set
            WARNING("GEP non-opaque obj size mismatch: " << idx << " vs type " << STy->getName() << "\n");
            continue;
          }
        }
      }

      // get the field number
      const DataLayout* DL = &(F->getParent()->getDataLayout());
      unsigned fieldNum = 0;
      int64_t offset = getGEPOffset(&GEP, DL);
      if (offset < 0) {
        // FIXME: handle negative offset, like container_of
        WARNING("GEP: " << GEP << " negative offset: " << offset << "\n");
        break;
      } else {
        fieldNum = offsetToFieldNum(GEP.getSourceElementType(), offset, DL, CGP.SA, F->getParent());
      }
      CG_LOG("GEP fieldNum: " << fieldNum << "\n");

      NodeIndex nidx = idx + fieldNum;
      // XXX: corner cases, e.g., struct with varaiable size array
      if ((CGP.NF.getObjectOffset(idx) + fieldNum) > allocSize) {
        WARNING("GEP: field number " << nidx << " out of bound (" << allocSize << ")!");
        nidx = allocSize - 1;
      }

      // propagate the ptr info
      CGP.funcPtsGraph[valNode].insert(nidx);
    }
  }
#endif
}

void CallGraphPass::InstHandler::visitBitCastInst(BitCastInst &I) {
  NodeIndex srcNode = CGP.NF.getValueNodeFor(I.getOperand(0));
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&I);
  assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find bitcast src node");
  CGP.EB.addAssignmentEdges(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitPHINode(PHINode &PHI) {
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&PHI);
  for (unsigned i = 0, e = PHI.getNumIncomingValues(); i != e; ++i) {
    Value *src = PHI.getIncomingValue(i);
    NodeIndex srcNode = CGP.NF.getValueNodeFor(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
    CGP.EB.addAssignmentEdges(srcNode, dstNode);
  }
}

void CallGraphPass::InstHandler::visitSelectInst(SelectInst &I) {
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&I);
  for (unsigned i = 1; i < I.getNumOperands(); i++) {
    Value *src = I.getOperand(i);
    NodeIndex srcNode = CGP.NF.getValueNodeFor(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node");
    CGP.EB.addAssignmentEdges(srcNode, dstNode);
  }
}

void CallGraphPass::InstHandler::visitExtractValueInst(ExtractValueInst &EVI) {
  // field insensitive, just connect the aggregate
  Value *agg = EVI.getAggregateOperand();
  NodeIndex aggNode = CGP.NF.getValueNodeFor(agg);
  NodeIndex valNode = CGP.NF.getValueNodeFor(&EVI);
  assert(aggNode != AndersNodeFactory::InvalidIndex && "Failed to find extractvalue agg node");
  CGP.EB.addAssignmentEdges(aggNode, valNode);
}

void CallGraphPass::InstHandler::visitInsertValueInst(InsertValueInst &IVI) {
  // field insensitive, just connect the aggregate
  Value *agg = IVI.getAggregateOperand();
  Value *val = IVI.getInsertedValueOperand();
  NodeIndex aggNode = CGP.NF.getValueNodeFor(agg);
  NodeIndex valNode = CGP.NF.getValueNodeFor(val);
  NodeIndex resNode = CGP.NF.getValueNodeFor(&IVI);
  assert(aggNode != AndersNodeFactory::InvalidIndex && "Failed to find insertvalue agg node");
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find insertvalue val node");
  CGP.EB.addAssignmentEdges(aggNode, resNode);
  CGP.EB.addAssignmentEdges(valNode, resNode);
}

void CallGraphPass::InstHandler::visitIntToPtrInst(IntToPtrInst &I) {
  // Handle int to ptr conversion - treat as creating a special node
  // Could track the integer value, but for now just mark as unknown
  WARNING("IntToPtr instruction: " << I << "\n");
}

void CallGraphPass::InstHandler::visitPtrToIntInst(PtrToIntInst &I) {
  // Handle ptr to int conversion - lose pointer information
  WARNING("PtrToInt instruction: " << I << "\n");
}

void CallGraphPass::InstHandler::visitVAArgInst(VAArgInst &I) {
  // Handle variable argument access
  WARNING("VAArg instruction: " << I << "\n");
}

void CallGraphPass::InstHandler::visitMemTransferInst(MemTransferInst &I) {
  // MemTransferInst covers memcpy and memmove intrinsics
  CGP.handleMemcpy(&I);
}

void CallGraphPass::InstHandler::visitMemSetInst(MemSetInst &I) {
  // MemSetInst covers memset intrinsics
  // For pointer analysis, memset doesn't transfer pointers, so we can ignore it
  CG_DEBUG("MemSet instruction (ignored for pointer analysis): " << I << "\n");
}

void CallGraphPass::buildEdgesFromPtsGraph(const PtsGraph &ptsGraph) {
  CG_LOG("Building CFL edges from PtsGraph with " << ptsGraph.size() << " entries\n");

  // Process each points-to relationship in the graph
  for (const auto& [srcNode, ptsSet] : ptsGraph) {
    // check the type of srcNode
    // if the srcNode is an object node, it's inserted when processing global initializers
    // which is similar to store val, obj;
    // otherwise, it's a value node, which is address of val = &obj
    if (NF.isObjectNode(srcNode)) {
      // Object node - process as store operation:
      // gv1 = &gobj1; gv2 = &gobj2; *gv1 = gv2;
      // field insensitive, make sure srcNode is base
      if (NF.isSpecialNode(srcNode)) {
        continue;
      }
      auto *src = NF.getValueForNode(srcNode);
      assert(src != NULL && "Failed to find value of srcNode");
      NodeIndex ptr = NF.getValueNodeFor(src);
      assert(ptr != AndersNodeFactory::InvalidIndex && "Failed to find node for src");
      NodeIndex deref = NF.createDereferenceNode(src);
      EB.addDereferenceEdges(ptr, deref);
      for (auto obj = ptsSet.find_first(), end = ptsSet.getSize(); obj < end; obj = ptsSet.find_next(obj)) {
        // field insensitive, make sure obj is base
        NodeIndex addr = obj;
        if (!NF.isSpecialNode(obj)) {
          auto *val = NF.getValueForNode(obj);
          assert(val != NULL && "Failed to find value of obj");
          addr = NF.getValueNodeFor(val);
          assert(addr != AndersNodeFactory::InvalidIndex && "Failed to find node for val");
        }
        EB.addAssignmentEdges(addr, deref);
      }
    } else {
      // Value node - process as address-of operation
      for (auto obj = ptsSet.find_first(), end = ptsSet.getSize(); obj < end; obj = ptsSet.find_next(obj)) {
        // field insensitive, make sure obj is base
        unsigned offset = NF.getObjectOffset(obj);
        NodeIndex objBase = NF.getOffsetObjectNode(obj, -(int)offset);
        EB.addDereferenceEdges(objBase, srcNode);
      }
    }
  }
}

bool CallGraphPass::doInitialization(Module *M) {

  for (auto &GV : M->globals()) {
    if (Ctx->ExtGobjs.find(GV.getGUID()) != Ctx->ExtGobjs.end())
      continue;
    auto init = GV.getInitializer();
    if (!init)
      continue;
    Type *Ty = init->getType();
    // collapse array type
    while (ArrayType *AT = dyn_cast<ArrayType>(Ty))
      Ty = AT->getElementType();
    if (StructType *st = dyn_cast<StructType>(Ty)) {
      const StructInfo *stInfo = SA.getStructInfo(st, M);
      if (stInfo) {
        CG_LOG("Record Global: " << GV.getName() << " : " << getScopeName(st, M) << " = " << stInfo << "\n");
        if (st->isLiteral()) WARNING("Global: " << GV.getName() << " type is literal!\n");
        NodeIndex valNode = NF.getValueNodeFor(&GV);
        globalStructs[stInfo].insert(valNode);
      }
    }
  }

  for (Function &F : *M) {
    // initialize callers
    auto RF = getFuncDef(&F);
    CallInstSet &CIS = Ctx->Callers[RF]; // use RF to retrieve callers
    for (User *U : F.users()) {
      if (CallInst *CI = dyn_cast<CallInst>(U)) {
        if (CI->getCalledFunction() == &F)
          CIS.insert(CI);
      }
    }

    // collect address-taken functions
    if (F.hasAddressTaken()) {
      Ctx->AddressTakenFuncs.insert(&F);

      // only add fval -> fobj edge in call graph analysis?
      NodeIndex valNode = NF.createValueNode(&F);
      NodeIndex objNode = NF.getObjectNodeFor(&F);
      assert(objNode != AndersNodeFactory::InvalidIndex && "Object node not found!");
      funcPtsGraph[valNode].insert(objNode);
      CG_LOG("AddressTaken: " << F.getName() << " : " << valNode << " -> " << objNode << "\n");
    }
  }

  if (M == Ctx->Modules.back().first) {
    // add edges when finishing the last module
    buildEdgesFromPtsGraph(funcPtsGraph);
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee mapping
  for (Function &F : *M) {
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      // map callsite to possible callees
      if (CallInst *CI = dyn_cast<CallInst>(&*i)) {
        if (CI->isInlineAsm())
          continue;
        FuncSet &FS = Ctx->Callees[CI];
        // calculate the caller info here
        for (const Function *CF : FS) {
          CallInstSet &CIS = Ctx->Callers[CF];
          CIS.insert(CI);
        }
        // collect indirect call targets by type
        if (Ctx->IndirectCallInsts.find(CI) != Ctx->IndirectCallInsts.end()) {
          FuncSet &TS = calleeByType[CI];
          findCalleesByType(CI, TS);
        }
      }
    }
  }

  if (M == Ctx->Modules.back().first) {
    // compare callees found by CFL and type matching
    size_t total = 0, match = 0;
    for (auto &it : calleeByType) {
      const CallBase *CS = it.first;
      FuncSet &TS = it.second;
      FuncSet &FS = Ctx->Callees[CS];
      total += TS.size();
      for (const Function *F : TS) {
        if (FS.find(F) != FS.end()) {
          match++;
        } else {
          // not found by CFL
          WARNING("Callee by type not found by CFL: " << F->getName() << " for " << *CS << "\n");
        }
      }
    }
    CG_LOG("Callee by type: total " << total << ", match by CFL " << match << "\n");
    // check if all address-taken functions are used in indirect calls
    size_t used = 0;
    for (const Function *F : Ctx->AddressTakenFuncs) {
      bool found = false;
      for (auto &it : Ctx->Callees) {
        FuncSet &FS = it.second;
        if (FS.find(F) != FS.end()) {
          found = true;
          break;
        }
      }
      if (found) {
        used++;
      } else {
        WARNING("Address-taken function not used in indirect calls: " << F->getName() << "\n");
        // print all users
        for (auto *U : F->users()) {
          if (!isa<Function>(U)) // skip personality
            errs() << "  User: " << *U << "\n";
        }
      }
    }
    CG_LOG("Address-taken functions: total " << Ctx->AddressTakenFuncs.size() << ", used " << used << "\n");
  }

  return false;
}

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  // process functions, only the first iteration
  if (iteration == 0) {
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      runOnFunction(&F);
    }
  }

  bool Changed = false;
  if (M == Ctx->Modules.back().first) {
    // solve CFL constraints after processing the last module
    std::unique_ptr<gracfl::SolverBase> solver = std::make_unique<gracfl::SolverFWGramParallel>(EB.getEdges(), *EB.getGrammar(), 16);
    // std::unique_ptr<gracfl::SolverBase> solver = std::make_unique<gracfl::SolverFWGram>(EB.getEdges(), *EB.getGrammar());
    auto initEdges = solver->getEdgeCount();
    CG_LOG("CFL Init Edges: " << initEdges << "\n");
    solver->runCFL();
    auto finalEdges = solver->getEdgeCount();
    CG_LOG("CFL Final Edges: " << finalEdges << "\n");

    // parse results and update the CFL edges
    std::vector<std::vector<std::unordered_set<unsigned long long>>> outputCFLGraph = solver->getGraph();
    for (auto *CS : Ctx->IndirectCallInsts) {
      CG_LOG("Handle indirect CallSite: " << *CS << "\n");
      Value *fptr = CS->getCalledOperand()->stripPointerCasts();
      NodeIndex fptrNode = NF.getValueNodeFor(fptr);
      if (fptrNode == AndersNodeFactory::InvalidIndex) {
        WARNING("FuncPtr for " << *CS << " node not found!\n");
        continue;
      }
      auto &ptsSet = funcPtsGraph[fptrNode];
      auto &cflSet = outputCFLGraph[fptrNode][EB.getLabelMAs()];
      for (auto idx : cflSet) {
        // CG_LOG("FuncPtr: " << *fptr << " node: " << fptrNode << " -> obj: " << idx << "\n");
        ptsSet.insert(idx);
        if (NF.isSpecialNode(idx)) {
          WARNING("Indirect Call: " << *fptr << " callee is a special node: " << idx << "\n");
          continue;
        }
        const Value *CV = NF.getValueForNode(idx);
        if (CV == NULL) {
          WARNING("No value for function node!\n");
          continue;
        }
        const Function *CF = dyn_cast<Function>(CV);
        if (CF == NULL) {
          // WARNING("Function pointer " << *fptr << " points to non-function: " << *CV << "\n");
          continue;
        }
        // due to field insensitivity, we may have FPs, do a type match
        if (!isCompatible(CS, CF)) {
          // WARNING("Function pointer " << *fptr << " type mismatch: " << *CF << "\n");
          continue;
        }
        if (Ctx->Callees[CS].insert(CF).second) {
          // if new callee added, we need to rerun
          Changed = true;
          CG_LOG("Handle indirect Call: callee: " << CF->getName() << "\n");
          handleCall(CS, CF);
        }
      }
    }
    iteration++;
  }

  return Changed;
}

// debug
void CallGraphPass::dumpFuncPtrs(raw_ostream &OS) {
  for (FuncPtrMap::iterator i = Ctx->FuncPtrs.begin(),
       e = Ctx->FuncPtrs.end(); i != e; ++i) {
    if (i->second.empty())
      continue;
    OS << i->first << "\n";
    FuncSet &v = i->second;
    for (FuncSet::iterator j = v.begin(), ej = v.end();
         j != ej; ++j) {
      OS << "  " << ((*j)->hasInternalLinkage() ? "f" : "F")
         << " " << (*j)->getName().str() << "\n";
    }
  }
}

void CallGraphPass::dumpCallees(raw_ostream &OS) {
  CG_LOG("\n[dumpCallees]\n");
  CG_LOG("Num of Callees: " << Ctx->Callees.size() << "\n");

  size_t empty = 0;
  for (CalleeMap::iterator i = Ctx->Callees.begin(),
       e = Ctx->Callees.end(); i != e; ++i) {

    auto CI = i->first;
    FuncSet &v = i->second;
    // only dump indirect call?
    if (CI->isInlineAsm() || CI->getCalledFunction())
      continue;

    if (v.empty()) {
      empty++;
      continue;
    }

    // OS << "CS:" << *CI << "\n";
    // const DebugLoc &LOC = CI->getDebugLoc();
    // OS << "LOC: ";
    // LOC.print(OS);
    // OS << "^@^";
    std::string prefix = "<" + CI->getParent()->getParent()->getParent()->getName().str() + ">"
      + CI->getParent()->getParent()->getName().str() + "::";
#if 1
    for (FuncSet::iterator j = v.begin(), ej = v.end();
         j != ej; ++j) {
      // OS << "\t" << ((*j)->hasInternalLinkage() ? "f" : "F")
      //    << " " << (*j)->getName() << "\n";
      OS << prefix << *CI << "\t";
      OS << (*j)->getName() << "\n";
    }
#endif
  }

  CG_LOG("[Empty Callees: " << empty << "]\n");
  for (CalleeMap::iterator i = Ctx->Callees.begin(),
       e = Ctx->Callees.end(); i != e; ++i) {
    auto CI = i->first;
    FuncSet &v = i->second;
    if (CI->isInlineAsm() || CI->getCalledFunction())
      continue;
    auto caller = CI->getParent()->getParent();
    if (reachable.find(caller) == reachable.end())
      continue;
    if (v.empty()) {
      OS << "!!EMPTY =>" << *CI << " @@" << caller->getName() << "\n";
      // OS << "Uninitialized function pointer is dereferenced!\n";
      auto &tv = calleeByType[CI];
      if (!tv.empty()) {
        OS << "TypeMatch: ";
        for (auto *F : tv) {
          OS << F->getName() << " ";
        }
        OS << "\n";
      }
    }
  }
  CG_LOG("\n[End of dumpCallees]\n");
}

void CallGraphPass::dumpCallers(raw_ostream &OS) {
  CG_LOG("\n[dumpCallers]\n");
  for (auto M : Ctx->Callers) {
    const Function *F = M.first;
    CallInstSet &CIS = M.second;
    OS << "F : " << getScopeName(F) << "\n";

    for (auto *CI : CIS) {
      const Function *CallerF = CI->getParent()->getParent();
      OS << "\t";
      if (CallerF && CallerF->hasName()) {
        OS << "(" << getScopeName(CallerF) << ") ";
      } else {
        OS << "(anonymous) ";
      }

      OS << *CI << "\n";
    }
  }
  CG_LOG("\n[End of dumpCallers]\n");
}
