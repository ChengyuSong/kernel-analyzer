/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2024 - 2025 Chengyu Song
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

#define FIELD_SENSITIVE 1

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

bool CallGraphPass::isCompatibleType(const Type *T1, const Type *T2) {
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
    const StructType *ST1 = cast<StructType>(T1);
    const StructType *ST2 = dyn_cast<StructType>(T2);
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
    const FunctionType *FT1 = cast<FunctionType>(T1);
    const FunctionType *FT2 = dyn_cast<FunctionType>(T2);
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
    errs() << "VarArg: " << F->getName() << "\n";
    //report_fatal_error("VarArg address taken function\n");
    // FIXME: handle vararg function
    return false;
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
    assert(AI != CS->arg_end() && "Argument number mismatch!");
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
  NodeIndex dstNode = NF.getValueNodeFor(dst);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Memcpy dst node not found!");
  // if (dstNode == AndersNodeFactory::InvalidIndex) {
  //   dstNode = NF.createValueNode(dst);
  //   CG_DEBUG("Create value node " << dstNode << " for memcpy dst " << *dst << "\n");
  // }
  NodeIndex srcNode = NF.getValueNodeFor(src);
  assert(srcNode != AndersNodeFactory::InvalidIndex && "Memcpy src node not found!");
  // if (srcNode == AndersNodeFactory::InvalidIndex) {
  //   srcNode = NF.createValueNode(src);
  //   CG_DEBUG("Create value node " << srcNode << " for memcpy src " << *src << "\n");
  // }
#ifndef FIELD_SENSITIVE
  // field insensitive: *dst = *src
  NodeIndex derefDst = NF.getDereferenceNodeFor(dstNode);
  if (derefDst == AndersNodeFactory::InvalidIndex) {
    derefDst = NF.createDereferenceNode(dstNode);
    CG_DEBUG("Create deref node " << derefDst << " for " << *dst << "\n");
    EB.addDereferenceEdges(dstNode, derefDst);
  }
  NodeIndex derefSrc = NF.getDereferenceNodeFor(srcNode);
  if (derefSrc == AndersNodeFactory::InvalidIndex) {
    derefSrc = NF.createDereferenceNode(srcNode);
    CG_DEBUG("Create deref node " << derefSrc << " for " << *src << "\n");
    EB.addDereferenceEdges(srcNode, derefSrc);
  }
  EB.addAssignmentEdges(derefSrc, derefDst);
#else
  //TODO: copy field by field
  WARNING("Field sensitive memcpy not implemented yet: " << *CS << "\n");
#endif

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
  // CG_DEBUG("Call: " << *CS << " -> " << CF->getName() << "\n");

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
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      NodeIndex argNode = NF.getValueNodeFor(arg);
      // assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      if (argNode == AndersNodeFactory::InvalidIndex) {
        argNode = NF.createValueNode(arg);
        CG_DEBUG("Create value node " << argNode << " for Arg " << *arg << "\n");
      }
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = NF.getValueNodeFor(farg);
      assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
      EB.addAssignmentEdges(argNode, formalNode);
    }
  }

  // handle return
  if (CF->getReturnType()->isPointerTy()) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = NF.getValueNodeFor(CS);
    assert(callNode != AndersNodeFactory::InvalidIndex && "Call node not found!");
    EB.addAssignmentEdges(retNode, callNode);
  }

  return false;
}

bool CallGraphPass::removeCallEdges(const CallBase *CS, const Function *CF) {
  assert(!CF->isIntrinsic() && "Intrinsic function should not be here!");

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
      EB.removeAssignmentEdges(argNode, formalNode);
    }
  } else {
    if (numArgs != CF->arg_size()) {
      WARNING("Call argument number mismatch! " << *CS << " -> " << CF->getName() << "\n");
      return false;
    }
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      NodeIndex argNode = NF.getValueNodeFor(arg);
      assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = NF.getValueNodeFor(farg);
      assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
      EB.removeAssignmentEdges(argNode, formalNode);
    }
  }

  // handle return
  if (CF->getReturnType()->isPointerTy()) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = NF.getValueNodeFor(CS);
    assert(callNode != AndersNodeFactory::InvalidIndex && "Call node not found!");
    EB.removeAssignmentEdges(retNode, callNode);
  }

  return false;
}

static inline const Type *getElementTy(const Type *T) {
  while (T) {
    if (const ArrayType *AT = dyn_cast<ArrayType>(T))
      T = AT->getElementType();
    else if (const VectorType *VT = dyn_cast<VectorType>(T))
      T = VT->getElementType();
    else
      break;
  }

  return T;
}

bool CallGraphPass::handleGEP(const GetElementPtrInst *GEP, AndersPtsSet &ptr2set, Module *M) {
  const Type *ptrTy = getElementTy(GEP->getSourceElementType());
  const StructType *STy = dyn_cast<StructType>(ptrTy);
  assert(STy != NULL && "GEP source element type is not struct type!");
  const StructInfo* stInfo = SA.getStructInfo(STy, M);
  assert(stInfo != NULL && "Struct info not found!");

  NodeIndex valNode = NF.getValueNodeFor(GEP);
  assert(valNode != AndersNodeFactory::InvalidIndex && "GEP value node not found!");
  auto &ptsSet = funcPtsGraph[valNode];
  auto &diff = updatedGEPs[valNode];

  // get the field number
  const DataLayout* DL = &(M->getDataLayout());
  unsigned fieldNum = 0;
  int64_t offset = getGEPOffset(GEP, DL);
  if (offset < 0) {
    // FIXME: handle negative offset, like container_of
    WARNING("GEP: " << GEP << " negative offset: " << offset << "\n");
    return false;
  } else {
    fieldNum = offsetToFieldNum(GEP->getSourceElementType(), offset, DL, SA, M);
  }
  CG_DEBUG("GEP offset = " << offset << " fieldNum = " << fieldNum << "\n");

  // iterate through the point2 set of the source ptr
  for (auto idx : ptr2set) {

    CG_DEBUG("GEP source obj " << idx << "\n");
    if (NF.isSpecialNode(idx)) {
      // special object, e.g., null or univeral
      EB.addAssignmentEdges(valNode, idx);
      continue;
    }

    // check if we need to resize the obj of the ptr
    // get allocated size
    unsigned allocSize = NF.getObjectSize(idx);
    unsigned ptrSize = stInfo->getExpandedSize();
    auto *AllocTy = NF.getObjectType(idx);
    assert(AllocTy != nullptr && "GEP: obj type is NULL!");
    if (ptrSize > allocSize) {
      if (NF.isOpaqueObject(idx)) {
        // we don't know the allocation size for opaque objects
        CG_LOG("GEP resize obj: " << idx << " to type " << STy->getName() << "\n");
        assert(NF.isHeapObject(idx) && "GEP: non-heap obj needs to be resized!");
        // resize the obj
        NodeIndex obj = extendObjectSize(idx, STy, NF, SA, funcPtsGraph);
        if (obj == AndersNodeFactory::InvalidIndex) {
          WARNING("GEP: failed to resize obj for " << *GEP << "\n");
          continue;
        }
        CG_LOG("GEP resized new obj: " << obj << "\n");
        reallocated[idx] = obj;
        idx = obj;
        allocSize = ptrSize;
      } else {
        // XXX: this is likely due to passing data as void*
        // lacking context sensitivity, we cannot distinguish them
        // so remove them from the resulting point2 set
        WARNING("GEP non-opaque obj size mismatch: " << idx << " vs type " << STy->getName() << "\n");
        continue;
      }
    } else if (!isCompatibleType(STy, AllocTy)) {
      // incompatible type, likely due to cast
      const StructType *ASTy = dyn_cast<StructType>(AllocTy);
      if (!ASTy) continue; // not struct, skip
      const StructInfo* astInfo = SA.getStructInfo(ASTy, M);
      unsigned off = astInfo->getFieldOffset(NF.getObjectOffset(idx));
      WARNING("GEP incompatible type: " << ASTy->getName() << " vs " << STy->getName() << ", offset = " << off << "\n");
      if (stInfo->getContainer(ASTy, off) != nullptr) {
        CG_LOG("\tcontainer of, proceed\n");
      } else if (allocSize == ptrSize && (ASTy->getName().find(STy->getName()) == 0 || STy->getName().find(ASTy->getName()) == 0)) {
        // likely due to different struct name suffix, e.g., struct.foo vs struct.foo.1
        CG_LOG("\tlikely due to different struct name suffix, proceed\n");
      } else {
        continue;
      }
    }

    NodeIndex nidx = idx + fieldNum;
    // XXX: corner cases, e.g., struct with varaiable size array
    if ((NF.getObjectOffset(idx) + fieldNum) >= allocSize) {
      WARNING("GEP: field number " << nidx << " out of bound (" << allocSize << ")!\n");
      // nidx = allocSize - 1;
      continue;
    }

    // propagate the ptr info
    assert(NF.isObjectNode(nidx) && "GEP points to a non-object node!");
    if (ptsSet.insert(nidx)) {
      NodeIndex deref = NF.createDereferenceNode(nidx);
      EB.addDereferenceEdges(nidx, deref);
      EB.addAssignmentEdges(deref, valNode);
      diff.insert(nidx);
    }
  }

  return false;
}

bool CallGraphPass::runOnFunction(Function *F) {

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

#ifndef FIELD_SENSITIVE
  for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
    const Instruction *I = &*itr;
    if (I->getType()->isPointerTy()) {
      NF.createValueNode(I);
    }
  }
#endif

  // Use InstVisitor to handle instructions
  InstHandler visitor(*this, F);
  visitor.visit(F);

  return false;
}

// Implementation of InstHandler visitor methods
void CallGraphPass::InstHandler::visitReturnInst(ReturnInst &I) {
  if (I.getNumOperands() > 0) {
    Value *rv = I.getOperand(0);
    if (!rv->getType()->isPointerTy()) {
      // XXX only consider pointer type
      return;
    }
    NodeIndex rvNode = CGP.NF.getValueNodeFor(rv);
    assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
    NodeIndex RT = CGP.NF.getReturnNodeFor(F);
    assert(RT != AndersNodeFactory::InvalidIndex && "Return node not found!");
    CGP.EB.addAssignmentEdges(rvNode, RT);
  }
}

void CallGraphPass::InstHandler::visitCallBase(CallBase &CS) {
  if (CS.isInlineAsm()) return;
  if (CGP.Ctx->AllocSites.count(&CS)) {
    // record allocation sites
    CGP.AllocSites.insert(CGP.NF.getValueNodeFor(&CS));
    return; // skip allocation sites
  }

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
  // create a deref node for base ptr of alloca
  NodeIndex ptrNode = CGP.NF.getValueNodeFor(&I);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find alloca node");
  NodeIndex derefNode = CGP.NF.createDereferenceNode(ptrNode);
  CG_DEBUG("Create deref node " << derefNode << " for " << I << "\n");
  CGP.EB.addDereferenceEdges(ptrNode, derefNode);
}

void CallGraphPass::InstHandler::visitLoadInst(LoadInst &I) {
  if (!I.getType()->isPointerTy()) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex valNode = CGP.NF.getValueNodeFor(&I);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find load value node");

  Value *ptr = I.getOperand(0);
  NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find load ptr node");

  NodeIndex derefNode = CGP.NF.getDereferenceNodeFor(ptrNode);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    derefNode = CGP.NF.createDereferenceNode(ptrNode);
    CG_DEBUG("Create deref node " << derefNode << " for " << *ptr << "\n");
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
  NodeIndex valNode = CGP.NF.getValueNodeFor(val);
  // assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find store value node");
  if (valNode == AndersNodeFactory::InvalidIndex) {
    valNode = CGP.NF.createValueNode(val);
    CG_DEBUG("Create value node " << valNode << " for store " << *val << "\n");
  }

  Value *ptr = I.getOperand(1);
  NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find store ptr node");

  NodeIndex derefNode = CGP.NF.getDereferenceNodeFor(ptrNode);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    derefNode = CGP.NF.createDereferenceNode(ptrNode);
    CG_DEBUG("Create deref node " << derefNode << " for " << *ptr << "\n");
    CGP.EB.addDereferenceEdges(ptrNode, derefNode);
  }

  CGP.EB.addAssignmentEdges(valNode, derefNode);
}

void CallGraphPass::InstHandler::visitGetElementPtrInst(GetElementPtrInst &GEP) {
  Value *ptr = GEP.getPointerOperand();
  NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find GEP ptr node");
  NodeIndex valNode = CGP.NF.getValueNodeFor(&GEP);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find GEP value node");

#ifndef FIELD_SENSITIVE
  CGP.EB.addAssignmentEdges(ptrNode, valNode);
#else
  auto *PTy = getElementTy(GEP.getSourceElementType());
  if (!PTy->isStructTy()) {
    // for non-struct type, just do assignment
    CGP.EB.addAssignmentEdges(ptrNode, valNode);
  } else {
    // collect GEPs for later processing
    this->CGP.GEPs.push_back(&GEP);
  }
#endif
}

void CallGraphPass::InstHandler::visitBitCastInst(BitCastInst &I) {
  NodeIndex srcNode = CGP.NF.getValueNodeFor(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    srcNode = CGP.NF.createValueNode(I.getOperand(0));
    CG_DEBUG("Create value node " << srcNode << " for bitcast src " << *(I.getOperand(0)) << "\n");
  }
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&I);
  // assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find bitcast dst node");
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.NF.createValueNode(&I);
    WARNING("Create value node " << dstNode << " for bitcast dst " << I << "\n");
  }
  CGP.EB.addAssignmentEdges(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitPHINode(PHINode &PHI) {
  if (!PHI.getType()->isPointerTy()) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&PHI);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find phi dst node");
  for (unsigned i = 0, e = PHI.getNumIncomingValues(); i != e; ++i) {
    Value *src = PHI.getIncomingValue(i);
    NodeIndex srcNode = CGP.NF.getValueNodeFor(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
    // if (srcNode == AndersNodeFactory::InvalidIndex) {
    //   srcNode = CGP.NF.createValueNode(src);
    //   CG_DEBUG("Create value node " << srcNode << " for PHI src " << *src << "\n");
    // }
    CGP.EB.addAssignmentEdges(srcNode, dstNode);
  }
}

void CallGraphPass::InstHandler::visitSelectInst(SelectInst &I) {
  if (!I.getType()->isPointerTy()) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&I);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find select dst node");
  // NodeIndex dstNode = CGP.NF.createValueNode(&I);
  for (unsigned i = 1; i < I.getNumOperands(); i++) {
    Value *src = I.getOperand(i);
    NodeIndex srcNode = CGP.NF.getValueNodeFor(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node");
    // if (srcNode == AndersNodeFactory::InvalidIndex) {
    //   srcNode = CGP.NF.createValueNode(src);
    //   CG_DEBUG("Create value node " << srcNode << " for select src " << *src << "\n");
    // }
    CGP.EB.addAssignmentEdges(srcNode, dstNode);
  }
}

void CallGraphPass::InstHandler::visitExtractValueInst(ExtractValueInst &EVI) {
  if (!EVI.getType()->isPointerTy()) {
    // XXX only consider pointer type
    return;
  }
  // field insensitive, just connect the aggregate
  Value *agg = EVI.getAggregateOperand();
  NodeIndex aggNode = CGP.NF.getValueNodeFor(agg);
  if (aggNode == AndersNodeFactory::InvalidIndex) {
    aggNode = CGP.NF.createValueNode(agg);
    CG_DEBUG("Create value node " << aggNode << " for ExtractValue " << *agg << "\n");
  }
  NodeIndex valNode = CGP.NF.getValueNodeFor(&EVI);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find extractvalue val node");
  CGP.EB.addAssignmentEdges(aggNode, valNode);
}

void CallGraphPass::InstHandler::visitInsertValueInst(InsertValueInst &IVI) {
  // field insensitive, just connect the aggregate
  Value *val = IVI.getInsertedValueOperand();
  if (!val->getType()->isPointerTy()) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex valNode = CGP.NF.getValueNodeFor(val);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find insertvalue val node");
  // if (valNode == AndersNodeFactory::InvalidIndex) {
  //   valNode = CGP.NF.createValueNode(val);
  //   CG_DEBUG("Create value node " << valNode << " for InsertValue val " << *val << "\n");
  // }
  Value *agg = IVI.getAggregateOperand();
  NodeIndex aggNode = CGP.NF.getValueNodeFor(agg);
  if (aggNode == AndersNodeFactory::InvalidIndex) {
    aggNode = CGP.NF.createValueNode(agg);
    CG_DEBUG("Create value node " << aggNode << " for InsertValue agg " << *agg << "\n");
  }
  NodeIndex resNode = CGP.NF.createValueNode(&IVI);
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

// Build CFL edges from a field-sensitive points-to graph
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
      // field sensitive, we don't have a ptr = &base.src edge yet
      NodeIndex ptr = NF.createDereferenceNode(srcNode);
      EB.addDereferenceEdges(srcNode, ptr);
      NodeIndex deref = NF.createDereferenceNode(ptr);
      EB.addDereferenceEdges(ptr, deref);
      for (auto obj : ptsSet) {
        NodeIndex addr = obj;
        if (!NF.isSpecialNode(obj)) {
          // field sensitive, we don't have a ptr = &base.obj edge yet
          addr = NF.createDereferenceNode(obj);
          EB.addDereferenceEdges(obj, addr);
        }
        EB.addAssignmentEdges(addr, deref);
      }
    } else {
      // Value node - process as address-of operation
      for (auto obj : ptsSet) {
        EB.addDereferenceEdges(obj, srcNode);
      }
    }
  }
}

// Process global variable initializer in field-insensitive way
void CallGraphPass::processInitializer(NodeIndex ptrNode, Constant *init) {
  if (!init)
    return;

  if (isa<ConstantPointerNull>(init)) {
    // ptr = null: add assignment edges null -> ptr
    EB.addAssignmentEdges(NF.getNullPtrNode(), ptrNode);
  } else if (isa<GlobalVariable>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &globalvar: add assignment edges globalvar_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    CG_DEBUG("add CFL assignment edges for global variable " << cast<GlobalVariable>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (isa<Function>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &function: add assignment edges function_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    CG_DEBUG("add CFL assignment edges for function " << cast<Function>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (ConstantArray *CA = dyn_cast<ConstantArray>(init)) {
    // Field-insensitive: all array elements assign to the same ptr
    for (unsigned i = 0; i != CA->getNumOperands(); ++i) {
      processInitializer(ptrNode, CA->getOperand(i));
    }
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(init)) {
    // Field-insensitive: all struct fields assign to the same ptr
    for (unsigned i = 0; i != CS->getNumOperands(); ++i) {
      processInitializer(ptrNode, CS->getOperand(i));
    }
  } else if (ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(init)) {
    Type *Ty = CAZ->getType();
    if (isa<ArrayType>(Ty) || isa<VectorType>(Ty)) {
      processInitializer(ptrNode, CAZ->getSequentialElement());
    } else if (StructType *CSTy = dyn_cast<StructType>(Ty)) {
      for (unsigned i = 0; i != CSTy->getNumElements(); ++i) {
        Constant *elem = CAZ->getStructElement(i);
        processInitializer(ptrNode, elem);
      }
    }
  } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(init)) {
    switch (CE->getOpcode()) {
      case Instruction::GetElementPtr: {
        // Field-insensitive: get the base pointer with casts stripped
        const Value* basePtr = cast<GEPOperator>(CE)->getPointerOperand()->stripPointerCasts();
        NodeIndex baseNode = NF.getValueNodeFor(basePtr);
        if (baseNode == AndersNodeFactory::InvalidIndex) {
          baseNode = NF.createValueNode(basePtr);
        }
        // ptr = base_ptr: add assignment edges base_ptr -> ptr
        EB.addAssignmentEdges(baseNode, ptrNode);
        break;
      }
      case Instruction::BitCast: {
        // BitCast: process the operand directly
        processInitializer(ptrNode, CE->getOperand(0));
        break;
      }
      case Instruction::IntToPtr: {
        // ptr = (ptr)int: add assignment edges constantInt -> ptr
        EB.addAssignmentEdges(NF.getConstantIntNode(), ptrNode);
        break;
      }
      default:
        CG_DEBUG("Unhandled constant expression: " << *init << "\n");
    }
  }
}

bool CallGraphPass::doInitialization(Module *M) {

  for (auto &GV : M->globals()) {
    if (Ctx->ExtGobjs.find(GV.getGUID()) != Ctx->ExtGobjs.end())
      continue;
    if (GV.isDeclaration())
      continue;
#ifndef FIELD_SENSITIVE
    // create a deref node for base ptr of global var
    NF.createValueNode(&GV);
#endif
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
      // create a value node for function pointer
      NodeIndex valNode = NF.createValueNode(&F);
#ifdef FIELD_SENSITIVE
      NodeIndex objNode = NF.getObjectNodeFor(&F);
      assert(objNode != AndersNodeFactory::InvalidIndex && "Object node not found!");
      funcPtsGraph[valNode].insert(objNode);
      CG_LOG("AddressTaken: " << F.getName() << " : " << valNode << " -> " << objNode << "\n");
#endif
    }

    if (!F.isDeclaration() && !F.isIntrinsic() && !F.empty() && !Ctx->AllocFuncs.count(&F)) {
#ifndef FIELD_SENSITIVE
      // create nodes for function arguments and return value
      if (F.getFunctionType()->isVarArg())
        NF.createVarargNode(&F);
      for (auto &arg : F.args()) {
        NF.createValueNode(&arg);
      }
      if (!F.getReturnType()->isVoidTy()) {
        NF.createReturnNode(&F);
      }
#else
      // in field-sensitive mode, allocate func arguments for functions without any uses
      if (F.use_empty() && F.getName() != "LLVMFuzzerTestOneInput") {
        assert(!F.hasAddressTaken() && "Function has address taken but no uses!");
        for (unsigned i = 0; i < F.arg_size(); i++) {
          Argument *arg = F.getArg(i);
          const Type *AT = arg->getType();
          if (AT->isPointerTy()) {
            NodeIndex objNode = NF.createObjectNode(arg, AT, false, true);
            assert(objNode != AndersNodeFactory::InvalidIndex && "Failed to create arg obj node!");
            CG_LOG("Create obj node " << objNode << " for pointer arg " << i << ", type = " << *AT
                   << " of function " << F.getName() << "\n");
            NodeIndex valNode = NF.getValueNodeFor(arg);
            assert(valNode != AndersNodeFactory::InvalidIndex && "Arg value node not found!");
            funcPtsGraph[valNode].insert(objNode);
            EB.addDereferenceEdges(objNode, valNode);
            reallocated.insert({objNode, 0});
          }
        }
      }
#endif
    }
  }

  if (M == Ctx->Modules.back().first) {
#ifndef FIELD_SENSITIVE
    for (auto const &itr: Ctx->ExtGobjs) {
      NF.createValueNode(itr.second);
    }
    for (auto const &itr: Ctx->ExtFuncs) {
      if (!itr.second->getReturnType()->isVoidTy())
        NF.createReturnNode(itr.second);
    }
#else
    // build CFL edges from field-sensitive points-to graph
    buildEdgesFromPtsGraph(funcPtsGraph);
#endif
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee mapping
  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty() || Ctx->AllocFuncs.count(&F))
      continue;

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

bool CallGraphPass::findCustomAllocators(cfl_result_t &outputCFLGraph) {
  bool foundNewAlloc = false;
  FuncSet newAllocFuncs;
  for (auto *F : Ctx->CandidateAllocFuncs) {
    // get return value
    NodeIndex retNode = NF.getReturnNodeFor(F);
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found for candidate alloc func!");
    auto &cflSet = outputCFLGraph[retNode][EB.getLabelV()]; // find the alias set
    for (auto idx : cflSet) {
      if (AllocSites.count(idx)) {
        // if return value is from a known allocation site
        CG_LOG("Custom allocator " << F->getName() << " return value from alloc site: " << idx << "\n");
        Ctx->AllocFuncs.insert(F);
        newAllocFuncs.insert(F);
        foundNewAlloc = true;
        // update edges
        for (auto const& U : F->users()) {
          if (const CallBase *CI = dyn_cast<CallBase>(U)) {
            if (CI->getCalledFunction() == F) {
              NodeIndex callNode = NF.getValueNodeFor(CI);
              assert(callNode != AndersNodeFactory::InvalidIndex && "CallBase node not found for candidate alloc func!");
              Ctx->AllocSites.insert(CI);
              AllocSites.insert(callNode);
              // remove call edges
              removeCallEdges(CI, F);
              // add new edge
              NodeIndex obj = createNodeForHeapObject(CI, 0, 0, NF, SA);
              EB.addDereferenceEdges(callNode, obj);
              CG_LOG("Update custom allocator call: " << *CI << "\n");
            }
          }
        }
        break;
      }
    }
  }

  if (foundNewAlloc) {
    // remove confirmed allocators from candidate set
    for (auto *F : newAllocFuncs) {
      Ctx->CandidateAllocFuncs.erase(F);
    }
  }

  return foundNewAlloc;
}

bool CallGraphPass::handleIndirectCall(cfl_result_t &outputCFLGraph) {
  // resolve indirect calls
  bool Changed = false;
  for (auto *CS : Ctx->IndirectCallInsts) {
    CG_DEBUG("Handle indirect CallSite: " << *CS << "\n");
    Value *fptr = CS->getCalledOperand()->stripPointerCasts();
    NodeIndex fptrNode = NF.getValueNodeFor(fptr);
    if (fptrNode == AndersNodeFactory::InvalidIndex) {
      WARNING("FuncPtr for " << *CS << " node not found!\n");
      continue;
    }
    // auto &ptsSet = funcPtsGraph[fptrNode];
    auto &cflSet = outputCFLGraph[fptrNode][EB.getLabelV()];
    for (auto idx : cflSet) {
      // CG_DEBUG("FuncPtr: node: " << fptrNode << " -> ptr: " << idx << "\n");
      // ptsSet.insert(idx);
      if (NF.isSpecialNode(idx)) {
        WARNING("Indirect Call: " << *CS << " callee is a special node: " << idx << "\n");
        continue;
      }
      const Value *CV = NF.getValueForNode(idx);
      if (CV == NULL) {
        // WARNING("No value for function node!\n");
        continue;
      }
      const Function *CF = dyn_cast<Function>(CV);
      if (CF == NULL) {
        // WARNING("Function pointer " << *fptr << " points to non-function: " << *CV << "\n");
        continue;
      }
      // due to field insensitivity, we may have FPs, do a type match
      if (!isCompatible(CS, CF)) {
        WARNING("Function pointer " << *CS << " type mismatch: " << CF->getName() << "\n");
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

  return Changed;
}

bool CallGraphPass::handleGEP(cfl_result_t &outputCFLGraph, Module *M) {
  // resolve GEPs
  bool Changed = false;
  for (auto *GEP : GEPs) {
    CG_DEBUG("Handle GEP: " << *GEP << " in function " << GEP->getFunction()->getName() << "\n");
    auto *ptr = GEP->getPointerOperand()->stripPointerCasts();
    NodeIndex ptrNode = NF.getValueNodeFor(ptr);
    if (ptrNode == AndersNodeFactory::InvalidIndex) {
      WARNING("GEP ptr for " << *GEP << " node not found!\n");
      continue;
    }
    AndersPtsSet &ptsSet = funcPtsGraph[ptrNode];
    AndersPtsSet &diff = updatedGEPs[ptrNode];
    auto &cflSet = outputCFLGraph[ptrNode][EB.getLabelV()];
    // auto start = std::chrono::high_resolution_clock::now();
    for (auto idx : cflSet) {
      // V gives us the aliasing set, now we need to find the point-to set
      if (idx == ptrNode) continue;
      auto itr = funcPtsGraph.find(idx);
      if (itr != funcPtsGraph.end()) {
        for (auto obj : itr->second) {
          if (ptsSet.insert(obj)) {
            // perform expensive checks only for new targets
            if (NF.isSpecialNode(obj)) {
              WARNING("GEP: " << *GEP << " points to a special node: " << obj << "\n");
              continue;
            } else if (!NF.isObjectNode(obj)) {
              WARNING("GEP: " << *GEP << " points to a non-object node: " << obj << "\n");
              continue;
            }
            // fix obj if its a dummy arg
            auto dit = reallocated.find(obj);
            if (dit != reallocated.end()) {
              if (dit->second != 0) {
                obj = dit->second; // already fixed
              } else {
                // obj is introduced as external arg, no type, need to fix
                auto *objVal = NF.getValueForNode(obj);
                assert(objVal && "No value for dummy arg obj node");
                NF.removeNodeForObject(objVal); // remove old obj node from nodeFactory
                const Type *PTy = GEP->getSourceElementType();
                NodeIndex objNode = createNodeForTypedVal(objVal, PTy, true, NF, SA); // assume heap
                if (objNode != AndersNodeFactory::InvalidIndex) {
                  EB.addDereferenceEdges(objNode, idx);
                  CG_LOG("Create Object Node: " << objNode << " for GEP ptr " << *GEP
                        << ", type = " << *PTy << " for arg node " << obj << "!\n");
                  dit->second = objNode; // update fixed map
                  obj = objNode; // use the new node
                } else {
                  WARNING("Failed to create object node for GEP ptr " << *GEP
                          << ", type = " << *PTy << "\n");
                }
              }
            }
            diff.insert(obj);
          }
        }
      }
    }
    // auto end = std::chrono::high_resolution_clock::now();
    // auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
    // CG_LOG("Time spent in GEP cflSet loop: " << duration << " us\n");
    if (!diff.isEmpty()) {
      handleGEP(GEP, diff, M);
      Changed = true;
      diff.clear();
    }
    assert(diff.isEmpty() && "GEP updated set not empty!");
  }

  return Changed;
}

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  // process functions, only the first iteration
  if (iteration == 0) {
#ifndef FIELD_SENSITIVE
    for (auto &GV : M->globals()) {
      if (GV.hasInitializer()) {
        NodeIndex valNode = NF.getValueNodeFor(&GV);
        assert(valNode != AndersNodeFactory::InvalidIndex && "Global value node not found!");
        NodeIndex deref = NF.createDereferenceNode(valNode);
        EB.addDereferenceEdges(valNode, deref);
        CG_DEBUG("Processing initializer for GV " << GV.getName() << "\n");
        auto init = GV.getInitializer();
        processInitializer(deref, init);
      }
    }
#endif

    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty() || Ctx->AllocFuncs.count(&F))
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

    auto outputCFLGraph = solver->getGraph();

    // handle custom allocators
    if (findCustomAllocators(outputCFLGraph)) {
      // if new allocators found, we need to rerun
      solver = std::make_unique<gracfl::SolverFWGramParallel>(EB.getEdges(), *EB.getGrammar(), 16);
      solver->runCFL();
      outputCFLGraph = solver->getGraph();
    }

    // parse results and update call edges
    Changed |= handleIndirectCall(outputCFLGraph);

#ifdef FIELD_SENSITIVE
    // parse results and update GEP edges
    Changed |= handleGEP(outputCFLGraph, M);
#endif

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

void CallGraphPass::dumpGlobals(raw_ostream &OS) {
  CG_LOG("\n[dumpGlobals]\n");
  std::unique_ptr<gracfl::SolverBase> solver = std::make_unique<gracfl::SolverFWGramParallel>(EB.getEdges(), *EB.getGrammar(), 16);
  solver->runCFL();
  auto outputCFLGraph = solver->getGraph();
  for (auto &it : Ctx->Gobjs) {
    Value *GV = it.second;
    NodeIndex valNode = NF.getValueNodeFor(GV);
    if (valNode != AndersNodeFactory::InvalidIndex) {
      // auto &alledges = outputCFLGraph[valNode];
      // for (size_t i = 0; i < alledges.size(); i++) {
      //   auto &cflSect = alledges[i];
      //   auto label = EB.getGrammar()->getIDToSymbolMap().find(i)->second;
      //   if (cflSect.empty()) continue;
      //   CG_DEBUG("GlobalVar: " << GV->getName() << " : " << valNode << ", label " << label << "\n");
      //   for (auto idx : cflSect) {
      //     if (idx == valNode)
      //       continue;
      //     if (NF.isSpecialNode(idx)) {
      //       CG_DEBUG("\tSpecialNode: " << idx << "\n");
      //       continue;
      //     }
      //     const Value *CV = NF.getValueForNode(idx);
      //     if (CV == NULL) {
      //       CG_DEBUG("\tNoValue: " << idx << "\n");
      //       continue;
      //     }
      //     CG_DEBUG("\t" << *CV << " : " << idx << "\n");
      //   }
      // }
      auto &cflSect = outputCFLGraph[valNode][EB.getLabelV()];
      if (cflSect.empty())
        continue;
      CG_DEBUG("GlobalVar: " << GV->getName() << " : " << valNode << " ->\n");
      for (auto idx : cflSect) {
        if (idx == valNode)
          continue;
        if (NF.isSpecialNode(idx)) {
          CG_DEBUG("\tSpecialNode: " << idx << "\n");
          continue;
        }
        const Value *CV = NF.getValueForNode(idx);
        if (CV == NULL) {
          CG_DEBUG("\tNoValue: " << idx << "\n");
          continue;
        }
        CG_DEBUG("\t" << *CV << " : " << idx << "\n");
      }
    }
  }
  CG_LOG("\n[End of dumpGlobals]\n");
}