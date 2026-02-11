/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2024 - 2026 Chengyu Song
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
#include <llvm/Support/Error.h>
#include <llvm/Support/FormatVariadic.h>

#include <vector>
#include <algorithm>

#include "CallGraph.h"
#include "Annotation.h"

#include "gracfl/include/solvers/Solver.hpp"

#define CG_LOG(stmt) KA_LOG(2, "CallGraph: " << stmt)
#define CG_DEBUG(stmt) KA_LOG(3, "CallGraph: " << stmt)

using namespace llvm;

// Helper to check if we should skip creating edges for a value
static bool shouldSkipValue(const Value *V) {
  if (!V)
    return true;

  // Skip nullptr
  if (isa<ConstantPointerNull>(V))
    return true;

  // Skip compiler-introduced values
  if (isCompilerIntroducedValue(V))
    return true;

  return false;
}

// Helper to check if we should skip creating edges for a function call
static bool shouldSkipFunction(const Function *F) {
  if (!F || !F->hasName())
    return false;

  StringRef name = F->getName();

  // Skip kernel utility functions
  if (isFreeFn(name) || isKernelUtilityFn(name))
    return true;

  return false;
}

Function* CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

// Strip LLVM's numeric suffix (e.g., ".0", ".123") from struct names.
// When linking multiple modules, LLVM appends these suffixes to avoid
// name collisions, but they represent the same C struct type.
static StringRef stripStructNameSuffix(StringRef Name) {
  size_t DotPos = Name.rfind('.');
  if (DotPos == StringRef::npos || DotPos == 0)
    return Name;
  // Only strip if everything after the last '.' is digits
  StringRef Suffix = Name.substr(DotPos + 1);
  if (!Suffix.empty() && Suffix.find_first_not_of("0123456789") == StringRef::npos)
    return Name.substr(0, DotPos);
  return Name;
}

// Walk GEP indexed type chain to find the innermost named struct field access.
// Returns true if a named non-union struct field was found, with structName
// and fieldIdx set to the stripped struct name and field index respectively.
bool CallGraphPass::getGEPStructField(const GEPOperator *GEP,
                                       std::string &structName,
                                       unsigned &fieldIdx) {
  bool found = false;
  Type *CurTy = GEP->getSourceElementType();

  // Skip the first index (pointer/array offset into base type)
  auto idx = GEP->idx_begin();
  if (idx == GEP->idx_end())
    return false;
  ++idx; // skip first index

  while (idx != GEP->idx_end()) {
    if (StructType *STy = dyn_cast<StructType>(CurTy)) {
      ConstantInt *CI = dyn_cast<ConstantInt>(*idx);
      if (!CI)
        break; // non-constant index, give up
      unsigned fIdx = CI->getZExtValue();
      // Record if this is a named, non-union struct
      if (!STy->isLiteral() && STy->hasName() &&
          !LLVM_STRING_STARTS_WITH(STy->getStructName(), "union")) {
        structName = stripStructNameSuffix(STy->getStructName()).str();
        fieldIdx = fIdx;
        found = true;
      }
      if (fIdx < STy->getNumElements())
        CurTy = STy->getElementType(fIdx);
      else
        break;
    } else if (ArrayType *ATy = dyn_cast<ArrayType>(CurTy)) {
      CurTy = ATy->getElementType();
    } else if (VectorType *VTy = dyn_cast<VectorType>(CurTy)) {
      CurTy = VTy->getElementType();
    } else {
      break;
    }
    ++idx;
  }

  return found;
}

bool CallGraphPass::isStructLayoutCompatible(const StructType *ST1,
                                              const StructType *ST2) {
  unsigned numEl = ST1->getNumElements();
  if (numEl != ST2->getNumElements())
    return false;

  for (unsigned i = 0; i < numEl; ++i) {
    if (!isCompatibleType(ST1->getElementType(i), ST2->getElementType(i)))
      return false;
  }
  return true;
}

bool CallGraphPass::isCompatibleType(const Type *T1, const Type *T2) {
  if (T1 == T2) {
      return true;
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
  } else if (T1->isIntegerTy()) {
    // All integer types are compatible (C allows implicit conversions)
    if (T2->isIntegerTy())
      return true;

    return false;
  } else if (T1->isPointerTy()) {
    // All pointer types are compatible (opaque pointers in LLVM 13+,
    // and C allows implicit void* conversions)
    if (T2->isPointerTy())
      return true;

    return false;
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

    // Both literal: compare structurally
    if (ST1->isLiteral() && ST2->isLiteral())
      return isStructLayoutCompatible(ST1, ST2);

    // One literal, one named: not compatible
    if (ST1->isLiteral() != ST2->isLiteral())
      return false;

    // Both named: compare names after stripping LLVM's numeric suffixes
    // (LLVM appends .0, .1, etc. when linking modules with same-named structs)
    StringRef Name1 = stripStructNameSuffix(ST1->getStructName());
    StringRef Name2 = stripStructNameSuffix(ST2->getStructName());
    return Name1.equals(Name2);
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
  if (F->isIntrinsic())
    return false;

  const FunctionType *FTy = F->getFunctionType();
  unsigned NumFixedParams = FTy->getNumParams();
  unsigned NumActualArgs = CS->arg_size();

  // For vararg functions, callsite must provide at least the fixed parameters
  if (FTy->isVarArg()) {
    if (NumActualArgs < NumFixedParams)
      return false;
  } else {
    // For non-vararg, require exact argument count match
    if (NumActualArgs != NumFixedParams)
      return false;
  }

  // Return type: if the callsite result is unused, accept any return type.
  // Otherwise require compatibility.
  if (!CS->use_empty() && !CS->getType()->isVoidTy()) {
    if (!isCompatibleType(F->getReturnType(), CS->getType()))
      return false;
  }

  // Type matching on the fixed parameters
  auto AI = CS->arg_begin();
  for (unsigned i = 0; i < NumFixedParams; ++i, ++AI) {
    Type *FormalTy = FTy->getParamType(i);
    Type *ActualTy = (*AI)->getType();

    if (!isCompatibleType(FormalTy, ActualTy))
      return false;
  }

  return true;
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
  // field-insensitive: *dst = *src
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

  return false;
}

bool CallGraphPass::handleCall(const CallBase *CS, const Function *CF) {
  if (CF->isIntrinsic()) {
    // handle intrinsic functions
    return false;
  }

  // Skip kernel utility functions to reduce edge explosion
  if (shouldSkipFunction(CF)) {
    CG_DEBUG("Skipping kernel utility function: " << CF->getName() << "\n");
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
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      if (shouldSkipValue(arg)) {
        CG_DEBUG("Skipping compiler-introduced argument: " << *arg << "\n");
        continue;
      }
      NodeIndex argNode = NF.getValueNodeFor(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      EB.addAssignmentEdges(argNode, formalNode);
    }
  } else {
    // Only match up to the number of formal parameters; extra actual
    // arguments at the callsite are ignored (permitted by permissive matching).
    unsigned numFormals = CF->arg_size();
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      if (shouldSkipValue(arg)) {
        CG_DEBUG("Skipping compiler-introduced argument: " << *arg << "\n");
        continue;
      }
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
    // The callsite may not have a value node if it discards the return value
    // (e.g., void-typed callsite matched via permissive isCompatible)
    NodeIndex callNode = NF.getValueNodeFor(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      EB.addAssignmentEdges(retNode, callNode);
  }

  return false;
}

bool CallGraphPass::removeCallEdges(const CallBase *CS, const Function *CF) {
  assert(!CF->isIntrinsic() && "Intrinsic function should not be here!");

  // handle args
  unsigned numArgs = CS->arg_size();
  unsigned numFormals = CF->arg_size();
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
    // Only iterate over the minimum of actual and formal args
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
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
    if (callNode != AndersNodeFactory::InvalidIndex)
      EB.removeAssignmentEdges(retNode, callNode);
  }

  return false;
}

bool CallGraphPass::runOnFunction(Function *F) {

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

  for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
    const Instruction *I = &*itr;
    if (I->getType()->isPointerTy()) {
      NF.createValueNode(I);
    }
    if (const ReturnInst *RI = dyn_cast<ReturnInst>(I))
      Ctx->RetSites[F] = RI;

    if (const CallBase *CB = dyn_cast<CallBase>(I)) {
      if (const Function *CF = CB->getCalledFunction()) {
        int size, flag;
        if (isAllocFn(CF->getName(), &size, &flag))
          Ctx->AllocSites.insert(CB);
      }
    }
  }

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

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(rv)) {
      CG_DEBUG("Skipping return value: " << *rv << "\n");
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
  if (CS.isInlineAsm()) return; // FIXME handle inline assembly
  if (CGP.Ctx->AllocSites.count(&CS)) {
    // record allocation sites
    CGP.AllocSites.insert(CGP.NF.getValueNodeFor(&CS));
    return; // skip allocation sites
  }

  // Check for function pointer cycles
  if (!CS.getCalledFunction()) {
    Value *CO = CS.getCalledOperand()->stripPointerCasts();
    if (auto *Load = dyn_cast<LoadInst>(CO)) {
      CG_DEBUG("Indirect call through loaded function pointer: " << *Load->getPointerOperand() << "\n");
    }
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
    } else if (auto *IF = dyn_cast<GlobalIFunc>(CO)) {
      auto it = CGP.IFuncTargets.find(IF);
      if (it != CGP.IFuncTargets.end()) {
        for (const Function *CF : it->second) {
          CGP.Ctx->Callees[&CS].insert(CF);
          CGP.handleCall(&CS, CF);
          CG_LOG("IFunc call: " << IF->getName() << " -> " << CF->getName() << "\n");
        }
      } else {
        CG_DEBUG("IFunc call: " << IF->getName() << " has no resolved targets\n");
      }
    } else {
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

  // Skip nullptr and compiler-introduced values
  if (shouldSkipValue(val)) {
    CG_DEBUG("Skipping value in Store: " << *val << "\n");
    return;
  }

  // Check for potential linked data structure patterns
  if (auto *GEP = dyn_cast<GetElementPtrInst>(val)) {
    auto *ptrOp = GEP->getPointerOperand();
    if (auto *Load = dyn_cast<LoadInst>(ptrOp)) {
      // Pattern: store GEP(load(ptr)), ptr - typical linked list cycle
      CG_DEBUG("Potential linked structure cycle: store GEP(load(" << *Load->getPointerOperand()
               << ")), " << *I.getPointerOperand() << "\n");
    }
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

  // Record struct field store for field-aware indirect call filtering.
  // Strip pointer casts (bitcasts) to see through patterns like:
  //   %gep = getelementptr %struct, %ptr, 0, 7
  //   %bc  = bitcast %gep to <other_type>*
  //   store %val, %bc
  if (auto *GEP = dyn_cast<GEPOperator>(ptr->stripPointerCasts())) {
    std::string sName;
    unsigned fIdx;
    if (CGP.getGEPStructField(GEP, sName, fIdx))
      CGP.fieldStoreRecords.push_back({valNode, sName, fIdx});
  }
}

void CallGraphPass::InstHandler::visitGetElementPtrInst(GetElementPtrInst &GEP) {
  Value *ptr = GEP.getPointerOperand();
  NodeIndex ptrNode = CGP.NF.getValueNodeFor(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find GEP ptr node");
  NodeIndex valNode = CGP.NF.getValueNodeFor(&GEP);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find GEP value node");

  CGP.EB.addAssignmentEdges(ptrNode, valNode);
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

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in PHI: " << *src << "\n");
      continue;
    }

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

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in Select: " << *src << "\n");
      continue;
    }

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
  bool resultIsPtr = EVI.getType()->isPointerTy();

  // Check if the aggregate operand already has tracked pointer content.
  // Skip constants (undef, zeroinitializer, etc.) — they map to ConstantIntIndex
  // which doesn't carry useful pointer information.
  Value *agg = EVI.getAggregateOperand();
  NodeIndex aggNode = AndersNodeFactory::InvalidIndex;
  if (!isa<Constant>(agg))
    aggNode = CGP.NF.getValueNodeFor(agg);

  // Nothing to track if the result isn't a pointer and the aggregate
  // has no tracked pointer content to propagate through nested extracts
  if (!resultIsPtr && aggNode == AndersNodeFactory::InvalidIndex)
    return;

  // field insensitive, just connect the aggregate
  NodeIndex valNode = CGP.NF.getValueNodeFor(&EVI);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.NF.createValueNode(&EVI);

  if (aggNode != AndersNodeFactory::InvalidIndex)
    CGP.EB.addAssignmentEdges(aggNode, valNode);
}

void CallGraphPass::InstHandler::visitInsertValueInst(InsertValueInst &IVI) {
  // field insensitive, just connect the aggregate
  Value *val = IVI.getInsertedValueOperand();
  bool valIsPtr = val->getType()->isPointerTy();

  // Check if the aggregate operand already has tracked pointer content
  // (e.g., from a prior insertvalue that inserted a pointer).
  // Skip constants (undef, zeroinitializer, etc.) — they map to ConstantIntIndex
  // which doesn't carry useful pointer information.
  Value *agg = IVI.getAggregateOperand();
  NodeIndex aggNode = AndersNodeFactory::InvalidIndex;
  if (!isa<Constant>(agg))
    aggNode = CGP.NF.getValueNodeFor(agg);

  // Nothing to track if the inserted value isn't a pointer and the aggregate
  // has no tracked pointer content
  if (!valIsPtr && aggNode == AndersNodeFactory::InvalidIndex)
    return;

  NodeIndex resNode = CGP.NF.getValueNodeFor(&IVI);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.NF.createValueNode(&IVI);

  // Propagate aggregate's pointer content to result
  if (aggNode != AndersNodeFactory::InvalidIndex)
    CGP.EB.addAssignmentEdges(aggNode, resNode);

  // Propagate inserted value if it's a pointer
  if (valIsPtr) {
    NodeIndex valNode = CGP.NF.getValueNodeFor(val);
    assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find insertvalue val node");
    CGP.EB.addAssignmentEdges(valNode, resNode);
  }
}

void CallGraphPass::InstHandler::visitIntToPtrInst(IntToPtrInst &I) {
  NodeIndex srcNode = CGP.NF.getValueNodeFor(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    WARNING("IntToPtr: src node not found: " << I << "\n");
    return;
  }
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    WARNING("IntToPtr: dst node not found: " << I << "\n");
    return;
  }
  CG_DEBUG("IntToPtr: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.EB.addAssignmentEdges(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitPtrToIntInst(PtrToIntInst &I) {
  NodeIndex srcNode = CGP.NF.getValueNodeFor(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    WARNING("PtrToInt: src node not found: " << I << "\n");
    return;
  }
  NodeIndex dstNode = CGP.NF.getValueNodeFor(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.NF.createValueNode(&I);
    CG_DEBUG("PtrToInt: created value node " << dstNode << " for " << I << "\n");
  }
  CG_DEBUG("PtrToInt: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.EB.addAssignmentEdges(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitVAArgInst(VAArgInst &I) {
  if (!I.getType()->isPointerTy())
    return;

  NodeIndex valNode = CGP.NF.getValueNodeFor(&I);
  if (valNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: result node not found: " << I << "\n");
    return;
  }

  Function *F = I.getParent()->getParent();
  NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
  if (varargNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: vararg node not found for function: " << F->getName() << "\n");
    return;
  }

  CG_DEBUG("VAArg: " << F->getName() << ": vararg node " << varargNode
           << " -> val node " << valNode << " for " << I << "\n");
  CGP.EB.addAssignmentEdges(varargNode, valNode);
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

// Process global variable initializer in field-insensitive way
void CallGraphPass::processInitializer(NodeIndex ptrNode, Constant *init,
                                        const std::string &enclosingStruct,
                                        int enclosingFieldIdx) {
  if (!init)
    return;

  // Skip nullptr - don't create edges for null assignments
  if (isa<ConstantPointerNull>(init)) {
    CG_DEBUG("Skipping nullptr in initializer\n");
    return;
  }

  // Skip compiler-introduced values in initializers
  if (shouldSkipValue(init)) {
    CG_DEBUG("Skipping compiler value in initializer: " << *init << "\n");
    return;
  }

  if (isa<GlobalVariable>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &globalvar: add assignment edges globalvar_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    // Record field store if enclosing struct is known
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      fieldStoreRecords.push_back({valNode, enclosingStruct, (unsigned)enclosingFieldIdx});
    CG_DEBUG("add CFL assignment edges for global variable " << cast<GlobalVariable>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (isa<Function>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &function: add assignment edges function_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    // Record direct function store into struct field
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      funcFieldStores[cast<Function>(init)].insert({enclosingStruct, (unsigned)enclosingFieldIdx});
    CG_DEBUG("add CFL assignment edges for function " << cast<Function>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (ConstantArray *CA = dyn_cast<ConstantArray>(init)) {
    // Field-insensitive: all array elements assign to the same ptr
    for (unsigned i = 0; i != CA->getNumOperands(); ++i) {
      processInitializer(ptrNode, CA->getOperand(i), enclosingStruct, enclosingFieldIdx);
    }
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(init)) {
    // Field-insensitive: all struct fields assign to the same ptr
    StructType *STy = CS->getType();
    for (unsigned i = 0; i != CS->getNumOperands(); ++i) {
      std::string curStruct = enclosingStruct;
      int curField = enclosingFieldIdx;
      if (STy && !STy->isLiteral() && STy->hasName() &&
          !LLVM_STRING_STARTS_WITH(STy->getStructName(), "union")) {
        curStruct = stripStructNameSuffix(STy->getStructName()).str();
        curField = i;
      }
      processInitializer(ptrNode, CS->getOperand(i), curStruct, curField);
    }
  } else if (ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(init)) {
    Type *Ty = CAZ->getType();
    if (isa<ArrayType>(Ty) || isa<VectorType>(Ty)) {
      processInitializer(ptrNode, CAZ->getSequentialElement(), enclosingStruct, enclosingFieldIdx);
    } else if (StructType *CSTy = dyn_cast<StructType>(Ty)) {
      for (unsigned i = 0; i != CSTy->getNumElements(); ++i) {
        std::string curStruct = enclosingStruct;
        int curField = enclosingFieldIdx;
        if (!CSTy->isLiteral() && CSTy->hasName() &&
            !LLVM_STRING_STARTS_WITH(CSTy->getStructName(), "union")) {
          curStruct = stripStructNameSuffix(CSTy->getStructName()).str();
          curField = i;
        }
        Constant *elem = CAZ->getStructElement(i);
        processInitializer(ptrNode, elem, curStruct, curField);
      }
    }
  } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(init)) {
    switch (CE->getOpcode()) {
      case Instruction::GetElementPtr: {
        // Field-insensitive: get the base pointer with casts stripped
        const GEPOperator *GEPOp = cast<GEPOperator>(CE);
        const Value* basePtr = GEPOp->getPointerOperand()->stripPointerCasts();
        NodeIndex baseNode = NF.getValueNodeFor(basePtr);
        if (baseNode == AndersNodeFactory::InvalidIndex) {
          baseNode = NF.createValueNode(basePtr);
        }
        // ptr = base_ptr: add assignment edges base_ptr -> ptr
        EB.addAssignmentEdges(baseNode, ptrNode);
        // Check if GEP accesses a struct field, update enclosing info
        std::string gepStruct;
        unsigned gepField;
        if (getGEPStructField(GEPOp, gepStruct, gepField))
          fieldStoreRecords.push_back({baseNode, gepStruct, gepField});
        break;
      }
      case Instruction::BitCast: {
        // BitCast: process the operand directly
        processInitializer(ptrNode, CE->getOperand(0), enclosingStruct, enclosingFieldIdx);
        break;
      }
      case Instruction::IntToPtr: {
        // ptr = (ptr)int: add assignment edges constantInt -> ptr
        // EB.addAssignmentEdges(NF.getConstantIntNode(), ptrNode);
        break;
      }
      default:
        CG_DEBUG("Unhandled constant expression: " << *init << "\n");
    }
  }
}

void CallGraphPass::processCtorsDtors(Module *M) {
  for (StringRef Name : {"llvm.global_ctors", "llvm.global_dtors"}) {
    GlobalVariable *GV = M->getGlobalVariable(Name);
    if (!GV || !GV->hasInitializer())
      continue;
    ConstantArray *CA = dyn_cast<ConstantArray>(GV->getInitializer());
    if (!CA)
      continue;
    for (auto &Op : CA->operands()) {
      if (isa<ConstantAggregateZero>(Op))
        continue;
      ConstantStruct *CS = cast<ConstantStruct>(Op);
      // Operand 1 is the function pointer
      if (Function *F = dyn_cast<Function>(CS->getOperand(1))) {
        auto *RF = getFuncDef(F);
        if (Ctx->CtorDtorFuncs.insert(RF).second)
          CG_LOG("CtorDtor: " << Name << " -> " << RF->getName() << "\n");
      }
    }
  }
}

void CallGraphPass::collectIFuncTargets(const GlobalIFunc *IF) {
  Function *Resolver = const_cast<GlobalIFunc*>(IF)->getResolverFunction();
  if (!Resolver || Resolver->isDeclaration()) {
    CG_DEBUG("IFunc: " << IF->getName() << " resolver not available\n");
    return;
  }
  FuncSet &Targets = IFuncTargets[IF];
  for (auto &BB : *Resolver) {
    if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
      if (!RI->getReturnValue())
        continue;
      Value *RV = RI->getReturnValue()->stripPointerCasts();
      if (auto *F = dyn_cast<Function>(RV)) {
        Targets.insert(getFuncDef(F));
      } else if (auto *LI = dyn_cast<LoadInst>(RV)) {
        // Handle pattern: store @func, %alloca; ... %rv = load %alloca; ret %rv
        Value *Ptr = LI->getPointerOperand();
        for (User *U : Ptr->users()) {
          if (auto *SI = dyn_cast<StoreInst>(U)) {
            if (SI->getPointerOperand() == Ptr) {
              if (auto *F = dyn_cast<Function>(SI->getValueOperand()->stripPointerCasts()))
                Targets.insert(getFuncDef(F));
            }
          }
        }
      }
    }
  }
  CG_LOG("IFunc: " << IF->getName() << " resolved via " << Resolver->getName()
         << " to " << Targets.size() << " target(s)\n");
  for (const Function *T : Targets)
    CG_LOG("  IFunc target: " << T->getName() << "\n");
}

bool CallGraphPass::doInitialization(Module *M) {

  for (auto &GV : M->globals()) {
    if (Ctx->ExtGobjs.find(GV.getGUID()) != Ctx->ExtGobjs.end())
      continue;
    if (GV.isDeclaration())
      continue;

    // Skip compiler-introduced globals
    if (shouldSkipValue(&GV)) {
      CG_DEBUG("Skipping compiler-introduced global: " << GV.getName() << "\n");
      continue;
    }

    NF.createValueNode(&GV);
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
      (void)valNode;
    }

    if (!F.isDeclaration() && !F.isIntrinsic() && !F.empty()) {
      // AllocFuncs is empty when skipping populating nodes
      int size = 0, flag = 0;
      if (isAllocFn(F.getName(), &size, &flag)) {
        Ctx->AllocFuncs.insert(&F);
      } else if (F.getReturnType()->isPointerTy()) {
        // collect pointer returning functions
        PtrReturnFuncs.push_back(&F);
      }
      
      // create nodes for function arguments and return value
      if (F.getFunctionType()->isVarArg())
        NF.createVarargNode(&F);
      for (auto &arg : F.args()) {
        NF.createValueNode(&arg);
      }
      if (!F.getReturnType()->isVoidTy()) {
        NF.createReturnNode(&F);
      }
    }
  }

  // Collect global constructors/destructors
  processCtorsDtors(M);

  // Collect ifunc resolver targets
  for (const GlobalIFunc &IF : M->ifuncs())
    collectIFuncTargets(&IF);

  if (M == Ctx->Modules.back().first) {
    for (auto const &itr: Ctx->ExtGobjs) {
      NF.createValueNode(itr.second);
    }
    for (auto const &itr: Ctx->ExtFuncs) {
      if (!itr.second->getReturnType()->isVoidTy())
        NF.createReturnNode(itr.second);
    }
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
        // update edge
        for (auto const& U : F->users()) {
          if (const CallBase *CI = dyn_cast<CallBase>(U)) {
            if (CI->getCalledFunction() == F) {
              NodeIndex callNode = NF.getValueNodeFor(CI);
              assert(callNode != AndersNodeFactory::InvalidIndex && "CallBase node not found for candidate alloc func!");
              Ctx->AllocSites.insert(CI);
              AllocSites.insert(callNode);
              // remove call edges
              removeCallEdges(CI, F);
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

void CallGraphPass::buildFieldStoreMap(cfl_result_t &outputCFLGraph) {
  unsigned labelV = EB.getLabelV();
  size_t funcFieldPairs = 0;

  for (const auto &rec : fieldStoreRecords) {
    // For each store record, query the CFL V-relation to find which
    // function value nodes V-reach the stored value node
    if (rec.valNode >= outputCFLGraph.size())
      continue;
    auto &cflSet = outputCFLGraph[rec.valNode][labelV];
    for (auto idx : cflSet) {
      if (NF.isSpecialNode(idx))
        continue;
      const Value *CV = NF.getValueForNode(idx);
      if (!CV)
        continue;
      const Function *F = dyn_cast<Function>(CV);
      if (!F)
        continue;
      if (funcFieldStores[F].insert({rec.structName, rec.fieldIdx}).second)
        funcFieldPairs++;
    }
  }

  CG_LOG("FieldStore map: " << fieldStoreRecords.size() << " records, "
         << funcFieldPairs << " function-field pairs, "
         << funcFieldStores.size() << " distinct functions\n");
}

void CallGraphPass::queryAllocatorCandidatesWithLLM() {
  if (!LLM || PtrReturnFuncs.empty())
    return;

  const StringRef SystemPrompt = "You classify allocator-like functions conservatively.";
  std::string UserPrompt;
  raw_string_ostream PromptOS(UserPrompt);
  PromptOS << "Given function declarations only (no bodies), identify likely custom allocator functions.\n";
  PromptOS << "Return strict JSON only in this format: {\"candidates\":[\"func_name1\",\"func_name2\"]}\n";
  PromptOS << "Only include names from the provided list.\n\n";
  PromptOS << "Declarations:\n";
  for (const Function *F : PtrReturnFuncs) {
    std::string FuncTy;
    raw_string_ostream FOS(FuncTy);
    FOS << *F->getFunctionType();
    FOS.flush();
    PromptOS << "- " << F->getName() << " : " << FuncTy << "\n";
  }
  PromptOS.flush();
  CG_DEBUG("LLM allocator query system prompt:\n" << SystemPrompt << "\n");
  CG_DEBUG("LLM allocator query user prompt:\n" << UserPrompt << "\n");

  auto Resp = LLM->requestJSON(
      SystemPrompt,
      UserPrompt);
  if (!Resp) {
    WARNING("LLM allocator candidate query failed: " << toString(Resp.takeError()) << "\n");
    return;
  }
  std::string RespText;
  raw_string_ostream RespOS(RespText);
  RespOS << formatv("{0}", *Resp);
  RespOS.flush();
  CG_DEBUG("LLM allocator response:\n" << RespText << "\n");

  const json::Array *Candidates = nullptr;
  if (const json::Object *Obj = Resp->getAsObject()) {
    Candidates = Obj->getArray("candidates");
    if (!Candidates)
      Candidates = Obj->getArray("functions");
  } else {
    Candidates = Resp->getAsArray();
  }

  if (!Candidates) {
    WARNING("LLM allocator candidate response missing 'candidates' array\n");
    return;
  }

  size_t Added = 0;
  for (const json::Value &V : *Candidates) {
    std::optional<StringRef> Name = V.getAsString();
    if (!Name)
      continue;
    for (Function *F : PtrReturnFuncs) {
      if (F->getName() == *Name &&
          Ctx->AllocFuncs.count(F) == 0 &&
          Ctx->CandidateAllocFuncs.insert(F).second) {
        Added++;
      }
    }
  }
  CG_LOG("LLM added " << Added << " candidate allocator(s)\n");
}

bool CallGraphPass::handleIndirectCall(cfl_result_t &outputCFLGraph) {
  // resolve indirect calls
  bool Changed = false;
  for (auto *CS : Ctx->IndirectCallInsts) {
    CG_DEBUG("Handle indirect CallSite: " << *CS << " in function "
        << CS->getFunction()->getName() << "\n");
    Value *fptr = CS->getCalledOperand()->stripPointerCasts();
    NodeIndex fptrNode = NF.getValueNodeFor(fptr);
    if (fptrNode == AndersNodeFactory::InvalidIndex) {
      WARNING("FuncPtr for " << *CS << " node not found!\n");
      continue;
    }

    // Extract call-site struct field info: trace through LoadInst → GEP
    std::string callSiteStruct;
    unsigned callSiteFieldIdx = 0;
    bool hasCallSiteField = false;
    if (auto *Load = dyn_cast<LoadInst>(fptr)) {
      Value *loadPtr = Load->getPointerOperand()->stripPointerCasts();
      if (auto *GEP = dyn_cast<GEPOperator>(loadPtr)) {
        hasCallSiteField = getGEPStructField(GEP, callSiteStruct, callSiteFieldIdx);
      }
    }

    auto &cflSet = outputCFLGraph[fptrNode][EB.getLabelV()];
    CG_DEBUG("  fptr node " << fptrNode << " V-set size: " << cflSet.size() << "\n");
    for (auto idx : cflSet) {
      if (NF.isSpecialNode(idx)) {
        WARNING("Indirect Call: " << *CS << " callee is a special node: " << idx << "\n");
        continue;
      }
      // Return nodes and vararg nodes also store Function* as their value,
      // but they represent the return value / vararg slot, not the function
      // pointer itself. Skip them — only true value nodes are function ptrs.
      if (NF.isReturnNode(idx)) {
        // CG_DEBUG("  V-alias node " << idx << ": return node for "
        //          << cast<Function>(NF.getValueForNode(idx))->getName() << "\n");
        continue;
      }
      if (NF.isVarargNode(idx)) {
        // CG_DEBUG("  V-alias node " << idx << ": vararg node for "
        //          << cast<Function>(NF.getValueForNode(idx))->getName() << "\n");
        continue;
      }
      const Value *CV = NF.getValueForNode(idx);
      if (CV == NULL) {
        // CG_DEBUG("  V-alias node " << idx << ": no value\n");
        continue;
      }
      const Function *CF = dyn_cast<Function>(CV);
      if (CF == NULL) {
        // CG_DEBUG("  V-alias node " << idx << ": non-function: " << *CV << "\n");
        continue;
      }
      // due to field insensitivity, we may have FPs, do a type match
      if (!isCompatible(CS, CF)) {
        continue;
      }
      // Struct-field-aware filtering:
      // If we know the call site loads from a specific struct field,
      // and we have positive evidence of which fields this function is
      // stored into, reject if none match.
      if (hasCallSiteField) {
        auto it = funcFieldStores.find(CF);
        if (it != funcFieldStores.end()) {
          const auto &fieldSet = it->second;
          if (fieldSet.find({callSiteStruct, callSiteFieldIdx}) == fieldSet.end()) {
            CG_LOG("FieldFilter: reject " << CF->getName()
                   << " for " << callSiteStruct << " field " << callSiteFieldIdx << "\n");
            continue;
          }
        }
        // If function has no entries in funcFieldStores, keep it (conservative)
      }
      if (Ctx->Callees[CS].insert(CF).second) {
        // if new callee added, we need to rerun
        Changed = true;
        CG_LOG("Handle indirect target: " << CF->getName() << "\n");
        handleCall(CS, CF);
      }
    }
  }

  return Changed;
}

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  // process global initializers and functions, only the first iteration
  if (iteration == 0) {
    for (auto &GV : M->globals()) {
      // Skip compiler-introduced globals
      if (shouldSkipValue(&GV)) {
        CG_DEBUG("Skipping initializer for compiler global: " << GV.getName() << "\n");
        continue;
      }

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

    // query LLM for allocator candidates before processing functions
    if (LLM && M == Ctx->Modules.front().first) {
      CG_LOG("LLM-assisted filtering is enabled.\n");
      queryAllocatorCandidatesWithLLM();
    }

    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty() || Ctx->AllocFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      runOnFunction(&F);
    }
  }

  bool Changed = false;
  if (M == Ctx->Modules.back().first) {
    // Analyze edge and cycle patterns before CFL solving
    CG_LOG("Analyzing constraint graph structure...\n");
    std::vector<std::pair<NodeIndex, size_t>> topNodes;
    EB.analyzeHighDegreeNodes(1000, 20, &topNodes);

    // Examine top nodes
    if (!topNodes.empty()) {
      CG_LOG("Examining top " << topNodes.size() << " high-degree nodes:\n");
      for (const auto& [nodeId, degree] : topNodes) {
        NF.dumpNode(nodeId);
      }
    }

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
    findCustomAllocators(outputCFLGraph);
    // if () {
      // if new allocators found, we need to rerun
      // solver = std::make_unique<gracfl::SolverFWGramParallel>(EB.getEdges(), *EB.getGrammar(), 16);
      // solver->runCFL();
      // outputCFLGraph = solver->getGraph();
    // }

    // build field-store map for struct-field-aware filtering
    buildFieldStoreMap(outputCFLGraph);

    // parse results and update call edges
    Changed |= handleIndirectCall(outputCFLGraph);

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
