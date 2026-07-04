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
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
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

bool CallGraphPass::findCalleesByType(CallInst *CI, FuncSet &FS) {
    CallBase &CS = *CI;
    //errs() << *CI << "\n";
    for (const Function *F : Ctx->AddressTakenFuncs) {

        // just compare known args
        if (F->getFunctionType()->isVarArg()) {
            //errs() << "VarArg: " << F->getName() << "\n";
            //report_fatal_error("VarArg address taken function\n");
        } else if (F->arg_size() != CS.arg_size()) {
            //errs() << "ArgNum mismatch: " << F.getName() << "\n";
            continue;
        } else if (!isCompatibleType(F->getReturnType(), CI->getType())) {
            continue;
        }

        if (F->isIntrinsic()) {
            //errs() << "Intrinsic: " << F.getName() << "\n";
            continue;
        }

        // type matching on args
        bool Matched = true;
        auto AI = CS.arg_begin();
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

        if (Matched)
            FS.insert(F);
    }

    return false;
}

bool CallGraphPass::handleCall(llvm::CallBase *CS, const llvm::Function *CF) {
  if (CF->isIntrinsic())
    return false;

  // assumes CF is the function definition
  if (CF->empty()) {
    // external function, nothing to do
    WARNING("Call: " << CF->getName() << " is empty!\n");
    return false;
  }

  bool Changed = false;

  // handle args
  unsigned numArgs = CS->arg_size();
  if (CF->isVarArg()) {
    NodeIndex formalNode = NF.getVarargNodeFor(CF);
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      NodeIndex argNode = NF.getValueNodeFor(arg);
#if 1
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
      }
      // FIXME: don't do anything for now
#else
      assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      auto itr = funcPtsGraph.find(argNode);
      assert(itr != funcPtsGraph.end() && "Actual argument node not found in the graph!");
      if (funcPtsGraph[formalNode].insert(itr->second) > 0) {
        CG_LOG("VarArg: (" << i << ") " << *CS << " -> " << CF->getName() << "\n");
      }
#endif
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
      auto itr = funcPtsGraph.find(argNode);
      if (itr != funcPtsGraph.end()) {
        Value *farg = CF->getArg(i);
        NodeIndex formalNode = NF.getValueNodeFor(farg);
        assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
        // annotate with func ptr info
        if (funcPtsObj.find(argNode) != funcPtsObj.end()) {
          if (funcPtsObj.insert(formalNode).second) {
            Changed = true;
            collectUsers(farg);
          }
        } else if (funcPtsObj.find(formalNode) != funcPtsObj.end()) {
          Changed |= funcPtsObj.insert(argNode).second;
        }
        // skip arg with type shortcut
        if (typeShortcutsObj.find(formalNode) != typeShortcutsObj.end()) {
          continue;
        }
#if 0
        for (auto idx : itr->second) {
          if (funcPtsGraph[formalNode].insert(idx)) {
            CG_LOG("Arg: (" << i << ") " << idx << " -> " << CF->getName() << "\n");
            Changed = true;
          }
        }
#else
        if (funcPtsGraph[formalNode].insert(itr->second) > 0) {
          CG_LOG("Arg: (" << i << ") " << *CS << " -> " << CF->getName() << "\n");
          Changed = true;
        }
#endif
      }
    }
  }

  // handle return
  if (!CF->getReturnType()->isVoidTy()) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = NF.getValueNodeFor(CS);
    assert(callNode != AndersNodeFactory::InvalidIndex && "Call node not found!");
    // annotate with func ptr info
    if (funcPtsObj.find(retNode) != funcPtsObj.end()) {
      Changed |= funcPtsObj.insert(callNode).second;
    } else if (funcPtsObj.find(callNode) != funcPtsObj.end()) {
      if (funcPtsObj.insert(retNode).second) {
        Changed = true;
        const ReturnInst *RI = Ctx->RetSites[CF];
        if (!RI || RI->getNumOperands() != 1) {
          WARNING("Call: " << CF->getName() << " has invalid return instruction\n");
        } else {
          collectDefs(RI->getOperand(0));
        }
      }
    }
    auto itr = funcPtsGraph.find(retNode);
    if (itr != funcPtsGraph.end()) {
      // if the point2 set of the return is not empty
      // XXX: special handling for returned pts
      for (auto idx : itr->second) {
        // if the obj is a heap obj and has no type, treating the CF as an allocator
        // and create a new heap obj
        if (NF.isHeapObject(idx) && NF.isOpaqueObject(idx) && CF->getName().find("alloc") != StringRef::npos) {
          idx = NF.createOpaqueObjectNode(CS, true);
          WARNING("Call: treating " << CF->getName() << " as an allocator (" << idx << ")\n");
        }
        CG_LOG("Ret: obj = " << idx << "\n");
        Changed |= funcPtsGraph[callNode].insert(idx);
      }
    }
  }

  return Changed;
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
  bool Changed = false;

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;

    // skip non-func ptr related instructions
    if (funcPts.find(I) == funcPts.end())
      continue;

    if (isa<BranchInst>(I) || isa<SwitchInst>(I) || isa<UnreachableInst>(I) ||
        isa<BinaryOperator>(I) || isa<SExtInst>(I) || isa<ZExtInst>(I) ||
        isa<TruncInst>(I) || isa<ICmpInst>(I) || isa<FCmpInst>(I))
      continue;

    CG_LOG("Processing instruction: " << *I << "\n");
    switch (I->getOpcode()) {
    case Instruction::Ret: {
      if (I->getNumOperands() > 0) {
        Value *rv = I->getOperand(0);
        NodeIndex rvNode = NF.getValueNodeFor(rv);
        assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
        NodeIndex RT = NF.getReturnNodeFor(F);
        assert(RT != AndersNodeFactory::InvalidIndex && "Return node not found!");
        // skip for type shortcut
        if (typeShortcutsObj.find(RT) != typeShortcutsObj.end()) {
          break;
        }
        // skip for non-func ptr related
        if (funcPtsObj.find(rvNode) == funcPtsObj.end()) {
          break;
        }
        auto itr = funcPtsGraph.find(rvNode);
        if (itr != funcPtsGraph.end()) {
          // if the point2 set of the return value is not empty
          if (funcPtsGraph[RT].insert(itr->second) > 0) {
            CG_LOG("Ret: " << *I << " <- " << F->getName() << "\n");
            Changed = true;
          }
        }
      }
      break;
    }
    case Instruction::Invoke:
    case Instruction::Call: {
      CallBase *CS = cast<CallBase>(I);
      if (CS->isInlineAsm()) break;
      if (Function *CF = CS->getCalledFunction()) {
        // direct call
        auto RCF = getFuncDef(CF);
        reachable.insert(RCF);
        Ctx->Callees[CS].insert(RCF);
        Changed |= handleCall(CS, RCF);
        break;
      }
      // indirect call
      Value *CO = CS->getCalledOperand();
      NodeIndex callee = NF.getValueNodeFor(CO);
      assert(callee != AndersNodeFactory::InvalidIndex && "Callee node not found!");
      auto itr = funcPtsGraph.find(callee);
      // iterate through all possible callees
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the callee is not empty
        for (auto idx : itr->second) {
          CG_LOG("Indirect Call: callee obj: " << idx << "\n");
          if (NF.isSpecialNode(idx)) {
            WARNING("Indirect Call: " << *CO << " callee is a special node: " << idx << "\n")
            continue;
          }
          assert(NF.isObjectNode(idx) && "Function pointer points to non-object!");
          const Value *CV = NF.getValueForNode(idx);
          if (CV == NULL) {
            WARNING("No value for function node!\n");
            continue;
          }
          Function *CF = dyn_cast<Function>(const_cast<Value*>(CV));
          if (CF == NULL) {
            WARNING("Function pointer " << *CO << " points to non-function: " << *CV << "\n");
            continue;
          }
          reachable.insert(CF);
          Ctx->Callees[CS].insert(CF);
          CG_LOG("Indirect Call: callee: " << CF->getName() << "\n");
          Changed |= handleCall(CS, CF);
        }
      } else {
        CG_LOG("Indirect Call: callee not found in the graph: " << callee << "\n");
        Changed |= funcPtsObj.insert(callee).second;
      }
      break;
    }
    case Instruction::Alloca: {
      // do nothing
      break;
    }
    case Instruction::Load: {
      NodeIndex valNode = NF.getValueNodeFor(I);
      // try apply type shortcuts first
      Type *Ty = I->getType();
      if (PointerType *ptrTy = dyn_cast<PointerType>(Ty)) {
        Type *ElTy = ptrTy->getElementType();
        if (ElTy->isStructTy()) {
          const StructInfo *stInfo = SA.getStructInfo(cast<StructType>(ElTy), F->getParent());
          auto itr = typeShortcuts.find(stInfo);
          if (itr != typeShortcuts.end()) {
            Changed |= funcPtsGraph[valNode].insert(itr->second);
            CG_LOG("Load: apply type shortcut: " << itr->second << "\n");
            collectUsers(I);
            //break;
          }
        }
      }
      // normal handling
      bool isNull = false;
      Value *ptr = I->getOperand(0);
      NodeIndex ptrNode = NF.getValueNodeFor(ptr);
      auto itr = funcPtsGraph.find(ptrNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the source ptr is not empty
        for (auto idx : itr->second) {
          // for every obj the source ptr points to, propagate the ptrs
          CG_LOG("Load: source obj: " << idx << "\n");
          if (idx == NF.getNullObjectNode() && itr->second.getSize() == 1) {
            CG_LOG("Loading from null obj, ptr = " << ptrNode << "\n");
            isNull = true;
            // XXX
            funcPtsGraph[valNode].insert(idx);
            break;
          }
          auto itr2 = funcPtsGraph.find(idx);
          if (itr2 != funcPtsGraph.end()) {
#if 1
            for (auto idx2 : itr2->second) {
              CG_LOG("Load: insert: " << idx2 << "\n");
              Changed |= funcPtsGraph[valNode].insert(idx2);
            }
#else
            Changed |= (funcPtsGraph[valNode].insert(itr2->second) > 0);
#endif
          } else {
            CG_LOG("Load: source obj not found in the graph: " << idx << "\n");
            collectUsers(ptr);
          }
        }
      }
      if (funcPtsObj.find(valNode) != funcPtsObj.end()) {
        if (funcPtsObj.insert(ptrNode).second) {
          Changed = true;
          CG_LOG("Load: source ptr contains func ptr: " << ptrNode << "\n");
          if (funcPtsGraph.find(ptrNode) == funcPtsGraph.end()) {
            Type *ptrTy = ptr->getType();
            CG_LOG("Load: func ptr not found in the graph: " << ptrNode << ", type = " << *ptrTy << "\n");
          }
          collectUsers(ptr);
        }
      }
      break;
    }
    case Instruction::Store: {
      Value *val = I->getOperand(0);
      if (!val->getType()->isPointerTy()) {
        // XXX only consider pointer type
        break;
      }
      Value *ptr = I->getOperand(1);
      NodeIndex valNode = NF.getValueNodeFor(val);
      NodeIndex ptrNode = NF.getValueNodeFor(ptr);
      auto itr = funcPtsGraph.find(valNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the value is not empty, i.e., a ptr
        // for every obj the dst ptr points to, propagate the func ptrs
        auto itr2 = funcPtsGraph.find(ptrNode);
        if (itr2 != funcPtsGraph.end()) {
          for (auto idx : itr2->second) {
            CG_LOG("Store: dst obj: " << idx << "\n");
            if (NF.isSpecialNode(idx)) {
              WARNING("Store: dst obj is a special node: " << idx << "\n")
              continue;
            }
            Changed |= (funcPtsGraph[idx].insert(itr->second) > 0);
          }
        }
      }
      if (funcPtsObj.find(valNode) != funcPtsObj.end()) {
        if (funcPtsObj.insert(ptrNode).second) {
          Changed = true;
          CG_LOG("Store: dest ptr contains func ptr: " << ptrNode << "\n");
          if (funcPtsGraph.find(ptrNode) == funcPtsGraph.end()) {
            Type *ptrTy = ptr->getType();
            CG_LOG("Store: func ptr not found in the graph: " << ptrNode << ", type = " << *ptrTy << "\n");
          }
          collectUsers(ptr);
        }
      }
      break;
    }
    case Instruction::GetElementPtr: {
      GetElementPtrInst *GEP = cast<GetElementPtrInst>(I);
      Value *ptr = GEP->getPointerOperand();
      Type *ptrTy = getElementTy(GEP->getSourceElementType());
      NodeIndex ptrNode = NF.getValueNodeFor(ptr);
      NodeIndex valNode = NF.getValueNodeFor(I);

      auto itr = funcPtsGraph.find(ptrNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the source ptr is not empty
        for (auto idx : itr->second) {

          CG_LOG("GEP source obj " << idx << ", end = " << end << "\n");
          if (NF.isSpecialNode(idx)) {
            // special object, e.g., null or univeral
            Changed |= funcPtsGraph[valNode].insert(idx);
            continue;
          }

          // check if we need to resize the obj of the ptr
          // get allocated size
          unsigned allocSize = NF.getObjectSize(idx);
          if (StructType *STy = dyn_cast<StructType>(ptrTy)) {
            const StructInfo* stInfo = SA.getStructInfo(STy, F->getParent());
            assert(stInfo != NULL && "Struct info not found!");
            unsigned ptrSize = stInfo->getExpandedSize();
            if (ptrSize > allocSize) {
              if (NF.isOpaqueObject(idx)) {
                // we don't know the allocation size for opaque objects
                CG_LOG("GEP resize obj: " << idx << " to type " << STy->getName() << "\n");
                assert(NF.isHeapObject(idx) && "GEP: non-heap obj needs to be resized!");
                // resize the obj
                idx = extendObjectSize(idx, STy, NF, SA, funcPtsGraph);
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
          int64_t offset = getGEPOffset(GEP, DL);
          if (offset < 0) {
            // FIXME: handle negative offset, like container_of
            WARNING("GEP: " << *I << " negative offset: " << offset << "\n");
            break;
          } else {
            fieldNum = offsetToFieldNum(GEP->getSourceElementType(), offset, DL, SA, F->getParent());
          }
          CG_LOG("GEP fieldNum: " << fieldNum << "\n");

          NodeIndex nidx = idx + fieldNum;
          // XXX: corner cases, e.g., struct with varaiable size array
          if ((NF.getObjectOffset(idx) + fieldNum) > allocSize) {
            WARNING("GEP: field number " << nidx << " out of bound (" << allocSize << ")!");
            nidx = allocSize - 1;
          }

          // propagate the ptr info
          Changed |= funcPtsGraph[valNode].insert(nidx);
        }
      }
      if (funcPtsObj.find(valNode) != funcPtsObj.end()) {
        if (funcPtsObj.insert(ptrNode).second) {
          Changed = true;
          CG_LOG("GEP: gep ptr contains func ptr: " << ptrNode << "\n");
          if (funcPtsGraph.find(ptrNode) == funcPtsGraph.end()) {
            Type *ptrTy = ptr->getType();
            CG_LOG("GEP: func ptr not found in the graph: " << ptrNode << ", type = " << *ptrTy << "\n");
          }
        }
      }
      break;
    }
    case Instruction::BitCast: {
      NodeIndex srcNode = NF.getValueNodeFor(I->getOperand(0));
      NodeIndex dstNode = NF.getValueNodeFor(I);
      assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find bitcast src node");
      auto itr = funcPtsGraph.find(srcNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the source ptr is not empty
        Changed |= (funcPtsGraph[dstNode].insert(itr->second) > 0);
      }
      if (funcPtsObj.find(srcNode) != funcPtsObj.end()) {
        if (funcPtsObj.insert(dstNode).second) {
          Changed = true;
          CG_LOG("bitcast: src ptr contains func ptr: " << srcNode << ", type = " << *I->getOperand(0)->getType() << "\n");
        }
      } else if (funcPtsObj.find(dstNode) != funcPtsObj.end()) {
        if (funcPtsObj.insert(srcNode).second) {
          Changed = true;
          CG_LOG("bitcast: dst ptr contains func ptr: " << dstNode << ", type = " << *I->getType() << "\n");
        }
      }
      break;
    }
    case Instruction::PHI: {
      PHINode* PHI = cast<PHINode>(I);
      NodeIndex dstNode = NF.getValueNodeFor(PHI);
      for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i) {
        Value *src = PHI->getIncomingValue(i);
        NodeIndex srcNode = NF.getValueNodeFor(src);
        assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
        auto itr = funcPtsGraph.find(srcNode);
        if (itr != funcPtsGraph.end()) {
          // if the point2 set of the source ptr is not empty
          Changed |= (funcPtsGraph[dstNode].insert(itr->second) > 0);
        }
        if (funcPtsObj.find(srcNode) != funcPtsObj.end()) {
          if (funcPtsObj.insert(dstNode).second) {
            Changed = true;
            CG_LOG("PHI: src ptr contains func ptr: " << srcNode << ", type = " << *src->getType() << "\n");
          }
        } else if (funcPtsObj.find(dstNode) != funcPtsObj.end()) {
          if (funcPtsObj.insert(srcNode).second) {
            Changed = true;
            CG_LOG("PHI: dst ptr contains func ptr: " << dstNode << ", type = " << *PHI->getType() << "\n");
          }
        }
      }
      break;
    }
    case Instruction::Select: {
      NodeIndex dstNode = NF.getValueNodeFor(I);
      for (unsigned i = 1; i < I->getNumOperands(); i++) {
        Value *src = I->getOperand(i);
        NodeIndex srcNode = NF.getValueNodeFor(src);
        assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node");
        auto itr = funcPtsGraph.find(srcNode);
        if (itr != funcPtsGraph.end()) {
          // if the point2 set of the source ptr is not empty
          Changed |= (funcPtsGraph[dstNode].insert(itr->second) > 0);
        }
        if (funcPtsObj.find(srcNode) != funcPtsObj.end()) {
          if (funcPtsObj.insert(dstNode).second) {
            Changed = true;
            CG_LOG("Select: src ptr contains func ptr: " << srcNode << ", type = " << *src->getType() << "\n");
          }
        } else if (funcPtsObj.find(dstNode) != funcPtsObj.end()) {
          if (funcPtsObj.insert(srcNode).second) {
            Changed = true;
            CG_LOG("Select: dst ptr contains func ptr: " << dstNode << ", type = " << *I->getType() << "\n");
          }
        }
      }
      break;
    }
    default: {
      WARNING("Unhandled instruction: " << *I << "\n");
    }
    } // end switch
  }

  return Changed;
}

void CallGraphPass::collectDefs(const Value *V) {
  if (funcPts.insert(V).second == false)
    return;
  NodeIndex valNode = NF.getValueNodeFor(V);
  if (valNode != AndersNodeFactory::InvalidIndex) {
    funcPtsObj.insert(valNode);
  }
  if (const Instruction *I = dyn_cast<Instruction>(V)) {
    for (auto &op : I->operands()) {
      collectDefs(op);
    }
  } else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(V)) {
    collectUsers(GV);
  }
}

void CallGraphPass::collectUsers(const Value *V) {
  if (funcPts.insert(V).second == false)
    return;
  NodeIndex valNode = NF.getValueNodeFor(V);
  if (valNode != AndersNodeFactory::InvalidIndex) {
    funcPtsObj.insert(valNode);
  }
  for (const User *U : V->users()) {
    if (const Instruction *I = dyn_cast<Instruction>(U)) {
      if (const CallInst *CI = dyn_cast<CallInst>(I)) {
        if (CI->getCalledOperand() == V) {
          continue; // not interested in direct call
        }
      }
      if (funcPts.insert(I).second) {
        CG_LOG("Collect User: " << *I << "\n");
        valNode = NF.getValueNodeFor(I);
        assert(valNode != AndersNodeFactory::InvalidIndex && "Value node not found!");
        funcPtsObj.insert(valNode);
        if (const StoreInst *SI = dyn_cast<StoreInst>(I)) {
          const Value *ptr = SI->getPointerOperand();
          collectUsers(ptr);
        }
      }
    } else if (const Constant *C = dyn_cast<Constant>(U)) {
      for (const User *CU : C->users()) {
        if (isa<GlobalVariable>(CU)) {
          CG_LOG("GV with func ptr: " << CU->getName() << "\n");
          NodeIndex objNode = NF.getObjectNodeFor(CU);
          if (objNode != AndersNodeFactory::InvalidIndex) {
            funcPtsObj.insert(objNode);
          }
        }
        collectUsers(CU);
      }
    } else {
      WARNING("Unhandled user type: " << *U << "\n");
    }
  }
}

bool CallGraphPass::doInitialization(Module *M) {

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
      collectUsers(&F);

      // only add fval -> fobj edge in call graph analysis?
      NodeIndex valNode = NF.createValueNode(&F);
      NodeIndex objNode = objNode = NF.getObjectNodeFor(&F);
      assert(objNode != AndersNodeFactory::InvalidIndex && "Object node not found!");
      funcPtsGraph[valNode].insert(objNode);
      funcPtsObj.insert(objNode);
      CG_LOG("AddressTaken: " << F.getName() << " : " << valNode << " -> " << objNode << "\n");
    }

    // reachable?
    if (F.getName().equals("main") || LLVM_STRING_STARTS_WITH(F.getName(), "SyS_")) {
      reachable.insert(&F);
    }

    // type shortcut heuristic?
    Type *retTy = F.getReturnType();
    if (PointerType *ptrTy = dyn_cast<PointerType>(retTy)) {
      Type *ElTy = ptrTy->getElementType();
      if (StructType *STy = dyn_cast<StructType>(ElTy)) {
        CG_LOG("TypeShortcut: function " << F.getName() << ", ret type = " << STy->getName() << "\n");
        const StructInfo *stInfo = SA.getStructInfo(STy, M);
        if (stInfo) {
          NodeIndex retNode = NF.getReturnNodeFor(&F);
          if (retNode != AndersNodeFactory::InvalidIndex)
            retStructs[stInfo].insert(retNode);
        } else {
          WARNING("TypeShortcut: struct info not found for " << STy->getName() << "\n");
        }
      }
    }

    for (auto const &A : F.args()) {
      Type *argTy = A.getType();
      if (PointerType *ptrTy = dyn_cast<PointerType>(argTy)) {
        Type *ElTy = ptrTy->getElementType();
        if (ElTy->isStructTy()) {
          const StructInfo *stInfo = SA.getStructInfo(cast<StructType>(ElTy), M);
          if (stInfo) {
            NodeIndex argNode = NF.getValueNodeFor(&A);
            if (argNode != AndersNodeFactory::InvalidIndex)
              argStructs[stInfo].insert(argNode);
          }
        }
      }
    }

    // scan for indirect calls
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      Instruction *I = &*i;
      if (CallBase *CS = dyn_cast<CallBase>(I)) {
        if (CS->isInlineAsm())
          continue;
        Value *CO = CS->getCalledOperand();
        if (isa<Instruction>(CO) || isa<Argument>(CO)) {
          // indirect call
          funcPts.insert(I);
          collectDefs(CO);
        }
      }
    }
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
        FuncSet &TS = calleeByType[CI];
        findCalleesByType(CI, TS);
      }
    }
  }

  return false;
}

bool CallGraphPass::doModulePass(Module *M) {
  bool Changed = false;

  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  // create type shortcut
  if (typeShortcuts.empty()) {
    // heuristic: create shortcut for struct ptr used as return value and argument
    for (auto const &[stInfo, nodes] : retStructs) {
      auto itr = argStructs.find(stInfo);
      if (itr != argStructs.end()) {
        // create obj nodes
        const StructType *stType = stInfo->getRealType();
        unsigned stSize = stInfo->getExpandedSize();
        NodeIndex obj = NF.createObjectNode(nullptr, stType, stInfo->isFieldUnion(0), true);
        assert(obj != AndersNodeFactory::InvalidIndex && "Failed to create object node!");
        for (unsigned i = 1; i < stSize; ++i)
          NF.createObjectNode(obj, i, stInfo->isFieldUnion(i), true);
        // setup the type shortcut
        typeShortcuts[stInfo] = obj;
        CG_LOG("TypeShortcut: " << stType->getName() << " -> " << obj << "\n");
        // add point2 info
        for (NodeIndex node : nodes) {
          funcPtsGraph[node].insert(obj);
          typeShortcutsObj.insert(node);
          CG_LOG("TypeShortcut: add ret " << node << " -> " << obj << "\n");
          // collect defs
          const Value *V = NF.getValueForNode(node);
          if (V && isa<Function>(V)) {
            const Function *F = cast<Function>(V);
            auto RF = getFuncDef(const_cast<Function*>(F));
            CG_LOG("TypeShortcut: handle function: " << F->getName() << "\n");
            const ReturnInst *RI = Ctx->RetSites[F];
            if (RI && RI->getNumOperands()) {
              collectDefs(RI->getOperand(0));
            }
            // handle callsites
            for (auto const& CI: Ctx->Callers[RF]) {
              CG_LOG("TypeShortcut: handle callsite: " << *CI << "\n");
              collectUsers(CI);
            }
          }
        }
        for (NodeIndex node : itr->second) {
          funcPtsGraph[node].insert(obj);
          typeShortcutsObj.insert(node);
          CG_LOG("TypeShortcut: add " << node << " -> " << obj << "\n");
          // collect users
          const Value *V = NF.getValueForNode(node);
          if (V) collectUsers(V);
        }
      }
    }
  }

  {
    // process gv initializers
    // this is necessary as llvm::Users are per module
    for (auto &GV : M->globals()) {
      // check for function pointer (container)
      if (!GV.hasInitializer())
        continue;
      auto valNode = NF.getValueNodeFor(&GV);
      if (funcPtsObj.find(valNode) != funcPtsObj.end())
        continue;
      auto objNode = NF.getObjectNodeFor(&GV);
      assert(objNode != AndersNodeFactory::InvalidIndex && "Global object node not found!");
      auto objSize = NF.getObjectSize(objNode);
      for (unsigned i = 0; i < objSize; ++i) {
        // collect function pointers
        auto field = objNode + i;
        auto itr = funcPtsGraph.find(field);
        if (itr == funcPtsGraph.end())
          continue;
        // check point2 of each field
        for (auto idx : itr->second) {
          if (funcPtsObj.find(idx) != funcPtsObj.end()) {
            funcPtsObj.insert(field);
          }
        }
        // propage from field to obj
        if (funcPtsObj.find(field) != funcPtsObj.end()) {
          if (funcPtsObj.insert(objNode).second)
            CG_LOG("Function pointer found in global " << GV.getName() << "\n");
        }
      }
      if (funcPtsObj.find(objNode) != funcPtsObj.end()) {
        funcPtsObj.insert(valNode).second;
        collectUsers(&GV);
      }
    }
  }

  {
    // process functions
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      // if (reachable.find(&F) != reachable.end())
      Changed |= runOnFunction(&F);
    }
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

void CallGraphPass::dumpCallees() {
    RES_REPORT("\n[dumpCallees]\n");
    raw_ostream &OS = outs();
    OS << "Num of Callees: " << Ctx->Callees.size() << "\n";
    for (CalleeMap::iterator i = Ctx->Callees.begin(), 
         e = Ctx->Callees.end(); i != e; ++i) {

        auto CI = i->first;
        FuncSet &v = i->second;
        // only dump indirect call?
        if (CI->isInlineAsm() || CI->getCalledFunction() /*|| v.empty()*/)
             continue;

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
            //OS << "\t" << ((*j)->hasInternalLinkage() ? "f" : "F")
            //    << " " << (*j)->getName() << "\n";
            OS << prefix << *CI << "\t";
            OS << (*j)->getName() << "\n";
        }
#endif
        // OS << "\n";

        // v = Ctx->Callees[CI];
        // OS << "Callees: ";
        // for (FuncSet::iterator j = v.begin(), ej = v.end();
        //      j != ej; ++j) {
        //     OS << (*j)->getName() << "::";
        // }
        // OS << "\n";
        if (v.empty()) {
            OS << "!!EMPTY =>" << *CI->getCalledOperand()<<"\n";
            OS<< "Uninitialized function pointer is dereferenced!\n";
        }
    }
    RES_REPORT("\n[End of dumpCallees]\n");
}

void CallGraphPass::dumpCallers() {
    RES_REPORT("\n[dumpCallers]\n");
    for (auto M : Ctx->Callers) {
        const Function *F = M.first;
        CallInstSet &CIS = M.second;
        RES_REPORT("F : " << getScopeName(F) << "\n");

        for (auto *CI : CIS) {
            const Function *CallerF = CI->getParent()->getParent();
            RES_REPORT("\t");
            if (CallerF && CallerF->hasName()) {
                RES_REPORT("(" << getScopeName(CallerF) << ") ");
            } else {
                RES_REPORT("(anonymous) ");
            }

            RES_REPORT(*CI << "\n");
        }
    }
    RES_REPORT("\n[End of dumpCallers]\n");
}
