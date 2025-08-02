/*
 * Reachability-based Call Graph Analysis
 *
 * Copyrigth (C) 2024 - 2025 Chengyu Song
 * Copyrigth (C) 2024 - 2025 Haochen Zeng
 *
 * For licensing details see LICENSE
 */


#include <llvm/Pass.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/Path.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include <algorithm>
#include <cassert>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <vector>
#include <cstdint>

#include "Reachable.h"
#include "Annotation.h"
#include "PointTo.h"


#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#define RA_LOG(stmt) KA_LOG(2, "Reachable: " << stmt)
#define RA_DEBUG(stmt) KA_LOG(3, "Reachable: " << stmt)

using namespace llvm;

Function* ReachableCallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

// check if T2 and be accepted as T1
bool ReachableCallGraphPass::isCompatibleType(Type *T1, Type *T2) {
  if (T1 == T2) {
      return true;
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
  } else if (T1->isIntegerTy()) {
    // assume pointer can be cased to the address space size
    if (T2->isPointerTy() && T1->getIntegerBitWidth() == T2->getPointerAddressSpace())
      return true;

    // assume all integer type are compatible
    if (T2->isIntegerTy() && T2->getIntegerBitWidth() == T1->getIntegerBitWidth())
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

    // check if both are packed
    if (ST1->isPacked() != ST2->isPacked()) {
      return false;
    }

    // check for literal struct
    if (ST1->isLiteral() != ST2->isLiteral()) {
      return false;
    }

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
    WARNING("Unhandled Types:" << *T1 << " :: " << *T2 << "\n");
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool ReachableCallGraphPass::findCalleesByType(CallBase *CB, FuncSet &FS) {
    bool Changed = false;
    RA_DEBUG("Handle indirect call: " << *CB << "\n");
    for (const Function *F : Ctx->AddressTakenFuncs) {
      // just compare known args
      if (F->getFunctionType()->isVarArg()) {
        //errs() << "VarArg: " << F->getName() << "\n";
        WARNING("VarArg address taken function\n");
        continue;
      } else if (F->arg_size() != CB->arg_size()) {
        RA_DEBUG("ArgNum mismatch: " << F->getName() << "\n");
        continue;
      } else if (!isCompatibleType(CB->getType(), F->getReturnType())) {
        RA_DEBUG("Return type mismatch: " << F->getName() << "\n");
        continue;
      }

      if (F->isIntrinsic()) {
        //errs() << "Intrinsic: " << F.getName() << "\n";
        continue;
      }

      // type matching on args
      bool Matched = true;
      auto AI = CB->arg_begin();
      for (auto FI = F->arg_begin(), FE = F->arg_end(); FI != FE; ++FI, ++AI) {
        // check type mis-match
        Type *FormalTy = FI->getType();
        Type *ActualTy = (*AI)->getType();

        if (isCompatibleType(FormalTy, ActualTy))
          continue;
        else {
          RA_DEBUG("ArgType mismatch: " << F->getName() << " " << *FormalTy << " :: " << *ActualTy << "\n");
          Matched = false;
          break;
        }
      }

      if (Matched) {
        RA_DEBUG("Matched: " << F->getName() << "\n");
        Changed |= FS.insert(F).second;
      }
    }

    return Changed;
}

bool ReachableCallGraphPass::runOnFunction(Function *F) {
  bool Changed = false;

  RA_LOG("### Run on function: " << F->getName() << "\n");
  for (auto &BB : *F) {
    // assign a BB ID
    if (BBIDs.find(&BB) == BBIDs.end()) {
      BBIDs[&BB] = nextBBID++;
      if (auto *SI = dyn_cast<SwitchInst>(BB.getTerminator())) {
        // assign a unique ID to the switch case
        nextBBID += SI->getNumCases();
      }
    }
    auto* TI = BB.getTerminator();
    // treat any BB ending in llvm::UnreachableInst and exception as an "exit"
    if (isa<UnreachableInst>(TI) || isa<ResumeInst>(TI)) {
      RA_DEBUG("Unreachable Inst BB: " << BBIDs[&BB] << "\n");
      exitBBs.insert(&BB);
    }
    for (auto &i : BB) {
      Instruction *I = &i;

      if (UseTypeBasedCallGraph) {
        if (CallBase *CI = dyn_cast<CallBase>(I)) {
          if (Function *CF = CI->getCalledFunction()) {
            // direct call
            auto RCF = getFuncDef(CF);
            Changed |= Ctx->Callees[CI].insert(RCF).second;
            Changed |= Ctx->Callers[RCF].insert(CI).second;
            // check for call to exit functions
            if (isExitFn(RCF->getName()) || CF->doesNotReturn()) {
              RA_DEBUG("Exit Call: " << *CI << "\n");
              exitBBs.insert(CI->getParent());
            }
          } else if (!CI->isInlineAsm()) {
            // indirect call
            auto &FS = calleeByType[CI];
            Changed |= findCalleesByType(CI, FS);
            for (auto F : FS) {
              RA_DEBUG("Adding indirect caller for " << F->getName() << "@" << F << "\n");
              Changed |= callerByType[F].insert(CI).second;
            }
            if (isa<InvokeInst>(CI)) {
              RA_DEBUG("Indirect invoke instruction: " << *CI << "\n");
            }
          }
        }
      }

      // check against target list
      StringRef f = F->getParent()->getSourceFileName();
      auto loc = I->getDebugLoc();
      if (loc) {
        auto scope = loc.getScope();
        if (DIScope *DS = dyn_cast<DIScope>(scope)) {
          f = DS->getFilename();
        }
        for (auto &target : targetList) {
          if (f.find(target.first) != std::string::npos && loc.getLine() == target.second) {
            RA_LOG("Target I: " << *I << "\n");
            distances[I->getParent()] = 0.0;
            targetBBs.insert(I->getParent());
            reachableBBs.insert(I->getParent());
          }
        }
      }

      // collect interesting callsites
      if (auto CI = dyn_cast<CallBase>(I)) {
        if (CI->isInlineAsm()) { // skip inline asm
          continue;
        }
        bool hasCallee = true; // likely
        auto itr = Ctx->Callees.find(CI);
        if (itr == Ctx->Callees.end()) {
          hasCallee = false;
          if (UseTypeBasedCallGraph) {
            itr = calleeByType.find(CI);
            hasCallee = (itr != calleeByType.end());
          }
        }
        if (!hasCallee) {
          RA_DEBUG("No callee for " << *CI << "\n");
          continue;
        }
        bool defined = false;
        for (auto F : itr->second) {
          if (F->isIntrinsic() || F->empty()) {
            continue; // skip intrinsic and declaration
          }
          defined = true;
        }
        if (defined /*&& PropagateThroughReturnEdgees*/) {
          // record the call site
          BBswithCalls[&BB].push_back(CI);
        }
      }
    }
  }

  return Changed;
}

bool ReachableCallGraphPass::doInitialization(Module *M) {

  for (Function &F : *M) {
    if (UseTypeBasedCallGraph) {
      // collect address-taken functions
      if (F.hasAddressTaken()) {
        RA_LOG("AddressTaken: " << F.getName() << "\n");
        // hmmm, turns out F can be declaration
        auto RF = getFuncDef(&F);
        if (F.getFunctionType()->isVarArg()) {
          RA_DEBUG("  VarArg: " << F.getName() << "\n");
        } else {
          Ctx->AddressTakenFuncs.insert(RF);
        }
      }
    }

    // if no entry specified, use the common one
    // collect the exit block of the entry function too
    bool isEntry = false;
    if (entryList.empty()) {
      isEntry = isEntryFn(F.getName());
    } else {
      auto itr = std::find(entryList.begin(), entryList.end(), F.getName().str());
      isEntry = (itr != entryList.end());
    }
    if (isEntry) {
      // Record entry block
      entryBBs.insert(&F.getEntryBlock());
      // Compute the maximum source line number for this function
      unsigned maxLine = 0;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto DL = I.getDebugLoc()) {
            maxLine = std::max(maxLine, DL.getLine());
          }
        }
      }
      // Seed exitBBs with normal exit terminators
      for (auto &BB : F) {
        auto *TI = BB.getTerminator();
        if (isa<ReturnInst>(TI) || isa<UnreachableInst>(TI) ||
            isa<ResumeInst>(TI) || TI->getNumSuccessors() == 0) {
          exitBBs.insert(&BB);
        }
        if (maxLine > 0) {
          // Also include any BB whose debug line equals the function's last line
          for (auto &I : BB) {
            if (auto DL = I.getDebugLoc()) {
              if (DL.getLine() == maxLine) {
                exitBBs.insert(&BB);
                break;
              }
            }
          }
        }
      } // end of finding exitBBs
    } // end of entry function processing
  } // end of processing all functions in this Module

  return false;
}

bool ReachableCallGraphPass::doFinalization(Module *M) {
  return false;
}

void ReachableCallGraphPass::propagateThroughReturnEdgees(
  std::unordered_set<const BasicBlock*> &reachable, 
  const BasicBlock* CBB) {
  auto hasCalls = BBswithCalls.find(CBB);
  if (hasCalls == BBswithCalls.end()) return;
  
  std::deque<const BasicBlock*> worklist;
  unsigned currDepth = retDepth[CBB];
  if (currDepth >= maxCallStackDepth) {
    RA_LOG("Max depth reached (" << maxCallStackDepth 
           << ") for BB " << BBIDs[CBB] << ", skipping propagation\n");
    return; // do not propagate beyond threshold
  }

  CallSequence calls = hasCalls->second;
  for (size_t i = calls.size(); i-- > 0; ) {
    // find the current callsite and there are additional callees before it
    const llvm::CallBase* CI = calls[i];
    // Look up callees for this call site with proper map/iterator logic
    // Unified lookup of direct or type-based callees
    const FuncSet *callees = nullptr;
    if (auto it = Ctx->Callees.find(CI); it != Ctx->Callees.end()) {
        callees = &it->second;
    } else if (UseTypeBasedCallGraph) {
        if (auto it2 = calleeByType.find(CI); it2 != calleeByType.end()) {
            callees = &it2->second;
        }
    }
    if (!callees) {
        RA_DEBUG("No callee for " << *CI << "\n");
        continue;
    }
    
    // Iterate over each callee function
    for (auto *F : *callees) {
      if (isExitFn(F->getName()) || F->doesNotReturn()) {
        RA_DEBUG("DoesNotReturn: " << F->getName() << "\n");
        break; // no further propagation for no-return functions
      }
      RA_LOG(F->getName() << " is reachable through ret edge to the targets\n");
      // add exit block(s) as reachable
      for (auto &TBB : *F) {
        if (isa<UnreachableInst>(TBB.getTerminator())) {
          continue; // skip unreachable BBs
        }
        if (isa<ReturnInst>(TBB.getTerminator())) {
          RA_DEBUG("Adding callee: " << F->getName() << "\n");
          if (reachable.find(&TBB) != reachable.end()) {
            continue; // already added
          }
          retDepth[&TBB] = currDepth + 1;
          worklist.push_back(&TBB);
        }
      } // end of BBs for this callee F
    } // end of candidate callees for this callsite CI
  } // end of all callsites for this CBB

  // BFS back propagate through predecessors
  // Do not add callers to prevent fake call edges.
  while (!worklist.empty()) {
    const BasicBlock *BB = worklist.front();
    worklist.pop_front();
    reachable.insert(BB);
    // process the current BBs
    propagateThroughReturnEdgees(reachable, BB);
    RA_DEBUG("Propagating Ret BB through: " << BBIDs[BB] << "\n");
    // add its predecessors
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      const BasicBlock *Pred = *PI;
      if (reachable.find(Pred) != reachable.end()) {
        continue; // already added
      }
      worklist.push_back(Pred);
    } // end of processing predecessors of this BB
  } // end of propagation through predecessors
}

void ReachableCallGraphPass::collectReachable(std::deque<const BasicBlock*> &worklist,
    std::unordered_set<const BasicBlock*> &reachable,
    const std::unordered_set<const BasicBlock*> &others) {
  bool isComputingReachable = others.empty();
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    // add callee when computing reachable BBs
    if (isComputingReachable) {
      // do not PropagateThroughReturnEdgees when computing unreachable BBs
      propagateThroughReturnEdgees(reachable, BB);
    }
    // add predecessors
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      const BasicBlock *Pred = *PI;
      // if the predecessor is reachable to the target
      // stop propagating unreachable BB through it
      if (others.find(Pred) != others.end()) {
        criticalBBs[Pred].push_back(BB);
        continue;
      }
      if (reachable.find(Pred) != reachable.end()) {
          continue; // already added
      } else if(reachable.insert(Pred).second) {
        RA_DEBUG("Adding " << BBIDs[BB] << "'s Pred: " << BBIDs[Pred] << "\n");
        worklist.push_back(Pred);
      }
    }
    // entry block, add caller, if not entry
    auto *F = BB->getParent();
    if (BB == &F->getEntryBlock()) {
      if (entryBBs.find(BB) != entryBBs.end()) {
        continue;
      }
      auto itr = Ctx->Callers.find(F);
      if (itr == Ctx->Callers.end()) {
        bool found = false;
        if (UseTypeBasedCallGraph) {
          itr = callerByType.find(F);
          found = (itr != callerByType.end());
        }
        if (!found) {
          WARNING("No caller for " << F->getName() << "\n");
          continue;
        }
      }

      if (isComputingReachable) {
        RA_LOG(F->getName() << " is reachable through call edge to the targets\n");
      }else {
        RA_LOG(F->getName() << " is reachable to the exit\n");
      }
      unsigned currDepth = callDepth[BB];
      for (auto *CI : itr->second) {
        auto *CBB = CI->getParent();
        unsigned newDepth = currDepth + 1;
        if (newDepth > maxCallStackDepth) {
          RA_LOG("Max depth reached (" << maxCallStackDepth 
                 << ") for function " << F->getName() << ", skipping caller\n");
          continue;  // do not propagate beyond threshold
        }
        if (reachable.find(CBB) != reachable.end()) {
          continue; // already added
        }
        // if all callsites have been processed, add the CBB
        RA_DEBUG("\tadding caller: " << CI->getFunction()->getName() << "\n");
        if (reachable.insert(CBB).second) {
          // if the caller BB CBB is reachable to the target
          // do not propagate unreachable BB through this call sites
          if (others.find(CBB) != others.end()) {
            criticalBBs[CBB].push_back(BB);
            continue;
          }
          callDepth[CBB] = newDepth;  // record depth before enqueue
          worklist.push_back(CBB);
        }
      } // end of callers
    } // end of entry block
  }
}

void ReachableCallGraphPass::run(ModuleList &modules) {
  ModuleList::iterator i, e;
  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    doInitialization(i->first);
  }

  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    for (Function &F : *i->first) {
      if (!F.isDeclaration() && !F.empty() && !F.isIntrinsic()) {
        runOnFunction(&F);
      }
    }
  }

  // check targets
  if (distances.empty()) {
    WARNING("No target found\n");
    return;
  }

  // check entries
  if (entryBBs.empty()) {
    WARNING("No entry BBs found\n");
    return;
  }

  // do a BFS search on the target list, find all reachable BBs first
  std::deque<const BasicBlock*> worklist;
  RA_LOG("\n\n=== Collecting reachable BBs ===\n\n");
  callDepth.clear();
  retDepth.clear();
  for (const auto &kv : distances) {
    worklist.push_back(kv.first);
  }
  collectReachable(worklist, reachableBBs);
  for (const auto *BB : exitBBs)
    reachableBBs.erase(BB);

  // do a BFS search on the call graph to find BB that can reach exits
  RA_LOG("\n\n=== Collecting exit BBs ===\n\n");
  worklist.clear();
  callDepth.clear();
  retDepth.clear();
  for (auto *BB : exitBBs) {
    worklist.push_back(BB);
  }
  collectReachable(worklist, exitBBs, reachableBBs);

  // check if target is reachable
  bool reached = false;
  for (auto &entry : entryBBs) {
    if (reachableBBs.find(entry) != reachableBBs.end()) {
      RA_LOG("\n\n=== Target is reachable from entry ===\n\n");
      reached = true;
    }
  }

  if (!reached) {
    WARNING("Target not reachable from entry BBs\n");
    return;
  }

  // now calculate distances in a bottom-up manner
  std::unordered_set<const BasicBlock*> queued;
  std::unordered_set<const CallBase*> queuedCalls;
  callDepth.clear();
  for (const auto &kv : distances) {
    callDepth[kv.first] = 0;
    worklist.push_back(kv.first);
    queued.insert(kv.first);
  }
  // fixed point iteration?
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    queued.erase(BB);
    unsigned currDepth = callDepth[BB];
    if (currDepth >= maxCallStackDepth) {
      continue;  // do not propagate beyond threshold
    }
    // check predecessors
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      auto *Pred = *PI;
      double numSucc = 0.0;
      double prob = 0.0;
      if (reachableBBs.find(Pred) == reachableBBs.end()) {
        RA_DEBUG("Skip unreachable Pred: " << *Pred << "\n");
        continue;
      }
      for (auto SI = succ_begin(Pred), SE = succ_end(Pred); SI != SE; ++SI) {
        auto *Succ = *SI;
        numSucc += 1.0;
        // unreachable one has prob 0
        if (reachableBBs.find(Succ) == reachableBBs.end()) {
          RA_DEBUG("Skip unreachable successor: " << *Succ << "\n");
          continue;
        }
        auto itr = distances.find(Succ);
        if (itr != distances.end()) {
          prob += 1.0 / std::pow(2, itr->second);
        }
      }
      prob /= numSucc;
      if (prob == 0.0) {
        WARNING("prob dropped to 0 for basic block in " << BB->getParent()->getName() << "\n");
        RA_DEBUG("\t " << *BB << "\n");
        continue;
      }
      auto dist = (-std::log2(prob));
      if (dist == std::numeric_limits<double>::max()) {
        WARNING("dist overflow for basic block\n");
        continue;
      }
      auto itr = distances.find(Pred);
      if (itr == distances.end() || itr->second > dist) {
        // RA_DEBUG("Adding Pred: " << *Pred << " with prob " << prob << "\n");
        distances[Pred] = dist;
        if (queued.insert(Pred).second){
          callDepth[Pred] = currDepth;
          worklist.push_back(Pred);
        }
      }
    }
    // entry block has no predecessor, add caller
    auto *F = BB->getParent();
    if (BB == &F->getEntryBlock()) {
      if (entryBBs.find(BB) != entryBBs.end()) {
        // break;
        continue;
      }
      auto itr = Ctx->Callers.find(F);
      if (itr == Ctx->Callers.end()) {
        bool found = false;
        if (UseTypeBasedCallGraph) {
          itr = callerByType.find(F);
          found = (itr != callerByType.end());
        }
        if (!found) {
          if (!F->getName().equals("main")) {
            WARNING("No caller for " << F->getName() << "\n");
          } else {
            RA_LOG("main is reached\n");
          }
          continue;
        }
      }
      // check callers
      RA_LOG(F->getName() << " is reachable from " << itr->second.size() << " callers\n");
      auto dist = distances[BB];
      for (auto CI : itr->second) {
        auto CBB = CI->getParent();
        auto CF = CI->getFunction();
        if (CF->isVarArg() && isPrintFn(CF->getName())) {
          RA_DEBUG("Skip print caller: " << CF->getName() << "\n");
          continue;
        }
        if (!CI->isIndirectCall()) {
          // for direct calls, prob can be propagated directly
          auto itr2 = callDistances.find(CI);
          if (itr2 == callDistances.end() || itr2->second > dist) {
            RA_DEBUG("Adding direct caller: " << CI->getFunction()->getName() << "\n");
            distances[CBB] = dist;
            if (queued.insert(CBB).second){
              callDepth[CBB] = currDepth + 1;
              worklist.push_back(CBB);
            }
          }
        } else {
          // indirect call is tricky, treat like predecessors
          // for each call site, check if all its callees have been processed
          double prob = 0.0;
          FuncSet &Callees = UseTypeBasedCallGraph ? calleeByType[CI] : Ctx->Callees[CI];
          RA_LOG("\tfrom indirect call @" << CF->getName() << ", callee size = " << Callees.size() << "\n");
          // XXX: skip potentially imprecise callsites?
          if (Callees.size() > 50) {
            RA_DEBUG("Skip indirect call with too many callees\n");
            continue;
          }
          // record the call site
          reachableIndirectCalls.insert(CI);
          // calculate distance
          for (auto F : Callees) {
            auto CEBB = &F->getEntryBlock();
            if (reachableBBs.find(CEBB) == reachableBBs.end()) {
              continue;
            }
            auto itr2 = distances.find(CEBB);
            if (itr2 != distances.end()) {
              prob += 1.0 / std::pow(2, itr2->second);
            }
          }
          // for indirect call, prob needs to be divided by the number of potential callees
          prob /= (double)Callees.size();
          if (prob == 0.0) {
            WARNING("prob dropped to 0 for indirect call\n");
            continue;
          }
          auto dist = (-std::log2(prob));
          if (dist == std::numeric_limits<double>::max()) {
            WARNING("dist overflow for indirect call\n");
            continue;
          }
          auto itr2 = callDistances.find(CI);
          if (itr2 == callDistances.end() || itr2->second > dist) {
            RA_DEBUG("Adding indirect caller: " << CI->getFunction()->getName() << "\n");
              distances[CBB] = dist;
            if (queued.insert(CBB).second){
              callDepth[CBB] = currDepth + 1;
              worklist.push_back(CBB);
            }
          }
        }
      }
    }
  }

  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    doFinalization(i->first);
  }
}

ReachableCallGraphPass::ReachableCallGraphPass(
    GlobalContext *Ctx_,
    std::string &TargetList,
    std::string &EntryList,
    bool typeBased,
    unsigned CallStackLen)
    : Ctx(Ctx_),
      UseTypeBasedCallGraph(typeBased),
      nextBBID(1000),
      maxCallStackDepth(CallStackLen) {
  // parse target list
  // format: filename:line_number
  if (!TargetList.empty()) {
    std::ifstream ifs(TargetList);
    if (!ifs.is_open()) {
      KA_ERR("Failed to open target list file: " << TargetList);
    }
    std::string line;
    while (std::getline(ifs, line)) {
      if (line.empty() || line[0] == '#')
        continue;
      auto colon = line.find(':');
      if (colon == std::string::npos) {
        KA_ERR("Invalid target list format: " << line);
      }
      std::string f = line.substr(0, colon);
      std::string l = line.substr(colon + 1);
      int il = std::stoi(l);
      RA_LOG("Target: " << f << ":" << il << "\n");
      targetList.push_back(std::make_pair(f, il));
    }
  }
  // parse entry list
  // format: function_name
  if (!EntryList.empty()) {
    std::ifstream ifs(EntryList);
    if (!ifs.is_open()) {
      KA_ERR("Failed to open entry list file: " << EntryList);
    }
    std::string line;
    while (std::getline(ifs, line)) {
      if (line.empty() || line[0] == '#')
        continue;
      RA_LOG("Entry: " << line << "\n");
      entryList.push_back(line);
    }
  }
}

std::string ReachableCallGraphPass::getSourceLocation(const BasicBlock *BB) {
    for (const auto &I : *BB) {
        auto loc = I.getDebugLoc();
        if (loc && loc.getLine() != 0) {
            // Get the filename from the debug location
            std::string f = loc->getFilename().str();
            // If filename is empty, get it from the parent function
            if (f.empty()) {
                f = BB->getParent()->getParent()->getSourceFileName();
            }
            // Remove leading "./" if present
            if (f.find("./") == 0) {
                f = f.substr(2);
            }
            // Extract the base filename by finding the last '/' or '\\'
            size_t pos = f.find_last_of("/\\");
            if (pos != std::string::npos) {
                f = f.substr(pos + 1);
            }
            return f + ":" + std::to_string(loc.getLine());
        }
    }
    return "NoLoc:0";
}

/// \brief Retrieve the first available debug location in \p BB that is not
/// inside /usr/ and store the **absolute, normalized path** in \p Filename.
/// Sets \p Line and \p Col accordingly.
///
/// This version does:
///  1) Loops over instructions in \p BB
///  2) Checks the debug location (and possibly inlined-at location)
///  3) Builds an absolute, normalized path (resolving "." and "..")
///  4) Skips if the path is empty, line=0, or the path starts with "/usr/"
///  5) Returns the first valid debug info found
void ReachableCallGraphPass::getDebugLocationFullPath(const BasicBlock &BB,
                              std::string &Filename,
                              unsigned &Line,
                              unsigned &Col) {
  Filename.clear();
  Line = 0;
  Col = 0;

  // We don't want paths that point to system libraries in /usr/
  static const std::string Xlibs("/usr/");

  // Iterate over instructions in the basic block
  for (auto &Inst : BB) {
    if (DILocation *Loc = Inst.getDebugLoc()) {
      // Extract directory & filename
      std::string Dir  = Loc->getDirectory().str();
      std::string File = Loc->getFilename().str();
      unsigned    L    = Loc->getLine();
      unsigned    C    = Loc->getColumn();

      // If there's no filename, check the inlined location
      if (File.empty()) {
        if (DILocation *inlinedAt = Loc->getInlinedAt()) {
          Dir  = inlinedAt->getDirectory().str();
          File = inlinedAt->getFilename().str();
          L    = inlinedAt->getLine();
          C    = inlinedAt->getColumn();
        }
      }

      // Skip if still no filename or line==0
      if (File.empty() || L == 0)
        continue;

      // Build an absolute path in a SmallString
      llvm::SmallString<256> FullPath;

      // 1) If Dir is already absolute, just start with that.
      //    Otherwise, use the current working directory as a base.
      if (!Dir.empty() && llvm::sys::path::is_absolute(Dir)) {
        FullPath = Dir;
      } else {
        llvm::sys::fs::current_path(FullPath); // get the current working dir
        if (!Dir.empty()) {
          llvm::sys::path::append(FullPath, Dir);
        }
      }

      // 2) Append the filename
      llvm::sys::path::append(FullPath, File);

      // 3) Remove dot segments (both "." and "..")
      llvm::sys::path::remove_dots(FullPath, /*remove_dot_dot=*/true);

      // Now FullPath is absolute & normalized
      // Check if it's in /usr/
      if (StringRef(FullPath).startswith(Xlibs))
        continue; // skip system-libs

      // Found a valid location => set output vars
      Filename = FullPath.str().str(); // convert to std::string
      Line     = L;
      Col      = C;
      break; // stop after the first valid location
    }
  }
}

void ReachableCallGraphPass::dumpDistance(std::ostream &OS, bool dumpUnreachable) {
  // Set precision for output
  OS << std::fixed << std::setprecision(6);
  // Copy and sort distances by ascending value
  std::vector<std::pair<const BasicBlock*, double>> sorted;
  sorted.reserve(distances.size());
  for (const auto &entry : distances) {
      sorted.emplace_back(entry.first, entry.second);
  }
  std::sort(sorted.begin(), sorted.end(),
            [](const auto &a, const auto &b) { return a.second < b.second; });
  // Output sorted distance entries
  for (const auto &pair : sorted) {
      const BasicBlock *BB = pair.first;
      double dist = pair.second;
      OS << BBIDs[BB] << ","
          << getBasicBlockId(BB) << ","
          << getSourceLocation(BB) << ","
          << (dist * 1000) << "\n";
  }

  // If dumpUnreachable is enabled, output unreachable basic blocks
  if (dumpUnreachable) {
    for (const auto *BB : exitBBs) {
      OS << BBIDs[BB] << ","
          << getBasicBlockId(BB) << ","
          << getSourceLocation(BB) 
          << ",-1\n";
    }
  }

  // Dump the covered functions
  std::unordered_set<const Function *> reachedFunctions;
  for (const auto &entry : distances) {
    reachedFunctions.insert(entry.first->getParent());
  }
  OS << "##########\n";
  for (const auto *F : reachedFunctions) {
    OS << "fun:" << F->getName().str() << "\n";
  }
}

void ReachableCallGraphPass::dumpPolicy(std::ostream &OS) {
  // set precision
  OS << std::fixed << std::setprecision(6);

  for (const auto &kv : distances) {
    auto *BB = kv.first;
    if (kv.second == 0.0) {
      // skip target BB
      continue;
    }
    auto term = BB->getTerminator();
    auto branch = dyn_cast<BranchInst>(term);
    if (!branch || !branch->isConditional())
      continue;
    auto TT = branch->getSuccessor(0);
    auto FT = branch->getSuccessor(1);

    bool reached = false;
    std::string tdist;
    auto itr = distances.find(FT);
    if (itr != distances.end()) {
      tdist = std::to_string(itr->second * 1000);
      reached = true;
    } else {
      tdist = "inf";
    }
    std::string fdist;
    itr = distances.find(TT);
    if (itr != distances.end()) {
      fdist = std::to_string(itr->second * 1000);
      reached = true;
    } else {
      fdist = "inf";
    }
    if (!reached) {
      bool hasCall = false;
      for (auto &I : *BB) {
        if (isa<CallInst>(I)) {
          hasCall = true;
          break;
        }
      }
      if (!hasCall) {
        WARNING("Branch reachable but both targets are not!! @"
            << getSourceLocation(BB) << " in " << BB->getParent()->getName()
            << "\n" << *BB
            << "\nAnd no call in the BB\n");
      }
    } else {
      OS << BBIDs[BB] << "," << tdist << "," << fdist << "," << BBIDs[FT] << "," << BBIDs[TT] << "\n";
    }
  }

  OS << "##########\n";

  for (auto const &CI : reachableIndirectCalls) {
    // dump callsite ID = (BBID, order)
    auto CBB = CI->getParent();
    auto CBBID = BBIDs[CBB];
    OS << CBBID << ",";
    unsigned order = 0;
    for (auto &I: *CBB) {
      if (isa<CallBase>(I)) {
        order++;
        if (&I == CI) break;
      }
    }
    OS << order << ":";
    FuncSet &Callees = UseTypeBasedCallGraph ? calleeByType[CI] : Ctx->Callees[CI];
    for (auto F : Callees) {
      auto CEBB = &F->getEntryBlock();
      auto itr = distances.find(CEBB);
      if (itr != distances.end()) {
        RA_DEBUG("Indirect call to " << F->getName() << " at " << CBBID << ": " << itr->second << "\n");
        OS << F->getGUID() << "," << itr->second * 1000 << ";";
      }
    }
    OS << "\n";
  }
}

void ReachableCallGraphPass::dumpIDMapping(ModuleList &modules, std::ostream &bbLocs, std::ostream &funcInfo) {
  ModuleList::iterator i, e;
  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    Module *M = i->first;
    for (auto &F : *M) {
      unsigned minLine = std::numeric_limits<unsigned>::max();
      unsigned maxLine = 0;
      std::string filepath;
      if (F.isDeclaration() || F.empty() || F.isIntrinsic()) {
        continue; // skip declaration and intrinsic
      }

      for (auto &BB : F) {
        unsigned line = 0;
        unsigned col = 0;
        getDebugLocationFullPath(BB, filepath, line, col);
        uint32_t bb_id = getBasicBlockId(&BB);

        if (line < minLine && line > 0) {
          minLine = line;
        }
        if (line > maxLine && line > 0) {
          maxLine = line;
        }
        if (!filepath.empty() && line != 0)
          bbLocs << BBIDs[&BB] << "," << bb_id << "," << F.getGUID() << "," << filepath << ":" << line << "\n";

      }
      if (!filepath.empty() && minLine != std::numeric_limits<unsigned>::max() && maxLine != 0)
        funcInfo << F.getGUID() << "," << F.getName().str() << "," << filepath << "," << minLine << "," << maxLine << "\n";
    }
  }
}

void ReachableCallGraphPass::dumpCriticalBBs(std::ostream &OS) {
  for (auto const &[BB, exits] : criticalBBs) {
    OS << BBIDs[BB];
    for (auto *exitBB : exits)
      OS << "," << BBIDs[exitBB];
    OS << "\n";
  }
}

bool ReachableCallGraphPass::annotateModules(ModuleList &modules, std::string suffix) {
  std::unordered_set<const llvm::BasicBlock*> inverseCriticalBBs;
  for (const auto &[k,v] : criticalBBs) {
    for (const auto *exitBB : v) {
      inverseCriticalBBs.insert(exitBB);
    }
  }
  ModuleList::iterator i, e;
  // double max_dist = INFINITY;
  // if (!distances.empty()) {
  //   max_dist = std::max_element(distances.begin(), distances.end(),
  //       [](const std::pair<const BasicBlock*, double> &a,
  //          const std::pair<const BasicBlock*, double> &b) {
  //         return a.second < b.second;
  //       })->second;
  // }

  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    Module *M = i->first;
    auto ModName = M->getName().str();
    auto NewName = ModName + suffix;
    auto VoidTy = Type::getVoidTy(M->getContext());
    auto Int64Ty = Type::getInt64Ty(M->getContext());
    auto *BoolTy = Type::getInt1Ty(M->getContext());
    auto *TrueVal = ConstantInt::getTrue(BoolTy);
    auto *FalseVal = ConstantInt::getFalse(BoolTy);
    GlobalVariable *HasReachedTarget = cast<GlobalVariable>(
          M->getOrInsertGlobal("has_reached_target", BoolTy));
    HasReachedTarget->setLinkage(GlobalValue::LinkOnceODRLinkage);
    HasReachedTarget->setComdat(M->getOrInsertComdat(HasReachedTarget->getName()));
    if (!HasReachedTarget->hasInitializer())
        HasReachedTarget->setInitializer(FalseVal);

    // FunctionCallee TraceDistanceFunc = M->getOrInsertFunction(
    //     "__taint_trace_distance", VoidTy, Int64Ty, Int64Ty);
    FunctionCallee TraceFunc = M->getOrInsertFunction(
    "__taint_trace_divergence", VoidTy, Int64Ty);
    for (auto &F : *M) {
      if (F.isDeclaration() || F.empty() || F.isIntrinsic()) {
        continue; // skip declaration and intrinsic
      }
      for (auto &BB : F) {
        if (isa<UnreachableInst>(BB.getTerminator()))
          continue; // skip unreachable BBs
        if (BB.getFirstInsertionPt() == BB.end())
          continue; // skip empty BBs

        // add an annotation for other instrumentation
        auto *BBID = ConstantInt::get(Int64Ty, BBIDs[&BB]);
        auto term = BB.getTerminator();
        MDNode *MD = MDNode::get(M->getContext(),
                                  {ConstantAsMetadata::get(BBID)});
        term->setMetadata("bbid", MD);

        // instrument __taint_trace_divergence callback
        if (inverseCriticalBBs.count(&BB)) {
          IRBuilder<> IRB(&*BB.getFirstInsertionPt());
          auto *CI = IRB.CreateCall(TraceFunc, {BBID});
          CI->setCannotMerge();
        }
        // Instrument code to set has_reached_target to true
        for (const llvm::BasicBlock* tb : targetBBs) {
          if (tb == &BB) {
            IRBuilder<> IRB(BB.getTerminator());
            IRB.CreateStore(TrueVal, HasReachedTarget)->setMetadata(
                M->getMDKindID("nosanitize"), MDNode::get(M->getContext(), None));
            break;
          }
        }
        // annotate reachable basic block with ID and distance
        // if (reachableBBs.count(&BB)) {
        //   // check if we have a distance
        //   auto itr = distances.find(&BB);
        //   double dist = (itr != distances.end()) ? itr->second : max_dist;
        //   dist *= 1000.0;
        //   // instrument a call to trace distance
        //   IRBuilder<> IRB(&*BB.getFirstInsertionPt());
        //   auto *Dist = ConstantInt::get(Int64Ty, (uint64_t)dist);
        //   IRB.CreateCall(TraceDistanceFunc, {BBID, Dist})->setCannotMerge();
        // }
      }
    }
    // verify
    llvm::verifyModule(*M, &llvm::errs());

    // save the module with a new name
    std::error_code EC;
    llvm::raw_fd_ostream OS(NewName, EC, llvm::sys::fs::OF_None);
    if (EC) {
        llvm::errs() << "Error opening file " << NewName << ": " << EC.message() << "\n";
        return false;
    }
    // Write the bitcode directly to the stream
    llvm::WriteBitcodeToFile(*M, OS);
    OS.flush();
  }

  return true;
}

void ReachableCallGraphPass::dumpCallees() {
    RES_REPORT("\n[dumpCallees]\n");
    raw_ostream &OS = outs();
    OS << "Num of Callees: " << calleeByType.size() << "\n";
    for (CalleeMap::iterator i = calleeByType.begin(),
         e = calleeByType.end(); i != e; ++i) {

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
#if LLVM_VERSION_MAJOR > 10
            OS << "!!EMPTY =>" << *CI->getCalledOperand()<<"\n";
#else
            OS << "!!EMPTY =>" << *CI->getCalledValue()<<"\n";
#endif
            OS<< "Uninitialized function pointer is dereferenced!\n";
        }
    }
    RES_REPORT("\n[End of dumpCallees]\n");
}

void ReachableCallGraphPass::dumpCallers() {
    RES_REPORT("\n[dumpCallers]\n");
    for (auto M : Ctx->Callers) {
        const Function *F = M.first;
        CallInstSet &CIS = M.second;
        RES_REPORT("F : " << getScopeName(F) << "\n");

        for (auto *CI : CIS) {
            auto CallerF = CI->getParent()->getParent();
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
