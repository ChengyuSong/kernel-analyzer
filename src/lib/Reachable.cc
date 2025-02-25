/*
 * Reachability-based Call Graph Analysis
 *
 * Copyrigth (C) 2024 Chengyu Song
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
    WARNING("Unhandled Types:" << *T1 << " :: " << *T2 << "\n");
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool ReachableCallGraphPass::findCalleesByType(CallInst *CI, FuncSet &FS) {
    CallBase &CS = *CI;
    bool Changed = false;
    RA_LOG("Handle indirect call: " << *CI << "\n");
    for (const Function *F : Ctx->AddressTakenFuncs) {
      // just compare known args
      if (F->getFunctionType()->isVarArg()) {
        //errs() << "VarArg: " << F->getName() << "\n";
        KA_ERR("VarArg address taken function\n");
      } else if (F->arg_size() != CS.arg_size()) {
        RA_DEBUG("ArgNum mismatch: " << F->getName() << "\n");
        continue;
      } else if (!isCompatibleType(F->getReturnType(), CI->getType())) {
        RA_DEBUG("Return type mismatch: " << F->getName() << "\n");
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
    for (auto &i : BB) {
      Instruction *I = &i;

      if (UseTypeBasedCallGraph) {
        if (CallInst *CI = dyn_cast<CallInst>(I)) {
          if (Function *CF = CI->getCalledFunction()) {
            // direct call
            auto RCF = getFuncDef(CF);
            Changed |= Ctx->Callees[CI].insert(RCF).second;
            Changed |= Ctx->Callers[RCF].insert(CI).second;
            // check for call to exit functions
            if (isExitFn(RCF->getName())) {
              RA_LOG("Exit Call: " << *CI << "\n");
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
          }
        } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
          if (Function *CF = II->getCalledFunction()) {
            // direct call
            auto RCF = getFuncDef(CF);
            Changed |= Ctx->Callees[II].insert(RCF).second;
            Changed |= Ctx->Callers[RCF].insert(II).second;
            // check for call to exit functions
            if (isExitFn(RCF->getName())) {
              RA_LOG("Exit Call: " << *II << "\n");
              exitBBs.insert(II->getParent());
            }
          } else if (!II->isInlineAsm()) {
            // indirect call
            KA_ERR("Indirect invoke not supported\n");
          }
        }
      }

      // check against target list
      auto f = F->getParent()->getSourceFileName();
      auto loc = I->getDebugLoc();
      if (loc) {
        for (auto &target : targetList) {
          if (f.find(target.first) != std::string::npos && loc.getLine() == target.second) {
            RA_LOG("Target I: " << *I << "\n");
            distances[I->getParent()] = 0.0;
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
          // RA_DEBUG("No callee for " << *CI << "\n");
          continue;
        }
        bool defined = false;
        for (auto F : itr->second) {
          if (F->isIntrinsic() || F->empty()) {
            continue; // skip intrinsic and declaration
          }
          defined = true;
        }
        if (defined) {
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
      entryBBs.insert(&F.getEntryBlock());
      for (auto &BB : F) {
        if (isa<ReturnInst>(BB.getTerminator())) {
          exitBBs.insert(&BB);
        }
      }
    }
  }

  return false;
}

bool ReachableCallGraphPass::doFinalization(Module *M) {
  return false;
}

void ReachableCallGraphPass::collectReachable(std::deque<const BasicBlock*> &worklist,
    std::unordered_set<const BasicBlock*> &reachable) {
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    // add predecessors
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      auto *Pred = *PI;
      if (reachable.insert(Pred).second) {
        worklist.push_back(Pred);
      }
    }
    // entry block, add caller, if not entry
    auto *F = BB->getParent();
    if (BB == &F->getEntryBlock()) {
      if (entryBBs.find(BB) != entryBBs.end()) {
        RA_LOG("Entry func " << F->getName() << " is reachable\n");
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

      RA_DEBUG(F->getName() << " is reachable\n");
      for (auto CI : itr->second) {
        auto CBB = CI->getParent();
        // go through instructions, handle additional callees
        bool willReturn = true;
        bool added = false;
        auto hasCalls = BBswithCalls.find(CBB);
        assert(hasCalls != BBswithCalls.end());
        auto calls = hasCalls->second;
        for (auto i = calls.size() - 1; i > 0; --i) {
          if (calls[i] == CI) {
            // find the current callsite and there are additional callees before it
            CI = calls[i - 1];
            auto fitr = Ctx->Callees.find(CI);
            if (fitr == Ctx->Callees.end()) {
              if (UseTypeBasedCallGraph) {
                fitr = calleeByType.find(CI);
              }
            }
            // any callsite here is guaranteed to have a callee
            for (auto F : fitr->second) {
              if (F->doesNotReturn()) {
                RA_DEBUG("DoesNotReturn: " << F->getName() << "\n");
                willReturn = false;
                break; // not need to continue
              }
              // add exit block(s) as reachable
              for (auto &TBB : *F) {
                if (isa<ReturnInst>(TBB.getTerminator())) {
                  RA_LOG("Adding callee: " << F->getName() << "\n");
                  if (reachable.insert(&TBB).second) {
                    worklist.push_back(&TBB);
                    added = true;
                  }
                }
              }
            }
            if (added) break; // one callsite at a time
          }
        }
        if (willReturn && !added) {
          // if all callees have been processed, add the CBB
          RA_DEBUG("\tadding caller: " << CI->getFunction()->getName() << "\n");
          if (reachable.insert(CBB).second) {
            worklist.push_back(CBB);
          }
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

  // do a BFS search on the call graph to find BB that can reach exits
  std::deque<const BasicBlock*> worklist;
  RA_DEBUG("\n\n=== Collecting exit BBs ===\n\n");
  worklist.insert(worklist.end(), exitBBs.begin(), exitBBs.end());
  collectReachable(worklist, exitBBs);

  // now do a BFS search on the target list, find all reachable BBs first
  RA_LOG("\n\n=== Collecting reachable BBs ===\n\n");
  for (const auto &kv : distances) {
    worklist.push_back(kv.first);
  }
  collectReachable(worklist, reachableBBs);

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
  for (const auto &kv : distances) {
    worklist.push_back(kv.first);
    queued.insert(kv.first);
  }
  // fixed point iteration?
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    queued.erase(BB);
    // go through instructions, looking for calls
    auto hasCalls = BBswithCalls.find(BB);
    if (hasCalls != BBswithCalls.end()) {
      auto &calls = hasCalls->second;
      bool finished = false;
      const CallBase *propagate = nullptr;
      double dist = NAN;
      for (auto i = calls.size() - 1;; --i) {
        // iterate through all callsites, in reverse order
        auto *CI = calls[i];
        if (queuedCalls.find(CI) != queuedCalls.end()) {
          // if the reachability comes from the callee
          RA_DEBUG("Find current callsite: " << *CI << "\n");
          queuedCalls.erase(CI);
          if (i > 0) {
            // there are additional callees before the current callsite
            // we need to propagate the reachability to them
            RA_DEBUG("Propagate to additional callees\n");
            // get the distance of current callsite
            auto itr = callDistances.find(CI);
            assert(itr != callDistances.end());
            dist = itr->second;
            // record the callsite to be propagated to
            propagate = calls[i - 1];
          } else {
            // all callees have been processed
            finished = true;
          }
          break; // always break if coming from callee
        }
        if (i == 0) break;
      }
      if (!finished) {
        // if not finished, we either have more callsite(s) to process,
        // or the reachability is coming from the successor,
        if (propagate == nullptr) {
          // in the later case, we want to propagate BB distance to the last callsite
          RA_DEBUG("Propagate BB distance to last callsite\n");
          propagate = calls.back();
          dist = distances[BB];
        }
        // propagate to return sites in the callee
        auto fitr = Ctx->Callees.find(propagate);
        if (fitr == Ctx->Callees.end()) {
          if (UseTypeBasedCallGraph) {
            fitr = calleeByType.find(propagate);
          }
        }
        bool added = false;
        // any callsite here is guaranteed to have a callee
        for (auto F : fitr->second) {
          // add exit block(s) as reachable
          for (auto &TBB : *F) {
            if (isa<ReturnInst>(TBB.getTerminator())) {
              auto itr = distances.find(&TBB);
              if (itr == distances.end() || itr->second > dist) {
                RA_DEBUG("Propagate distance " << dist << " to callee: " << F->getName() << "\n");
                distances[&TBB] = dist;
                if (queued.insert(&TBB).second) {
                  worklist.push_back(&TBB);
                }
                added = true;
              }
            }
          }
        }
        if (added) {
          // if we have propagated reachability to a callee, it will come back,
          // so we don't need to propagate to predecessors for now
          continue;
        } else {
          // there is another callsite but no propagation is needed
          // simulate the propagation by adding the callsite to the queue
          queuedCalls.insert(propagate);
          if (queued.insert(BB).second)
              worklist.push_back(BB);
          continue;
        }
      } else {
        // if all callsites have been processed, use the distance of the first
        // callsite as the distance of the BB
        RA_DEBUG("All callees processed\n");
        auto itr = callDistances.find(calls.front());
        assert(itr != callDistances.end());
        dist = itr->second;
        distances[BB] = dist;
      }
    }
    // check predecessors
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      auto *Pred = *PI;
      double numSucc = 0.0;
      double prob = 0.0;
      for (auto SI = succ_begin(Pred), SE = succ_end(Pred); SI != SE; ++SI) {
        auto *Succ = *SI;
        numSucc += 1.0;
        // unreachable one has prob 0
        if (reachableBBs.find(Succ) == reachableBBs.end())
          continue;
        auto itr = distances.find(Succ);
        if (itr != distances.end()) {
          prob += 1.0 / std::pow(2, itr->second);
        }
      }
      prob /= numSucc;
      if (prob == 0.0) {
        WARNING("prob dropped to 0 for basic block\n");
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
        if (queued.insert(Pred).second)
          worklist.push_back(Pred);
      }
    }
    // entry block has no predecessor, add caller
    auto *F = BB->getParent();
    if (BB == &F->getEntryBlock()) {
      if (entryBBs.find(BB) != entryBBs.end()) {
        RA_LOG("Entry func " << F->getName() << " is reachable\n");
        break;
        // continue;
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
            // distances[CBB] = dist;
            callDistances[CI] = dist;
            queuedCalls.insert(CI);
            if (queued.insert(CBB).second)
              worklist.push_back(CBB);
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
            // distances[CBB] = dist;
            callDistances[CI] = dist;
            queuedCalls.insert(CI);
            if (queued.insert(CBB).second)
              worklist.push_back(CBB);
          }
        }
      }
    }
  }

  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    doFinalization(i->first);
  }
}

ReachableCallGraphPass::ReachableCallGraphPass(GlobalContext *Ctx_,
  std::string &TargetList, std::string &EntryList, bool typeBased)
  : Ctx(Ctx_), UseTypeBasedCallGraph(typeBased) {
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
void getDebugLocationFullPath(const BasicBlock &BB,
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

void ReachableCallGraphPass::dumpDistance(std::ostream &OS, bool dumpSolution, bool dumpUnreachable) {
  std::deque<const BasicBlock*> worklist;
  std::unordered_set<const BasicBlock*> visited;
  double currentDist = std::numeric_limits<double>::max();;
  for (auto BB : entryBBs) {
    if (distances.find(BB) != distances.end()) {
      RA_LOG("Entry BB of " << BB->getParent()->getName() << " is reachable\n");
      worklist.push_back(BB);
      visited.insert(BB);
    }
  }
  if (worklist.empty()) {
    WARNING("Target not reachable from entry BBs\n");
    return;
  }

  // set precision
  OS << std::fixed << std::setprecision(6);

  // dump reachable bb
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    auto dist = distances[BB];
    if (dumpSolution && (dist < currentDist)) {
      currentDist = dist;
      RA_LOG("Best option: " << BB->getParent()->getName() << " at " << currentDist << "\n");
    }
    OS << getBasicBlockId(BB) << "," << getSourceLocation(BB) << "," << distances[BB] * 1000 << "\n";

    for (auto &I : *BB) {
      // check for callees
      if (const CallBase *CI = dyn_cast<CallBase>(&I)) {
        auto itr = Ctx->Callees.find(CI);
        if (itr == Ctx->Callees.end() && UseTypeBasedCallGraph) {
          itr = calleeByType.find(CI);
        }
        for (auto F: itr->second) {
          auto *FBB = &F->getEntryBlock();
          if (distances.find(FBB) != distances.end() && visited.insert(FBB).second) {
            worklist.push_back(FBB);
          }
        }
      }
    }
    for (auto SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      auto *Succ = *SI;
      if (distances.find(Succ) != distances.end() && visited.insert(Succ).second) {
        worklist.push_back(Succ);
      }
    }
  }
  // dump unreachable bb
  if (dumpUnreachable) {
    for (auto BB : exitBBs) {
      if (distances.find(BB) == distances.end()) {
        OS << getBasicBlockId(BB) << "," << getSourceLocation(BB) << ",-1\n";
      }
    }
  }
}

void ReachableCallGraphPass::dumpPolicy(std::ostream &OS) {

  // set precision
  OS << std::fixed << std::setprecision(6);

  for (const auto &kv : distances) {
    auto *BB = kv.first;
    auto term = BB->getTerminator();
    auto branch = dyn_cast<BranchInst>(term);
    if (!branch || !branch->isConditional())
      continue;
    auto TT = branch->getSuccessor(0);
    auto FT = branch->getSuccessor(1);
    bool reached = false;
    OS << getBasicBlockId(BB) << ",";
    auto itr = distances.find(FT);
    if (itr != distances.end()) {
      OS << itr->second * 1000 << ",";
      reached = true;
    } else {
      OS << "inf,";
    }
    itr = distances.find(TT);
    if (itr != distances.end()) {
      OS << itr->second * 1000 << "\n";
      reached = true;
    } else {
      OS << "inf\n";
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
        WARNING("Branch reachable but both targets are not!! " << *BB
            << "\nAnd no call in the BB\n");
      }
    }
  }

  OS << "##########\n";

  for (auto const &CI : reachableIndirectCalls) {
    // dump callsite ID = (BBID, order)
    auto CBB = CI->getParent();
    auto CBBID = getBasicBlockId(CBB);
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
          bbLocs << bb_id << "," << F.getGUID() << "," << filepath << ":" << line << "\n";

      }
      if (!filepath.empty() && minLine != std::numeric_limits<unsigned>::max() && maxLine != 0)
        funcInfo << F.getGUID() << "," << F.getName().str() << "," << filepath << "," << minLine << "," << maxLine << "\n";
    }
  }
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
