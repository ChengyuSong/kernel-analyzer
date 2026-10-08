/*
 * Driver pieces shared by KAMain and the CFL baseline (KABaseline):
 * process setup, input loading, memory limit, the iterative module-pass
 * driver, and the corpus-level preparation every analysis needs.
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 Byoungyoung Lee
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2015 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <chrono>
#include <cstring>
#include <fstream>
#include <map>
#include <new>
#include <set>
#include <sys/resource.h>
#include <thread>
#include <unistd.h>

#include "Driver.h"
#include "IRCensus.h"

using namespace llvm;

// RSS watchdog (mem-limit-mode=rss): polls resident size and fails
// loud before the kernel OOM-killer picks a victim. Forked batch
// workers lose the parent's thread — they re-arm via this hook.
uint64_t KAMemLimitRssBytes = 0;
void kaStartRssWatchdog() {
  if (KAMemLimitRssBytes == 0)
    return;
  std::thread([] {
    for (;;) {
      std::this_thread::sleep_for(std::chrono::seconds(2));
      std::ifstream st("/proc/self/status");
      std::string line;
      while (std::getline(st, line)) {
        if (line.rfind("VmRSS:", 0) != 0)
          continue;
        const uint64_t kb = std::stoull(line.substr(6));
        if (kb * 1024ull > KAMemLimitRssBytes) {
          errs() << "ERROR: Out of memory: VmRSS " << (kb >> 20)
                 << " GB exceeded the " << (KAMemLimitRssBytes >> 30)
                 << " GB limit. Increase --mem-limit, use "
                    "--mem-limit-mode=off under a cgroup, or reduce "
                    "input/batch size.\n";
          _exit(1);
        }
        break;
      }
    }
  }).detach();
}

GlobalContext GlobalCtx;

#define Diag llvm::errs()

void IterativeModulePass::run(ModuleList &modules) {

  ModuleList::iterator i, e;
  Diag << "[" << ID << "] Initializing " << modules.size() << " modules\n";
  bool again = true;
  Iteration = 0;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      again |= doInitialization(i->first);
      // Diag << ".";
    }
    Iteration++;
  }
  Diag << "\n";

  unsigned changed = 1;
  while (changed) {
    changed = 0;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      Diag << "[" << ID << " / " << Iteration << "] ";
      // FIXME: Seems the module name is incorrect, and perhaps it's a bug.
      Diag << "[" << i->second << "]\n";

      bool ret = doModulePass(i->first);
      if (ret) {
        ++changed;
        Diag << "\t [CHANGED]\n";
      } else
        Diag << "\n";
    }
    Diag << "[" << ID << "] Updated in " << changed << " modules.\n";
    Iteration++;
  }

  Diag << "[" << ID << "] Postprocessing ...\n";
  again = true;
  Iteration = 0;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      // TODO: Dump the results.
      again |= doFinalization(i->first);
    }
    Iteration++;
  }

  Diag << "[" << ID << "] Done!\n\n";
}

// --cfl-clone-per-caller: expand listed functions per direct call site.
static void clonePerCaller(Module *M) {
  if (CFLClonePerCaller.empty()) return;
  SmallVector<StringRef, 8> given;
  StringRef(CFLClonePerCaller).split(given, ',', -1, false);
  // Callers before callees: a caller's clones then each get their own
  // clones of the callee (cloning the callee first would leave every
  // caller clone sharing the callee clone of its one call site).
  SmallVector<StringRef, 8> names;
  {
    std::vector<StringRef> rest(given.begin(), given.end());
    auto calledByRest = [&](StringRef b) {
      Function *FB = M->getFunction(b.trim());
      if (!FB) return false;
      for (User *U : FB->users())
        if (auto *CB = dyn_cast<CallBase>(U))
          for (StringRef a : rest)
            if (a != b && CB->getFunction()->getName() == a.trim())
              return true;
      return false;
    };
    while (!rest.empty()) {
      size_t pick = 0;
      for (size_t i = 0; i < rest.size(); i++)
        if (!calledByRest(rest[i])) { pick = i; break; }
      names.push_back(rest[pick]);
      rest.erase(rest.begin() + pick);
    }
  }
  for (StringRef nm : names) {
    Function *F = M->getFunction(nm.trim());
    if (!F || F->isDeclaration()) continue;
    // External call sites only: a recursive function's clone keeps its
    // recursion inside itself (the whole recursion runs in that caller's
    // context: fts3ExprIterate2 carries one caller's callback and context).
    SmallVector<CallBase *, 16> sites;
    for (User *U : F->users())
      if (auto *CB = dyn_cast<CallBase>(U))
        if (CB->getCalledOperand() == F && CB->getFunction() != F) sites.push_back(CB);
    if (sites.size() < 2) continue;
    unsigned k = 0;
    for (CallBase *CB : sites) {
      ValueToValueMapTy VMap;
      Function *C = CloneFunction(F, VMap);
      C->setName(F->getName() + ".site" + Twine(k++));
      C->setLinkage(GlobalValue::InternalLinkage);
      for (Instruction &I : instructions(*C))
        if (auto *SC = dyn_cast<CallBase>(&I))
          if (SC->getCalledOperand() == F) SC->setCalledFunction(C);
      CB->setCalledFunction(C);
    }
    // The original stays (uncalled): later phases hold raw Function*
    // observers, and erasing it left them dangling (teardown crash).
    bool calledOutside = false;
    for (User *U : F->users())
      calledOutside |= !isa<CallBase>(U) || cast<CallBase>(U)->getFunction() != F;
    errs() << "ClonePerCaller: " << nm << " -> " << k << " clones"
           << (!calledOutside ? " (original now uncalled)"
                              : " (original kept: address taken)")
           << "\n";
  }
}

void doBasicInitialization(Module *M) {
  // struct analysis
  GlobalCtx.structAnalyzer.run(M, &(M->getDataLayout()));

  // collect global object definitions
  for (GlobalVariable &GV : M->globals()) {
    auto GVID = GV.getGUID();
    if (GV.hasExternalLinkage() || GV.hasExternalWeakLinkage()) {
      if (!GV.isDeclaration()) {
        assert(GV.hasInitializer());
        if (GlobalCtx.Gobjs.count(GVID) != 0) {
          // check for weak linkage
          if (GV.hasWeakLinkage()) {
            // keep the previous definition, even if it's weak too
            continue;
          } else if (!GlobalCtx.Gobjs[GVID]->hasWeakLinkage()) {
            // both are not weak
            WARNING("Global variable " << GV.getName()
                << " has been defined multiple times, previously in "
                << GlobalCtx.Gobjs[GVID]->getParent()->getModuleIdentifier()
                << ", and now in " << M->getModuleIdentifier() << "\n");
            continue;
          } // else fall through to replace weak definition
        }
        GlobalCtx.Gobjs[GVID] = &GV;
      } else {
        GlobalCtx.ExtGobjs[GVID] = &GV;
      }
    } else if (GV.hasInitializer()) {
      GlobalCtx.Gobjs[GVID] = &GV;
    }
  }

  // collect global function definitions
  for (Function &F : *M) {
    // Accept external, linkonce_odr, and weak_odr linkage.
    // C++ constructors/destructors often have linkonce_odr or weak_odr
    // linkage (e.g., inline definitions, template instantiations).
    if (!F.hasLocalLinkage()) {
      auto FID = F.getGUID();
      if (!F.isDeclaration() && !F.empty()) {
        if (GlobalCtx.Funcs.count(FID) != 0) {
          // check for weak/linkonce linkage
          if (F.isWeakForLinker()) {
            // keep the previous definition
            continue;
          } else if (!GlobalCtx.Funcs[FID]->isWeakForLinker()) {
            // both are strong definitions
            WARNING("Function " << F.getName()
                << " has been defined multiple times, previously in "
                << GlobalCtx.Funcs[FID]->getParent()->getModuleIdentifier()
                << ", and now in " << M->getModuleIdentifier() << "\n");
            continue;
          } // else fall through to replace weak/linkonce definition
        }
        GlobalCtx.Funcs[FID] = &F;
      } else {
        GlobalCtx.ExtFuncs[FID] = &F;
      }
    }
  }

  // Resolve global aliases (e.g., Itanium ABI C1->C2 constructor
  // aliases) with LINKER SEMANTICS: a strong alias overrides a weak
  // definition (kernel COND_SYSCALL: sys_ni.o carries weak -ENOSYS
  // stubs for hundreds of syscalls whose real bodies live elsewhere
  // behind strong aliases; count==0-only insertion made the binding
  // module-order-dependent — found via cross-machine pin divergence,
  // 2026-09-01).
  for (GlobalAlias &GA : M->aliases()) {
    if (GA.hasLocalLinkage())
      continue;
    auto *Aliasee = dyn_cast<Function>(GA.getAliasee()->stripPointerCasts());
    if (!Aliasee || Aliasee->isDeclaration() || Aliasee->empty())
      continue;
    auto AliasID = GA.getGUID();
    auto it = GlobalCtx.Funcs.find(AliasID);
    if (it == GlobalCtx.Funcs.end()) {
      GlobalCtx.Funcs[AliasID] = Aliasee;
    } else if (!GA.isWeakForLinker() && it->second->isWeakForLinker()) {
      // strong alias beats weak def (the COND_SYSCALL case). NOTE:
      // the stored Function is the prior BINDING's target; for a
      // prior strong-alias binding its aliasee's strength stands in
      // for the alias's — exact only up to duplicate strong symbols,
      // which are illegal input and warned below.
      GlobalCtx.Funcs[AliasID] = Aliasee;
    } else if (!GA.isWeakForLinker() && !it->second->isWeakForLinker() &&
               it->second != Aliasee) {
      WARNING("Alias " << GA.getName() << " conflicts with existing "
              "strong binding " << it->second->getName() << "\n");
    } // weak alias never overrides an existing binding
    // also remove from ExtFuncs if present
    GlobalCtx.ExtFuncs.erase(AliasID);
  }
}

void kaStartProcess(int argc, char **argv) {
  kaElapsedSec(); // anchor the --log-timestamps clock at process start

#ifdef SET_STACK_SIZE
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0) {
    rl.rlim_cur = SET_STACK_SIZE;
    setrlimit(RLIMIT_STACK, &rl);
  }
#endif

  // Print a stack trace if we signal out.
  sys::PrintStackTraceOnErrorSignal(argv[0]);
}

void kaRefuseRemovedFlags(int argc, char **argv,
                          ArrayRef<RemovedFlag> removed) {
  bool any = false;
  for (int i = 1; i < argc; i++) {
    StringRef A(argv[i]);
    if (!A.consume_front("-"))
      continue;
    A.consume_front("-");
    const StringRef name = A.split('=').first;
    for (const RemovedFlag &R : removed)
      if (name == R.name) {
        errs() << argv[0] << ": --" << R.name << " was removed: "
               << R.replacement << "\n";
        any = true;
      }
  }
  if (any)
    exit(1);
}

int kaReadInputList(const char *argv0) {
  if (!BCListFile.empty()) {
    std::ifstream ListFile(BCListFile);
    if (!ListFile.is_open()) {
      errs() << argv0 << ": error opening bc-list file '" << BCListFile << "'\n";
      return 1;
    }
    std::string Line;
    while (std::getline(ListFile, Line)) {
      if (!Line.empty())
        InputFilenames.push_back(Line);
    }
  }

  if (InputFilenames.empty()) {
    errs() << argv0 << ": no input files specified (use positional args or --bc-list)\n";
    return 1;
  }

  return 0;
}

int kaApplyMemLimit() {
  if (MemLimitMode != "rss" && MemLimitMode != "as" && MemLimitMode != "off") {
    errs() << "ERROR: --mem-limit-mode must be rss, as, or off\n";
    return 1;
  }
  if (MemLimitPct > 0 && MemLimitMode != "off") {
    long pages = sysconf(_SC_PHYS_PAGES);
    long pageSize = sysconf(_SC_PAGE_SIZE);
    if (pages > 0 && pageSize > 0) {
      rlim_t totalBytes = (rlim_t)pages * pageSize;
      rlim_t limitBytes = totalBytes * std::min(MemLimitPct.getValue(), 100) / 100;
      if (MemLimitMode == "as") {
        struct rlimit rl;
        rl.rlim_cur = rl.rlim_max = limitBytes;
        if (setrlimit(RLIMIT_AS, &rl) == 0) {
          Diag << "Memory limit set to " << (limitBytes >> 30) << " GB ("
               << MemLimitPct << "% of " << (totalBytes >> 30)
               << " GB RAM, RLIMIT_AS)\n";
        } else {
          errs() << "Warning: failed to set memory limit\n";
        }
      } else {
        // RSS watchdog: poll resident size and fail LOUD before the
        // kernel OOM-killer picks a victim. Unlike RLIMIT_AS this
        // measures memory actually used — allocator arena
        // reservations, transient vector doublings, fragmentation and
        // mapped bitcode files do not count (the big-machine run died
        // at 289GB RSS under a 560GB AS cap on a 700GB box).
        Diag << "Memory limit set to " << (limitBytes >> 30) << " GB ("
             << MemLimitPct << "% of " << (totalBytes >> 30)
             << " GB RAM, RSS watchdog)\n";
        KAMemLimitRssBytes = (uint64_t)limitBytes;
        kaStartRssWatchdog();
      }
      // Disable core dumps — a core from a memory-exhausted process is huge
      struct rlimit rc;
      rc.rlim_cur = rc.rlim_max = 0;
      setrlimit(RLIMIT_CORE, &rc);
      // Handle allocation failure in any thread (including solver workers)
      std::set_new_handler([] {
        errs() << "ERROR: Out of memory. Increase --mem-limit or reduce input size.\n";
        _exit(1);
      });
    }
  }
  return 0;
}

int kaLoadModules(const char *argv0) {
  SMDiagnostic Err;

  // Loading modules
  Diag << "Total " << InputFilenames.size() << " file(s)\n";

  for (unsigned i = 0; i < InputFilenames.size(); ++i) {
    // use separate LLVMContext to avoid type renaming
    Diag << "Input Filename : "<< InputFilenames[i] << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

    if (M == NULL) {
      errs() << argv0 << ": error loading file '"
        << InputFilenames[i] << "'\n";
      continue;
    }
    // (load failures are counted below; an all-failed corpus must not
    // "succeed" on zero modules)

    Module *Module = M.release();
    StringRef MName = StringRef(strdup(InputFilenames[i].data()));
    GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
    GlobalCtx.ModuleMaps[Module] = InputFilenames[i];

    clonePerCaller(Module);
    doBasicInitialization(Module);
  }

  if (GlobalCtx.Modules.empty() && !InputFilenames.empty()) {
    errs() << argv0 << ": FATAL: 0 of " << InputFilenames.size()
           << " input files loaded (wrong paths / not bitcode?) — refusing "
              "to run the analysis on an empty corpus\n";
    return 1;
  }
  if (GlobalCtx.Modules.size() < InputFilenames.size())
    errs() << "[WARN] " << (InputFilenames.size() - GlobalCtx.Modules.size())
           << "/" << InputFilenames.size()
           << " input files failed to load — answers cover the loaded "
              "subset only\n";

  // one more preprocessing to clear defined global variables and functions
  for (auto &[id, gv] : GlobalCtx.Gobjs) { GlobalCtx.ExtGobjs.erase(id); }
  for (auto &[id, f] : GlobalCtx.Funcs) { GlobalCtx.ExtFuncs.erase(id); }

  // Initialize node factory
  GlobalCtx.nodeFactory.setStructAnalyzer(&GlobalCtx.structAnalyzer);
  GlobalCtx.nodeFactory.setGobjMap(&GlobalCtx.Gobjs);
  GlobalCtx.nodeFactory.setExtGobjMap(&GlobalCtx.ExtGobjs);
  GlobalCtx.nodeFactory.setFuncMap(&GlobalCtx.Funcs);
  GlobalCtx.nodeFactory.setExtFuncMap(&GlobalCtx.ExtFuncs);

  return 0;
}

void kaSelectFieldBuckets() {
  // Data-driven Z_P selection (--cfl-field-buckets-auto): modules are
  // loaded, so census the fn-ptr slot offsets and pick the smallest
  // prime meeting the residual target. Explicit --cfl-field-buckets
  // takes precedence.
  if (CFLFieldBucketsAuto) {
    if (CFLFieldBuckets.getNumOccurrences() > 0) {
      errs() << "FieldBucketsAuto: explicit --cfl-field-buckets="
             << CFLFieldBuckets << " wins; auto selection skipped\n";
    } else {
      std::map<std::string, std::set<uint64_t>> slots;
      kaCollectFnPtrOffsets(
          GlobalCtx.Modules,
          [&](StringRef sName, uint64_t off, StringRef) {
            slots[sName.str()].insert(off);
          });
      uint64_t totalPairs = 0;
      for (auto &kv : slots) {
        uint64_t n = kv.second.size();
        totalPairs += n * (n - 1) / 2;
      }
      auto residualAt = [&](unsigned P) {
        uint64_t coll = 0;
        for (auto &kv : slots) {
          std::map<uint64_t, uint64_t> res;
          for (uint64_t o : kv.second)
            res[o % P]++;
          for (auto &rc : res)
            coll += rc.second * (rc.second - 1) / 2;
        }
        return coll;
      };
      auto isPrime = [](unsigned n) {
        if (n < 2) return false;
        for (unsigned d = 2; d * d <= n; d++)
          if (n % d == 0) return false;
        return true;
      };
      unsigned chosen = 0;
      uint64_t chosenColl = 0;
      const uint64_t budget =
          totalPairs * (uint64_t)CFLAutoBucketsResidualBP / 10000;
      for (unsigned P = 11; P <= CFLAutoBucketsMax; P++) {
        if (!isPrime(P)) continue;
        uint64_t c = residualAt(P);
        if (c <= budget) { chosen = P; chosenColl = c; break; }
      }
      if (chosen == 0) {
        // No prime within the cap meets the target: take the best
        // prime under the cap and say so loudly (no silent fallback).
        uint64_t bestC = UINT64_MAX;
        for (unsigned P = 11; P <= CFLAutoBucketsMax; P++) {
          if (!isPrime(P)) continue;
          uint64_t c = residualAt(P);
          if (c < bestC) { bestC = c; chosen = P; }
        }
        chosenColl = bestC;
        errs() << "WARNING: FieldBucketsAuto: residual target "
               << CFLAutoBucketsResidualBP << "bp needs P > cap "
               << CFLAutoBucketsMax << "; taking P=" << chosen
               << " with " << chosenColl << "/" << totalPairs
               << " colliding same-struct pairs\n";
      }
      CFLFieldBuckets = chosen;
      errs() << "FieldBucketsAuto: P=" << chosen << " ("
             << slots.size() << " structs, " << totalPairs
             << " same-struct offset pairs, " << chosenColl
             << " colliding at P = "
             << (totalPairs ? 10000.0 * chosenColl / totalPairs : 0.0)
             << "bp; cap " << CFLAutoBucketsMax << ")\n";
    }
  }

}

int kaIRCensusGate(bool &exitNow) {
  exitNow = false;
  if (IRCensusOpt || IRCensusStrict || !IRCensusOut.empty()) {
    IRCensusResult CR =
        runIRCensus(&GlobalCtx, IRCensusOut, /*printTables=*/IRCensusOpt);
    if (IRCensusStrict && CR.undispKinds > 0) {
      errs() << "IR-CENSUS STRICT: closed-world violated — "
             << CR.undispKinds << " undispositioned construct kind(s):\n";
      for (const std::string &N : CR.undispNames)
        errs() << "IR-CENSUS STRICT:   " << N << "\n";
      errs() << "IR-CENSUS STRICT: the edge builder's default visitor is a "
                "silent no-op; refusing to analyze a corpus it has no "
                "disposition for\n";
      abort();
    }
    if (IRCensusOpt) {
      exitNow = true;
      return CR.undispKinds > 0 ? 1 : 0;
    }
    // strict/out without --ir-census: gate passed, continue to analysis
  }
  return 0;
}
