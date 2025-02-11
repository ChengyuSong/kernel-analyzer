/*
 * main function
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 Byoungyoung Lee
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2015 - 2024 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/SystemUtils.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/Path.h>

#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>

#include "Global.h"
#include "Pass.h"
#include "PointTo.h"
#include "TyPMPass.h"
#include "Reachable.h"

using namespace llvm;

cl::list<std::string> InputFilenames(
  cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
  "verbose", cl::desc("Verbose level"), cl::init(0));

cl::opt<std::string> TargetList(
  "target-list", cl::desc("Target list"), cl::init(""));

cl::opt<std::string> EntryList(
  "entry-list", cl::desc("Entry list"), cl::init(""));

cl::opt<std::string> DumpPolicy(
  "dump-policy", cl::desc("Dump static policy"), cl::init(""));

cl::opt<std::string> DumpDistance(
  "dump-distance", cl::desc("Dump distance"), cl::init(""));


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

void doBasicInitialization(Module *M) {
  // struct analysis
  GlobalCtx.structAnalyzer.run(M, &(M->getDataLayout()));

  // collect global object definitions
  for (GlobalVariable &GV : M->globals()) {
    auto GVID = GV.getGUID();
    if (GV.hasExternalLinkage()) {
      if (!GV.isDeclaration()) {
        assert(GV.hasInitializer());
        if (GlobalCtx.Gobjs.count(GVID) != 0) {
          WARNING("Global variable " << GV.getName()
              << " has been defined multiple times, previously in "
              << GlobalCtx.Gobjs[GVID]->getParent()->getModuleIdentifier()
              << ", and now in " << M->getModuleIdentifier() << "\n");
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
    if (F.hasExternalLinkage()) {
      // external linkage always ends up with the function name
      auto FID = F.getGUID();
      if (!F.isDeclaration() && !F.empty()) {
	if (GlobalCtx.Funcs.count(FID) != 0) {
	  WARNING("Function " << F.getName()
              << " has been defined multiple times, previously in "
              << GlobalCtx.Funcs[FID]->getParent()->getModuleIdentifier()
              << ", and now in " << M->getModuleIdentifier() << "\n");
	}
        GlobalCtx.Funcs[FID] = &F;
      } else {
        GlobalCtx.ExtFuncs[FID] = &F;
      }
    }
  }
}

int main(int argc, char **argv) {

#ifdef SET_STACK_SIZE
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0) {
    rl.rlim_cur = SET_STACK_SIZE;
    setrlimit(RLIMIT_STACK, &rl);
  }
#endif

  // Print a stack trace if we signal out.
#if LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 9
  sys::PrintStackTraceOnErrorSignal();
#else
  sys::PrintStackTraceOnErrorSignal(argv[0]);
#endif
  PrettyStackTraceProgram X(argc, argv);

  llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

  cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
  SMDiagnostic Err;

  // Loading modules
  Diag << "Total " << InputFilenames.size() << " file(s)\n";

  for (unsigned i = 0; i < InputFilenames.size(); ++i) {
    // use separate LLVMContext to avoid type renaming
    Diag << "Input Filename : "<< InputFilenames[i] << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

    if (M == NULL) {
      errs() << argv[0] << ": error loading file '"
        << InputFilenames[i] << "'\n";
      continue;
    }

    Module *Module = M.release();
    StringRef MName = StringRef(strdup(InputFilenames[i].data()));
    GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
    GlobalCtx.ModuleMaps[Module] = InputFilenames[i];

    doBasicInitialization(Module);
  }

  // one more preprocessing to clear defined global variables and functions
  for (auto &[id, gv] : GlobalCtx.Gobjs) { GlobalCtx.ExtGobjs.erase(id); }
  for (auto &[id, f] : GlobalCtx.Funcs) { GlobalCtx.ExtFuncs.erase(id); }

  // Main workflow
  TyPMCGPass TyCG(&GlobalCtx);
  TyCG.run(GlobalCtx.Modules);

  ReachableCallGraphPass RCGPass(&GlobalCtx, TargetList, EntryList, false);
  RCGPass.run(GlobalCtx.Modules);
  if (!DumpPolicy.empty()) {
    std::ofstream policy(DumpPolicy);
    RCGPass.dumpPolicy(policy);
  }
  if (!DumpDistance.empty()) {
    std::ofstream distance(DumpDistance);
    RCGPass.dumpDistance(distance, true, true);
  }

  return 0;
}
