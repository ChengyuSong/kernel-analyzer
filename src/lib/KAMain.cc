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
#include "CallGraph.h"
#include "Pass.h"
#include "PointTo.h"

using namespace llvm;

cl::list<std::string> InputFilenames(
  cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
  "verbose", cl::desc("Verbose level"), cl::init(0));

// cl::opt<bool> DumpCallees(
//   "dump-call-graph", cl::desc("Dump call graph"), cl::NotHidden, cl::init(false));

// cl::opt<bool> DumpCallers(
//   "dump-caller-graph", cl::desc("Dump caller graph"), cl::NotHidden, cl::init(false));

// cl::opt<bool> DoSafeStack(
//   "safe-stack", cl::desc("Perfrom safe stack analysis"), cl::NotHidden, cl::init(false));

// cl::opt<bool> DumpStackStats(
//   "dump-stack-stats", cl::desc("Dump stack stats"), cl::NotHidden, cl::init(false));

// cl::opt<bool> DoLSS(
//   "linux-ss", cl::desc("Discover security sensitive data in Linux kernel"),
//   cl::NotHidden, cl::init(false));

GlobalContext GlobalCtx;

#define Diag llvm::errs()

void IterativeModulePass::run(ModuleList &modules) {

  ModuleList::iterator i, e;
  Diag << "[" << ID << "] Initializing " << modules.size() << " modules ";
  bool again = true;
  Iteration = 0;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      again |= doInitialization(i->first);
      Diag << ".";
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
    if (GV.hasExternalLinkage()) {
      auto GVID = GV.getGUID();
      if (!GV.isDeclaration()) {
        assert(GlobalCtx.Gobjs.count(GVID) == 0);
        GlobalCtx.Gobjs[GVID] = &GV;
      } else {
        GlobalCtx.ExtGobjs[GVID] = &GV;
      }
    }
  }

  // collect global function definitions
  for (Function &F : *M) {
    if (F.hasExternalLinkage()) {
      // external linkage always ends up with the function name
      auto FID = F.getGUID();
      if (!F.isDeclaration() && !F.empty()) {
        assert(GlobalCtx.Funcs.count(FID) == 0);
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

  // initialize nodefactory
  populateNodeFactory(GlobalCtx);

  // Main workflow
  CallGraphPass CGPass(&GlobalCtx);
  CGPass.run(GlobalCtx.Modules);
  CGPass.dumpCallees(errs());

//   if (DumpCallees)
//     CGPass.dumpCallees();

//   if (DumpCallers)
//     CGPass.dumpCallers();

//   if (DoSafeStack) {
// #ifdef DO_RANGE_ANALYSIS
//     RangePass RPass(&GlobalCtx);
//     RPass.run(GlobalCtx.Modules);
// #endif

//     SafeStackPass SSPass(&GlobalCtx);
//     SSPass.run(GlobalCtx.Modules);
//     if (DumpStackStats)
//       SSPass.dumpStats();
//   }

//   if (DoLSS) {
//     LinuxSS LSS(&GlobalCtx);
//     LSS.run(GlobalCtx.Modules);
//   }

  return 0;
}

