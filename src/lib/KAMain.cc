/*
 * main function
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 Byoungyoung Lee
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2015 - 2026 Chengyu Song
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
#include <fstream>
#include <new>
#include <sys/resource.h>
#include <unistd.h>

#include "Global.h"
#include "Pass.h"
#include "PointTo.h"
#include "CallGraph.h"
#include "Reachable.h"
#include "LLMClient.h"
#include "LLMAnalysis.h"

using namespace llvm;

cl::list<std::string> InputFilenames(
  cl::Positional, cl::ZeroOrMore, cl::desc("<input bitcode files>"));

cl::opt<std::string> BCListFile(
  "bc-list", cl::desc("File containing input bitcode file paths, one per line"), cl::init(""));

cl::opt<unsigned> VerboseLevel(
  "verbose", cl::desc("Verbose level"), cl::init(0));

cl::opt<bool> CFLGlobalDedup(
  "cfl-global-dedup",
  cl::desc("Enable global union-find dedup with dense ID remapping for CFL edge construction"),
  cl::init(true));

cl::opt<bool> CFLLocalAllocaSummary(
  "cfl-local-alloca-summary",
  cl::desc("Enable non-escaping local alloca store/load summarization in CFL edge construction"),
  cl::init(true));

cl::opt<std::string> DumpBidMapping(
  "dump-bid-mapping", cl::desc("Dump basic block ID mapping, format: bid,fun_GUID,filepath:linenum"), cl::init(""));

cl::opt<std::string> DumpFuncInfo(
  "dump-func-info", cl::desc("Dump function info, format: fun_GUID,fun_name,filepath,start_linenum,end_linenum"), cl::init(""));

cl::opt<std::string> DumpAnnotatedIR(
  "dump-annotated-ir", cl::desc("Dump annotated IR"), cl::init(""));

cl::opt<std::string> GrammarFile(
  "grammar-file", cl::desc("Grammar file for CFL-reachability analysis"), cl::init(""));

cl::opt<std::string> CFLEdgeOutput(
  "cfl-edge-output", cl::desc("Output file for CFL-reachability edges"), cl::init(""));

cl::opt<std::string> VSnapshotOutput(
  "v-snapshot", cl::desc("Output file for compact CFL V-relation snapshot"), cl::init(""));

cl::opt<std::string> LLMServerHost(
  "llm-server-host", cl::desc("Hostname of local LLM server"), cl::init(""));

cl::opt<unsigned> LLMServerPort(
  "llm-server-port", cl::desc("Port of local LLM server"), cl::init(0));

cl::opt<bool> QueryLLM(
  "query-llm", cl::desc("Run LLM queries, save results to files, then exit"), cl::init(false));

cl::opt<std::string> AllocatorFile(
  "allocator-file", cl::desc("Path to allocator candidates JSON file (read or write)"), cl::init(""));

cl::opt<std::string> ContainerFile(
  "container-file", cl::desc("Path to container functions JSON file (read or write)"), cl::init(""));

cl::opt<std::string> CallGraphJSON(
  "callgraph-json", cl::desc("Export call graph to JSON file"), cl::init(""));

cl::opt<int> MemLimitPct(
  "mem-limit", cl::desc("Memory limit as percentage of physical RAM (0 = unlimited, default 80)"), cl::init(80));

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

  // Resolve global aliases (e.g., Itanium ABI C1->C2 constructor aliases)
  for (GlobalAlias &GA : M->aliases()) {
    if (GA.hasLocalLinkage())
      continue;
    auto *Aliasee = dyn_cast<Function>(GA.getAliasee()->stripPointerCasts());
    if (!Aliasee || Aliasee->isDeclaration() || Aliasee->empty())
      continue;
    auto AliasID = GA.getGUID();
    if (GlobalCtx.Funcs.count(AliasID) == 0)
      GlobalCtx.Funcs[AliasID] = Aliasee;
    // also remove from ExtFuncs if present
    GlobalCtx.ExtFuncs.erase(AliasID);
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

  if (!BCListFile.empty()) {
    std::ifstream ListFile(BCListFile);
    if (!ListFile.is_open()) {
      errs() << argv[0] << ": error opening bc-list file '" << BCListFile << "'\n";
      return 1;
    }
    std::string Line;
    while (std::getline(ListFile, Line)) {
      if (!Line.empty())
        InputFilenames.push_back(Line);
    }
  }

  if (InputFilenames.empty()) {
    errs() << argv[0] << ": no input files specified (use positional args or --bc-list)\n";
    return 1;
  }

  if (MemLimitPct > 0) {
    long pages = sysconf(_SC_PHYS_PAGES);
    long pageSize = sysconf(_SC_PAGE_SIZE);
    if (pages > 0 && pageSize > 0) {
      rlim_t totalBytes = (rlim_t)pages * pageSize;
      rlim_t limitBytes = totalBytes * std::min(MemLimitPct.getValue(), 100) / 100;
      struct rlimit rl;
      rl.rlim_cur = rl.rlim_max = limitBytes;
      if (setrlimit(RLIMIT_AS, &rl) == 0) {
        Diag << "Memory limit set to " << (limitBytes >> 30) << " GB ("
             << MemLimitPct << "% of " << (totalBytes >> 30) << " GB RAM)\n";
      } else {
        errs() << "Warning: failed to set memory limit\n";
      }
      // Disable core dumps — a core from a memory-exhausted process is huge
      rl.rlim_cur = rl.rlim_max = 0;
      setrlimit(RLIMIT_CORE, &rl);
      // Handle allocation failure in any thread (including solver workers)
      std::set_new_handler([] {
        errs() << "ERROR: Out of memory. Increase --mem-limit or reduce input size.\n";
        _exit(1);
      });
    }
  }
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

  // Initialize node factory
  GlobalCtx.nodeFactory.setStructAnalyzer(&GlobalCtx.structAnalyzer);
  GlobalCtx.nodeFactory.setGobjMap(&GlobalCtx.Gobjs);
  GlobalCtx.nodeFactory.setExtGobjMap(&GlobalCtx.ExtGobjs);
  GlobalCtx.nodeFactory.setFuncMap(&GlobalCtx.Funcs);
  GlobalCtx.nodeFactory.setExtFuncMap(&GlobalCtx.ExtFuncs);

  // Main workflow

  // CFL-reachability edge construction
  if (GrammarFile.empty()) {
    if (!GlobalCtx.edgeBuilder.initializeGrammar(DefaultP2Grammar)) {
      errs() << "Failed to initialize CFL edge builder with default grammar\n";
    }
  } else {
    if (!GlobalCtx.edgeBuilder.initializeGrammar(GrammarFile)) {
      errs() << "Failed to initialize CFL edge builder with grammar file: " << GrammarFile << "\n";
    }
  }

  std::unique_ptr<LLMClient> LLM;
  if (!LLMServerHost.empty()) {
    if (LLMServerPort == 0) {
      WARNING("Ignoring --llm-server-host because --llm-server-port is 0\n");
    } else {
      std::string Endpoint = "http://" + LLMServerHost + ":" +
                             std::to_string(LLMServerPort) +
                             "/v1/chat/completions";
      LLMClientConfig LLMConfig;
      LLMConfig.Enabled = true;
      LLMConfig.Endpoint = Endpoint;
      LLM = std::make_unique<LLMClient>(std::move(LLMConfig));
      Diag << "LLM server endpoint: " << Endpoint << "\n";
    }
  }

  // LLM query / file loading for allocator candidates
  if (QueryLLM) {
    if (!LLM) {
      errs() << "Error: --query-llm requires --llm-server-host and --llm-server-port\n";
      return 1;
    }
    for (auto &[M, Name] : GlobalCtx.Modules) {
      queryAllocatorCandidates(&GlobalCtx, LLM.get(), M);
    }
    if (!AllocatorFile.empty())
      saveAllocatorResults(&GlobalCtx, AllocatorFile);
    return 0;
  } else {
    // If not querying LLM, load candidates from files if provided
    // loadAllocatorFile returns: 1 = loaded, 0 = file not available, -1 = parse error
    bool allocLoaded = !AllocatorFile.empty() && loadAllocatorFile(&GlobalCtx, AllocatorFile) > 0;
    if (!allocLoaded && LLM) {
      for (auto &[M, Name] : GlobalCtx.Modules) {
        queryAllocatorCandidates(&GlobalCtx, LLM.get(), M);
      }
    }
  }
  // load container candidates from file or query LLM
  if (!ContainerFile.empty()) {
    loadContainerFile(&GlobalCtx, ContainerFile);
  }

  CallGraphPass CGPass(&GlobalCtx, LLM.get());
  CGPass.run(GlobalCtx.Modules);

  if (!CFLEdgeOutput.empty()) {
    GlobalCtx.edgeBuilder.outputEdgesToFile(CFLEdgeOutput);
  }

  if (!CallGraphJSON.empty()) {
    CGPass.dumpCallGraphJSON(CallGraphJSON);
  }
  if (!VSnapshotOutput.empty()) {
    CGPass.dumpVSnapshot(VSnapshotOutput);
  }

  if (!AllocatorFile.empty())
    saveAllocatorResults(&GlobalCtx, AllocatorFile);

  return 0;
}
