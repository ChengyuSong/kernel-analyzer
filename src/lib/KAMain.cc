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

#include <chrono>
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
#include "IRSidecar.h"
#include "IRCensus.h"

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

cl::opt<std::string> CompressedGraphOutput(
  "cfl-compressed-output",
  cl::desc("Output compressed CFL constraint graph"),
  cl::init(""));

cl::list<std::string> CompressedGraphInputs(
  "cfl-compressed-input",
  cl::desc("Compressed graph files for compositional solving"));

cl::opt<bool> CFLCompositional(
  "cfl-compositional",
  cl::desc("Run per-TU CFL solving and compose compressed results (default on)"),
  cl::init(true));

cl::opt<bool> CFLPreSolveMerge(
  "cfl-presolve-merge",
  cl::desc("Solve the memory-free a/f sublanguage first and merge mutual-V' "
           "classes before the full CFL solve (default off)"),
  cl::init(false));

cl::opt<bool> CFLFptrSlice(
  "cfl-fptr-slice",
  cl::desc("Keep only constraint-graph components reachable from function "
           "pointers (callgraph-only slicing, default off)"),
  cl::init(false));

cl::opt<bool> CFLFlowsTo(
  "cfl-flows-to",
  cl::desc("Resolve icalls by answer-anchored root propagation instead of "
           "all-pairs CFL saturation (v0: field-insensitive, monolithic)"),
  cl::init(false));

cl::opt<bool> CFLFlowsToSlice(
  "cfl-flows-to-slice",
  cl::desc("Before flows-to propagation, prune to the derivation slice: "
           "1-bit function->fptr taint with Steensgaard-class memory "
           "jumps, closed under alias-evidence origins"),
  cl::init(false));

cl::opt<bool> CFLResidueCopies(
  "cfl-residue-copies",
  cl::desc("Encode unknown-layout memcpy and aggregate accesses as per-"
           "residue field copies instead of wildcard loops (flows-to "
           "only; precise for struct-copy idioms, costly on container-"
           "churn C++ — evaluate per target codebase)"),
  cl::init(false));

cl::opt<std::string> CFLTraceFunc(
  "cfl-trace-func",
  cl::desc("Trace flows-to fact propagation for the address-taken function "
           "whose name contains this substring: log every class its root "
           "reaches (capped) and the final reach set, to localize where a "
           "flow is lost"),
  cl::init(""));

cl::opt<std::string> CFLTraceFptr(
  "cfl-trace-fptr",
  cl::desc("After the flows-to fixpoint, dump a backward slice from the "
           "fptr class of icalls in functions whose name contains this "
           "substring, annotated with traced-root presence, to localize "
           "where a flow is severed"),
  cl::init(""));

cl::opt<std::string> CFLTraceValue(
  "cfl-trace-value",
  cl::desc("At the flows-to fixpoint, dump class/facts/cells for every "
           "pointer value in functions whose name contains this substring"),
  cl::init(""));

cl::opt<bool> CFLCoTravelStats(
  "cfl-cotravel-stats",
  cl::desc("After the flows-to fixpoint, report root co-travel statistics: "
           "roots with identical (class, shift) incidence columns are "
           "bundleable into one plane bit — the ratio bounds the root-"
           "bundling win (native R planes only, bridged RB excluded)"),
  cl::init(false));

cl::opt<unsigned> CFLFlowsToMaxIters(
  "cfl-flows-to-max-iters",
  cl::desc("Cap on flows-to outer fixpoint iterations (resolve icalls -> "
           "wire callee arg/ret flows -> re-solve). Hitting the cap with "
           "unprocessed wirings is reported as an UNSOUND-RISK warning"),
  cl::init(10));

cl::opt<bool> CFLPrintfVarargSink(
  "cfl-printf-vararg-sink",
  cl::desc("Skip vararg-summary wiring at variadic callsites whose constant "
           "format string (last fixed param, __printf convention) proves the "
           "varargs are read-only renderer inputs: no capture, no dispatch, "
           "no %pV forwarding, no %n. Non-constant or non-benign formats "
           "keep full wiring"),
  cl::init(true));

cl::opt<bool> CFLVerifyClosure(
  "cfl-verify-closure",
  cl::desc("After the flows-to fixpoint, run one full non-delta scan of all "
           "propagation/join/bridge rules and assert none still fires — a "
           "per-run certificate of the closure property the delta/backlog "
           "machinery is supposed to maintain (the Lean SolverModel "
           "assumption)"),
  cl::init(false));

cl::opt<bool> CFLSolverProfile(
  "cfl-solver-profile",
  cl::desc("rdtsc phase accounting inside the flows-to pop loop (join / "
           "bridge / scan / wflag / a-prop / f-prop) to locate the time "
           "sink before optimizing"),
  cl::init(false));

cl::opt<unsigned> CFLFieldBuckets(
  "cfl-field-buckets",
  cl::desc("Number of bucketed field-offset labels for field-sensitive CFL "
           "memory modeling (0 = field-insensitive, default)"),
  cl::init(0));

cl::opt<bool> IRCensusOpt(
  "ir-census",
  cl::desc("Enumerate every IR construct kind in the corpus, classify "
           "each against the edge builder's disposition table (handled / "
           "justified no-op / suspect / undispositioned), print the "
           "census, then exit — the encoder totality audit"),
  cl::init(false));

cl::opt<bool> IRCensusStrict(
  "ir-census-strict",
  cl::desc("Closed-world enforcement: run the census and ABORT if any "
           "construct kind in the corpus lacks a disposition. With "
           "--ir-census: audit-and-exit (exit 1 on violation). Alone: "
           "gate — census summary runs before the analysis and a "
           "violation kills the run instead of silently dropping edges"),
  cl::init(false));

cl::opt<std::string> IRCensusOut(
  "ir-census-out",
  cl::desc("Write the full census as JSON to this path: dispositions, "
           "intrinsics, constexprs, ALL external callees, the classified "
           "inline-asm table, and the unsoundness ledger (implies "
           "running the census)"),
  cl::init(""));

cl::opt<bool> CFLStaticCall(
  "cfl-static-call",
  cl::desc("Model kernel static_call: direct calls to undefined "
           "__SCT__X trampolines dispatch through __SCK__X's func "
           "slot (initializer + in-corpus __static_call_update stores "
           "are already IR-visible); the callsite becomes an icall "
           "resolved by flows-to. Off = trampoline stays an opaque "
           "extern call (pre-#14 boundary assumption)"),
  cl::init(true));

cl::opt<bool> CFLLinkerArrays(
  "cfl-linker-arrays",
  cl::desc("Model linker-materialized pointer arrays: alias each "
           "undefined __start_X/__stop_X extern global to the union of "
           "section-X members (IR globals with that section attribute "
           "plus module-asm PREL32 entry targets), and treat module-asm-"
           "referenced functions as address-taken. Kernel initcalls / "
           "__param / pci_fixup / ftrace_events / setup / bpf_raw_tp. "
           "Off = those loads resolve to nothing (pre-#22 behavior)"),
  cl::init(true));

cl::opt<bool> CFLBidiPrune(
  "cfl-bidi-prune",
  cl::desc("Before the flows-to solve, compute the field-matched "
           "bidirected partition (union-find with label-collision "
           "unification, O(m a(n))) and report how many origin roots are "
           "statically prunable: their partition's d/f cone never touches "
           "an fptr partition. Measurement only; minting unchanged"),
  cl::init(false));

cl::opt<bool> CFLRootRelevance(
  "cfl-root-relevance",
  cl::desc("After the flows-to fixpoint, measure the answer-relevant root "
           "fraction: function roots read at icall planes plus roots whose "
           "cluster key triggered a merge whose class lies on a backward "
           "path from some fptr class. Sizes the demand-driven-roots "
           "lever (solver work ~ |E| x |roots|)"),
  cl::init(false));

cl::opt<bool> CFLFlowsToIncremental(
  "cfl-flows-to-incremental",
  cl::desc("Continue the flows-to solve across resolution iterations "
           "instead of re-solving from scratch (wins at library scale; "
           "NEGATIVE at whole-kernel scale — plane duplication at wired "
           "call boundaries — and has an open answer-set discrepancy "
           "there; see docs/cfl-graph-explosion-and-scaling.md)"),
  cl::init(false));

cl::opt<unsigned> CFLSolverThreads(
  "cfl-solver-threads",
  cl::desc("Worker threads for the flows-to solver's bulk-synchronous "
           "wave phases (1 = sequential, 0 = hardware concurrency)"),
  cl::init(1));

cl::opt<unsigned> CFLSolverBlock(
  "cfl-solver-block",
  cl::desc("Classes per rank-ordered block within a solver wave; smaller "
           "blocks keep more within-wave downhill forwarding, larger "
           "blocks expose more parallelism"),
  cl::init(8192));

cl::opt<bool> CFLCGCacheStrict(
  "cfl-cache-strict",
  cl::desc("Strict compositional cache validation (coverage/freshness/compatibility)"),
  cl::init(true));

cl::opt<bool> CFLCGCacheRepair(
  "cfl-cache-repair",
  cl::desc("Repair compositional cache by recomputing missing/stale/incompatible modules"),
  cl::init(false));

cl::opt<bool> CFLCGAllowDuplicateCoverage(
  "cfl-cache-allow-duplicate-coverage",
  cl::desc("Allow multiple input .cflcg files to claim the same covered module"),
  cl::init(false));

cl::opt<std::string> CallGraphJSON(
  "callgraph-json", cl::desc("Export call graph to JSON file"), cl::init(""));

cl::opt<bool> CFLDumpCalleeMismatch(
  "cfl-dump-callee-mismatch",
  cl::desc("Per-callsite WARNING for callees found by type but not by CFL "
           "(can produce GBs of log on large inputs)"),
  cl::init(false));

cl::opt<bool> CFLDumpICalls(
  "cfl-dump-icalls",
  cl::desc("Dump one ICALL line per resolved (callsite, callee) pair; sort "
           "the lines to diff runs (5M+ lines on whole-kernel inputs)"),
  cl::init(false));

cl::opt<std::string> IRSidecarDir(
  "ir-sidecar-dir",
  cl::desc("Directory to write per-bc IR fact sidecar JSON files (<bc>.facts.json)"),
  cl::init(""));

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
    if (!GlobalCtx.edgeBuilder.initializeGrammar(
            buildP2GrammarWithFields(CFLFieldBuckets))) {
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
    if (IRCensusOpt)
      return CR.undispKinds > 0 ? 1 : 0;
    // strict/out without --ir-census: gate passed, continue to analysis
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

  if (CFLCompositional && !CFLGlobalDedup) {
    WARNING("--cfl-compositional requires --cfl-global-dedup; forcing it on\n");
    CFLGlobalDedup = true;
  }

  CallGraphPass CGPass(&GlobalCtx);
  auto tRun = std::chrono::steady_clock::now();
  CGPass.run(GlobalCtx.Modules);
  auto tRunEnd = std::chrono::steady_clock::now();
  Diag << "TIMER CGPass.run "
       << std::chrono::duration_cast<std::chrono::milliseconds>(tRunEnd - tRun).count()
       << " ms\n";

  // Run compositional CFL solve if requested
  if (CFLCompositional) {
    auto tComp = std::chrono::steady_clock::now();
    if (!CGPass.runCompositionalSolve()) {
      errs() << "Compositional solve failed\n";
      return 1;
    }
    Diag << "TIMER runCompositionalSolve "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tComp).count()
         << " ms\n";
  }

  if (!CFLEdgeOutput.empty()) {
    GlobalCtx.edgeBuilder.outputEdgesToFile(CFLEdgeOutput);
  }

  if (!CallGraphJSON.empty()) {
    CGPass.dumpCallGraphJSON(CallGraphJSON);
  }
  if (!VSnapshotOutput.empty()) {
    CGPass.dumpVSnapshot(VSnapshotOutput);
  }
  if (!IRSidecarDir.empty()) {
    IRSidecarExporter Sidecar(&GlobalCtx);
    Sidecar.dump(IRSidecarDir);
  }

  if (!AllocatorFile.empty())
    saveAllocatorResults(&GlobalCtx, AllocatorFile);

  return 0;
}
