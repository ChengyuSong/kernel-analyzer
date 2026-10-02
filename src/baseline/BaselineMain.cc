/*
 * KABaseline: the CFL-reachability call-graph baseline (CFLCGPass), the
 * RQ1 comparison tool. Same IR front end and constraint graph as KAMain;
 * the graph is handed to GraCFL with the points-to grammar and saturated
 * monolithically or per translation unit (--cfl-compositional).
 *
 * Copyright (C) 2015 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/PrettyStackTrace.h>

#include <chrono>
#include <string>
#include <vector>

#include "BaselineFlags.h"
#include "CFLCGPass.h"
#include "Driver.h"
#include "Grammar.h"
#include "IRSidecar.h"

using namespace llvm;

cl::opt<std::string> GrammarFile(
  "grammar-file", cl::desc("Grammar file for CFL-reachability analysis"), cl::init(""));

cl::opt<std::string> CFLEdgeOutput(
  "cfl-edge-output", cl::desc("Output file for CFL-reachability edges"), cl::init(""));

cl::opt<std::string> VSnapshotOutput(
  "v-snapshot", cl::desc("Output file for compact CFL V-relation snapshot"), cl::init(""));

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

#define Diag llvm::errs()

int main(int argc, char **argv) {
  kaStartProcess(argc, argv);
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

  cl::ParseCommandLineOptions(
      argc, argv, "KABaseline: CFL-reachability call graph (GraCFL)\n");

  if (int rc = kaReadInputList(argv[0]))
    return rc;

  // KAMain's defaults that the saturation modes never had are off here
  // unless asked for (their graph-build severs are sound only paired with
  // the flows-to resolution loop, or they need monolithic adoption); then
  // options only the flows-to solver honors, which would be silently
  // ignored, are refused.
  {
    for (cl::opt<bool> *O :
         {&CFLTracepointKeys, &CFLStaticOpsTables, &CFLPreSolveCone,
          &CFLProposeChainSummaries, &CFLRegFieldApply, &CFLRegFieldObj,
          &CFLProposeSolvedSummaries, &CFLAdoptProposedSummaries})
      if (O->getNumOccurrences() == 0)
        *O = false;
    if (FuncSummaryFile.getNumOccurrences() == 0)
      FuncSummaryFile = "";

    std::vector<std::string> flowsToOnly;
    for (cl::opt<bool> *O :
         {&CFLLazyMint, &CFLFlowsToSlice, &CFLResidueCopies, &CFLConflationReport, &CFLRootRelevance, &CFLProbeOriginSplit, &CFLProbeBlobFormation, &CFLCensusStrata, &CFLCertUserCopy, &CFLConfirmSinks, &CFLSinkInstr, &CFLCensusPtrToInt, &CFLCensusTracepoint, &CFLCensusTypeRej, &CFLCensusExternBound, &CFLTracepointKeys, &CFLStaticOpsTables, &CFLCensusIcallShape, &CFLPreSolveExact, &CFLPreSolveCone, &CFLCensusCouplers, &CFLCensusNexus, &CFLKeyChannels, &CFLReachable, &CFLLazyAddress})
      if (*O)
        flowsToOnly.push_back(O->ArgStr.str());
    for (const cl::Option *O : std::initializer_list<const cl::Option *>{
             &CFLNexusFields, &CFLBatchRoots, &CFLAblateMints,
             &CFLFlowsToMaxIters, &CFLSolverThreads, &CFLSolverBlock,
             &CFLDumpAGraph})
      if (O->getNumOccurrences() > 0)
        flowsToOnly.push_back(O->ArgStr.str());
    for (const std::string &Name : flowsToOnly)
      errs() << argv[0] << ": --" << Name
             << " only affects the flows-to solver (KAMain)\n";
    if (!flowsToOnly.empty())
      return 1;
    if (CFLCompositional && !CFLGlobalDedup) {
      WARNING("--cfl-compositional requires --cfl-global-dedup; forcing it on\n");
      CFLGlobalDedup = true;
    }
  }

  if (int rc = kaApplyMemLimit())
    return rc;
  if (int rc = kaLoadModules(argv[0]))
    return rc;

  kaSelectFieldBuckets();
  GlobalCtx.constraintGraph.setFieldBuckets(CFLFieldBuckets);

  bool exitNow = false;
  if (int rc = kaIRCensusGate(exitNow); rc || exitNow)
    return rc;

  CFLCGPass CGPass(&GlobalCtx, buildP2GrammarWithFields(CFLFieldBuckets),
                   GrammarFile);
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

  if (!CFLEdgeOutput.empty())
    CGPass.edgeView().outputEdgesToFile(CFLEdgeOutput);
  if (!CallGraphJSON.empty())
    CGPass.dumpCallGraphJSON(CallGraphJSON);
  if (!VSnapshotOutput.empty())
    CGPass.dumpVSnapshot(VSnapshotOutput);
  if (!IRSidecarDir.empty()) {
    IRSidecarExporter Sidecar(&GlobalCtx);
    Sidecar.dump(IRSidecarDir);
  }

  return 0;
}
