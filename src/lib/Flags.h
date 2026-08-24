#ifndef _FLAGS_H
#define _FLAGS_H

#include <llvm/Support/CommandLine.h>

// Global flags.
using namespace llvm;

extern cl::list<std::string> InputFilenames;
extern cl::opt<unsigned> VerboseLevel;
extern cl::opt<bool> LogTimestamps;
extern cl::opt<bool> CFLGlobalDedup;
extern cl::opt<bool> CFLLocalAllocaSummary;
extern cl::opt<bool> CFLCGCacheStrict;
extern cl::opt<bool> CFLCGCacheRepair;
extern cl::opt<bool> CFLCGAllowDuplicateCoverage;
extern cl::opt<std::string> VSnapshotOutput;
extern cl::opt<std::string> CompressedGraphOutput;
extern cl::list<std::string> CompressedGraphInputs;
extern cl::opt<bool> CFLCompositional;
extern cl::opt<bool> CFLPreSolveMerge;
extern cl::opt<bool> CFLPreSolveOnce;
extern cl::opt<bool> CFLLinkerArrays;
extern cl::opt<bool> CFLStaticCall;
extern cl::opt<bool> CFLFptrSlice;
extern cl::opt<bool> CFLFlowsTo;
extern cl::opt<bool> CFLFlowsToSlice;
extern cl::opt<bool> CFLResidueCopies;
extern cl::opt<std::string> CFLTraceFunc;
extern cl::opt<std::string> CFLTraceFptr;
extern cl::opt<std::string> CFLTraceValue;
extern cl::opt<bool> CFLCoTravelStats;
extern cl::opt<bool> CFLSolverProfile;
extern cl::opt<bool> CFLVerifyClosure;
extern cl::opt<bool> CFLPrintfVarargSink;
extern cl::opt<unsigned> CFLFlowsToMaxIters;
extern cl::opt<unsigned> CFLFieldBuckets;
extern cl::opt<bool> CFLBidiPrune;
extern cl::opt<bool> CFLLazyMint;
extern cl::opt<bool> CFLCensusInvoke;
extern cl::opt<bool> CFLCensusFields;
extern cl::opt<bool> CFLProbeOriginSplit;
extern cl::opt<bool> CFLProbeOpsMono;
extern cl::opt<bool> CFLOpsPairs;
extern cl::opt<bool> CFLProposeOpsSt;
extern cl::opt<std::string> CFLProbeSinkAblate;
extern cl::opt<bool> CFLProbeBlobFormation;
extern cl::opt<bool> CFLCensusStrata;
extern cl::opt<std::string> CFLProbeStratumAblate;
extern cl::opt<bool> CFLProbeUserCopyAblate;
extern cl::opt<bool> CFLCertUserCopy;
extern cl::opt<bool> CFLConfirmSinks;
extern cl::opt<bool> CFLSinkInstr;
extern cl::opt<bool> CFLCensusPtrToInt;
extern cl::opt<bool> CFLCensusTracepoint;
extern cl::opt<bool> CFLCensusTypeRej;
extern cl::opt<std::string> CFLGTTypeCensus;
extern cl::opt<bool> CFLDumpFnptrOffsets;
extern cl::opt<bool> CFLCensusExternBound;
extern cl::opt<bool> CFLTracepointKeys;
extern cl::opt<bool> CFLStaticOpsTables;
extern cl::opt<bool> CFLRodataCopy;
extern cl::opt<bool> CFLCensusIcallShape;
extern cl::opt<bool> CFLProbeBornHub;
extern cl::opt<bool> CFLPreSolveExact;
extern cl::opt<bool> CFLPreSolveCone;
extern cl::opt<bool> CFLJoinCone;
extern cl::opt<bool> CFLCensusCouplers;
extern cl::opt<bool> CFLCensusNexus;
extern cl::opt<std::string> CFLNexusFields;
extern cl::opt<bool> CFLInternPlanes;
extern cl::opt<bool> CFLJoinFastpath;
extern cl::opt<bool> CFLOriginBundles;
extern cl::opt<unsigned long long> CFLBundleEpochFacts;
extern cl::opt<bool> CFLRegFieldReport;
extern cl::opt<bool> CFLRegFieldApply;
extern cl::opt<bool> CFLRegFieldAudit;
extern cl::opt<bool> CFLIterCapOk;
extern cl::opt<bool> CFLInternSweep;
extern cl::opt<bool> CFLBundleProbe;
extern cl::opt<bool> CFLProposeNoopSummaries;
extern cl::opt<bool> CFLProposeAtomSummaries;
extern cl::opt<bool> CFLAdoptProposedSummaries;
extern cl::opt<std::string> CFLAdoptSkip;
extern cl::opt<bool> CFLAtomsGlobalStores;
extern cl::opt<bool> CFLProposeSolvedSummaries;
extern cl::opt<bool> CFLProposeChainSummaries;
extern cl::opt<bool> CFLProbeWitnessSep;
extern cl::opt<bool> CFLWitnessAnswers;
extern cl::opt<bool> CFLProbeNoFormalPresolve;
extern cl::opt<unsigned> CFLBatchRoots;
extern cl::opt<unsigned> CFLBatchWorkers;
extern cl::opt<std::string> CFLBatchSpill;
// RSS watchdog (KAMain.cc): forked batch workers re-arm it post-fork.
extern uint64_t KAMemLimitRssBytes;
void kaStartRssWatchdog();
extern cl::opt<bool> CFLConfirmInvoke;
extern cl::opt<bool> CFLConflationReport;
extern cl::opt<std::string> CFLAblateFuncs;
extern cl::opt<std::string> FuncSummaryFile;
extern cl::opt<std::string> CFLAblateMints;
extern cl::opt<bool> CFLConfirmFresh;
extern cl::opt<bool> CFLProbeRodataJoins;
extern cl::opt<bool> CFLRootRelevance;
extern cl::opt<bool> CFLFlowsToIncremental;
extern cl::opt<unsigned> CFLSolverThreads;
extern cl::opt<unsigned> CFLSolverBlock;

#endif
