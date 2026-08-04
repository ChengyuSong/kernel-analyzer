#ifndef _FLAGS_H
#define _FLAGS_H

#include <llvm/Support/CommandLine.h>

// Global flags.
using namespace llvm;

extern cl::list<std::string> InputFilenames;
extern cl::opt<unsigned> VerboseLevel;
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
