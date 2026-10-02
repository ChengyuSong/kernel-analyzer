#ifndef _FLAGS_H
#define _FLAGS_H

#include <llvm/Support/CommandLine.h>

#include <string>

// Options shared by KAMain and KABaseline, defined in Flags.cc. A binary's
// own options are declared next to its main().
using namespace llvm;

extern cl::list<std::string> InputFilenames;
extern cl::opt<std::string> BCListFile;
extern cl::opt<unsigned> VerboseLevel;
extern cl::opt<bool> CFLGlobalDedup;
extern cl::opt<bool> CFLLocalAllocaSummary;
extern cl::opt<std::string> DumpBidMapping;
extern cl::opt<std::string> DumpFuncInfo;
extern cl::opt<std::string> DumpAnnotatedIR;
extern cl::opt<bool> CFLPreSolveOnce;
extern cl::opt<bool> CFLFlowsToSlice;
extern cl::opt<bool> CFLResidueCopies;
extern cl::opt<std::string> CFLTraceFunc;
extern cl::opt<bool> CFLTraceFirst;
extern cl::opt<std::string> CFLTraceFptr;
extern cl::opt<bool> CFLChannelCone;
extern cl::opt<bool> CFLExtGlobalsOwnIdentity;
extern cl::opt<bool> CFLReachable;
extern cl::opt<std::string> CFLEntryList;
extern cl::opt<bool> CFLKeyIdentity;
extern cl::opt<std::string> CFLClonePerCaller;
extern cl::opt<std::string> CFLDumpClass;
extern cl::opt<std::string> CFLDumpSCC;
extern cl::opt<bool> CFLHolderIdentity;
extern cl::opt<std::string> CFLTraceMeet;
extern cl::opt<std::string> CFLTraceValue;
extern cl::opt<bool> CFLCoTravelStats;
extern cl::opt<unsigned> CFLFlowsToMaxIters;
extern cl::opt<bool> CFLPrintfVarargSink;
extern cl::opt<bool> CFLVerifyClosure;
extern cl::opt<bool> CFLSolverProfile;
extern cl::opt<bool> LogTimestamps;
extern cl::opt<unsigned> CFLFieldBuckets;
extern cl::opt<bool> IRCensusOpt;
extern cl::opt<bool> IRCensusStrict;
extern cl::opt<std::string> IRCensusOut;
extern cl::opt<bool> CFLStaticCall;
extern cl::opt<bool> CFLLinkerArrays;
extern cl::opt<bool> CFLBidiPrune;
extern cl::opt<bool> CFLLazyMint;
extern cl::opt<bool> CFLCensusInvoke;
extern cl::opt<bool> CFLCensusFields;
extern cl::opt<bool> CFLRegFieldReport;
extern cl::opt<bool> CFLRegFieldApply;
extern cl::opt<bool> CFLIterCapOk;
extern cl::opt<bool> CFLRegFieldAudit;
extern cl::opt<bool> CFLRegFieldObj;
extern cl::opt<std::string> CFLRegFieldWatch;
extern cl::opt<bool> CFLChannelCells;
extern cl::opt<bool> CFLFilterLedger;
extern cl::opt<bool> CFLCertUserCopy;
extern cl::opt<bool> CFLConfirmSinks;
extern cl::opt<bool> CFLSinkInstr;
extern cl::opt<bool> CFLCensusPtrToInt;
extern cl::opt<bool> CFLCensusTypeRej;
extern cl::opt<std::string> CFLGTTypeCensus;
extern cl::opt<bool> CFLFieldBucketsAuto;
extern cl::opt<unsigned> CFLAutoBucketsResidualBP;
extern cl::opt<unsigned> CFLAutoBucketsMax;
extern cl::opt<bool> CFLDumpGTAux;
extern cl::opt<bool> CFLDumpFnptrOffsets;
extern cl::opt<bool> CFLCensusExternBound;
extern cl::opt<bool> CFLCensusTracepoint;
extern cl::opt<bool> CFLTracepointKeys;
extern cl::opt<bool> CFLStaticOpsTables;
extern cl::opt<bool> CFLCensusIcallShape;
extern cl::opt<bool> CFLPreSolveExact;
extern cl::opt<bool> CFLPreSolveCone;
extern cl::opt<bool> CFLCensusCouplers;
extern cl::opt<bool> CFLCensusNexus;
extern cl::opt<std::string> CFLNexusFields;
extern cl::opt<bool> CFLInternPlanes;
extern cl::opt<bool> CFLJoinFastpath;
extern cl::opt<bool> CFLProposeNoopSummaries;
extern cl::opt<bool> CFLWitnessAnswers;
extern cl::opt<bool> CFLProposeSolvedSummaries;
extern cl::opt<bool> CFLProposeChainSummaries;
extern cl::opt<bool> CFLAtomsGlobalStores;
extern cl::opt<std::string> CFLAdoptSkip;
extern cl::opt<bool> CFLAdoptProposedSummaries;
extern cl::opt<bool> CFLProposeAtomSummaries;
extern cl::opt<bool> CFLInternSweep;
extern cl::opt<unsigned> CFLBatchRoots;
extern cl::opt<unsigned> CFLBatchWorkers;
extern cl::opt<std::string> CFLBatchSpill;
extern cl::opt<bool> CFLProbeBlobFormation;
extern cl::opt<bool> CFLConfirmInvoke;
extern cl::opt<bool> CFLConfirmFresh;
extern cl::opt<std::string> CFLAblateMints;
extern cl::opt<std::string> FuncSummaryFile;
extern cl::opt<std::string> CFLAblateFuncs;
extern cl::opt<bool> CFLConflationReport;
extern cl::opt<bool> CFLRootRelevance;
extern cl::opt<unsigned> CFLSolverThreads;
extern cl::opt<unsigned> CFLSolverBlock;
extern cl::opt<std::string> CallGraphJSON;
extern cl::opt<bool> CFLDumpCalleeMismatch;
extern cl::opt<std::string> CFLDumpAGraph;
extern cl::opt<bool> CFLDumpICalls;
extern cl::opt<std::string> CFLDumpIcallsJson;
extern cl::opt<std::string> CFLDumpTypeJson;
extern cl::opt<std::string> CFLDumpMerges;
extern cl::opt<bool> CFLLazyAddress;
extern cl::opt<unsigned> CFLLazyCap;
extern cl::opt<std::string> CFLLazyTraceObject;
extern cl::opt<bool> CFLLazyTypedAccess;
extern cl::opt<bool> CFLLazyTypeIdentity;
extern cl::opt<bool> CFLChannelDemand;
extern cl::opt<std::string> CFLDemandSite;
extern cl::opt<bool> CFLVarargsStrict;
extern cl::opt<std::string> IRSidecarDir;
extern cl::opt<int> MemLimitPct;
extern cl::opt<std::string> MemLimitMode;

// RSS watchdog (Driver.cc): forked batch workers re-arm it post-fork.
extern uint64_t KAMemLimitRssBytes;
void kaStartRssWatchdog();

#endif
