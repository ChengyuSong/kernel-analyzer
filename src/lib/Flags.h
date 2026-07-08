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
extern cl::opt<bool> CFLFptrSlice;
extern cl::opt<bool> CFLFlowsTo;
extern cl::opt<bool> CFLFlowsToSlice;
extern cl::opt<unsigned> CFLFieldBuckets;

#endif
