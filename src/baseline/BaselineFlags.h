#ifndef KA_BASELINE_FLAGS_H
#define KA_BASELINE_FLAGS_H

#include <llvm/Support/CommandLine.h>

#include <string>

// Options of the CFL baseline only (defined in BaselineMain.cc).

extern llvm::cl::opt<std::string> GrammarFile;
extern llvm::cl::opt<std::string> CFLEdgeOutput;
extern llvm::cl::opt<std::string> VSnapshotOutput;
extern llvm::cl::opt<std::string> CompressedGraphOutput;
extern llvm::cl::list<std::string> CompressedGraphInputs;
extern llvm::cl::opt<bool> CFLCompositional;
extern llvm::cl::opt<bool> CFLPreSolveMerge;
extern llvm::cl::opt<bool> CFLFptrSlice;
extern llvm::cl::opt<bool> CFLCGCacheStrict;
extern llvm::cl::opt<bool> CFLCGCacheRepair;
extern llvm::cl::opt<bool> CFLCGAllowDuplicateCoverage;

#endif
