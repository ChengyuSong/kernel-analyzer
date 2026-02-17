#ifndef _FLAGS_H
#define _FLAGS_H

#include <llvm/Support/CommandLine.h>

// Global flags.
using namespace llvm;

extern cl::list<std::string> InputFilenames;
extern cl::opt<unsigned> VerboseLevel;
extern cl::opt<bool> CFLLocalRepMerge;
extern cl::opt<bool> CFLLocalAllocaSummary;

#endif
