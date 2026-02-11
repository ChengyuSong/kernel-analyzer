#ifndef _LLM_ANALYSIS_H
#define _LLM_ANALYSIS_H

#include <llvm/IR/Module.h>
#include <llvm/ADT/StringRef.h>

class GlobalContext;
class LLMClient;

// Per-module LLM queries: iterate functions in M, collect candidates, query LLM,
// populate Ctx->CandidateAllocFuncs / Ctx->ContainerFuncs
void queryAllocatorCandidates(GlobalContext *Ctx, LLMClient *LLM, llvm::Module *M);
void queryContainerCandidates(GlobalContext *Ctx, LLMClient *LLM, llvm::Module *M);

// File save/load
bool saveAllocatorResults(GlobalContext *Ctx, llvm::StringRef Path);
bool saveContainerResults(GlobalContext *Ctx, llvm::StringRef Path);
bool loadAllocatorFile(GlobalContext *Ctx, llvm::StringRef Path);
bool loadContainerFile(GlobalContext *Ctx, llvm::StringRef Path);

#endif
