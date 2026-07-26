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

// Kerneldoc-driven INVOKE mining (task #28 tier 3): one grep pass over
// KernelSrc finds kerneldoc blocks for corpus-defined functions; blocks
// with callback idioms are batched to the LLM, which extracts the
// registration contract (fn param, data param, callee formal) with the
// doc sentence as evidence. Validated proposals are WRITTEN to OutPath
// in func_summaries.txt line format with provenance comments — never
// auto-applied; the confirmer / file review remain the soundness gate.
// DryRun extracts and prints prompts without contacting the LLM.
void queryInvokeCandidates(GlobalContext *Ctx, LLMClient *LLM,
                           llvm::StringRef KernelSrc, llvm::StringRef OutPath,
                           bool DryRun);

// File save/load
bool saveAllocatorResults(GlobalContext *Ctx, llvm::StringRef Path);
bool saveContainerResults(GlobalContext *Ctx, llvm::StringRef Path);
// Returns: 1 = loaded OK, 0 = file not available (fallback to LLM), -1 = parse error
int loadAllocatorFile(GlobalContext *Ctx, llvm::StringRef Path);
int loadContainerFile(GlobalContext *Ctx, llvm::StringRef Path);

#endif
