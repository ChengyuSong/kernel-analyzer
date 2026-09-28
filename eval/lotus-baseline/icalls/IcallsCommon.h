//===- IcallsCommon.h - per-site indirect-call dump, shared part ----------===//
//
// [kanalyzer eval] Every icalls-<family> executable runs one Lotus pointer
// or call-graph analysis and writes its per-site indirect-call targets in
// the SoK parsed_log key space, the convention of KAMain
// --cfl-dump-icalls-json and of the other eval/67 dumpers:
//
//   key   "<DILocation scope filename>:<line>"   (sites on a line union)
//   value sorted callee names
//
// A site is every CallBase in a defined function that is not inline asm
// and whose called operand, stripped of casts and aliases, is not a
// Function. Sites without a debug location cannot be keyed and are only
// counted. Every keyed site gets a key, with an empty list if the analysis
// gives it no target.
//
// Sidecars: an analysis answer can be a points-to result or a fill (a
// fallback, universal/unknown/top object, budget cut-off). Each backend
// declares its fill reasons; for reason R the tool writes
// <json minus .json>.R.sites with one key per line (possibly empty), so a
// reader can separate "resolved by points-to" from "filled". At a sidecar
// site the JSON holds the analysis's OWN answer for that case (documented
// per backend); -icalls-no-fill keeps only functions actually present in
// the points-to set.
//
// Targets are defined functions by default, the rule of the sibling Lotus
// rows (lotus-alias-call-graph drops declarations when it adds CG edges);
// -icalls-include-declarations keeps declarations too. Intrinsics never.
//===----------------------------------------------------------------------===//
#pragma once

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Module.h"

#include <chrono>
#include <functional>
#include <string>
#include <vector>

namespace icalls {

struct Answer {
  std::vector<const llvm::Function *> Targets;
  std::vector<std::string> Reasons; // each must be declared by the backend
};

using Resolver = std::function<Answer(llvm::CallBase &)>;

/// True for a site in the key space (see header comment).
bool isIndirectSite(const llvm::CallBase &CB);

/// All sites of \p M in module order (debug location or not).
std::vector<llvm::CallBase *> collectSites(llvm::Module &M);

/// Whether fills are suppressed (-icalls-no-fill).
bool noFill();

/// Fill helpers (analysis semantics use them; order irrelevant).
std::vector<const llvm::Function *> addressTakenFunctions(const llvm::Module &M);
std::vector<const llvm::Function *> allFunctions(const llvm::Module &M);

/// Print a fatal error and exit(2). Never returns.
[[noreturn]] void fatal(const llvm::Twine &Msg);

/// Resolve every site with \p R and write the JSON and sidecars.
/// \p Reasons lists the sidecar reasons this backend can produce.
void emit(llvm::Module &M, llvm::StringRef Backend,
          llvm::ArrayRef<std::string> Reasons, const Resolver &R,
          double SolveSec);

/// Seconds since \p Start (steady clock), for the summary line.
double secondsSince(const std::chrono::steady_clock::time_point &Start);

} // namespace icalls

// Defined once per executable (one analysis family per binary, so the
// families' headers, logging macros and cl::opts never meet in one TU).
namespace icalls {
/// Backend names this executable accepts, "|"-separated (for --help).
const char *backendNames();
/// Run backend \p Name on \p M and call emit(). Returns the exit code;
/// an unknown name is a fatal error.
int runBackend(llvm::Module &M, llvm::StringRef Name);
} // namespace icalls
