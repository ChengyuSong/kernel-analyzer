//===- Sparrow.cpp - icalls-sparrow: SparrowAA (Andersen) call targets ----===//
//
// [kanalyzer eval] Backend sparrow. SparrowAA has no on-the-fly call graph:
// while generating constraints it binds every indirect call to EVERY
// address-taken function with matching arity (vararg exempt) and matching
// pointer/non-pointer shape of return and fixed parameters
// (ConstraintCollect.cpp:636-756). Argument/return flows therefore already
// use that over-approximation, and the points-to sets read here inherit it.
// Context policy from -andersen-k-cs (default 0 = insensitive); with k>0
// the query is the union over contexts. External calls use ptr.spec /
// modref.spec from $LOTUS_CONFIG_DIR.
//
// Per site: getPointsToSet(called operand) mapped to Functions (the Value
// overload; no signature filter). The AndersPtsSet overload tells whether
// the set holds the universal object, or the operand has no node (the API
// contract: "assume v can point to everything"). In both cases the answer
// is every address-taken function (sidecar "universal";
// -icalls-no-fill keeps only the Functions in the set).
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/InclusionBased/SparrowAA/Andersen.h"

#include "llvm/Support/raw_ostream.h"

#include <cstdlib>

// AndersNodeFactory::UniversalObjIndex (private; NodeFactory.h:150).
static constexpr unsigned UniversalObjIndex = 1;

const char *icalls::backendNames() { return "sparrow"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  if (Name != "sparrow")
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");
  if (!std::getenv("LOTUS_CONFIG_DIR"))
    fatal("LOTUS_CONFIG_DIR is not set (SparrowAA needs ptr/modref.spec)");

  const auto T0 = std::chrono::steady_clock::now();
  const ContextPolicy Policy = getSelectedAndersenContextPolicy();
  Andersen AA(M, Policy); // the constructor runs the analysis
  const double SolveSec = secondsSince(T0);
  llvm::errs() << "icalls: sparrow: context=" << Policy.name << "\n";

  const std::vector<const llvm::Function *> AddressTaken =
      addressTakenFunctions(M);
  emit(M, Name, {"universal"},
       [&](llvm::CallBase &CB) {
         Answer A;
         const llvm::Value *Op = CB.getCalledOperand();
         AndersPtsSet Raw;
         const bool Known = AA.getPointsToSet(Op, Raw);
         const bool Universal = !Known || Raw.has(UniversalObjIndex);
         if (Known) {
           std::vector<const llvm::Value *> Pts;
           AA.getPointsToSet(Op, Pts);
           for (const llvm::Value *V : Pts)
             if (auto *F = llvm::dyn_cast<llvm::Function>(V))
               A.Targets.push_back(F);
         }
         if (Universal) {
           A.Reasons.push_back("universal");
           if (!noFill())
             A.Targets = AddressTaken;
         }
         return A;
       },
       SolveSec);
  return 0;
}
