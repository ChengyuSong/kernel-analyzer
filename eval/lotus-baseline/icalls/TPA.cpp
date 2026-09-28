//===- TPA.cpp - icalls-tpa: TPA semi-sparse flow-sensitive call targets --===//
//
// [kanalyzer eval] Backend tpa, set up exactly like tools/alias/
// lotus-alias-tpa.cpp: IR normalization prepass (it rewrites the module;
// sites are enumerated afterwards), k-limit context strategy with
// -icalls-tpa-k (0 = context-insensitive), external pointer table ptr.spec
// from $LOTUS_CONFIG_DIR (the image sets it to /lotus/config; a missing
// file is fatal: without it every library call writes Universal).
//
// Per site: the called operand's points-to set, union over all contexts
// (PointerAnalysis::getPtsSet(Value*)).
//   - The solver creates pointers lazily; a called operand with no pointer
//     was never reached. getPtsSet asserts on it, so it is guarded: empty
//     answer, sidecar "unreached".
//   - A set with the Universal object: TPA's own answer
//     (PointerAnalysis::getCallees) is every address-taken function, with
//     no signature filter. Sidecar "universal"; -icalls-no-fill keeps only
//     the Function objects in the set.
//   - Otherwise: the Function objects in the set (no signature filter).
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/InclusionBased/TPA/Context/ContextPolicy.h"
#include "Alias/InclusionBased/TPA/Context/KLimitContext.h"
#include "Alias/InclusionBased/TPA/PointerAnalysis/Analysis/SemiSparsePointerAnalysis.h"
#include "Alias/InclusionBased/TPA/PointerAnalysis/FrontEnd/SemiSparseProgramBuilder.h"
#include "Alias/InclusionBased/TPA/Transforms/RunPrepass.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdlib>

namespace cl = llvm::cl;

static cl::opt<unsigned>
    TpaK("icalls-tpa-k", cl::init(0),
         cl::desc("TPA k-limit (k-CFA at every call; 0 = insensitive)"));

const char *icalls::backendNames() { return "tpa"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  if (Name != "tpa")
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");
  const char *ConfigDir = std::getenv("LOTUS_CONFIG_DIR");
  if (!ConfigDir)
    fatal("LOTUS_CONFIG_DIR is not set (TPA needs <dir>/ptr.spec)");
  llvm::SmallString<256> Spec(ConfigDir);
  llvm::sys::path::append(Spec, "ptr.spec");
  if (!llvm::sys::fs::exists(Spec))
    fatal("pointer spec not found: " + Spec.str());

  const auto T0 = std::chrono::steady_clock::now();
  transform::runPrepassOn(M);
  context::setContextStrategy(context::ContextStrategy::KLimit);
  context::KLimitContext::setLimit(TpaK);
  tpa::SemiSparseProgramBuilder Builder;
  tpa::SemiSparseProgram Program = Builder.runOnModule(M);
  tpa::SemiSparsePointerAnalysis Analysis;
  Analysis.loadExternalPointerTable(Spec.c_str());
  Analysis.runOnProgram(Program);
  const double SolveSec = secondsSince(T0);
  llvm::errs() << "icalls: tpa: k=" << TpaK << " spec=" << Spec << "\n";

  const tpa::MemoryObject *Universal =
      tpa::MemoryManager::getUniversalObject();
  emit(M, Name, {"universal", "unreached"},
       [&](llvm::CallBase &CB) {
         Answer A;
         const llvm::Value *Op = CB.getCalledOperand();
         if (Analysis.getPointerManager()
                 .getPointersWithValue(Op->stripPointerCasts())
                 .empty()) {
           A.Reasons.push_back("unreached");
           return A;
         }
         const tpa::PtsSet Pts = Analysis.getPtsSet(Op);
         const bool HasUniversal = Pts.has(Universal);
         if (HasUniversal)
           A.Reasons.push_back("universal");
         if (HasUniversal && !noFill()) {
           for (const llvm::Function *F : Analysis.getCallees(&CB))
             A.Targets.push_back(F);
           return A;
         }
         for (const tpa::MemoryObject *Obj : Pts) {
           const tpa::AllocSite &Site = Obj->getAllocSite();
           if (Site.getAllocType() == tpa::AllocSiteTag::Function)
             A.Targets.push_back(Site.getFunction());
         }
         return A;
       },
       SolveSec);
  return 0;
}
