/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */


#include <llvm/ADT/BitVector.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/FormatVariadic.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/SHA256.h>

#include <vector>
#include <array>
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <atomic>
#include <condition_variable>
#include <fstream>
#include <map>
#include <mutex>
#include <numeric>
#include <set>
#include <thread>
#include <unordered_map>
#include <unordered_set>

#include <cstdio>
#include <deque>
#include <sys/wait.h>
#include <unistd.h>

#include "CallGraph.h"
#include "IRCensus.h"
#include "Annotation.h"
#include "VSnapshot.h"

#include "gracfl/include/solvers/Solver.hpp"

#define CG_LOG(stmt) KA_LOG(2, "CallGraph: " << stmt)
#define CG_DEBUG(stmt) KA_LOG(3, "CallGraph: " << stmt)

using namespace llvm;

namespace {
struct EdgeKey {
  uint from;
  uint to;
  uint label;

  bool operator==(const EdgeKey &Other) const {
    return from == Other.from && to == Other.to && label == Other.label;
  }
};

struct EdgeKeyHash {
  size_t operator()(const EdgeKey &K) const {
    size_t H = static_cast<size_t>(K.from);
    H ^= static_cast<size_t>(K.to) + 0x9e3779b97f4a7c15ULL + (H << 6) + (H >> 2);
    H ^= static_cast<size_t>(K.label) + 0x9e3779b97f4a7c15ULL + (H << 6) + (H >> 2);
    return H;
  }
};

struct CflcgGrammarMeta {
  uint32_t labelA = 0;
  uint32_t labelNA = 0;
  uint32_t labelD = 0;
  uint32_t labelND = 0;
  uint32_t labelM = 0;
  uint32_t labelV = 0;
  uint32_t cflcgVersion = CompressedGraphData::kVersion;
  bool globalDedup = false;
  bool localAllocaSummary = false;
  std::string grammarSignature;
  std::string grammarFingerprint;
};

struct CflcgMetadata {
  uint32_t version = 2;
  std::string stage;
  CflcgGrammarMeta analysisKey;
  std::vector<std::string> coveredModules;
  std::unordered_map<std::string, std::string> moduleHashes;
  bool hasAnalysisKey = false;
  bool hasCoverage = false;
  bool hasModuleHashes = false;
};

static std::string normalizeModuleIdentifier(StringRef rawId) {
  if (rawId.empty())
    return "<unknown-module>";
  SmallString<256> normalized(rawId);
  if (!sys::path::is_absolute(normalized)) {
    std::error_code ec = sys::fs::make_absolute(normalized);
    (void)ec;
  }
  sys::path::remove_dots(normalized, /*remove_dot_dot=*/true);
  return normalized.str().str();
}

static std::string computeSHA256Hex(StringRef content) {
  llvm::SHA256 hasher;
  hasher.update(content);
  auto digest = hasher.final();
#if LLVM_VERSION_MAJOR >= 15
  return toHex(ArrayRef<uint8_t>(digest), /*LowerCase=*/true);
#else
  return toHex(arrayRefFromStringRef(digest), /*LowerCase=*/true);
#endif
}

static bool computeFileSHA256(StringRef path, std::string &outHash, std::string *ErrMsg = nullptr) {
  auto bufOrErr = MemoryBuffer::getFile(path, /*IsText=*/false,
                                        /*RequiresNullTerminator=*/false);
  if (!bufOrErr) {
    if (ErrMsg) {
      *ErrMsg = (Twine("failed to read module for hashing: ") + path + ": " +
                 std::error_code(bufOrErr.getError()).message()).str();
    }
    return false;
  }
  outHash = computeSHA256Hex(bufOrErr.get()->getBuffer());
  return true;
}

static std::string computeGrammarSignature(const gracfl::Grammar *G) {
  if (!G)
    return "";
  std::vector<std::pair<std::string, uint32_t>> entries;
  const auto &symToId = G->getSymbolToIDMap();
  entries.reserve(symToId.size());
  for (const auto &[sym, id] : symToId)
    entries.emplace_back(sym, static_cast<uint32_t>(id));
  std::sort(entries.begin(), entries.end(),
            [](const auto &A, const auto &B) { return A.first < B.first; });
  std::string material;
  material.reserve(entries.size() * 12);
  for (const auto &[sym, id] : entries) {
    material.append(sym);
    material.push_back('=');
    material.append(std::to_string(id));
    material.push_back(';');
  }
  return material;
}

static CflcgGrammarMeta getCurrentCflcgGrammarMeta(const CFLEdgeBuilder &EB) {
  CflcgGrammarMeta M;
  M.labelA = EB.getLabelAssign();
  M.labelNA = EB.getLabelAssignInv();
  M.labelD = EB.getLabelDeref();
  M.labelND = EB.getLabelDerefInv();
  M.labelM = EB.getLabelM();
  M.labelV = EB.getLabelV();
  M.globalDedup = static_cast<bool>(CFLGlobalDedup);
  M.localAllocaSummary = static_cast<bool>(CFLLocalAllocaSummary);
  M.grammarSignature = computeGrammarSignature(EB.getGrammar());
  M.grammarFingerprint = computeSHA256Hex(M.grammarSignature);
  return M;
}

static std::string encodeCflcgMetadata(
    const CflcgGrammarMeta &M,
    StringRef stage,
    const std::vector<std::string> &coveredModules,
    const std::unordered_map<std::string, std::string> &moduleHashes) {
  json::Object Obj;
  Obj["tool"] = "kanalyzer";
  Obj["schema"] = "cflcg";
  Obj["version"] = 2;
  Obj["stage"] = stage.str();

  json::Object analysis;
  analysis["label_a"] = static_cast<int64_t>(M.labelA);
  analysis["label_na"] = static_cast<int64_t>(M.labelNA);
  analysis["label_d"] = static_cast<int64_t>(M.labelD);
  analysis["label_nd"] = static_cast<int64_t>(M.labelND);
  analysis["label_m"] = static_cast<int64_t>(M.labelM);
  analysis["label_v"] = static_cast<int64_t>(M.labelV);
  analysis["grammar_signature"] = M.grammarSignature;
  analysis["grammar_fingerprint"] = M.grammarFingerprint;
  analysis["global_dedup"] = M.globalDedup;
  analysis["local_alloca_summary"] = M.localAllocaSummary;
  analysis["cflcg_version"] = static_cast<int64_t>(M.cflcgVersion);
  Obj["analysis_key"] = std::move(analysis);

  std::vector<std::string> sortedModules = coveredModules;
  std::sort(sortedModules.begin(), sortedModules.end());
  sortedModules.erase(std::unique(sortedModules.begin(), sortedModules.end()),
                      sortedModules.end());

  json::Array coveredArr;
  for (const auto &moduleId : sortedModules)
    coveredArr.push_back(moduleId);
  Obj["covered_modules"] = std::move(coveredArr);

  json::Object hashObj;
  for (const auto &moduleId : sortedModules) {
    auto it = moduleHashes.find(moduleId);
    if (it != moduleHashes.end())
      hashObj[moduleId] = it->second;
  }
  Obj["module_hashes"] = std::move(hashObj);
  return formatv("{0}", json::Value(std::move(Obj))).str();
}

static bool parseCflcgMetadata(StringRef raw, CflcgMetadata &Out) {
  if (raw.empty())
    return false;
  auto Parsed = json::parse(raw);
  if (!Parsed)
    return false;
  const auto *Obj = Parsed->getAsObject();
  if (!Obj)
    return false;
  auto getU32 = [&](StringRef key, uint32_t &dst) -> bool {
    auto v = Obj->getInteger(key);
    if (!v || *v < 0 || *v > UINT32_MAX)
      return false;
    dst = static_cast<uint32_t>(*v);
    return true;
  };
  Out = CflcgMetadata();
  if (auto Version = Obj->getInteger("version");
      Version && *Version >= 0 && *Version <= UINT32_MAX) {
    Out.version = static_cast<uint32_t>(*Version);
  }
  if (auto Stage = Obj->getString("stage"))
    Out.stage = Stage->str();

  bool parsedAnyAnalysis = false;

  if (const auto *AnalysisObj = Obj->getObject("analysis_key")) {
    auto getU32From = [&](const json::Object &Src, StringRef key, uint32_t &dst) -> bool {
      auto v = Src.getInteger(key);
      if (!v || *v < 0 || *v > UINT32_MAX)
        return false;
      dst = static_cast<uint32_t>(*v);
      return true;
    };
    auto fp = AnalysisObj->getString("grammar_fingerprint");
    auto sig = AnalysisObj->getString("grammar_signature");
    auto dedup = AnalysisObj->getBoolean("global_dedup");
    auto localAlloca = AnalysisObj->getBoolean("local_alloca_summary");
    uint32_t cflcgVersion = CompressedGraphData::kVersion;
    if (auto Ver = AnalysisObj->getInteger("cflcg_version");
        Ver && *Ver >= 0 && *Ver <= UINT32_MAX) {
      cflcgVersion = static_cast<uint32_t>(*Ver);
    }
    if (!fp || !sig || !dedup || !localAlloca ||
        !getU32From(*AnalysisObj, "label_a", Out.analysisKey.labelA) ||
        !getU32From(*AnalysisObj, "label_na", Out.analysisKey.labelNA) ||
        !getU32From(*AnalysisObj, "label_d", Out.analysisKey.labelD) ||
        !getU32From(*AnalysisObj, "label_nd", Out.analysisKey.labelND) ||
        !getU32From(*AnalysisObj, "label_m", Out.analysisKey.labelM) ||
        !getU32From(*AnalysisObj, "label_v", Out.analysisKey.labelV))
      return false;
    Out.analysisKey.grammarSignature = sig->str();
    Out.analysisKey.grammarFingerprint = fp->str();
    Out.analysisKey.globalDedup = *dedup;
    Out.analysisKey.localAllocaSummary = *localAlloca;
    Out.analysisKey.cflcgVersion = cflcgVersion;
    Out.hasAnalysisKey = true;
    parsedAnyAnalysis = true;
  } else {
    // Legacy metadata (version 1): labels + grammar fingerprint at top-level.
    auto fp = Obj->getString("grammar_fingerprint");
    if (fp &&
        getU32("label_a", Out.analysisKey.labelA) &&
        getU32("label_na", Out.analysisKey.labelNA) &&
        getU32("label_d", Out.analysisKey.labelD) &&
        getU32("label_nd", Out.analysisKey.labelND) &&
        getU32("label_m", Out.analysisKey.labelM) &&
        getU32("label_v", Out.analysisKey.labelV)) {
      Out.analysisKey.grammarFingerprint = fp->str();
      parsedAnyAnalysis = true;
    }
  }
  if (!parsedAnyAnalysis)
    return false;

  if (auto Covered = Obj->getArray("covered_modules")) {
    Out.coveredModules.reserve(Covered->size());
    for (const auto &v : *Covered) {
      auto s = v.getAsString();
      if (!s)
        return false;
      Out.coveredModules.push_back(normalizeModuleIdentifier(*s));
    }
    std::sort(Out.coveredModules.begin(), Out.coveredModules.end());
    Out.coveredModules.erase(std::unique(Out.coveredModules.begin(),
                                         Out.coveredModules.end()),
                             Out.coveredModules.end());
    Out.hasCoverage = true;
  }

  if (const auto *Hashes = Obj->getObject("module_hashes")) {
    for (const auto &[k, v] : *Hashes) {
      auto s = v.getAsString();
      if (!s)
        return false;
      Out.moduleHashes[normalizeModuleIdentifier(k)] = s->str();
    }
    Out.hasModuleHashes = true;
  }

  return true;
}

static bool cflcgMetadataCompatible(const CflcgGrammarMeta &A,
                                    const CflcgGrammarMeta &B) {
  return A.labelA == B.labelA &&
         A.labelNA == B.labelNA &&
         A.labelD == B.labelD &&
         A.labelND == B.labelND &&
         A.labelM == B.labelM &&
         A.labelV == B.labelV &&
         A.cflcgVersion == B.cflcgVersion &&
         A.globalDedup == B.globalDedup &&
         A.localAllocaSummary == B.localAllocaSummary &&
         A.grammarFingerprint == B.grammarFingerprint;
}

static bool isZeroOffsetGEP(const Value *V) {
  const auto *GEP = dyn_cast<GEPOperator>(V);
  if (!GEP)
    return false;
  for (const Use &IdxU : GEP->indices()) {
    const Value *Idx = IdxU.get();
    const auto *CI = dyn_cast<ConstantInt>(Idx);
    if (!CI || !CI->isZero())
      return false;
  }
  return true;
}

static const Value *stripAllocaAliasBase(const Value *V) {
  const Value *Cur = V;
  while (Cur) {
    const Value *Stripped = Cur->stripPointerCasts();
    if (Stripped != Cur) {
      Cur = Stripped;
      continue;
    }
    const auto *GEP = dyn_cast<GEPOperator>(Cur);
    if (!GEP || !isZeroOffsetGEP(GEP))
      break;
    Cur = GEP->getPointerOperand();
  }
  return Cur;
}

static bool isIgnorableAllocaIntrinsic(const CallBase *CB) {
  const Function *CF = CB ? CB->getCalledFunction() : nullptr;
  if (!CF || !CF->isIntrinsic())
    return false;
  switch (CF->getIntrinsicID()) {
    case Intrinsic::dbg_declare:
    case Intrinsic::dbg_value:
#if LLVM_VERSION_MAJOR >= 15
    case Intrinsic::dbg_assign:
#endif
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
      return true;
    default:
      return false;
  }
}

} // namespace

// Helper to check if we should skip creating edges for a value
// --- printf-family vararg sink classification -------------------------
// A variadic callsite whose (constant) format string proves the varargs
// are only read — never captured, dispatched, or forwarded — does not
// need its tail wired into the callee's vararg summary node. On kernel
// code the printf family is the dominant vararg population and its
// summary nodes glue unrelated objects together (kernel/mm subset: the
// printf vararg web accounted for 91% of cell-cluster merges and the
// widest fact classes). Relies on the __printf convention: the format is
// the LAST FIXED parameter. Conservative fallbacks: non-constant format,
// unknown conversion, %n (writes through a pointer), and %pV (captures a
// va_list inside struct va_format) all keep full wiring.
static uint64_t printfSinkCallsites = 0, printfSinkArgsSkipped = 0;
static uint64_t printfNonConstFmt = 0, printfNonBenignFmt = 0;

static bool getConstantFmtString(const Value *V, StringRef &out) {
  V = V->stripPointerCasts();
  if (const auto *GEP = dyn_cast<GEPOperator>(V)) {
    if (!GEP->hasAllZeroIndices())
      return false;
    V = GEP->getPointerOperand()->stripPointerCasts();
  }
  const auto *GV = dyn_cast<GlobalVariable>(V);
  if (!GV || !GV->hasInitializer())
    return false;
  const auto *CDA = dyn_cast<ConstantDataArray>(GV->getInitializer());
  if (!CDA || !CDA->isCString())
    return false;
  out = CDA->getAsCString();
  return true;
}

static bool formatVarargsBenign(StringRef fmt) {
  for (size_t i = 0; i < fmt.size(); i++) {
    if (fmt[i] != '%')
      continue;
    if (++i >= fmt.size())
      return false; // trailing '%': malformed
    if (fmt[i] == '%')
      continue;
    while (i < fmt.size() &&
           (isDigit(fmt[i]) || StringRef("-+ #0'.*").contains(fmt[i])))
      i++;
    while (i < fmt.size() && StringRef("hlLzjtq").contains(fmt[i]))
      i++;
    if (i >= fmt.size())
      return false;
    const char c = fmt[i];
    if (c == 'p') {
      // %p extensions are read-only symbol/address renderers EXCEPT %pV.
      if (i + 1 < fmt.size() && fmt[i + 1] == 'V')
        return false;
      continue;
    }
    if (StringRef("diouxXcCsSeEfgGaA").contains(c))
      continue;
    return false; // %n or unknown conversion: keep full wiring
  }
  return true;
}

static bool printfVarargSinkCallsite(const CallBase *CS, const Function *CF,
                                     bool countStats = false) {
  const unsigned numFormals = CF->arg_size();
  if (numFormals == 0 || CS->arg_size() <= numFormals)
    return false; // no variadic tail to skip
  StringRef fmt;
  if (!getConstantFmtString(CS->getArgOperand(numFormals - 1), fmt)) {
    if (countStats) printfNonConstFmt++;
    return false;
  }
  if (!formatVarargsBenign(fmt)) {
    if (countStats) printfNonBenignFmt++;
    return false;
  }
  return true;
}

static bool shouldSkipValue(const Value *V) {
  if (!V)
    return true;

  // Skip nullptr
  if (isa<ConstantPointerNull>(V))
    return true;

  // Skip compiler-introduced values
  if (isCompilerIntroducedValue(V))
    return true;

  return false;
}

// Helper: returns true if T is a pointer or a vector-of-pointer type.
static bool containsPointerTypeImpl(Type *T, SmallPtrSetImpl<Type *> &Seen) {
  if (!T)
    return false;
  if (!Seen.insert(T).second)
    return false;

  if (T->isPointerTy())
    return true;

  if (auto *VT = dyn_cast<VectorType>(T))
    return containsPointerTypeImpl(VT->getElementType(), Seen);

  if (auto *AT = dyn_cast<ArrayType>(T))
    return containsPointerTypeImpl(AT->getElementType(), Seen);

  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->isOpaque())
      return false;
    for (Type *ElemTy : ST->elements()) {
      if (containsPointerTypeImpl(ElemTy, Seen))
        return true;
    }
  }

  return false;
}

// Helper: returns true if T is a pointer, a vector-of-pointer type, or an
// aggregate (array/struct) that recursively contains pointers.
static bool containsPointerType(Type *T) {
  SmallPtrSet<Type *, 16> Seen;
  return containsPointerTypeImpl(T, Seen);
}

static bool isLoweredVAListTypeImpl(Type *T, SmallPtrSetImpl<Type *> &Seen) {
  if (!T)
    return false;
  if (!Seen.insert(T).second)
    return false;

  if (auto *AT = dyn_cast<ArrayType>(T))
    return isLoweredVAListTypeImpl(AT->getElementType(), Seen);
  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->hasName()) {
      StringRef N = ST->getName();
      if (N.contains("va_list") || N.contains("__va_list_tag"))
        return true;
    }
    if (ST->isOpaque())
      return false;
    for (Type *ElemTy : ST->elements()) {
      if (isLoweredVAListTypeImpl(ElemTy, Seen))
        return true;
    }
  }
  return false;
}

static bool isLoweredVAListType(Type *T) {
  SmallPtrSet<Type *, 16> Seen;
  return isLoweredVAListTypeImpl(T, Seen);
}

static bool derivesFromLoweredVAListImpl(const Value *V,
                                         SmallPtrSetImpl<const Value *> &Seen,
                                         unsigned Depth) {
  if (!V || Depth > 64)
    return false;

  V = V->stripPointerCasts();

  if (!Seen.insert(V).second)
    return false;

  if (const auto *AI = dyn_cast<AllocaInst>(V))
    return isLoweredVAListType(AI->getAllocatedType());

  if (const auto *GEP = dyn_cast<GEPOperator>(V))
    return derivesFromLoweredVAListImpl(GEP->getPointerOperand(), Seen, Depth + 1);

  if (const auto *LI = dyn_cast<LoadInst>(V))
    return derivesFromLoweredVAListImpl(LI->getPointerOperand(), Seen, Depth + 1);

  if (const auto *PN = dyn_cast<PHINode>(V)) {
    for (const Value *In : PN->incoming_values()) {
      if (derivesFromLoweredVAListImpl(In, Seen, Depth + 1))
        return true;
    }
    return false;
  }

  if (const auto *SI = dyn_cast<SelectInst>(V))
    return derivesFromLoweredVAListImpl(SI->getTrueValue(), Seen, Depth + 1) ||
           derivesFromLoweredVAListImpl(SI->getFalseValue(), Seen, Depth + 1);

  if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
    switch (CE->getOpcode()) {
      case Instruction::GetElementPtr:
      case Instruction::BitCast:
      case Instruction::AddrSpaceCast:
        return derivesFromLoweredVAListImpl(CE->getOperand(0), Seen, Depth + 1);
      default:
        return false;
    }
  }

  return false;
}

// Detect lowered vararg loads (e.g. loads from __va_list_tag-based state)
// when frontends lower va_arg to memory operations instead of VAArgInst.
static bool derivesFromLoweredVAList(const Value *V) {
  SmallPtrSet<const Value *, 32> Seen;
  return derivesFromLoweredVAListImpl(V, Seen, 0);
}

// Helper to check if we should skip creating edges for a function call
static bool shouldSkipFunction(const Function *F) {
  if (!F || !F->hasName())
    return false;

  StringRef name = F->getName();

  // Skip kernel utility functions
  if (isFreeFn(name) || isKernelUtilityFn(name))
    return true;

  return false;
}

static unsigned detectPhysicalCoreCount() {
  if (const char *override = std::getenv("KACFL_THREADS")) {
    char *end = nullptr;
    long value = std::strtol(override, &end, 10);
    if (end != override && value > 0)
      return static_cast<unsigned>(value);
  }

  std::ifstream cpuinfo("/proc/cpuinfo");
  if (cpuinfo.is_open()) {
    std::set<std::pair<int, int>> physicalCores;
    int physicalId = -1;
    int coreId = -1;
    std::string line;

    auto flushProcessor = [&]() {
      if (coreId >= 0) {
        if (physicalId < 0)
          physicalId = 0;
        physicalCores.emplace(physicalId, coreId);
      }
      physicalId = -1;
      coreId = -1;
    };

    while (std::getline(cpuinfo, line)) {
      if (line.empty()) {
        flushProcessor();
        continue;
      }

      const size_t colon = line.find(':');
      if (colon == std::string::npos)
        continue;

      std::string key = line.substr(0, colon);
      std::string value = line.substr(colon + 1);
      auto ltrim = [](std::string &s) {
        const size_t pos = s.find_first_not_of(" \t");
        s.erase(0, pos == std::string::npos ? s.size() : pos);
      };
      auto rtrim = [](std::string &s) {
        const size_t pos = s.find_last_not_of(" \t");
        if (pos == std::string::npos)
          s.clear();
        else
          s.erase(pos + 1);
      };
      ltrim(key);
      rtrim(key);
      ltrim(value);
      rtrim(value);

      if (key == "physical id") {
        physicalId = std::atoi(value.c_str());
      } else if (key == "core id") {
        coreId = std::atoi(value.c_str());
      }
    }
    flushProcessor();

    if (!physicalCores.empty())
      return static_cast<unsigned>(physicalCores.size());
  }

  const unsigned logical = std::thread::hardware_concurrency();
  return logical > 0 ? logical : 1;
}

CallGraphPass::CallGraphPass(GlobalContext *Ctx_)
    : IterativeModulePass(Ctx_, "CallGraph"),
      NF(Ctx->nodeFactory),
      EB(Ctx->edgeBuilder),
      cflThreads(detectPhysicalCoreCount()),
      cflSolvedInputEdgeCount(0),
      cflForceRebuild(true),
      iteration(0) {}

Function* CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

// Strip LLVM's numeric suffix (e.g., ".0", ".123") from struct names.
// When linking multiple modules, LLVM appends these suffixes to avoid
// name collisions, but they represent the same C struct type.
static StringRef stripStructNameSuffix(StringRef Name) {
  size_t DotPos = Name.rfind('.');
  if (DotPos == StringRef::npos || DotPos == 0)
    return Name;
  // Only strip if everything after the last '.' is digits
  StringRef Suffix = Name.substr(DotPos + 1);
  if (!Suffix.empty() && Suffix.find_first_not_of("0123456789") == StringRef::npos)
    return Name.substr(0, DotPos);
  return Name;
}

// Walk GEP indexed type chain to find the innermost named struct field access.
// Returns true if a named non-union struct field was found, with structName
// and fieldIdx set to the stripped struct name and field index respectively.
bool CallGraphPass::getGEPStructField(const GEPOperator *GEP,
                                       std::string &structName,
                                       unsigned &fieldIdx) {
  bool found = false;
  Type *CurTy = GEP->getSourceElementType();

  // Skip the first index (pointer/array offset into base type)
  auto idx = GEP->idx_begin();
  if (idx == GEP->idx_end())
    return false;
  ++idx; // skip first index

  while (idx != GEP->idx_end()) {
    if (StructType *STy = dyn_cast<StructType>(CurTy)) {
      ConstantInt *CI = dyn_cast<ConstantInt>(*idx);
      if (!CI)
        break; // non-constant index, give up
      unsigned fIdx = CI->getZExtValue();
      // Record if this is a named, non-union struct
      if (!STy->isLiteral() && STy->hasName() &&
          !LLVM_STRING_STARTS_WITH(STy->getStructName(), "union")) {
        structName = stripStructNameSuffix(STy->getStructName()).str();
        fieldIdx = fIdx;
        found = true;
      }
      if (fIdx < STy->getNumElements())
        CurTy = STy->getElementType(fIdx);
      else
        break;
    } else if (ArrayType *ATy = dyn_cast<ArrayType>(CurTy)) {
      CurTy = ATy->getElementType();
    } else if (VectorType *VTy = dyn_cast<VectorType>(CurTy)) {
      CurTy = VTy->getElementType();
    } else {
      break;
    }
    ++idx;
  }

  return found;
}

bool CallGraphPass::getFieldKeyFromPointerOperand(const Value *Ptr,
                                                  std::string &structName,
                                                  unsigned &fieldIdx,
                                                  Type *&fieldTy) const {
  fieldTy = nullptr;
  if (!Ptr)
    return false;

  // Handle nested GEP chains by walking upward through pointer operands until
  // we can recover a named struct field key.
  const Value *Cur = Ptr;
  SmallPtrSet<const Value *, 16> Seen;
  constexpr unsigned kMaxDepth = 32;
  for (unsigned Depth = 0; Cur && Depth < kMaxDepth; ++Depth) {
    Cur = Cur->stripPointerCastsAndAliases();
    if (!Seen.insert(Cur).second)
      break;

    const auto *GEP = dyn_cast<GEPOperator>(Cur);
    if (!GEP)
      break;

    if (getGEPStructField(GEP, structName, fieldIdx)) {
      fieldTy = GEP->getResultElementType();
      return true;
    }

    Cur = GEP->getPointerOperand();
  }

  return false;
}

bool CallGraphPass::getGlobalFieldBoundaryKey(const Value *V,
                                              std::string &key) const {
  const auto *CE = dyn_cast_or_null<ConstantExpr>(V);
  if (!CE || CE->getOpcode() != Instruction::GetElementPtr)
    return false;

  const auto *GEP = dyn_cast<GEPOperator>(CE);
  if (!GEP)
    return false;

  std::string structName;
  unsigned fieldIdx = 0;
  if (!getGEPStructField(GEP, structName, fieldIdx))
    return false;

  const Value *base = GEP->getPointerOperand()->stripPointerCasts();
  const auto *GV = dyn_cast<GlobalVariable>(base);
  if (!GV)
    return false;

  key = ("globfield:" + std::to_string(GV->getGUID()) + ":" +
         std::to_string(fieldIdx));
  return true;
}

bool CallGraphPass::getCallSiteFieldKey(const Value *FPtr,
                                        std::string &structName,
                                        unsigned &fieldIdx) const {
  const auto *LI = dyn_cast_or_null<LoadInst>(FPtr);
  if (!LI)
    return false;

  const Value *loadPtr = LI->getPointerOperand()->stripPointerCasts();
  const auto *GEP = dyn_cast<GEPOperator>(loadPtr);
  if (!GEP)
    return false;

  if (!getGEPStructField(GEP, structName, fieldIdx))
    return false;

  // Pattern: load ptr from a struct-typed field pointer without an explicit
  // trailing ", 0" index (e.g. load ptr, ptr gep(..., i32 field)).
  // In LLVM this loads the first element of that nested struct. Refine to the
  // nested field key so field filtering can distinguish callback slots.
  const auto *ST = dyn_cast<StructType>(GEP->getResultElementType());
  if (!ST || ST->isLiteral() || !ST->hasName() || ST->isOpaque() ||
      LLVM_STRING_STARTS_WITH(ST->getStructName(), "union"))
    return true;
  if (ST->getNumElements() == 0)
    return true;
  if (!ST->getElementType(0)->isPointerTy() || !LI->getType()->isPointerTy())
    return true;

  structName = stripStructNameSuffix(ST->getStructName()).str();
  fieldIdx = 0;
  return true;
}

bool CallGraphPass::isStructLayoutCompatible(const StructType *ST1,
                                              const StructType *ST2) {
  unsigned numEl = ST1->getNumElements();
  if (numEl != ST2->getNumElements())
    return false;

  for (unsigned i = 0; i < numEl; ++i) {
    if (!isCompatibleType(ST1->getElementType(i), ST2->getElementType(i)))
      return false;
  }
  return true;
}

bool CallGraphPass::isCompatibleType(const Type *T1, const Type *T2) {
  if (T1 == T2) {
      return true;
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
  } else if (T1->isIntegerTy()) {
    // All integer types are compatible (C allows implicit conversions)
    if (T2->isIntegerTy())
      return true;

    return false;
  } else if (T1->isPointerTy()) {
    // All pointer types are compatible (opaque pointers in LLVM 13+,
    // and C allows implicit void* conversions)
    if (T2->isPointerTy())
      return true;

    return false;
  } else if (T1->isArrayTy()) {
    if (!T2->isArrayTy())
      return false;

    Type *ElT1 = T1->getArrayElementType();
    Type *ElT2 = T2->getArrayElementType();
    return isCompatibleType(ElT1, ElT2);
  } else if (T1->isStructTy()) {
    const StructType *ST1 = cast<StructType>(T1);
    const StructType *ST2 = dyn_cast<StructType>(T2);
    if (!ST2)
      return false;

    // Both literal: compare structurally
    if (ST1->isLiteral() && ST2->isLiteral())
      return isStructLayoutCompatible(ST1, ST2);

    // One literal, one named: not compatible
    if (ST1->isLiteral() != ST2->isLiteral())
      return false;

    // Both named: compare names after stripping LLVM's numeric suffixes
    // (LLVM appends .0, .1, etc. when linking modules with same-named structs)
    StringRef Name1 = stripStructNameSuffix(ST1->getStructName());
    StringRef Name2 = stripStructNameSuffix(ST2->getStructName());
    return Name1.equals(Name2);
  } else if (T1->isFunctionTy()) {
    const FunctionType *FT1 = cast<FunctionType>(T1);
    const FunctionType *FT2 = dyn_cast<FunctionType>(T2);
    if (!FT2)
      return false;

    if (!isCompatibleType(FT1->getReturnType(), FT2->getReturnType()))
      return false;

    // assume varg is always compatible with varg?
    if (FT1->isVarArg()) {
      if (FT2->isVarArg())
        return true;
      else
        return false;
    }

    // compare args, again ...
    unsigned numParam1 = FT1->getNumParams();
    if (numParam1 != FT2->getNumParams())
      return false;

    for (unsigned i = 0; i < numParam1; ++i) {
      if (!isCompatibleType(FT1->getParamType(i), FT2->getParamType(i)))
        return false;
    }
    return true;
  } else if (T1->getTypeID() <= Type::FP128TyID) {
    return T1->getTypeID() == T2->getTypeID();
  } else {
    errs() << "Unhandled Types:" << *T1 << " :: " << *T2 << "\n";
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool CallGraphPass::isCompatible(const CallBase *CS, const Function *F) {
  if (F->isIntrinsic())
    return false;

  const FunctionType *FTy = F->getFunctionType();
  unsigned NumFixedParams = FTy->getNumParams();
  unsigned NumActualArgs = CS->arg_size();

  // For vararg functions, callsite must provide at least the fixed parameters
  if (FTy->isVarArg()) {
    if (NumActualArgs < NumFixedParams)
      return false;
  } else {
    // For non-vararg, require exact argument count match
    if (NumActualArgs != NumFixedParams)
      return false;
  }

  // Return type: if the callsite result is unused, accept any return type.
  // Otherwise require compatibility.
  if (!CS->use_empty() && !CS->getType()->isVoidTy()) {
    if (!isCompatibleType(F->getReturnType(), CS->getType()))
      return false;
  }

  // Type matching on the fixed parameters
  auto AI = CS->arg_begin();
  for (unsigned i = 0; i < NumFixedParams; ++i, ++AI) {
    Type *FormalTy = FTy->getParamType(i);
    Type *ActualTy = (*AI)->getType();

    if (!isCompatibleType(FormalTy, ActualTy))
      return false;
  }

  return true;
}

bool CallGraphPass::findCalleesByType(const CallBase *CS, FuncSet &FS) {
  //errs() << *CS << "\n";
  for (const Function *F : Ctx->AddressTakenFuncs) {
    if (isCompatible(CS, const_cast<Function*>(F)))
      FS.insert(F);
  }

  return false;
}

bool CallGraphPass::handleMemcpy(const CallBase *CS) {
  Value *dst = CS->getArgOperand(0);
  Value *src = CS->getArgOperand(1);
  CG_LOG("Memcpy: " << *dst << " = " << *src << "\n");
  NodeIndex dstNode = getRepNodeForValue(dst);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Memcpy dst node not found!");
  // if (dstNode == AndersNodeFactory::InvalidIndex) {
  //   dstNode = NF.createValueNode(dst);
  //   CG_DEBUG("Create value node " << dstNode << " for memcpy dst " << *dst << "\n");
  // }
  NodeIndex srcNode = getRepNodeForValue(src);
  assert(srcNode != AndersNodeFactory::InvalidIndex && "Memcpy src node not found!");
  // if (srcNode == AndersNodeFactory::InvalidIndex) {
  //   srcNode = NF.createValueNode(src);
  //   CG_DEBUG("Create value node " << srcNode << " for memcpy src " << *src << "\n");
  // }
  // field-insensitive: *dst = *src
  NodeIndex derefDst = getRepDerefNode(dstNode);
  NodeIndex derefSrc = getRepDerefNode(srcNode);
  addAssignmentEdge(derefSrc, derefDst);

  // Field mode: the deref-to-deref edge only links the offset-0 cells, but an
  // aggregate copy moves every field. When both operands agree on the copied
  // struct type, emit directional per-field cell copies (precise). Otherwise
  // fall back to value-aliasing the two pointers plus wildcard loops (sound
  // for any layout, but smears fields and directions).
  if (EB.hasFieldLabels()) {
    auto pointeeCopyType = [](const Value *P) -> Type * {
      const Value *V = P->stripPointerCasts();
      if (const auto *AI = dyn_cast<AllocaInst>(V))
        return AI->getAllocatedType();
      if (const auto *GV = dyn_cast<GlobalVariable>(V))
        return GV->getValueType();
      if (const auto *GEP = dyn_cast<GEPOperator>(V))
        return GEP->getResultElementType();
      return nullptr;
    };
    Type *dstTy = pointeeCopyType(dst);
    Type *srcTy = pointeeCopyType(src);
    while (dstTy && (isa<ArrayType>(dstTy) || isa<VectorType>(dstTy)))
      dstTy = dstTy->getContainedType(0);
    while (srcTy && (isa<ArrayType>(srcTy) || isa<VectorType>(srcTy)))
      srcTy = srcTy->getContainedType(0);
    // Size gate for the residue copy: small constant-length copies are
    // the struct-copy idiom (assignment lowering, copy_from_user-style
    // targets) and deserve the precise encoding; large or variable
    // lengths are bulk data moves (container backing stores), where
    // faithfully chaining residue cells through every reallocation
    // explodes fact volume for zero callgraph value (measured on
    // harfbuzz: >646M facts and climbing vs 570M with the wildcard).
    const auto *lenCI = CS->arg_size() > 2
                            ? dyn_cast<ConstantInt>(CS->getArgOperand(2))
                            : nullptr;
    const bool smallCopy = lenCI && lenCI->getZExtValue() <= 512;
    if (dstTy && dstTy == srcTy && isa<StructType>(dstTy) && curDL) {
      emitFieldwiseCopyEdges(srcNode, dstNode, dstTy, 0);
    } else if (CFLResidueCopies && CFLFlowsTo && smallCopy) {
      // Layout-free residue copy: a byte copy preserves offsets, so under
      // the mod-P encoding "for every residue r: *(dst+r) = *(src+r)" is
      // sound for any length and any opaque pointee — no type info, no
      // wildcard smear, and directional (the old fallback value-aliased
      // both pointers bidirectionally). Residue 0 is the deref-to-deref
      // edge already emitted above. Flows-to only: the extra f-edges
      // multiply the Dn/Up chain scaffolding the saturation solver
      // materializes (8x+ solve blowup measured on libpng).
      const unsigned P = EB.getNumFieldBuckets();
      NodeIndex sParent = getCanonicalNode(srcNode);
      NodeIndex dParent = getCanonicalNode(dstNode);
      for (unsigned r = 1; r < P; r++) {
        NodeIndex sF = getFieldPtrNode(sParent, (int64_t)r);
        NodeIndex dF = getFieldPtrNode(dParent, (int64_t)r);
        EB.addFieldEdges(sParent, getCanonicalNode(sF), (int)r);
        EB.addFieldEdges(dParent, getCanonicalNode(dF), (int)r);
        addAssignmentEdge(getRepDerefNode(getCanonicalNode(sF)),
                          getRepDerefNode(getCanonicalNode(dF)));
      }
    } else {
      addAssignmentEdge(srcNode, dstNode);
      addAssignmentEdge(dstNode, srcNode);
      addFieldWildcardLoop(srcNode, "memcpy-bulk-or-nonflowsto");
      addFieldWildcardLoop(dstNode, "memcpy-bulk-or-nonflowsto");
    }
  }

  return false;
}

// Directional per-field content copy for an aggregate copy of type `Ty` from
// *srcAddr to *dstAddr: for every pointer-bearing field, connect the source
// field cell to the destination field cell through matched f-edges. Arrays
// collapse to their element; unions stop descent with wildcard loops.
void CallGraphPass::emitFieldwiseCopyEdges(NodeIndex srcAddr, NodeIndex dstAddr,
                                           Type *Ty, unsigned depth) {
  while (Ty && (isa<ArrayType>(Ty) || isa<VectorType>(Ty)))
    Ty = Ty->getContainedType(0);
  auto *STy = dyn_cast_or_null<StructType>(Ty);
  if (!STy) {
    // Pointer-bearing scalar cell: copy the cell itself.
    addAssignmentEdge(getRepDerefNode(getCanonicalNode(srcAddr)),
                      getRepDerefNode(getCanonicalNode(dstAddr)));
    return;
  }
  if (depth > 8 ||
      (STy->hasName() && LLVM_STRING_STARTS_WITH(STy->getStructName(), "union"))) {
    addFieldWildcardLoop(srcAddr, "fieldwise-copy-depth-cap");
    addFieldWildcardLoop(dstAddr, "fieldwise-copy-depth-cap");
    addAssignmentEdge(getRepDerefNode(getCanonicalNode(srcAddr)),
                      getRepDerefNode(getCanonicalNode(dstAddr)));
    return;
  }
  const StructLayout *SL = curDL->getStructLayout(STy);
  for (unsigned i = 0; i < STy->getNumElements(); i++) {
    Type *elemTy = STy->getElementType(i);
    if (!containsPointerType(elemTy))
      continue;
    int64_t off = (int64_t)SL->getElementOffset(i);
    NodeIndex sF = srcAddr, dF = dstAddr;
    if (off != 0) {
      NodeIndex sParent = getCanonicalNode(srcAddr);
      NodeIndex dParent = getCanonicalNode(dstAddr);
      sF = getFieldPtrNode(sParent, off);
      dF = getFieldPtrNode(dParent, off);
      EB.addFieldEdges(sParent, getCanonicalNode(sF), fieldBucket(off));
      EB.addFieldEdges(dParent, getCanonicalNode(dF), fieldBucket(off));
    }
    emitFieldwiseCopyEdges(sF, dF, elemTy, depth + 1);
  }
}

bool CallGraphPass::handleCall(const CallBase *CS, const Function *CF,
                               int opsSkipArg) {
  if (CF->isIntrinsic()) {
    // handle intrinsic functions
    return false;
  }

  // Transfer summary: the atoms fully describe the interface — apply
  // them and skip arg/ret wiring (per-callsite semantics, no shared
  // formal/ret mixing). FRESH-bearing summaries normally short-circuit
  // earlier via the AllocSites branch; this path serves non-fresh
  // summaries and fresh ones reached through indirect resolution.
  bool retBound = false;
  {
    auto sit = Ctx->FuncSummaries.find(CF);
    if (sit != Ctx->FuncSummaries.end()) {
      if (!applySummaryAtoms(CS, *sit->second, &retBound))
        return false;
      // Invoke atom with dynamic fn at this callsite: fall through to
      // the pooled arg/ret wiring (sound, LEDGERed). retBound=true
      // means an INVOKE :ret atom already wired this callsite's
      // return per-fn — the shared HOF return edge is the severed
      // ret-pooling channel, so it must NOT also be added below.
    }
  }

  // Skip utility functions to reduce edge explosion
  if (shouldSkipFunction(CF)) {
    CG_DEBUG("Skipping utility function: " << CF->getName() << "\n");
    return false;
  }

  if (CF->empty()) {
    // External function — handle memcpy/memmove specially.
    WARNING("Call: " << CF->getName() << " is empty!\n");
    if (CF->getName() == "memcpy" || CF->getName() == "memmove")
      handleMemcpy(CS);

    // In compositional mode, fall through to create on-demand arg/ret nodes
    // so cross-TU data flow is captured in the compressed graph.
    if (CompressedGraphOutput.empty() && !CFLCompositional)
      return false;
  }

  wireCallArgs(CS, CF, opsSkipArg);

  // handle return (pointer or pointer-bearing aggregate, e.g. {ptr,ptr})
  if (!retBound && containsPointerType(CF->getReturnType())) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    if (retNode == AndersNodeFactory::InvalidIndex ||
        retNode == NF.getUniversalPtrNode()) {
      // On-demand return node for declared function.
      retNode = NF.createReturnNode(CF);
    }
    retNode = getCanonicalNode(retNode);
    // The callsite may not have a value node if it discards the return value
    // (e.g., void-typed callsite matched via permissive isCompatible)
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      addAssignmentEdge(retNode, callNode);
  }

  return false;
}

// Actual->formal (and variadic-tail) wiring for a callsite, shared by
// handleCall and the summary dynamic-fn pooled fallback at allocator
// branches (which must feed the callee body WITHOUT the shared-return
// edge: the callsite's fresh object is its return identity).
void CallGraphPass::wireCallArgs(const CallBase *CS, const Function *CF,
                                 int skipArg) {
  // handle args:
  // - fixed arguments map to formal params
  // - variadic tail (if any) maps to the callee's vararg summary node
  unsigned numArgs = CS->arg_size();
  unsigned numFormals = CF->arg_size();
  unsigned minArgs = std::min(numArgs, numFormals);
  for (unsigned i = 0; i < minArgs; i++) {
    if ((int)i == skipArg)
      continue; // ops-pairs tightening: receiver bound per-pair instead
    Value *arg = CS->getArgOperand(i);
    // First-class aggregates ({ptr,ptr} closures, coerced small structs)
    // carry pointer identity by value — skip only pointer-free types.
    if (!containsPointerType(arg->getType()))
      continue; // skip non-pointer args
    if (shouldSkipValue(arg)) {
      CG_DEBUG("Skipping compiler-introduced argument: " << *arg << "\n");
      continue;
    }
    NodeIndex argNode = getRepNodeForValue(arg);
    if (argNode == AndersNodeFactory::InvalidIndex) {
      argNode = NF.createValueNode(arg);
      argNode = getCanonicalNode(argNode);
      CG_DEBUG("Create value node " << argNode << " for Arg " << *arg << "\n");
    }
    Value *farg = CF->getArg(i);
    NodeIndex formalNode = getRepNodeForValue(farg);
    if (formalNode == AndersNodeFactory::InvalidIndex) {
      // On-demand node for declared function formal argument.
      formalNode = NF.createValueNode(farg);
      formalNode = getCanonicalNode(formalNode);
    }
    addAssignmentEdge(argNode, formalNode);
  }
  if (CF->isVarArg()) {
    if (CFLPrintfVarargSink && printfVarargSinkCallsite(CS, CF, true)) {
      // Benign printf-style callsite: varargs are read-only renderer
      // inputs; skip the vararg-summary wiring entirely.
      printfSinkCallsites++;
      printfSinkArgsSkipped += numArgs - numFormals;
    } else {
      NodeIndex varargNode = NF.getVarargNodeFor(CF);
      if (varargNode == AndersNodeFactory::InvalidIndex)
        varargNode = NF.createVarargNode(CF);
      varargNode = getCanonicalNode(varargNode);
      for (unsigned i = numFormals; i < numArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!containsPointerType(arg->getType()))
          continue; // skip non-pointer args
        if (shouldSkipValue(arg)) {
          CG_DEBUG("Skipping compiler-introduced variadic argument: " << *arg << "\n");
          continue;
        }
        NodeIndex argNode = getRepNodeForValue(arg);
        if (argNode == AndersNodeFactory::InvalidIndex) {
          argNode = NF.createValueNode(arg);
          argNode = getCanonicalNode(argNode);
        }
        addAssignmentEdge(argNode, varargNode);
      }
    }
  }

}

bool CallGraphPass::handleContainerCall(const CallBase *CS, const Function *CF) {
  auto it = Ctx->ContainerFuncs.find(CF);
  if (it == Ctx->ContainerFuncs.end())
    return false;

  const auto &Info = it->second;
  CG_DEBUG("ContainerCall: " << CF->getName() << " at " << *CS << "\n");

  // Get the container object node
  unsigned containerIdx = (unsigned)Info.containerArg;
  if (containerIdx >= CS->arg_size())
    return false;
  Value *containerArg = CS->getArgOperand(containerIdx);
  if (!containerArg->getType()->isPointerTy())
    return false;
  NodeIndex containerNode = getRepNodeForValue(containerArg);
  if (containerNode == AndersNodeFactory::InvalidIndex) {
    containerNode = NF.createValueNode(containerArg);
    containerNode = getCanonicalNode(containerNode);
    CG_DEBUG("Create value node " << containerNode
             << " for container arg " << *containerArg << "\n");
  }

  // Get or create dereference node for the container (represents "*container")
  // Field mode: container helpers access arbitrary interior fields.
  if (EB.hasFieldLabels())
    addFieldWildcardLoop(containerNode, "container-helper");
  NodeIndex derefNode = getRepDerefNode(containerNode);

  // Handle store args: val -> *container (assignment edges)
  for (int storeIdx : Info.storeArgs) {
    if ((unsigned)storeIdx >= CS->arg_size())
      continue;
    Value *val = CS->getArgOperand(storeIdx);
    if (!val->getType()->isPointerTy())
      continue;
    if (shouldSkipValue(val))
      continue;
    NodeIndex valNode = getRepNodeForValue(val);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(val);
      valNode = getCanonicalNode(valNode);
      CG_DEBUG("Create value node " << valNode
               << " for store arg " << *val << "\n");
    }
    addAssignmentEdge(valNode, derefNode);
    CG_DEBUG("ContainerStore: " << valNode << " -> " << derefNode << "\n");
  }

  // Handle load return: *container -> callsite result
  if (Info.loadReturn && CF->getReturnType()->isPointerTy()) {
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex) {
      addAssignmentEdge(derefNode, callNode);
      CG_DEBUG("ContainerLoad: " << derefNode << " -> " << callNode << "\n");
    }
  }

  return false;
}

bool CallGraphPass::removeCallEdges(const CallBase *CS, const Function *CF) {
  assert(!CF->isIntrinsic() && "Intrinsic function should not be here!");

  // handle args
  unsigned numArgs = CS->arg_size();
  unsigned numFormals = CF->arg_size();
  // Remove fixed-arg edges
  unsigned minArgs = std::min(numArgs, numFormals);
  for (unsigned i = 0; i < minArgs; i++) {
    Value *arg = CS->getArgOperand(i);
    // Must mirror handleCall: pointer-bearing aggregates are wired too.
    if (!containsPointerType(arg->getType()))
      continue; // skip non-pointer args
    if (shouldSkipValue(arg))
      continue; // handleCall never wired these
    NodeIndex argNode = getRepNodeForValue(arg);
    assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
    Value *farg = CF->getArg(i);
    NodeIndex formalNode = getRepNodeForValue(farg);
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    EB.removeAssignmentEdges(getCanonicalNode(argNode), getCanonicalNode(formalNode));
  }
  // Remove variadic-tail edges
  if (CF->isVarArg() &&
      !(CFLPrintfVarargSink && printfVarargSinkCallsite(CS, CF))) {
    NodeIndex varargNode = getCanonicalNode(NF.getVarargNodeFor(CF));
    assert(varargNode != AndersNodeFactory::InvalidIndex && "Vararg node not found!");
    for (unsigned i = numFormals; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!containsPointerType(arg->getType()))
        continue;
      if (shouldSkipValue(arg))
        continue; // handleCall never wired these
      NodeIndex argNode = getRepNodeForValue(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      EB.removeAssignmentEdges(getCanonicalNode(argNode), varargNode);
    }
  }

  // handle return (must mirror handleCall)
  if (containsPointerType(CF->getReturnType())) {
    NodeIndex retNode = getCanonicalNode(NF.getReturnNodeFor(CF));
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      EB.removeAssignmentEdges(getCanonicalNode(retNode), getCanonicalNode(callNode));
  }

  return false;
}

NodeIndex CallGraphPass::getCanonicalNode(NodeIndex n) const {
  if (n == AndersNodeFactory::InvalidIndex)
    return n;

  auto it = canonicalNodeMap.find(n);
  if (it == canonicalNodeMap.end())
    return n;

  NodeIndex root = it->second;
  while (root != AndersNodeFactory::InvalidIndex) {
    auto next = canonicalNodeMap.find(root);
    if (next == canonicalNodeMap.end() || next->second == root)
      break;
    root = next->second;
  }
  return root;
}

void CallGraphPass::collectCanonicalMembers(NodeIndex n, std::vector<NodeIndex> &out) const {
  out.clear();
  if (n == AndersNodeFactory::InvalidIndex)
    return;

  NodeIndex root = getCanonicalNode(n);
  auto it = canonicalClassMembers.find(root);
  if (it == canonicalClassMembers.end() || it->second.empty()) {
    out.push_back(root);
    return;
  }

  out.reserve(it->second.size());
  for (NodeIndex member : it->second)
    out.push_back(member);
}

NodeIndex CallGraphPass::getRepNodeForValue(const Value *V) {
  if (!V)
    return AndersNodeFactory::InvalidIndex;
  NodeIndex n = NF.getValueNodeFor(V);
  if (n == AndersNodeFactory::InvalidIndex)
    return n;
  // Canonical ConstantExpr-GEP nodes need their base connection emitted
  // (once per module) wherever they appear as operands: field-chain
  // edges in field mode, the plain GetElementPtr 'a' edge otherwise.
  if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
    if (CE->getOpcode() == Instruction::GetElementPtr)
      ensureConstGEPFieldEdges(CE);
  }
  return getCanonicalNode(n);
}

// Universal-ptr exposure ledger (task #22 postmortem): the universal
// fallback silently absorbed 17.7k wired edges once — every touch is
// now counted and reported so a repeat is loud, not a 3h kernel run.
static size_t g_uniEdgeTouches = 0, g_uniDerefTouches = 0,
              g_uniFptrIcalls = 0;

NodeIndex CallGraphPass::getRepDerefNode(NodeIndex ptrNode) {
  if (ptrNode == NF.getUniversalPtrNode() ||
      ptrNode == NF.getUniversalObjNode())
    g_uniDerefTouches++; // memory modeled through unknown-extern hub
  if (ptrNode == AndersNodeFactory::InvalidIndex)
    return AndersNodeFactory::InvalidIndex;

  NodeIndex canonical = getCanonicalNode(ptrNode);
  NodeIndex derefNode = NF.getDereferenceNodeFor(canonical);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    derefNode = NF.createDereferenceNode(canonical);
    CG_DEBUG("Create deref node " << derefNode << " for canonical node " << canonical << "\n");
  }

  // In compositional per-TU mode, canonical nodes may be shared across TUs.
  // Re-emit ptr<->deref constraints once per module so each TU edge slice
  // retains the local memory edge context after splitting.
  if (moduleDerefEdgeRoots.insert(canonical).second)
    EB.addDereferenceEdges(canonical, derefNode);

  return derefNode;
}

void CallGraphPass::addAssignmentEdge(NodeIndex src, NodeIndex dst) {
  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex s = getCanonicalNode(src);
  NodeIndex d = getCanonicalNode(dst);
  if (s == d) return;
  if (s == NF.getUniversalPtrNode() || d == NF.getUniversalPtrNode() ||
      s == NF.getUniversalObjNode() || d == NF.getUniversalObjNode())
    g_uniEdgeTouches++;
  EB.addAssignmentEdges(s, d);
}

// ---- Field-sensitive memory modeling helpers (--cfl-field-buckets > 0) ----

int CallGraphPass::fieldBucket(int64_t off) const {
  const unsigned K = EB.getNumFieldBuckets();
  assert(K > 0 && "fieldBucket called without field labels");
  // Modular residue, NOT a hash: bucket sums must track offset sums so the
  // shift-indexed grammar can compose nested steps against flat ones
  // ((a+b) mod K == (a mod K + b mod K) mod K). Signed-safe for
  // container_of-style negative offsets. Prefer prime K: typical offsets
  // are 8-aligned, and a prime modulus keeps them from collapsing onto a
  // couple of residues.
  int64_t r = off % (int64_t)K;
  return (int)(r < 0 ? r + (int64_t)K : r);
}

NodeIndex CallGraphPass::getFieldPtrNode(NodeIndex parentCanon, int64_t off) {
  auto key = std::make_pair(parentCanon, off);
  auto it = fieldPtrNodes.find(key);
  if (it != fieldPtrNodes.end())
    return it->second;
  NodeIndex n = NF.createValueNode();
  fieldPtrNodes.emplace(key, n);
  CG_DEBUG("Create field ptr node " << n << " for (" << parentCanon
           << ", +" << off << ")\n");
  return n;
}

// Decompose a GEP into per-struct-level byte offsets:
//   - struct index steps contribute their in-struct byte offset (0 skipped:
//     field 0 shares the parent's address)
//   - array/vector index steps are skipped (arrays are collapsed, matching
//     the Andersen-side model in offsetToFieldNum)
//   - a first index over a struct/array source strides whole objects, which
//     preserves field structure under collapse, so it is skipped too
//   - a nonzero or variable first index over a scalar source (i8-style byte
//     arithmetic) has no recoverable field structure -> caller must use the
//     wildcard fallback
bool CallGraphPass::decomposeGEPLevels(const GEPOperator *GEP,
                                       const DataLayout &DL,
                                       SmallVectorImpl<int64_t> &levels) const {
  levels.clear();
  bool first = true;
  for (auto GTI = gep_type_begin(GEP), E = gep_type_end(GEP); GTI != E; ++GTI) {
    const Value *idx = GTI.getOperand();
    if (StructType *STy = GTI.getStructTypeOrNull()) {
      const auto *CI = dyn_cast<ConstantInt>(idx);
      if (!CI)
        return false; // malformed; be conservative
      const StructLayout *SL = DL.getStructLayout(STy);
      int64_t off = (int64_t)SL->getElementOffset(CI->getZExtValue());
      if (off != 0)
        levels.push_back(off);
    } else if (first) {
      Type *Ty = GTI.getIndexedType();
      if (!Ty->isStructTy() && !Ty->isArrayTy() && !Ty->isVectorTy()) {
        const auto *CI = dyn_cast<ConstantInt>(idx);
        if (!CI)
          return false; // variable scalar arithmetic -> wildcard fallback
        // Constant scalar-typed offsets are known field steps, including
        // the two container_of shapes: raw negative offsets and the
        // -O1-folded positive byte offsets from mid-object pointers.
        int64_t off =
            CI->getSExtValue() * (int64_t)DL.getTypeAllocSize(Ty);
        if (off != 0)
          levels.push_back(off);
      }
    }
    first = false;
  }
  return true;
}

void CallGraphPass::addFieldChainEdges(NodeIndex baseNode, NodeIndex resultNode,
                                       ArrayRef<int64_t> levels) {
  assert(!levels.empty() && "addFieldChainEdges requires at least one level");
  NodeIndex cur = getCanonicalNode(baseNode);
  for (size_t k = 0; k < levels.size(); k++) {
    const bool last = (k + 1 == levels.size());
    NodeIndex next = last ? getCanonicalNode(resultNode)
                          : getFieldPtrNode(cur, levels[k]);
    if (next == cur)
      continue;
    EB.addFieldEdges(cur, next, fieldBucket(levels[k]));
    cur = next;
  }
}

void CallGraphPass::addFieldWildcardLoop(NodeIndex n, const char *why) {
  if (n == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex canon = getCanonicalNode(n);
  if (moduleFieldWildcardRoots.insert(canon).second) {
    EB.addFieldWildcardSelfLoop(canon);
    wildcardReasons[why]++;
  }
}

void CallGraphPass::applyFieldFallback(NodeIndex baseNode, NodeIndex resultNode,
                                       const char *why) {
  addAssignmentEdge(baseNode, resultNode);
  addFieldWildcardLoop(baseNode, why);
}

void CallGraphPass::mergeCanonicalClasses(NodeIndex a, NodeIndex b) {
  // merging anything with the universal class would conflate the
  // unknown-extern hub with a real object — catastrophic and silent;
  // refuse loudly (no silent fallback)
  assert(a != NF.getUniversalPtrNode() && b != NF.getUniversalPtrNode() &&
         a != NF.getUniversalObjNode() && b != NF.getUniversalObjNode() &&
         "attempt to canonical-merge the universal class");
  a = getCanonicalNode(a);
  b = getCanonicalNode(b);
  if (a == b)
    return;
  if (b < a)
    std::swap(a, b); // smaller index as stable representative
  auto &membersA = canonicalClassMembers[a];
  if (membersA.empty())
    membersA.insert(a);
  auto itB = canonicalClassMembers.find(b);
  if (itB != canonicalClassMembers.end()) {
    for (NodeIndex m : itB->second) {
      canonicalNodeMap[m] = a;
      membersA.insert(m);
    }
    canonicalClassMembers.erase(b);
  }
  canonicalNodeMap[b] = a;
  membersA.insert(b);
}

// task #38 rung 2: canonical nodes of the presolve fptr backward cone,
// persisted for the in-solve join-cone experiment (--cfl-join-cone).
static std::vector<NodeIndex> g_presolveConeCanon;

// --cfl-census-couplers (task #38, user thesis: kernel modularity at the
// DATA-OBJECT level). Subsystem = first two path components of the
// origin's defining module. A cross-subsystem WELD = a merge whose two
// sides each own data origins from subsystems the other lacks — after
// it, readers of either cell see both subsystems' objects. Fn origins
// are excluded (the identity channels already bind ops per object).
static boost::unordered_flat_map<std::string, uint8_t> g_subsysIds;
static boost::unordered_flat_map<std::string, uint32_t> g_weldRepOf;
static std::vector<std::string> g_subsysNames;
static uint8_t subsysBitOf(const llvm::Module *M2) {
  if (!M2) return 63;
  llvm::StringRef p2 = M2->getModuleIdentifier();
  p2.consume_front("./");
  size_t s1 = p2.find('/');
  size_t s2 = s1 == llvm::StringRef::npos ? s1 : p2.find('/', s1 + 1);
  std::string key =
      (s2 == llvm::StringRef::npos ? p2 : p2.substr(0, s2)).str();
  auto [it, ins] = g_subsysIds.emplace(key, (uint8_t)g_subsysNames.size());
  if (ins) {
    if (g_subsysNames.size() >= 63) { it->second = 62; return 62; }
    g_subsysNames.push_back(key);
  }
  return it->second;
}

void CallGraphPass::preSolveCopyFieldMerge(const std::vector<gracfl::Edge> &edges,
                                           const std::vector<size_t> *idx) {
  // Labels participating in the memory-free sublanguage.
  const uint32_t la = EB.getLabelAssign(), lai = EB.getLabelAssignInv();
  auto isCopyFieldLabel = [&](uint32_t l) {
    if (l == la || l == lai)
      return true;
    if (!EB.hasFieldLabels())
      return false;
    if (l == EB.getLabelFieldAny() || l == EB.getLabelFieldAnyInv())
      return true;
    for (unsigned b = 0; b < EB.getNumFieldBuckets(); b++)
      if (l == EB.getLabelField(b) || l == EB.getLabelFieldInv(b))
        return true;
    return false;
  };
  // Source values must not glue unrelated classes: two slots holding the
  // same function/global would chain-merge through it (common-sink smear),
  // manufacturing false targets. Drop their edges from the sublanguage.
  auto isBarrierNode = [&](NodeIndex canon) {
    if (NF.isSpecialNode(canon))
      return true;
    const Value *v = NF.getValueForNode(canon);
    return v && (isa<Function>(v) || isa<GlobalVariable>(v));
  };

  std::unordered_map<NodeIndex, uint32_t> toLocal;
  std::vector<NodeIndex> toCanon;
  std::vector<gracfl::Edge> subEdges;
  auto localId = [&](NodeIndex canon) -> uint32_t {
    auto [it, inserted] = toLocal.emplace(canon, (uint32_t)toCanon.size());
    if (inserted)
      toCanon.push_back(canon);
    return it->second;
  };

  const size_t n = idx ? idx->size() : edges.size();
  for (size_t i = 0; i < n; i++) {
    const auto &E = edges[idx ? (*idx)[i] : i];
    if (!isCopyFieldLabel(E.label))
      continue;
    NodeIndex from = getCanonicalNode(E.from);
    NodeIndex to = getCanonicalNode(E.to);
    if (from == to)
      continue;
    if (isBarrierNode(from) || isBarrierNode(to))
      continue;
    subEdges.emplace_back(localId(from), localId(to), E.label);
  }
  if (subEdges.empty())
    return;

  CG_LOG("Pre-solve merge: sublanguage graph " << toCanon.size()
         << " nodes, " << subEdges.size() << " edges\n");
  auto tSolve = std::chrono::steady_clock::now();

  // --cfl-presolve-exact (task #38): merge ONLY raw mutual-flow SCCs
  // (x ->a* y AND y ->a* x = provable value equality — exact). The
  // V-component path below quotients by CONNECTIVITY of the symmetric
  // alias relation V := -a* a* (with M splices) — alias is not
  // transitive, so component-merging is Steensgaard-style
  // over-unification: at km it manufactures a 41,350-member born class
  // whose true mutual-flow core is 41 nodes. Exact mode trades that
  // compression back for precision; cost measured, not assumed.
  if (CFLPreSolveExact) {
    const uint32_t M2 = (uint32_t)toCanon.size();
    const uint32_t laX = EB.getLabelAssign();
    auto isFwdX = [&](uint32_t l) {
      if (l == laX)
        return true;
      if (!EB.hasFieldLabels())
        return false;
      if (l == EB.getLabelFieldAny())
        return true;
      for (unsigned b2 = 0; b2 < EB.getNumFieldBuckets(); b2++)
        if (l == EB.getLabelField(b2))
          return true;
      return false;
    };
    std::vector<std::vector<uint32_t>> adjX(M2);
    for (auto &E : subEdges)
      if (isFwdX(E.label))
        adjX[E.from].push_back(E.to);
    // iterative Tarjan
    std::vector<uint32_t> idx(M2, UINT32_MAX), low(M2, 0), comp(M2,
                                                                UINT32_MAX);
    std::vector<char> onStk(M2, 0);
    std::vector<uint32_t> stk;
    uint32_t counter = 0, nComp = 0;
    std::vector<std::pair<uint32_t, size_t>> call;
    for (uint32_t s2 = 0; s2 < M2; s2++) {
      if (idx[s2] != UINT32_MAX)
        continue;
      call.emplace_back(s2, 0);
      while (!call.empty()) {
        auto &[u, ci] = call.back();
        if (ci == 0) {
          idx[u] = low[u] = counter++;
          stk.push_back(u);
          onStk[u] = 1;
        }
        if (ci < adjX[u].size()) {
          uint32_t w = adjX[u][ci++];
          if (idx[w] == UINT32_MAX) {
            call.emplace_back(w, 0);
          } else if (onStk[w]) {
            low[u] = std::min(low[u], idx[w]);
          }
        } else {
          if (low[u] == idx[u]) {
            while (true) {
              uint32_t w = stk.back();
              stk.pop_back();
              onStk[w] = 0;
              comp[w] = nComp;
              if (w == u)
                break;
            }
            nComp++;
          }
          uint32_t uu = u;
          call.pop_back();
          if (!call.empty())
            low[call.back().first] =
                std::min(low[call.back().first], low[uu]);
        }
      }
    }
    std::vector<NodeIndex> repX(nComp, AndersNodeFactory::InvalidIndex);
    size_t mergedX = 0;
    uint32_t biggest = 0;
    std::vector<uint32_t> csz(nComp, 0);
    for (uint32_t ln = 0; ln < M2; ln++) {
      csz[comp[ln]]++;
      if (repX[comp[ln]] == AndersNodeFactory::InvalidIndex)
        repX[comp[ln]] = toCanon[ln];
      else {
        mergeCanonicalClasses(repX[comp[ln]], toCanon[ln]);
        mergedX++;
      }
    }
    for (uint32_t c2 = 0; c2 < nComp; c2++) biggest = std::max(biggest, csz[c2]);
    CG_LOG("Pre-solve merge (EXACT): " << M2 << " nodes -> " << nComp
           << " mutual-flow SCCs, " << mergedX << " merges (largest "
           << biggest << "), "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tSolve).count()
           << " ms; V-component merge SKIPPED\n");
    return;
  }
  gracfl::SolverFWGramParallel sub(subEdges, *EB.getGrammar(), cflThreads);
  sub.runCFL();
  const auto &graph = sub.getReachability();

  std::vector<uint32_t> nodeToSCC;
  uint32_t numSCCs = 0;
  computeVSCC(graph, EB.getLabelV(), nodeToSCC, numSCCs);

  // --cfl-probe-born-hub (task #38): is the BORN giant held together by
  // a few articulation hubs, or is it a dense expander? Induce the
  // forward-flow subgraph on the largest V' SCC's members, then
  // repeatedly remove the highest-degree live node and recompute the
  // largest strongly connected component — the shatter curve decides
  // whether phase-1 cutting is viable. Measurement only.
  if (CFLProbeBornHub) {
    std::unordered_map<uint32_t, uint32_t> sccSz;
    for (uint32_t scc : nodeToSCC)
      if (scc != UINT32_MAX)
        sccSz[scc]++;
    uint32_t big = UINT32_MAX, bigSz = 0;
    for (auto &kv : sccSz)
      if (kv.second > bigSz) {
        bigSz = kv.second;
        big = kv.first;
      }
    if (big != UINT32_MAX && bigSz > 100) {
      std::vector<uint32_t> lid2m(toCanon.size(), UINT32_MAX);
      std::vector<uint32_t> mem;
      for (uint32_t ln = 0; ln < toCanon.size() && ln < nodeToSCC.size();
           ln++)
        if (nodeToSCC[ln] == big) {
          lid2m[ln] = (uint32_t)mem.size();
          mem.push_back(ln);
        }
      const uint32_t M = (uint32_t)mem.size();
      const uint32_t laF = EB.getLabelAssign();
      auto isFwd = [&](uint32_t l) {
        if (l == laF)
          return true;
        if (!EB.hasFieldLabels())
          return false;
        if (l == EB.getLabelFieldAny())
          return true;
        for (unsigned b2 = 0; b2 < EB.getNumFieldBuckets(); b2++)
          if (l == EB.getLabelField(b2))
            return true;
        return false;
      };
      std::vector<std::vector<uint32_t>> adj(M), radj(M);
      std::vector<uint32_t> deg(M, 0);
      for (auto &E : subEdges) {
        if (!isFwd(E.label))
          continue;
        uint32_t f = lid2m[E.from], t = lid2m[E.to];
        if (f == UINT32_MAX || t == UINT32_MAX || f == t)
          continue;
        adj[f].push_back(t);
        radj[t].push_back(f);
        deg[f]++;
        deg[t]++;
      }
      std::vector<char> rm(M, 0);
      // iterative Kosaraju restricted to live nodes
      auto largestSCC = [&]() -> uint32_t {
        std::vector<uint32_t> order;
        order.reserve(M);
        std::vector<char> vis(M, 0);
        std::vector<std::pair<uint32_t, size_t>> st;
        for (uint32_t s2 = 0; s2 < M; s2++) {
          if (vis[s2] || rm[s2])
            continue;
          st.emplace_back(s2, 0);
          vis[s2] = 1;
          while (!st.empty()) {
            auto &[u, i2] = st.back();
            if (i2 < adj[u].size()) {
              uint32_t w = adj[u][i2++];
              if (!vis[w] && !rm[w]) {
                vis[w] = 1;
                st.emplace_back(w, 0);
              }
            } else {
              order.push_back(u);
              st.pop_back();
            }
          }
        }
        std::fill(vis.begin(), vis.end(), 0);
        uint32_t bestC = 0;
        std::vector<uint32_t> stack2;
        for (auto it2 = order.rbegin(); it2 != order.rend(); ++it2) {
          uint32_t s2 = *it2;
          if (vis[s2] || rm[s2])
            continue;
          uint32_t cnt = 0;
          stack2.push_back(s2);
          vis[s2] = 1;
          while (!stack2.empty()) {
            uint32_t u = stack2.back();
            stack2.pop_back();
            cnt++;
            for (uint32_t w : radj[u])
              if (!vis[w] && !rm[w]) {
                vis[w] = 1;
                stack2.push_back(w);
              }
          }
          bestC = std::max(bestC, cnt);
        }
        return bestC;
      };
      auto nodeName = [&](uint32_t m2) -> std::string {
        const Value *v2 = NF.getValueForNode(toCanon[mem[m2]]);
        if (!v2)
          return "<synthetic>";
        if (v2->hasName())
          return v2->getName().str();
        if (const auto *I2 = dyn_cast<Instruction>(v2))
          return (I2->getFunction()->getName() + "::" + I2->getOpcodeName())
              .str();
        return "<unnamed>";
      };
      errs() << "BornHub: V' giant " << bigSz << " members, induced fwd "
             << "largest SCC " << largestSCC() << "\n";
      for (int round = 0; round < 24; round++) {
        uint32_t top = UINT32_MAX, topDeg = 0;
        for (uint32_t m2 = 0; m2 < M; m2++) {
          if (rm[m2])
            continue;
          uint32_t d2 = 0;
          for (uint32_t w : adj[m2])
            if (!rm[w])
              d2++;
          for (uint32_t w : radj[m2])
            if (!rm[w])
              d2++;
          if (d2 > topDeg) {
            topDeg = d2;
            top = m2;
          }
        }
        if (top == UINT32_MAX)
          break;
        rm[top] = 1;
        errs() << "BornHub: -" << (round + 1) << " deg " << topDeg << " "
               << nodeName(top) << " -> largest SCC " << largestSCC()
               << "\n";
      }
    }
  }

  // --cfl-presolve-cone (task #38 hybrid): exact treatment only where
  // answers live. Nodes in the backward value-flow cone of icall
  // called operands are NEVER component-merged (their facts must not
  // smear); everything else keeps the cheap V-component quotient. The
  // cone nodes still get their own exact mutual-flow SCC merges via the
  // in-solve a-scc collapse, so no compression is lost among true
  // value-equals. Full-exact mode measured 9.2x at km for -2,710/+0;
  // this buys the precision where it counts at a bounded class-count
  // increase (|cone|).
  std::vector<char> inCone;
  if (CFLPreSolveCone) {
    const uint32_t Mc = (uint32_t)toCanon.size();
    inCone.assign(Mc, 0);
    const uint32_t laC = EB.getLabelAssign();
    auto isFwdC = [&](uint32_t l) {
      if (l == laC)
        return true;
      if (!EB.hasFieldLabels())
        return false;
      if (l == EB.getLabelFieldAny())
        return true;
      for (unsigned b2 = 0; b2 < EB.getNumFieldBuckets(); b2++)
        if (l == EB.getLabelField(b2))
          return true;
      return false;
    };
    std::vector<std::vector<uint32_t>> radjC(Mc);
    for (auto &E : subEdges)
      if (isFwdC(E.label))
        radjC[E.to].push_back(E.from);
    std::vector<uint32_t> bfs;
    for (const CallBase *CS2 : Ctx->IndirectCallInsts) {
      NodeIndex n2 = NF.getValueNodeFor(
          CS2->getCalledOperand()->stripPointerCastsAndAliases());
      if (n2 == AndersNodeFactory::InvalidIndex)
        continue;
      auto lit = toLocal.find(getCanonicalNode(n2));
      if (lit == toLocal.end() || inCone[lit->second])
        continue;
      inCone[lit->second] = 1;
      bfs.push_back(lit->second);
    }
    for (size_t qi = 0; qi < bfs.size(); qi++)
      for (uint32_t w : radjC[bfs[qi]])
        if (!inCone[w]) {
          inCone[w] = 1;
          bfs.push_back(w);
        }
    g_presolveConeCanon.clear();
    for (uint32_t ln = 0; ln < Mc; ln++)
      if (inCone[ln])
        g_presolveConeCanon.push_back(toCanon[ln]);
    CG_LOG("Pre-solve merge (CONE): " << bfs.size() << "/" << Mc
           << " nodes in the fptr backward cone kept exact\n");
  }

  std::vector<NodeIndex> sccRep(numSCCs, AndersNodeFactory::InvalidIndex);
  size_t merged = 0, coneSkipped = 0;
  for (uint32_t ln = 0; ln < toCanon.size() && ln < nodeToSCC.size(); ln++) {
    uint32_t scc = nodeToSCC[ln];
    if (scc == UINT32_MAX)
      continue;
    if (!inCone.empty() && inCone[ln]) {
      coneSkipped++;
      continue; // answer-relevant: no component quotient for this node
    }
    if (sccRep[scc] == AndersNodeFactory::InvalidIndex) {
      sccRep[scc] = toCanon[ln];
    } else {
      mergeCanonicalClasses(sccRep[scc], toCanon[ln]);
      merged++;
    }
  }
  if (coneSkipped)
    CG_LOG("Pre-solve merge (CONE): " << coneSkipped
           << " cone nodes excluded from component merging\n");
  CG_LOG("Pre-solve merge: " << toCanon.size() << " nodes -> " << numSCCs
         << " V' classes, " << merged << " merges, "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tSolve).count()
         << " ms\n");

  // Diagnostic: the largest V' classes are the copy/field components whose
  // V-closure dominates solve cost; name their members to attribute the
  // blowup to concrete code constructs.
  if (VerboseLevel >= 2) {
    std::unordered_map<uint32_t, uint32_t> classSize;
    for (uint32_t ln = 0; ln < toCanon.size() && ln < nodeToSCC.size(); ln++)
      if (nodeToSCC[ln] != UINT32_MAX)
        classSize[nodeToSCC[ln]]++;
    std::vector<std::pair<uint32_t, uint32_t>> ranked; // (size, scc)
    ranked.reserve(classSize.size());
    uint64_t sumSq = 0;
    for (auto &[scc, sz] : classSize) {
      ranked.emplace_back(sz, scc);
      sumSq += (uint64_t)sz * sz;
    }
    std::sort(ranked.rbegin(), ranked.rend());
    CG_LOG("Pre-solve merge: sum of squared class sizes = " << sumSq
           << " (lower bound on V' facts)\n");
    for (size_t r = 0; r < ranked.size() && r < 10; r++) {
      CG_LOG("  V' class #" << r << ": " << ranked[r].first << " nodes;"
             << " sample members:\n");
      unsigned shown = 0;
      for (uint32_t ln = 0; ln < toCanon.size() && shown < 4; ln++) {
        if (nodeToSCC[ln] != ranked[r].second)
          continue;
        const Value *V = NF.getValueForNode(toCanon[ln]);
        if (!V)
          continue;
        if (const auto *I = dyn_cast<Instruction>(V)) {
          CG_LOG("    inst in " << I->getFunction()->getName() << ": " << *I << "\n");
        } else if (V->hasName()) {
          CG_LOG("    value: " << V->getName() << "\n");
        } else {
          continue;
        }
        shown++;
      }
    }
  }
}

// Fptr-flow slicing (--cfl-fptr-slice): drop constraint-graph components
// that cannot participate in any function-pointer derivation. Function
// pointers originate only at address-taken Function value nodes (type-free
// ground truth, robust to opaque pointers), and every CFL derivation follows
// constraint edges; therefore a node in a weakly-connected component that
// contains no Function node can never contribute a callee fact. Keep exactly
// the seeded components.
void CallGraphPass::sliceEdgesToFptrComponents(std::vector<size_t> &idx) {
  const auto &edges = EB.getEdges();
  std::unordered_map<NodeIndex, NodeIndex> parent;
  std::function<NodeIndex(NodeIndex)> find = [&](NodeIndex n) {
    auto it = parent.find(n);
    if (it == parent.end()) { parent[n] = n; return n; }
    NodeIndex root = n;
    while (parent[root] != root) root = parent[root];
    while (parent[n] != root) { NodeIndex p = parent[n]; parent[n] = root; n = p; }
    return root;
  };
  for (size_t i : idx) {
    NodeIndex a = find(getCanonicalNode(edges[i].from));
    NodeIndex b = find(getCanonicalNode(edges[i].to));
    if (a != b) parent[a] = b;
  }
  std::unordered_set<NodeIndex> seededRoots;
  for (const Function *F : Ctx->AddressTakenFuncs) {
    NodeIndex n = NF.getValueNodeFor(F);
    if (n == AndersNodeFactory::InvalidIndex) continue;
    NodeIndex c = getCanonicalNode(n);
    if (parent.count(c)) seededRoots.insert(find(c));
  }
  size_t kept = 0, before = idx.size();
  for (size_t i = 0; i < idx.size(); i++) {
    if (seededRoots.count(find(getCanonicalNode(edges[idx[i]].from)))) {
      fptrSliceKept.insert(getCanonicalNode(edges[idx[i]].from));
      fptrSliceKept.insert(getCanonicalNode(edges[idx[i]].to));
      idx[kept++] = idx[i];
    }
  }
  idx.resize(kept);
  CG_LOG("Fptr slice: " << before << " edges -> " << kept << " ("
         << seededRoots.size() << " fptr components kept)\n");
}


namespace {
// Hybrid sparse/dense root-fact set for the flows-to solver. Sparse mode
// is a sorted unique u32 vector; past kPromote elements it promotes to a
// dense BitVector over [0, Universe) and never demotes. Semantics are
// identical to the former per-plane BitVectors; the representation
// matters because at kernel scale (333k roots) a dense plane is 41.6KB
// and even seeding OOMs, while most kernel classes hold a handful of
// facts. clear() empties but keeps a dense buffer (hot delta planes);
// release() frees it (merged-away losers).
// ---- Task #41: process-parallel batches (fork/CoW workers) ----
// A forked worker records the EFFECTUAL solver events of its batches —
// first-time cluster-key inserts and union-find merges — plus its
// harvested answer bits. The parent replays the event streams in
// worker order against the master quotient: replayed joins recreate
// keys/VX bridges and turn cross-worker key collisions into the
// cross-batch merges (the Jacobi form of the sequential rounds).
struct BatchEvt {
  uint8_t kind; // 0 = join (a=cell, b=origin rid, c=shift), 1 = merge(a,b)
  uint32_t a, b, c;
};
static bool g_batchRecord = false;
static std::vector<BatchEvt> g_batchEvts;

class FactSet {
  llvm::SmallVector<uint32_t, 2> S; // sorted, unique (sparse mode)
  std::unique_ptr<llvm::BitVector> D; // non-null => dense mode
  static constexpr size_t kPromote = 128;
  void promote() {
    D = std::make_unique<llvm::BitVector>(Universe);
    for (uint32_t o : S) D->set(o);
    S.clear();
  }

public:
  static uint32_t Universe;
  bool none() const { return D ? D->none() : S.empty(); }
  bool any() const { return !none(); }
  size_t count() const { return D ? D->count() : S.size(); }
  bool test(uint32_t o) const {
    if (D) return o < D->size() && D->test(o);
    return std::binary_search(S.begin(), S.end(), o);
  }
  void set(uint32_t o) {
    if (D) {
      // Universe can grow between drains (incrementally minted roots);
      // dense buffers widen lazily on first touch past their old width.
      if (o >= D->size()) D->resize(std::max<uint32_t>(Universe, o + 1));
      D->set(o);
      return;
    }
    auto it = std::lower_bound(S.begin(), S.end(), o);
    if (it != S.end() && *it == o) return;
    S.insert(it, o);
    if (S.size() > kPromote) promote();
  }
  void reset(uint32_t o) {
    if (D) { if (o < D->size()) D->reset(o); return; }
    auto it = std::lower_bound(S.begin(), S.end(), o);
    if (it != S.end() && *it == o) S.erase(it);
  }
  void clear() {
    if (D) D->reset();
    S.clear();
  }
  void release() {
    D.reset();
    llvm::SmallVector<uint32_t, 2>().swap(S); // drop heap capacity too
  }
  void copyFrom(const FactSet &o) {
    if (o.D) {
      if (D) *D = *o.D; else D = std::make_unique<llvm::BitVector>(*o.D);
      S.clear();
    } else if (D) {
      D->reset();
      for (uint32_t x : o.S) {
        if (x >= D->size()) D->resize(std::max<uint32_t>(Universe, x + 1));
        D->set(x);
      }
    } else {
      S = o.S;
    }
  }
  void unionWith(const FactSet &o) {
    if (o.none()) return;
    if (o.D) {
      if (!D) promote();
      *D |= *o.D;
    } else if (D) {
      for (uint32_t x : o.S) {
        if (x >= D->size()) D->resize(std::max<uint32_t>(Universe, x + 1));
        D->set(x);
      }
    } else {
      llvm::SmallVector<uint32_t, 8> merged;
      merged.reserve(S.size() + o.S.size());
      std::set_union(S.begin(), S.end(), o.S.begin(), o.S.end(),
                     std::back_inserter(merged));
      S = std::move(merged);
      if (S.size() > kPromote) promote();
    }
  }
  void subtract(const FactSet &o) { // this \= o
    if (none() || o.none()) return;
    if (D) {
      if (o.D) D->reset(*o.D);
      else for (uint32_t x : o.S) if (x < D->size()) D->reset(x);
    } else if (o.D) {
      S.erase(std::remove_if(S.begin(), S.end(),
                             [&](uint32_t x) { return o.test(x); }),
              S.end());
    } else {
      llvm::SmallVector<uint32_t, 8> kept;
      std::set_difference(S.begin(), S.end(), o.S.begin(), o.S.end(),
                          std::back_inserter(kept));
      S = std::move(kept);
    }
  }
  void intersectWith(const FactSet &o) {
    if (none()) return;
    if (o.none()) { clear(); return; }
    if (D && o.D) {
      *D &= *o.D;
    } else if (D) { // dense this, sparse other
      llvm::SmallVector<uint32_t, kPromote> surv;
      for (uint32_t x : o.S)
        if (test(x)) surv.push_back(x);
      D->reset();
      for (uint32_t x : surv) D->set(x);
    } else if (o.D) {
      S.erase(std::remove_if(S.begin(), S.end(),
                             [&](uint32_t x) { return !o.test(x); }),
              S.end());
    } else {
      llvm::SmallVector<uint32_t, 8> kept;
      std::set_intersection(S.begin(), S.end(), o.S.begin(), o.S.end(),
                            std::back_inserter(kept));
      S = std::move(kept);
    }
  }
  template <typename F> void forEach(F f) const {
    if (D) {
      for (int i = D->find_first(); i != -1; i = D->find_next(i))
        f((uint32_t)i);
    } else {
      for (uint32_t x : S) f(x);
    }
  }
};
uint32_t FactSet::Universe = 0;

// Bulk-synchronous worker pool for the flows-to wave phases: run(f)
// executes f(tid) on all T threads (the caller participates as tid 0)
// and returns only after every worker finished — a full barrier, so
// phase boundaries are also happens-before edges for the shared solver
// state toggled between phases (union-find freeze, lock discipline).
class WavePool {
  unsigned T;
  std::vector<std::thread> workers;
  std::mutex m;
  std::condition_variable cvGo, cvDone;
  uint64_t epoch = 0;
  unsigned pending = 0;
  bool quit = false;
  std::function<void(unsigned)> fn;

public:
  explicit WavePool(unsigned T_) : T(T_) {
    for (unsigned t = 1; t < T; t++)
      workers.emplace_back([this, t] {
        uint64_t seen = 0;
        std::unique_lock<std::mutex> lk(m);
        while (true) {
          cvGo.wait(lk, [&] { return quit || epoch != seen; });
          if (quit) return;
          seen = epoch;
          lk.unlock();
          fn(t);
          lk.lock();
          if (--pending == 0) cvDone.notify_all();
        }
      });
  }
  unsigned size() const { return T; }
  void run(std::function<void(unsigned)> f) {
    if (T == 1) { f(0); return; }
    {
      std::lock_guard<std::mutex> lk(m);
      fn = std::move(f);
      pending = T - 1;
      epoch++;
    }
    cvGo.notify_all();
    fn(0);
    std::unique_lock<std::mutex> lk(m);
    cvDone.wait(lk, [&] { return pending == 0; });
  }
  ~WavePool() {
    {
      std::lock_guard<std::mutex> lk(m);
      quit = true;
    }
    cvGo.notify_all();
    for (auto &w : workers) w.join();
  }
};
} // namespace

// Answer-anchored flows-to resolution (ORCFL prototype). After the
// quotient (presolve merge collapses a-cycles so the copy graph is a DAG of
// classes), V restricted to function sources is pure forward propagation:
// functions have no incoming assignments. Facts are (origin root, net field
// shift) pairs mirroring the shift-indexed grammar: a-edges and M-joins
// preserve the shift, an f<r> edge adds r mod P, an fx wildcard absorbs to
// the unknown shift X. The M splice is a join rule: two cells alias when
// their parents share a fact exactly — same origin AND same shift (V), or
// either side at X (VX). container_of round trips need no special casing:
// down 8 then down 8 carries the same shift as flat down 16. Storage is
// rectangular (fact sets), never pairwise V.

// Tracepoint keyed channels (task #35). One registration family, four
// entry points; the census (km + kernel, 2026-08-02) classifies 100%
// of their callsites as CONST-key or one of the two struct-mediated
// registrars, and 100% of __traceiter_* bodies name their key.
static bool isTracepointRegFn(StringRef n) {
  return n == "tracepoint_probe_register" ||
         n == "tracepoint_probe_register_prio" ||
         n == "tracepoint_probe_register_prio_may_exist" ||
         n == "tracepoint_probe_unregister";
}
static size_t g_tpKeyConstBinds = 0, g_tpKeyMediatorBinds = 0,
              g_tpKeyDispatchWires = 0, g_tpKeyUnclassified = 0,
              g_tpKeyKeylessIter = 0, g_tpKeyUnmapped = 0,
              g_tpKeyClassFnSkipped = 0, g_tpKeyMediatorDataPools = 0,
              g_tpKeyIterLoadsSevered = 0;
// Keys bound by the initializer walker — mediator callsites pool their
// dynamic data argument (trace_event_file, bpf_prog) into every
// walker-bound key's data cell (data was globally pooled before this
// model too; only the fn plane is keyed).
static std::vector<const GlobalVariable *> g_tpWalkerKeys;
// v3 (task #35): ANSWER-LEVEL primitive. The graph cannot carry per-key
// fn channels at kernel scale: probe VALUE classes are V-merged into
// the giant (fn identity is a casualty of the quotient — TRACE-BWD
// showed __traceiter operands AND probe classes both inside one merged
// mega-class), so any graph channel imports the pool at the source.
// The census-complete registration table IS the answer for __traceiter
// sites; the resolution loop takes targets from here (the #14
// static_call precedent) and its normal arg wiring feeds the probes.
static boost::unordered_flat_map<NodeIndex, FuncSet> g_tpKeyProbes;
static boost::unordered_flat_map<const llvm::CallBase *, NodeIndex>
    g_tpIterIcallKey;
static boost::unordered_flat_set<NodeIndex> g_tpKeyHasDynProbe;
static size_t g_tpKeyModelAnswered = 0, g_tpKeyDynProbe = 0,
              g_tpKeyFallbackSites = 0, g_tpKeyTypeRej = 0;

// --cfl-static-ops-tables (task #36): answer-level channel for
// static_call keys updated from ops-struct tables — the kvm_x86 /
// x86_pmu / apic_call families (1,225,715 pin pairs, ~all type-
// fallback: the update's fn argument is a dynamic load the graph
// never resolves). The update site's IR names the correlation
// structurally — load gep(%struct.kvm_x86_ops, base, 0, N) — and the
// binding inventory is the set of same-typed global initializers
// (vmx_x86_ops/svm_x86_ops, intel/amd pmu, the apic drivers). Keys
// with any non-conforming update argument (e.g. bpf_dispatcher's JIT
// image) are UNTABLED and their sites keep graph behavior, LOUDLY.
struct SctPending {
  std::string keyName;    // __SCK__<suffix>
  std::string structName; // canonical (suffix-stripped) struct name
  unsigned fieldIdx;
};
static std::vector<SctPending> g_sctPendings;
static boost::unordered_flat_map<std::string, FuncSet> g_sctKeyTable;
static boost::unordered_flat_set<std::string> g_sctKeyUntabled;
static bool g_sctTableBuilt = false;
static size_t g_sctUpdConst = 0, g_sctUpdLoad = 0, g_sctUpdNonconform = 0,
              g_sctTablesScanned = 0, g_sctPendingNoTable = 0,
              g_sctSitesModelAnswered = 0, g_sctSitesUntabled = 0,
              g_sctTypeRej = 0;
static StringRef sctCanonStructName(StringRef n) {
  // "struct.kvm_x86_ops.123" -> "struct.kvm_x86_ops" (per-TU suffixes)
  size_t dot = n.rfind('.');
  if (dot != StringRef::npos && dot + 1 < n.size() &&
      isdigit(static_cast<unsigned char>(n[dot + 1])))
    return n.substr(0, dot);
  return n;
}

// The dispatch key of a __traceiter_* body: the base of the constexpr
// GEP its funcs-head load reads from. Memoized; single-threaded visit.
static const GlobalVariable *traceiterKeyOf(const Function *F) {
  static boost::unordered_flat_map<const Function *, const GlobalVariable *>
      memo;
  auto it = memo.find(F);
  if (it != memo.end())
    return it->second;
  const GlobalVariable *key = nullptr;
  for (const Instruction &I : instructions(*F)) {
    const auto *LI = dyn_cast<LoadInst>(&I);
    if (!LI)
      continue;
    const Value *P = LI->getPointerOperand();
    if (const auto *CE = dyn_cast<ConstantExpr>(P))
      if (CE->getOpcode() == Instruction::GetElementPtr)
        P = CE->getOperand(0);
    if (const auto *GV = dyn_cast<GlobalVariable>(P->stripPointerCasts()))
      if (GV->getName().starts_with("__tracepoint_")) {
        key = GV;
        break;
      }
  }
  memo[F] = key;
  return key;
}

static size_t g_rodataJoinsSkipped = 0; // --cfl-probe-rodata-joins
static size_t g_sinkAblatedJoins = 0; // --cfl-probe-sink-ablate (UNSOUND)
// --cfl-sink-instr / --cfl-confirm-sinks (task #31/#32 design)
static size_t g_sinkSitesConfirmed = 0, g_sinkSitesEscaped = 0,
              g_sinkSitesViolated = 0;
static bool g_sinkContractChecked = false;
static std::map<std::string, size_t> g_sinkEscapeSinks; // sink -> sites
// task #34 re-key v3: OPAQUE-ARENA model. Two join-time seal re-keys
// were falsified at km before this: (v1) sealing cellsOf[class] of the
// confirmer's anchor values over-reached 24x (-59,737 vs name-keyed
// -2,442; presolve copy chains merge payload pointers into
// generic-pointer classes, sweeping foreign deref sites at
// irq/bpf/clocksource); (v2) sealing only each anchor's own deref node
// under-reached to -0/+0 (673 anchors collapse to 3 presolve cell
// classes; the giant-join glue forms at the rb-page OBJECT cells
// reached through OTHER pointers, so facts flow around the boundary
// cells). The object-keyed scope the name patterns approximated is
// instead obtained STRUCTURALLY: each payload accessor's callsites
// return a pointer to one shared opaque arena object (per accessor),
// replacing the ret binding into ring-buffer internals. Payload
// write->read flow is PRESERVED (sounder than the seal, which cut it);
// only the false unification of payload cells with kernel-object cells
// never forms. No join-time check, no name patterns on minted objects.
static bool isSinkPayloadAccessor(StringRef n) {
  return n == "ring_buffer_event_data" || n == "perf_trace_buf_alloc";
}
static size_t g_sinkArenaSites = 0;
static NodeIndex g_sinkArenaObj[2] = {AndersNodeFactory::InvalidIndex,
                                      AndersNodeFactory::InvalidIndex};

// task #32: stratum classification of an inttoptr's int computation —
// shared by the census and the --cfl-probe-stratum-ablate probe.
enum StrataBucket {
  STRATA_DIRECTMAP,
  STRATA_VMEMMAP,
  STRATA_KERNELMAP,
  STRATA_MMFN,
  STRATA_TRACE,
  STRATA_OTHER,
  STRATA_NBUCK
};
static StrataBucket strataClassify(const Value *V0, const Function *F) {
  SmallVector<const Value *, 16> wl{V0};
  SmallPtrSet<const Value *, 16> seen;
  unsigned steps = 0;
  while (!wl.empty() && steps++ < 64) {
    const Value *V = wl.pop_back_val();
    if (!seen.insert(V).second)
      continue;
    if (const auto *CI = dyn_cast<ConstantInt>(V)) {
      uint64_t c = CI->getZExtValue();
      if (c == 0xffff888000000000ull)
        return STRATA_DIRECTMAP;
      if (c == 0xffffea0000000000ull)
        return STRATA_VMEMMAP;
      if (c == 0xffffffff80000000ull)
        return STRATA_KERNELMAP;
      continue;
    }
    if (const auto *LI = dyn_cast<LoadInst>(V)) {
      const Value *P = LI->getPointerOperand()->stripPointerCasts();
      if (const auto *GV = dyn_cast<GlobalVariable>(P)) {
        StringRef n = GV->getName();
        if (n == "page_offset_base")
          return STRATA_DIRECTMAP;
        if (n == "vmemmap_base")
          return STRATA_VMEMMAP;
        if (n == "phys_base")
          return STRATA_KERNELMAP;
      }
      continue; // don't walk through memory
    }
    if (const auto *I2 = dyn_cast<Instruction>(V)) {
      if (isa<BinaryOperator>(I2) || isa<CastInst>(I2) ||
          isa<SelectInst>(I2) || isa<PHINode>(I2))
        for (const Use &Op : I2->operands())
          wl.push_back(Op.get());
    }
  }
  StringRef fn = F->getName();
  if (fn.starts_with("perf_trace_") || fn.contains("trace_event") ||
      fn.starts_with("__bpf_trace_"))
    return STRATA_TRACE;
  if (fn.contains("pte") || fn.contains("pmd") || fn.contains("pud") ||
      fn.contains("pgd") || fn.contains("pfn") || fn.contains("_page"))
    return STRATA_MMFN;
  return STRATA_OTHER;
}
static bool strataIsPhys(StrataBucket b) {
  return b == STRATA_DIRECTMAP || b == STRATA_VMEMMAP ||
         b == STRATA_KERNELMAP || b == STRATA_MMFN;
}
static size_t g_strataAblated = 0; // probe: severed inttoptr bridges

// --cfl-probe-usercopy-ablate (task #32): user ingress reaches kernel
// memory through two uaccess shapes, both severed here.
//   (1) bulk copies (_copy_from_user et al.): the body's rep-movsb
//       `~{memory}`-clobber asm is the SOLE source of pointer-memory
//       edges (task #23 raw-ptr closure aliases *dest<->*src and stores
//       the pointer inputs into those cells). Gated by the enclosing
//       primitive name so egress (copy_to_user) and the direction-
//       agnostic shared movsb helpers are left intact.
//   (2) scalar reads (get_user): the value materializes at the CALLER's
//       `call __get_user_N` asm as a register output loaded through the
//       user pointer (the result aggregate can be ptr-typed). The
//       enclosing fn is arbitrary, so this shape is gated by the asm
//       text mentioning __get_user ("__put_user"/egress won't match).
static bool isUserCopyFromFn(llvm::StringRef n) {
  return n == "copy_from_user" || n == "_copy_from_user" ||
         n == "__copy_from_user" || n == "__copy_from_user_inatomic" ||
         n == "copy_from_user_nofault" || n == "strncpy_from_user";
}
static size_t g_userCopyAsmSevered = 0;   // from-user copy-body asm sites cut
static size_t g_userGetAsmSevered = 0;    // caller-side get_user asm sites cut
static size_t g_userCopyDerefsSevered = 0; // raw-ptr memory derefs suppressed

// --cfl-cert-usercopy (task #32): the positive-direction check. At the
// SAME two ingress shapes the ablation severs, mint a synthetic origin
// object U and assign it into the asm's raw-ptr memory cells — "user
// bytes" become a trackable root. After solve, any icall fptr class
// whose fact planes carry a U root is a stratum crossing to inventory
// (U is not a function, so it never adds a callee — but the extra
// roots can add cluster joins, so this config's ANSWERS are not
// pin-comparable).
static std::vector<std::pair<NodeIndex, std::string>>
    g_userCertObjs; // (U object node, site label)
static size_t g_userCertCopySites = 0, g_userCertGetSites = 0;

static size_t g_opsTightSites = 0, g_opsTightRej = 0; // --cfl-ops-pairs step 2
static size_t g_tagRoundTrips = 0; // fs: ptrtoint wildcards suppressed
                                   // (tag-bit-only local closures)
bool CallGraphPass::runFlowsToResolution() {
  auto tStart = std::chrono::steady_clock::now();
  const auto &edges = EB.getEdges();
  const uint32_t la = EB.getLabelAssign();
  const uint32_t ld = EB.getLabelDeref();
  const unsigned NB = EB.getNumFieldBuckets(); // 0 = field-insensitive
  std::unordered_map<uint32_t, uint32_t> bucketOfLabel;
  uint32_t lfx = UINT32_MAX;
  if (NB > 0) {
    for (unsigned b = 0; b < NB; b++)
      bucketOfLabel[EB.getLabelField(b)] = b;
    lfx = EB.getLabelFieldAny();
  }

  // Dense ids over canonical nodes.
  std::unordered_map<NodeIndex, uint32_t> toDense;
  std::vector<NodeIndex> toOrig;
  auto dense = [&](NodeIndex canon) {
    auto [it, ins] = toDense.emplace(canon, (uint32_t)toOrig.size());
    if (ins) toOrig.push_back(canon);
    return it->second;
  };
  std::vector<std::pair<uint32_t, uint32_t>> aEdges;
  std::vector<std::pair<uint32_t, uint32_t>> dEdges; // parent -> cell
  std::vector<std::tuple<uint32_t, uint32_t, uint32_t>> fEdges; // base,res,bkt
  boost::unordered_flat_set<uint32_t> wildcardNodes; // fx self-loop bases
  for (const auto &E : edges) {
    NodeIndex cf = getCanonicalNode(E.from), ct = getCanonicalNode(E.to);
    if (E.label == la) {
      if (cf != ct) aEdges.emplace_back(dense(cf), dense(ct));
    } else if (E.label == ld) {
      dEdges.emplace_back(dense(cf), dense(ct));
    } else if (NB > 0 && E.label == lfx) {
      wildcardNodes.insert(dense(cf));
    } else if (NB > 0) {
      auto bIt = bucketOfLabel.find(E.label);
      if (bIt != bucketOfLabel.end())
        fEdges.emplace_back(dense(cf), dense(ct), bIt->second);
    }
  }
  uint32_t N = toOrig.size(); // grows when resolution wiring adds nodes
  // Fixed-capacity headroom for the atomic per-class arrays (they cannot
  // be resized in place): incremental wiring adds at most a few classes
  // per resolved callsite (allocator callsite values, heap objects,
  // previously edge-less formals).
  const uint32_t solverCapN = N + (1u << 18);
  std::vector<std::vector<uint32_t>> outA(N);
  for (auto [s, t] : aEdges) outA[s].push_back(t);
  // f-edges as shift transformers: (target, residue).
  std::vector<std::vector<std::pair<uint32_t, uint32_t>>> outF(N);
  for (auto &[b, r, bk] : fEdges)
    outF[b].emplace_back(r, bk);

  // In-degree over the FULL a/f-graph, before any slicing: a node whose
  // incoming edges are sliced away was not a value origin and must not be
  // minted as a root; a field-pointer result is fully described by its
  // base's facts plus the shift, so it is not an origin either.
  std::vector<bool> hasIn(N, false);
  for (auto [s, t] : aEdges) hasIn[t] = true;
  for (auto &[b, r, bk] : fEdges) hasIn[r] = true;
  std::unordered_map<NodeIndex, const Function *> funcOfCanon;
  for (const Function *F : Ctx->AddressTakenFuncs) {
    NodeIndex n = NF.getValueNodeFor(F);
    if (n != AndersNodeFactory::InvalidIndex)
      funcOfCanon[getCanonicalNode(n)] = F;
  }

  // Derivation slice (1-bit taint): keep only classes that can appear in
  // some function->fptr derivation, or that supply alias evidence (shared
  // value origins) for a memory join usable by one. Alias is
  // over-approximated by Steensgaard classes (unification), which the
  // precise shared-root join then refines on the slice.
  std::vector<char> inSlice; // empty => no slicing
  if (CFLFlowsToSlice) {
    auto tSlice = std::chrono::steady_clock::now();
    // Steensgaard: union a-edge endpoints; one representative cell per
    // class, unioning cells whenever their owning classes merge.
    std::vector<uint32_t> ufp(N);
    for (uint32_t i = 0; i < N; i++) ufp[i] = i;
    auto find = [&](uint32_t x) {
      while (ufp[x] != x) { ufp[x] = ufp[ufp[x]]; x = ufp[x]; }
      return x;
    };
    std::vector<uint32_t> cellRep(N, UINT32_MAX);
    std::vector<std::pair<uint32_t, uint32_t>> pending;
    auto unite = [&](uint32_t a, uint32_t b) {
      a = find(a); b = find(b);
      if (a == b) return;
      ufp[b] = a;
      if (cellRep[b] != UINT32_MAX) {
        if (cellRep[a] != UINT32_MAX)
          pending.emplace_back(cellRep[a], cellRep[b]);
        else
          cellRep[a] = cellRep[b];
      }
    };
    auto drain = [&]() {
      while (!pending.empty()) {
        auto [x, y] = pending.back();
        pending.pop_back();
        unite(x, y);
      }
    };
    for (auto [s, t] : aEdges) { unite(s, t); drain(); }
    // Field steps fold to copies here (field-insensitive Steensgaard):
    // Fld(r1,r2) implies V(b1,b2), so unifying result with base keeps the
    // over-approximation valid for the field-sensitive join too.
    for (auto &[b, r, bk] : fEdges) { unite(b, r); drain(); }
    for (auto [p, c] : dEdges) {
      uint32_t rp = find(p);
      if (cellRep[rp] == UINT32_MAX) cellRep[rp] = find(c);
      else { pending.emplace_back(cellRep[rp], c); drain(); }
    }

    std::vector<char> isCell(N, 0);
    for (auto [p, c] : dEdges) isCell[c] = 1;
    std::unordered_map<uint32_t, std::vector<uint32_t>> classCells;
    for (uint32_t c = 0; c < N; c++)
      if (isCell[c]) classCells[find(c)].push_back(c);
    std::vector<std::vector<uint32_t>> cellParents(N);
    for (auto [p, c] : dEdges) cellParents[c].push_back(p);
    // Facts flow through f-edges (shifted), so sweeps and the evidence
    // closure treat them as plain flow edges.
    std::vector<std::vector<uint32_t>> outAF(N), inA(N);
    for (auto [s, t] : aEdges) { outAF[s].push_back(t); inA[t].push_back(s); }
    for (auto &[b, r, bk] : fEdges) { outAF[b].push_back(r); inA[r].push_back(b); }

    // 1-bit BFS with a memory jump: a marked cell marks every cell of its
    // Steensgaard class (over-approximates the join copies, both ways —
    // joins are bidirectional).
    auto sweep = [&](std::vector<char> &mark,
                     const std::vector<uint32_t> &seeds,
                     const std::vector<std::vector<uint32_t>> &adj) {
      boost::unordered_flat_set<uint32_t> jumped;
      std::vector<uint32_t> q;
      auto add = [&](uint32_t v) {
        if (!mark[v]) { mark[v] = 1; q.push_back(v); }
      };
      for (uint32_t v : seeds) add(v);
      while (!q.empty()) {
        uint32_t v = q.back();
        q.pop_back();
        if (isCell[v]) {
          uint32_t cls = find(v);
          if (jumped.insert(cls).second)
            for (uint32_t c : classCells[cls]) add(c);
        }
        for (uint32_t t : adj[v]) add(t);
      }
    };

    std::vector<uint32_t> fSeeds, bSeeds;
    for (const auto &kv : funcOfCanon) {
      auto it = toDense.find(kv.first);
      if (it != toDense.end()) fSeeds.push_back(it->second);
    }
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto it = toDense.find(getCanonicalNode(fn));
      if (it != toDense.end()) bSeeds.push_back(it->second);
    }
    std::vector<char> Fm(N, 0), Bm(N, 0);
    sweep(Fm, fSeeds, outAF);
    sweep(Bm, bSeeds, inA);

    // Evidence closure: a memory join on a kept derivation is justified by
    // value origins its two parents share, and those origins flow to the
    // parents along paths that may cross further joins — recurse. Touching
    // a cell class keeps its cells and walks backward from their parents;
    // any cell reached backward touches its own class in turn.
    std::vector<char> Em(N, 0);
    boost::unordered_flat_set<uint32_t> touched;
    std::vector<uint32_t> qE;
    auto addE = [&](uint32_t v) {
      if (!Em[v]) { Em[v] = 1; qE.push_back(v); }
    };
    auto touchClass = [&](uint32_t cls) {
      if (!touched.insert(cls).second) return;
      for (uint32_t c : classCells[cls]) {
        addE(c);
        for (uint32_t p : cellParents[c]) addE(p);
      }
    };
    for (uint32_t c = 0; c < N; c++)
      if (isCell[c] && Fm[c] && Bm[c]) touchClass(find(c));
    while (!qE.empty()) {
      uint32_t v = qE.back();
      qE.pop_back();
      if (isCell[v]) touchClass(find(v));
      for (uint32_t u : inA[v]) addE(u);
    }

    inSlice.assign(N, 0);
    size_t nCore = 0, nSlice = 0;
    for (uint32_t v = 0; v < N; v++) {
      bool core = Fm[v] && Bm[v];
      nCore += core;
      inSlice[v] = core || Em[v];
      nSlice += inSlice[v];
    }
    size_t fullA = aEdges.size(), fullD = dEdges.size(), fullF = fEdges.size();
    {
      std::vector<std::pair<uint32_t, uint32_t>> keep;
      keep.reserve(aEdges.size());
      for (auto [s, t] : aEdges)
        if (inSlice[s] && inSlice[t]) keep.emplace_back(s, t);
      aEdges.swap(keep);
    }
    {
      std::vector<std::pair<uint32_t, uint32_t>> keep;
      for (auto [p, c] : dEdges)
        if (inSlice[p] && inSlice[c]) keep.emplace_back(p, c);
      dEdges.swap(keep);
    }
    {
      std::vector<std::tuple<uint32_t, uint32_t, uint32_t>> keep;
      for (auto &[b, r, bk] : fEdges)
        if (inSlice[b] && inSlice[r]) keep.emplace_back(b, r, bk);
      fEdges.swap(keep);
    }
    {
      boost::unordered_flat_set<uint32_t> keep;
      for (uint32_t w : wildcardNodes)
        if (inSlice[w]) keep.insert(w);
      wildcardNodes.swap(keep);
    }
    for (auto &v : outA) v.clear();
    for (auto [s, t] : aEdges) outA[s].push_back(t);
    for (auto &v : outF) v.clear();
    for (auto &[b, r, bk] : fEdges) outF[b].emplace_back(r, bk);
    CG_LOG("FlowsTo slice: " << nSlice << "/" << N << " classes kept ("
           << nCore << " core), " << aEdges.size() << "/" << fullA
           << " a-edges, " << dEdges.size() << "/" << fullD << " d-edges, "
           << fEdges.size() << "/" << fullF << " f-edges, "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tSlice).count()
           << " ms\n");
  }

  // Every load/store has its own assistant cell node, so a pointer class
  // carries one cell per access site — keep them all; the join rule must
  // see the store-side and load-side cells of the same class.
  std::vector<std::vector<uint32_t>> cellsOf(N);
  for (auto [p, c] : dEdges) {
    auto &cs = cellsOf[p];
    if (std::find(cs.begin(), cs.end(), c) == cs.end()) cs.push_back(c);
  }
  // Facts are (origin root, shift) pairs, stored as NSHIFT bit planes per
  // class: plane s is a bitset over origins present at shift s. Shift
  // values: 0..NB-1 exact residues, NB = unknown (X). Field-insensitive
  // (NB=0) degenerates to a single plane.
  const uint32_t NSHIFT = NB + 1;
  const uint32_t SHIFT_X = NB;

  // Root ids: any origin class, plus function classes flagged for answers.
  // Presolve copy/field merges can union an alloca/global/alloc-site value
  // class with in-edged nodes; such a class still names a distinct object
  // and must be minted even with hasIn set — otherwise the object's
  // identity is silently erased (harfbuzz hb_map_iter sret/memcpy chains).
  // --cfl-probe-rodata-joins: does this class contain a link-time
  // constant global? Such an origin's identity keys joins between
  // READERS of immutable memory — the aliasing carries no store->load
  // flow (no runtime stores into rodata). The probe skips those joins
  // wholesale to UPPER-BOUND the closure-size win of the copy-not-unify
  // refinement (task #25); it over-removes (const-table home-cell reads
  // also ride these joins), so answers may drop — measurement only.
  auto valueIsRodata = [&](NodeIndex m) {
    const Value *v = NF.getValueForNode(m);
    const auto *GV = dyn_cast_or_null<GlobalVariable>(v);
    return GV && GV->isConstant();
  };
  auto classIsRodata = [&](NodeIndex canon) {
    if (valueIsRodata(canon)) return true;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m : mit->second)
        if (valueIsRodata(m)) return true;
    return false;
  };
  auto valueIsOrigin = [&](NodeIndex m) {
    if (!NF.isValueNode(m))
      return false;
    if (AllocSites.count(m))
      return true;
    const Value *v = NF.getValueForNode(m);
    return v && (isa<AllocaInst>(v) || isa<GlobalVariable>(v));
  };
  std::vector<char> hasOrigin(N, 0);
  for (uint32_t n = 0; n < N; n++) {
    NodeIndex canon = toOrig[n];
    bool org = valueIsOrigin(canon);
    if (!org) {
      auto mit = canonicalClassMembers.find(canon);
      if (mit != canonicalClassMembers.end())
        for (NodeIndex m : mit->second)
          if (valueIsOrigin(m)) { org = true; break; }
    }
    hasOrigin[n] = org;
  }
  // --cfl-bidi-prune: field-matched bidirected partition oracle
  // (BidirectedReach / field-sensitive-Steensgaard style, O(m a(n))):
  // unify a-edge endpoints; per-partition label->target out-maps where
  // colliding d / f<r> labels unify their targets (wildcard bases fold
  // all f labels into one). SOUND relevance cone (FI argument in the
  // scaling doc): an origin's facts can only key joins at cells inside
  // the forward d/f closure of its partition, and every downstream
  // consequence stays inside that closure; if the closure never meets
  // an fptr partition, the origin cannot influence any answer.
  // Measurement mode: report the statically prunable origin fraction.
  std::vector<char> bidiMarked; // partition-class relevance (by class id)
  std::vector<uint32_t> bidiUF;
  if (CFLBidiPrune) {
    auto tBidi = std::chrono::steady_clock::now();
    bidiUF.resize(N);
    for (uint32_t i = 0; i < N; i++) bidiUF[i] = i;
    std::function<uint32_t(uint32_t)> bfind = [&](uint32_t x) {
      while (bidiUF[x] != x) { bidiUF[x] = bidiUF[bidiUF[x]]; x = bidiUF[x]; }
      return x;
    };
    // label 0 = deref (d); label 1+r = field residue r; wildcard bases
    // fold every field label to 1 (unknown shift matches all).
    std::vector<boost::unordered_flat_map<uint32_t, uint32_t>> omap(N);
    std::vector<char> blind(N, 0);
    for (uint32_t w : wildcardNodes) blind[w] = 1;
    std::vector<std::pair<uint32_t, uint32_t>> pend;
    std::function<void(uint32_t, uint32_t, uint32_t)> addLbl =
        [&](uint32_t x, uint32_t l, uint32_t y) {
          x = bfind(x);
          if (blind[x] && l >= 1) l = 1;
          auto [it, ins] = omap[x].try_emplace(l, y);
          if (!ins && bfind(it->second) != bfind(y))
            pend.emplace_back(it->second, y);
        };
    auto bunite = [&](uint32_t x, uint32_t y) {
      x = bfind(x); y = bfind(y);
      if (x == y) return;
      if (omap[x].size() < omap[y].size()) std::swap(x, y);
      bidiUF[y] = x;
      if (blind[y] && !blind[x]) {
        blind[x] = 1;
        // fold x's field labels together under the new blindness
        std::vector<uint32_t> ftgts;
        for (auto it = omap[x].begin(); it != omap[x].end();) {
          if (it->first >= 1) { ftgts.push_back(it->second); it = omap[x].erase(it); }
          else ++it;
        }
        for (uint32_t t : ftgts) addLbl(x, 1, t);
      }
      for (auto &[l, t] : omap[y]) addLbl(x, l, t);
      omap[y].clear();
    };
    for (auto [s2, t2] : aEdges) bunite(s2, t2);
    for (auto [p2, c2] : dEdges) addLbl(p2, 0, c2);
    for (auto &[b2, r2, bk2] : fEdges) addLbl(b2, 1 + bk2, r2);
    while (!pend.empty()) {
      auto [x, y] = pend.back();
      pend.pop_back();
      bunite(x, y);
    }
    // Backward BFS from fptr partitions over reversed partition edges.
    std::vector<std::vector<uint32_t>> rev(N);
    for (uint32_t n = 0; n < N; n++) {
      if (bfind(n) != n) continue;
      for (auto &[l, t] : omap[n]) rev[bfind(t)].push_back(n);
    }
    bidiMarked.assign(N, 0);
    std::vector<uint32_t> bfs;
    size_t fptrParts = 0;
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn2 = NF.getValueNodeFor(fp);
      if (fn2 == AndersNodeFactory::InvalidIndex) continue;
      auto dIt = toDense.find(getCanonicalNode(fn2));
      if (dIt == toDense.end()) continue;
      uint32_t rp = bfind(dIt->second);
      if (!bidiMarked[rp]) { bidiMarked[rp] = 1; bfs.push_back(rp); fptrParts++; }
    }
    while (!bfs.empty()) {
      uint32_t n = bfs.back();
      bfs.pop_back();
      for (uint32_t p2 : rev[n]) {
        uint32_t rp = bfind(p2);
        if (!bidiMarked[rp]) { bidiMarked[rp] = 1; bfs.push_back(rp); }
      }
    }
    size_t parts = 0, markedParts = 0;
    for (uint32_t n = 0; n < N; n++) {
      if (bfind(n) != n) continue;
      parts++;
      if (bidiMarked[n]) markedParts++;
    }
    CG_LOG("BidiPrune: " << parts << " partitions over " << N
           << " classes, " << markedParts << " in the fptr cone ("
           << fptrParts << " fptr partitions), "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tBidi).count()
           << " ms\n");
    // expose relevance per CLASS for the mint loop's tally
    for (uint32_t n = 0; n < N; n++) bidiMarked[n] = bidiMarked[bfind(n)];
  }
  // --cfl-lazy-mint (task #21): demand-driven roots to the exact bound.
  // A = classes backward-reachable from any fptr class over a/f flow
  // edges PLUS cell->owner hops: a cell in A makes every origin
  // reaching its owning pointer a potential join witness on an answer
  // path, and the owner hop must apply to the whole closure — not only
  // to fptr-feeding cells — or the witnesses of intermediate joins
  // (merges an answer path's connectivity depends on) are missed.
  // Origin/identity candidates outside A are DEFERRED, never dropped:
  // every drain fixpoint recomputes A on the merge-coarsened quotient
  // (facts propagate over a/f edges exactly as reachability, so
  // "observed potential" = this closure on the LIVE quotient) and
  // mints the newly admitted ones; stability of A and the root set is
  // the restricted fixpoint (first-missed-join induction, scaling doc
  // §2026-07-18). Function roots are always minted: answer alphabet.
  std::vector<uint32_t> lazyDeferred; // deferred candidate classes (dense)
  std::vector<char> lazyA;            // initial-quotient closure
  if (CFLLazyMint) {
    if (NB > 0)
      WARNING("[UNSOUND-RISK] --cfl-lazy-mint with field buckets: the "
              "A-closure has no same-origin exact/X coupling, so VX "
              "bridges creatable only by unminted origins are missed; "
              "existing bridges are traversed\n");
    auto tLazy = std::chrono::steady_clock::now();
    std::vector<std::vector<uint32_t>> rin(N);
    for (auto [s, t] : aEdges) rin[t].push_back(s);
    for (auto &[b, r, bk] : fEdges) rin[r].push_back(b);
    for (auto [p, c] : dEdges) rin[c].push_back(p); // cell -> owner hop
    lazyA.assign(N, 0);
    std::vector<uint32_t> bfs;
    size_t fptrCls = 0;
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto dIt = toDense.find(getCanonicalNode(fn));
      if (dIt == toDense.end()) continue;
      if (!lazyA[dIt->second]) {
        lazyA[dIt->second] = 1;
        bfs.push_back(dIt->second);
        fptrCls++;
      }
    }
    while (!bfs.empty()) {
      uint32_t n = bfs.back();
      bfs.pop_back();
      for (uint32_t p : rin[n])
        if (!lazyA[p]) { lazyA[p] = 1; bfs.push_back(p); }
    }
    size_t inA = 0;
    for (uint32_t n = 0; n < N; n++) inA += lazyA[n];
    CG_LOG("LazyMint: initial A " << inA << "/" << N << " classes ("
           << fptrCls << " fptr classes), "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tLazy).count()
           << " ms\n");
  }
  // --cfl-nexus-fields (task #39, class B): surgical field sensitivity.
  // Only origins of nexus-typed objects mint at exact shift 0; every
  // other root mints directly on the wildcard plane — bit-identical to
  // FI for that origin (one (o,X) join cluster, no exact keys, no VX
  // bridges), so the residue-plane cost is confined to the nexus
  // population. Typing: globals/allocas by value type; heap sites by
  // USE — any GEP whose source element type is a nexus struct marks
  // its stripped base class, then a backward closure over a-edges
  // carries the mark to the allocation-site classes (crossing cells on
  // purpose: `tsk = load ...; gep tsk` chains reach the fork-side
  // stores and their alloc callsites). Over-marking costs planes,
  // never soundness; under-marking degrades to today's FI.
  std::vector<char> nexusCls;
  std::vector<char> rootNexus; // rid-indexed: 1 = exact mint
  // 'all' = every named struct type is nexus (origin-complete bound:
  // measures whether OBJECT origins alone reproduce full fs13 — fn
  // and identity roots still wildcard-mint).
  // '+ids' suffix: also exact-mint IDENTITY roots (formals, no-in
  // classes) whose class is nexus-marked — diagnostic for how much
  // fs13 discrimination lives on identity residues vs object origins.
  StringRef nexusSpec0(CFLNexusFields);
  const bool nexusIds = nexusSpec0.consume_back("+ids");
  const bool nexusAll = nexusSpec0 == "all";
  const bool nexusGate = NB > 0 && !CFLNexusFields.empty();
  if (nexusGate) {
    boost::unordered_flat_set<std::string> nexusNames;
    {
      StringRef spec = nexusSpec0;
      if (spec == "default")
        spec = "task_struct,file,cred,signal_struct,device,module";
      while (!spec.empty()) {
        auto [head, rest] = spec.split(',');
        if (!head.empty())
          nexusNames.insert(("struct." + head).str());
        spec = rest;
      }
    }
    // Containment closure via the StructAnalyzer: a struct that EMBEDS
    // a nexus type is itself nexus — its allocation sites GEP with the
    // CONTAINING type's name (bpf_link inside bpf_tracing_link), so
    // name matching without the closure misses embedded-type origins
    // entirely (the km widened-list null). StructInfo::containers
    // already records every embedder; worklist = transitive closure.
    if (!nexusAll) {
      const size_t listed = nexusNames.size();
      const llvm::Module *M0 = Ctx->Modules.begin()->first;
      std::vector<std::string> work(nexusNames.begin(), nexusNames.end());
      while (!work.empty()) {
        const std::string cur = std::move(work.back());
        work.pop_back();
        std::set<std::string> outc;
        Ctx->structAnalyzer.getContainer(cur, M0, outc);
        for (const std::string &c : outc) {
          std::string canon = sctCanonStructName(c).str();
          if (nexusNames.insert(canon).second)
            work.push_back(std::move(canon));
        }
      }
      CG_LOG("NexusFields: containment closure " << listed << " listed -> "
             << nexusNames.size() << " types\n");
    }
    auto nexusValueType = [&](llvm::Type *T) {
      while (auto *AT = dyn_cast<ArrayType>(T))
        T = AT->getElementType();
      auto *ST = dyn_cast<StructType>(T);
      if (!ST)
        return false;
      if (nexusAll)
        return true; // literal structs included: origin-complete bound
      return ST->hasName() &&
             nexusNames.count(sctCanonStructName(ST->getName()).str()) > 0;
    };
    nexusCls.assign(N, 0);
    size_t mGep = 0, mVal = 0, mClo = 0;
    for (auto &mp : Ctx->Modules)
      for (Function &F : *mp.first)
        for (Instruction &I : instructions(F)) {
          auto *GEP = dyn_cast<GetElementPtrInst>(&I);
          if (!GEP || !nexusValueType(GEP->getSourceElementType()))
            continue;
          const Value *base =
              GEP->getPointerOperand()->stripPointerCastsAndAliases();
          NodeIndex vn = getRepNodeForValue(base);
          if (vn == AndersNodeFactory::InvalidIndex)
            continue;
          auto dIt = toDense.find(getCanonicalNode(vn));
          if (dIt != toDense.end() && !nexusCls[dIt->second]) {
            nexusCls[dIt->second] = 1;
            mGep++;
          }
        }
    auto valTyped = [&](NodeIndex m) {
      const Value *v = NF.getValueForNode(m);
      if (const auto *GV = dyn_cast_or_null<GlobalVariable>(v))
        return nexusValueType(GV->getValueType());
      if (const auto *AI = dyn_cast_or_null<AllocaInst>(v))
        return nexusValueType(AI->getAllocatedType());
      return false;
    };
    for (uint32_t n2 = 0; n2 < N; n2++) {
      if (nexusCls[n2])
        continue;
      bool hit = valTyped(toOrig[n2]);
      if (!hit) {
        auto mit = canonicalClassMembers.find(toOrig[n2]);
        if (mit != canonicalClassMembers.end())
          for (NodeIndex m : mit->second)
            if ((hit = valTyped(m)))
              break;
      }
      if (hit) {
        nexusCls[n2] = 1;
        mVal++;
      }
    }
    // Backward waves over a-edges: each pass extends the mark one edge
    // upstream (more within a pass in favorable edge order — the cap
    // is a cost heuristic, extra marks are planes, not unsoundness).
    for (int depth = 0; depth < 8; depth++) {
      const size_t before = mClo;
      for (auto [ea, eb] : aEdges)
        if (nexusCls[eb] && !nexusCls[ea]) {
          nexusCls[ea] = 1;
          mClo++;
        }
      if (mClo == before)
        break;
    }
    size_t mTot = 0;
    for (uint32_t n2 = 0; n2 < N; n2++)
      mTot += nexusCls[n2];
    CG_LOG("NexusFields: " << nexusNames.size() << " nexus types; "
           << mGep << " gep-base + " << mVal << " value-typed + " << mClo
           << " backward-closure = " << mTot << "/" << N
           << " classes marked (NB=" << NB << ")\n");
  }
  std::unordered_map<uint32_t, const Function *> funcRootOf;
  std::vector<uint32_t> rootClassOf; // rid -> minted class
  std::vector<char> rootParkable;    // rid -> pure no-in identity
  std::vector<char> rootRodata;      // rid -> class holds a const global
  std::vector<std::pair<uint32_t, uint32_t>> seeds; // (class, root id)
  uint32_t nextRoot = 0;
  size_t bidiPrunable = 0;
  // usercopy-certificate classes must be minted unconditionally: letting
  // the bidi/lazy oracles skip them would pre-decide the very question
  // the certificate asks (does this origin reach an fptr operand?).
  boost::unordered_flat_set<uint32_t> certCls;
  if (CFLCertUserCopy)
    for (auto &p : g_userCertObjs) {
      auto dIt = toDense.find(getCanonicalNode(p.first));
      if (dIt != toDense.end()) certCls.insert(dIt->second);
    }
  for (uint32_t n = 0; n < N; n++) {
    if (!inSlice.empty() && !inSlice[n]) continue;
    auto fit = funcOfCanon.find(toOrig[n]);
    const bool isFunc = fit != funcOfCanon.end();
    const bool isCert = !certCls.empty() && certCls.count(n);
    if (!hasIn[n] || isFunc || hasOrigin[n] || isCert) {
      if (!bidiMarked.empty() && !isFunc && !isCert && !bidiMarked[n]) {
        // Outside the fptr cone: this origin's facts can key joins only
        // at cells inside its partition's d/f closure, which never
        // meets an fptr partition — it cannot influence any answer.
        // The oracle recomputes per outer iteration, so cone growth
        // from newly wired callee edges re-admits origins as needed.
        bidiPrunable++;
        continue;
      }
      if (!lazyA.empty() && !isFunc && !isCert && !lazyA[n]) {
        // Not backward-reachable from any answer on the initial
        // quotient: defer — the post-drain expansion re-checks on the
        // live quotient and mints the moment the class enters A.
        lazyDeferred.push_back(n);
        continue;
      }
      // --cfl-ablate-mints: MEASUREMENT-ONLY UNSOUND PROBE — skip
      // minting identity roots whose canonical value matches a named
      // global, or is an instruction inside a named function. Used to
      // causally separate hub-SEEDING witnesses from hub-RIDING ones
      // (task #25: .str.5 / guc_wq_item_append candidates).
      if (!CFLAblateMints.empty() && !isFunc) {
        const Value *cv = NF.getValueForNode(toOrig[n]);
        StringRef key;
        if (cv) {
          if (const auto *I2 = dyn_cast<Instruction>(cv))
            key = I2->getFunction()->getName();
          else if (cv->hasName())
            key = cv->getName();
        }
        bool hit = false;
        if (!key.empty()) {
          StringRef spec(CFLAblateMints);
          while (!spec.empty() && !hit) {
            auto [head, rest] = spec.split(',');
            hit = !head.empty() && key == head;
            spec = rest;
          }
        }
        if (hit) {
          static size_t g_mintAblated = 0;
          if (++g_mintAblated <= 5 || g_mintAblated % 1000 == 0)
            WARNING("[MEASUREMENT-ONLY UNSOUND] mint ablated for class of "
                    << (cv ? cv->getName() : StringRef("<inst>")) << " ("
                    << g_mintAblated << " total)\n");
          continue;
        }
      }
      uint32_t rid = nextRoot++;
      seeds.emplace_back(n, rid);
      rootClassOf.push_back(n); // rid-indexed
      if (isFunc) funcRootOf[rid] = fit->second;
      // Parkable: minted only because no in-edge exists YET. When
      // resolution wiring gives the class an in-edge, a from-scratch
      // rebuild would not mint it (its identity becomes derived from
      // its callers); incremental solving instead PARKS the root —
      // stops seeding its bit across newly wired edges — so obsolete
      // formal identities don't double the fact volume.
      rootParkable.push_back(!isFunc && !hasOrigin[n]);
      rootRodata.push_back(!isFunc && classIsRodata(toOrig[n]));
      // Exact residues ONLY for nexus-typed OBJECT origins. Function
      // roots mint on the wildcard plane too: answers union the X
      // plane, rotation is absorbing at X, and the (fn,X) join key is
      // FI-identical — while exact fn facts would blanket the graph
      // and spread across every plane at each f-edge rotation (fn
      // facts are the dominant mass). Identity-only roots (formals,
      // no-in classes) likewise stay wildcard: the object's origin
      // fact carries the field split.
      if (nexusGate)
        rootNexus.push_back(nexusCls[n] && (nexusIds || hasOrigin[n]));
    }
  }

  // ---- Provenance-protected cells (task #30, --cfl-ops-pairs) ----
  // Certified container origins get copy-out semantics: WRITER cells
  // (any in-edge) merge into the per-origin protected cell as today;
  // READER cells (no in-edge) BRIDGE to it — the solver's existing
  // non-transitive pairwise fact exchange — instead of unifying. One
  // polymorphic reader thus no longer collapses two containers' cells
  // into a single class (the t_ops wall). Readers arriving before any
  // writer wait and attach when the cell materializes; a bridged
  // reader that later gains an in-edge is DEMOTED — merged into every
  // cell it bridge-joined (soundness first, LEDGERed). Scoped to
  // NB==0 (canonical field-insensitive config).
  struct ProtState {
    uint32_t cell = UINT32_MAX;
    llvm::SmallVector<uint32_t, 2> waiting;
  };
  // --cfl-probe-blob-formation (task #31): formation-time causality
  // for giant classes. Names captured AT MERGE TIME while both sides
  // are still small are faithful; the finished blob's member name is
  // not (the fwnode misattribution). clsSize is always maintained
  // (one add per merge); events only under the flag.
  std::vector<uint32_t> clsSize;
  struct BlobEv {
    uint32_t keeper, szA, szB;
    std::string nA, nB;
    const char *ctx;
    std::string origin; // join events: whose key coalesced them
  };
  std::vector<BlobEv> blobEvents;
  const char *blobCtx = "?";
  uint32_t blobCtxOrigin = UINT32_MAX;
  clsSize.assign(N, 1);
  for (uint32_t n2 = 0; n2 < N; n2++) {
    auto cit2 = canonicalClassMembers.find(toOrig[n2]);
    if (cit2 != canonicalClassMembers.end() && cit2->second.size() > 1)
      clsSize[n2] = (uint32_t)cit2->second.size();
  }
  if (CFLProbeBlobFormation) {
    std::vector<std::pair<uint32_t, uint32_t>> top0;
    for (uint32_t n2 = 0; n2 < N; n2++) top0.emplace_back(clsSize[n2], n2);
    std::partial_sort(top0.begin(), top0.begin() + std::min<size_t>(10, top0.size()),
                      top0.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(10, top0.size()); i++) {
      errs() << "BlobForm: INITIAL class size=" << top0[i].first << " c"
             << top0[i].second << "\n";
      if (i < 5) {
        // sample members: WHAT does the pre-solve blob contain?
        auto mit3 = canonicalClassMembers.find(toOrig[top0[i].second]);
        if (mit3 != canonicalClassMembers.end()) {
          size_t shown3 = 0;
          std::map<std::string, size_t> fnHist;
          for (NodeIndex m3 : mit3->second) {
            const Value *V3 = NF.getValueForNode(m3);
            if (!V3)
              continue;
            if (const auto *I3 = dyn_cast<Instruction>(V3))
              fnHist[I3->getFunction()->getName().str()]++;
            else if (V3->hasName() && shown3++ < 8)
              errs() << "BlobForm:   member(global) " << V3->getName()
                     << "\n";
          }
          std::vector<std::pair<size_t, const std::string *>> fh;
          for (auto &kv : fnHist)
            fh.emplace_back(kv.second, &kv.first);
          std::sort(fh.begin(), fh.end(), std::greater<>());
          for (size_t j = 0; j < std::min<size_t>(10, fh.size()); j++)
            errs() << "BlobForm:   member-fns " << fh[j].first << "x "
                   << *fh[j].second << "\n";
        }
      }
    }
  }
  // Protection activates for certified ops containers (task #30) and/or
  // rodata origins (task #25 copy-not-unify — same machinery: writer
  // joins merge, reader joins bridge non-transitively, mixed demotes).
  const bool protOn = NB == 0 && ((CFLOpsPairs && !opsPairs.empty()) ||
                                  CFLRodataCopy || CFLJoinCone);
  boost::unordered_flat_set<uint32_t> protRid;
  boost::unordered_flat_set<uint32_t> protCls; // container value classes
  boost::unordered_flat_map<uint32_t, ProtState> prot; // rid -> state
  boost::unordered_flat_map<uint32_t, llvm::SmallVector<uint32_t, 2>>
      readerBridgedTo; // reader class -> rids it bridge-joined
  std::vector<uint32_t> protDemoteQ;
  // Self-limiting protection: a cell class anchoring > K protected keys
  // has already lost its discrimination (writer collapse) — bridging
  // readers to it only COPIES its mega-plane per reader (the kernel
  // iteration-1 OOM). Such classes are marked collapsed: existing
  // bridge partners are merged back in and future readers merge (plain
  // pooled semantics for that family).
  boost::unordered_flat_map<uint32_t, uint32_t> protAnchor; // cell -> #keys
  boost::unordered_flat_set<uint32_t> protCollapsed;
  std::vector<uint32_t> protCollapseQ;
  static constexpr uint32_t PROT_ANCHOR_K = 4;
  // Coalescence census: when a writer class that already anchors one
  // protected key joins ANOTHER key, the two families fuse — blame the
  // writer (exemplar member instruction) so the hub's composition is
  // measurable: few nameable helpers -> summary severing wins; diffuse
  // -> field-keyed cells / provenance rework territory.
  std::map<std::string, std::pair<size_t, uint32_t>> protCoalesceBlame;
  // Writer-merge composition: name EVERY writer class at the moment it
  // merges into a protected cell — before the blob swallows it and the
  // exemplar drifts. This is the true composition census of the
  // "connected registration-writer universe".
  std::map<std::string, size_t> protWriterBlame;

  auto protBlameName = [&](uint32_t cls) -> std::string {
    if (cls >= toOrig.size())
      return "<synthetic>";
    NodeIndex canon = toOrig[cls];
    const Value *V2 = NF.getValueForNode(canon);
    auto nameOf = [](const Value *V3) -> std::string {
      if (!V3)
        return std::string();
      if (const auto *I2 = dyn_cast<Instruction>(V3))
        return (I2->getFunction()->getName() + "::" + I2->getOpcodeName())
            .str();
      if (V3->hasName())
        return V3->getName().str();
      return std::string();
    };
    std::string n = nameOf(V2);
    if (!n.empty())
      return n;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m2 : mit->second) {
        n = nameOf(NF.getValueForNode(m2));
        if (!n.empty())
          return n;
      }
    return "<unnamed>";
  };
  std::vector<char> protIn; // hasIn, class-folded (private copy)
  size_t protWriterMerges = 0, protReaderBridges = 0, protDemotions = 0,
         protWaitAttached = 0, protCollapses = 0, protPooledReaders = 0;
  std::vector<char> coneIn; // task #38 rung 2: answer-cone cell classes
  if (protOn) {
    protIn.assign(hasIn.begin(), hasIn.end());
    if (CFLJoinCone) {
      coneIn.assign(N, 0);
      size_t marked = 0, unmapped = 0;
      for (NodeIndex cn : g_presolveConeCanon) {
        auto dIt = toDense.find(getCanonicalNode(cn));
        if (dIt == toDense.end()) {
          unmapped++;
          continue;
        }
        if (!coneIn[dIt->second]) {
          coneIn[dIt->second] = 1; // pre-merge: dense ids are canonical
          marked++;
        }
      }
      CG_LOG("JoinCone: " << marked << " cone cell classes marked ("
             << unmapped << " unmapped)\n");
    }
    // EVERY certified container value class is protection-eligible:
    // globals, helper-returned alloc callsites, locals. Readers that
    // co-witness an UNPROTECTED origin merge through that key and
    // drag the protected cells down with them (t_ops2: the mk_widget
    // heap origin re-unified a1/b1's readers, then demotions collapsed
    // both cells) — so the container set must be protected wholesale,
    // INCLUDING the origins that feed a container value: the actual
    // origin root of a RETALLOC container is minted on the alloc
    // callsite class inside the helper, connected to the container by
    // the static ret-chain a-edges. Close backward over a-edges
    // (depth- and size-capped; partial closure is merely weaker
    // protection, never unsound).
    {
      SmallVector<uint32_t, 32> frontier;
      for (auto &kv : opsPairs)
        for (const Value *C2 : kv.second.containers) {
          NodeIndex vn = getRepNodeForValue(C2);
          if (vn == AndersNodeFactory::InvalidIndex)
            continue;
          auto dit = toDense.find(getCanonicalNode(vn));
          if (dit != toDense.end() && protCls.insert(dit->second).second)
            frontier.push_back(dit->second);
        }
      for (int depth = 0; depth < 8 && !frontier.empty(); depth++) {
        boost::unordered_flat_set<uint32_t> tgt(frontier.begin(),
                                                frontier.end());
        frontier.clear();
        for (auto [ea, eb] : aEdges)
          if (tgt.count(eb) && protCls.insert(ea).second)
            frontier.push_back(ea);
        if (protCls.size() > 8192) {
          CG_LOG("ProtCells: backward closure capped at " << protCls.size()
                 << " classes (depth " << depth << ")\n");
          break;
        }
      }
    }
    for (auto &sd : seeds)
      if (protCls.count(sd.first))
        protRid.insert(sd.second);
  }
  // Coupler census state: per-class subsystem masks over OWNED data
  // origins; weld events recorded in merge().
  std::vector<uint64_t> ownedMask;
  boost::unordered_flat_map<std::string, std::pair<uint64_t, uint64_t>>
      weldBlame; // name -> (count, united-bits)
  size_t weldEvents = 0, mergeEvents = 0;
  if (CFLCensusCouplers) {
    ownedMask.assign(N, 0);
    for (uint32_t rid = 0; rid < nextRoot; rid++) {
      if (funcRootOf.count(rid))
        continue; // fn identities excluded: data-object plane only
      const Value *ov = NF.getValueForNode(toOrig[rootClassOf[rid]]);
      const llvm::Module *om = nullptr;
      if (ov) {
        if (const auto *oi = dyn_cast<Instruction>(ov))
          om = oi->getModule();
        else if (const auto *og = dyn_cast<GlobalValue>(ov))
          om = og->getParent();
      }
      ownedMask[rootClassOf[rid]] |= 1ull << subsysBitOf(om); // pre-merge: canonical
    }
    CG_LOG("Couplers: " << g_subsysNames.size()
           << " subsystems over data origins\n");
  }
  if (CFLJoinCone && NB == 0) {
    // rung 2 (task #38): every origin is protection-eligible; the
    // reader path below then bridges ONLY answer-cone cells — the
    // non-transitive copy-out is bought exactly where answers live.
    for (uint32_t rid = 0; rid < nextRoot; rid++)
      protRid.insert(rid);
    CG_LOG("JoinCone: all " << nextRoot << " origins protection-eligible\n");
  }
  if (CFLRodataCopy && NB == 0) {
    // task #25: every rodata origin is protection-eligible — const
    // memory has exactly one writer (its initializer), so writer joins
    // establish the cell and every reader bridges copy-out. rootRodata
    // excludes function origins by construction.
    size_t nRP = 0;
    for (uint32_t rid = 0; rid < nextRoot; rid++)
      if (rootRodata[rid] && protRid.insert(rid).second)
        nRP++;
    CG_LOG("RodataCopy: " << nRP
           << " rodata origins protected (copy-not-unify)\n");
  }

  // Root-class tracking so incremental wiring can mint identity roots
  // for classes that BECOME origins mid-fixpoint (new allocation sites)
  // without duplicating existing ones.
  std::vector<char> isRoot(N, 0);
  for (auto &sd : seeds) isRoot[sd.first] = 1;

  // Solver core: union-find clusters + bit-plane difference propagation.
  // Exact-fact joins are transitive (same (o, s) => same abstract cell),
  // so cluster members MERGE into one class — no hub nodes, no duplicated
  // fact sets, no k-fold re-propagation. The (o, X) cluster is unioned
  // with every exact-shift cluster of the same origin when both exist
  // (VX; identical fixpoint to the former bidirectional hub links, which
  // equalized member fact sets anyway). Propagation is word-parallel:
  // OR whole planes across a-edges, plane-rotated OR across f-edges.
  FactSet::Universe = nextRoot;
  if (!bidiMarked.empty())
    CG_LOG("BidiPrune: pruned " << bidiPrunable << " origins outside the "
           << "fptr cone; minted " << nextRoot << " roots ("
           << (100.0 * bidiPrunable / std::max<size_t>(1, bidiPrunable + nextRoot))
           << "% pruned)\n");
  CG_LOG("FlowsTo: minted " << nextRoot << " roots ("
         << funcRootOf.size() << " function), " << wildcardNodes.size()
         << " wildcard nodes, " << NSHIFT << " shift planes\n");
  if (!lazyA.empty())
    CG_LOG("LazyMint: deferred " << lazyDeferred.size()
           << " candidate roots outside initial A ("
           << (100.0 * lazyDeferred.size() /
               std::max<size_t>(1, lazyDeferred.size() + nextRoot))
           << "% of candidates)\n");
  for (auto &[why, cnt] : wildcardReasons)
    CG_LOG("FlowsTo wildcard[" << why << "]: " << cnt << "\n");
  // --cfl-trace-func: follow one function root's fact through the solve.
  int64_t traceRoot = -1;
  if (!CFLTraceFunc.empty()) {
    for (auto &[rid, F] : funcRootOf)
      if (F->getName().contains(CFLTraceFunc)) {
        traceRoot = rid;
        errs() << "TRACE root " << rid << " = " << F->getName() << "\n";
        break;
      }
    if (traceRoot < 0)
      errs() << "TRACE: no function root matches '" << CFLTraceFunc << "'\n";
  }
  size_t traceEvents = 0;
  const char *tHow = "seed";
  uint32_t tFrom = UINT32_MAX;
  auto traceHit = [&](uint32_t n, uint32_t s, bool bridged) {
    if (traceEvents++ > 200000) return;
    errs() << "TRACE + c" << n << " s" << s << (bridged ? " [br]" : "")
           << " via " << tHow << " from c";
    if (tFrom == UINT32_MAX) errs() << "?"; else errs() << tFrom;
    errs() << "\n";
  };
  // Threading: parallel phases freeze the union-find (no merges, no path
  // compression — find is a pure read walk) and guard every write to
  // another class's planes with that class's spinlock. Merges, cluster
  // registry inserts and SCC collapses run only between phases, on the
  // main thread; WavePool::run barriers give the happens-before edges.
  unsigned solverThreads = CFLSolverThreads == 0
                               ? std::max(1u, std::thread::hardware_concurrency())
                               : (unsigned)CFLSolverThreads;
  if (traceRoot >= 0 && solverThreads > 1) {
    CG_LOG("FlowsTo: --cfl-trace-func is single-threaded; forcing "
           "--cfl-solver-threads=1\n");
    solverThreads = 1;
  }
  if (CFLBatchWorkers > 1 && solverThreads > 1) {
    // fork() does not carry the wave pool's threads into workers, and
    // the parent only replays events — all parallelism is processes.
    CG_LOG("FlowsTo: --cfl-batch-workers active; drains run "
           "single-threaded per worker\n");
    solverThreads = 1;
  }
  bool parallelPhase = false; // true only inside a parallel wave phase
  std::unique_ptr<std::atomic<uint8_t>[]> classLk(
      new std::atomic<uint8_t>[solverCapN]);
  for (uint32_t i = 0; i < solverCapN; i++)
    classLk[i].store(0, std::memory_order_relaxed);
  auto lockC = [&](uint32_t n) {
    if (!parallelPhase) return;
    while (classLk[n].exchange(1, std::memory_order_acquire))
      while (classLk[n].load(std::memory_order_relaxed))
        __builtin_ia32_pause();
  };
  auto unlockC = [&](uint32_t n) {
    if (!parallelPhase) return;
    classLk[n].store(0, std::memory_order_release);
  };
  std::vector<uint32_t> ufp(N), ufrank(N, 0);
  for (uint32_t i = 0; i < N; i++) ufp[i] = i;
  auto find = [&](uint32_t x) {
    if (parallelPhase) { // frozen: read-only walk, no compression writes
      while (ufp[x] != x) x = ufp[x];
      return x;
    }
    while (ufp[x] != x) { ufp[x] = ufp[ufp[x]]; x = ufp[x]; }
    return x;
  };
  // Per-class planes: R = native facts; RB = bridged facts (arrived over
  // a VX bridge; disjoint from R). Bridged facts behave identically in
  // joins, a/f propagation (emitting native downstream — a load out of
  // the cell is genuine value flow), and wildcard projection; the single
  // restriction is that they may not cross another bridge. This encodes
  // the grammar's pairwise VX exactly: M-hops never chain without value
  // flow in between, so one provenance bit suffices (bridges are
  // bipartite between the (o,X) cluster and exact clusters).
  // Deltas: dirty = a/f-propagation backlog (both kinds), jdirty = join
  // backlog (both kinds, refiltered by `joined`), dirtyBr = bridge-
  // crossing backlog (native only).
  std::vector<std::vector<FactSet>> R(N), RB(N), dirty(N),
      jdirty(N), dirtyBr(N), joined(N);
  for (uint32_t i = 0; i < N; i++) {
    R[i].resize(NSHIFT);
    RB[i].resize(NSHIFT);
    dirty[i].resize(NSHIFT);
    jdirty[i].resize(NSHIFT);
    dirtyBr[i].resize(NSHIFT);
    joined[i].resize(NSHIFT); // facts already pushed to ALL cells of class
  }
  std::vector<std::vector<uint32_t>> bridgesOf(N); // VX partners (class ids)
  std::vector<char> wflag(N, 0);
  for (uint32_t w : wildcardNodes) wflag[w] = 1;
  // Wave scheduling: pop classes in topological order of the initial
  // propagation graph's condensation, so deltas flow downhill and each
  // plane is touched once per wave with its full accumulated delta,
  // instead of once per scattered arrival (a-prop is cold-miss latency
  // bound; access ORDER is the cheapest locality lever). Ranks are a
  // static heuristic — any pop order converges to the same fixpoint.
  std::vector<uint32_t> topoRank(N, 0);
  {
    std::vector<uint32_t> low(N), dfn(N, 0), tstk;
    std::vector<std::pair<uint32_t, size_t>> cstk;
    std::vector<bool> onS(N, false);
    uint32_t timer = 1, nComp = 0;
    auto succAt = [&](uint32_t u, size_t i) -> uint32_t {
      if (i < outA[u].size()) return outA[u][i];
      return outF[u][i - outA[u].size()].first;
    };
    for (uint32_t st = 0; st < N; st++) {
      if (dfn[st]) continue;
      cstk.emplace_back(st, 0);
      dfn[st] = low[st] = timer++;
      tstk.push_back(st);
      onS[st] = true;
      while (!cstk.empty()) {
        auto &[u, ei] = cstk.back();
        if (ei < outA[u].size() + outF[u].size()) {
          uint32_t v = succAt(u, ei++);
          if (!dfn[v]) {
            dfn[v] = low[v] = timer++;
            tstk.push_back(v);
            onS[v] = true;
            cstk.emplace_back(v, 0);
          } else if (onS[v]) {
            low[u] = std::min(low[u], dfn[v]);
          }
        } else {
          if (low[u] == dfn[u]) {
            while (true) {
              uint32_t w = tstk.back();
              tstk.pop_back();
              onS[w] = false;
              topoRank[w] = nComp;
              if (w == u) break;
            }
            nComp++;
          }
          uint32_t uu = u;
          cstk.pop_back();
          if (!cstk.empty())
            low[cstk.back().first] =
                std::min(low[cstk.back().first], low[uu]);
        }
      }
    }
    // Tarjan emits SCCs in reverse topological order: invert so sources
    // carry the smallest ranks.
    for (uint32_t i = 0; i < N; i++) topoRank[i] = nComp - 1 - topoRank[i];
  }
  std::vector<uint32_t> worklist;
  std::unique_ptr<std::atomic<uint8_t>[]> inWL(new std::atomic<uint8_t>[solverCapN]);
  for (uint32_t i = 0; i < solverCapN; i++)
    inWL[i].store(0, std::memory_order_relaxed);
  uint64_t factCount = 0;
  uint64_t iterations = 0;
  // Per-thread solver context: scratch planes for the hot add paths
  // (copyFrom reuses buffers — no per-call heap churn; safe because
  // addBits and addBitsBridged never call themselves or each other),
  // local worklist/fact deltas flushed at phase barriers, deferred join
  // requests, and profile counters. Sequential code paths (seeding,
  // merges, join apply, SCC collapse) always use ctxs[0].
  struct SolverCtx {
    FactSet nbA, promA, nbB;                 // add-path scratch
    FactSet d, todoS, dbS, dNatS, dBrS;      // pop-loop scratch
    std::vector<uint32_t> sweepElems;
    std::vector<uint32_t> localWork;
    uint64_t localFacts = 0, pops = 0;
    uint64_t cyJoin = 0, cyBridge = 0, cyScan = 0, cyW = 0, cyA = 0,
             cyF = 0;
    uint64_t nJoinLk = 0, nAOr = 0, nFOr = 0, orWords = 0;
    uint64_t sweepOffered = 0, sweepKept = 0;
  };
  // deque, not vector: forked batch workers grow it for their own
  // thread pool, and ctx0 below must stay a valid reference.
  std::deque<SolverCtx> ctxs(solverThreads);
  SolverCtx &ctx0 = ctxs[0];
  auto push = [&](uint32_t n, SolverCtx &ctx) {
    if (!inWL[n].exchange(1, std::memory_order_relaxed))
      ctx.localWork.push_back(n);
  };
  auto flushCtx = [&](SolverCtx &ctx) {
    factCount += ctx.localFacts;
    ctx.localFacts = 0;
    iterations += ctx.pops;
    ctx.pops = 0;
    worklist.insert(worklist.end(), ctx.localWork.begin(),
                    ctx.localWork.end());
    ctx.localWork.clear();
  };
  // OR src natively into rep n's plane s. Bits new to the class enter all
  // three deltas; bits previously only bridged are promoted (their joins
  // and a/f propagation already ran — only bridge-crossing is new).
  // In parallel phases the whole plane update runs under n's spinlock.
  auto addBits = [&](uint32_t n, uint32_t s, const FactSet &src,
                     SolverCtx &ctx) {
    if (src.none()) return;
    FactSet &nb = ctx.nbA;
    lockC(n);
    nb.copyFrom(src);
    nb.subtract(R[n][s]);
    if (nb.none()) { unlockC(n); return; }
    FactSet &promoted = ctx.promA;
    promoted.clear();
    if (!RB[n][s].none()) {
      promoted.copyFrom(nb);
      promoted.intersectWith(RB[n][s]);
      RB[n][s].subtract(nb);
      nb.subtract(promoted); // truly-new bits only
    }
    R[n][s].unionWith(nb);
    if (!promoted.none()) {
      R[n][s].unionWith(promoted);
      dirtyBr[n][s].unionWith(promoted);
    }
    if (!nb.none()) {
      dirty[n][s].unionWith(nb);
      jdirty[n][s].unionWith(nb);
      dirtyBr[n][s].unionWith(nb);
      ctx.localFacts += nb.count();
      if (traceRoot >= 0 && nb.test((uint32_t)traceRoot))
        traceHit(n, s, false);
    }
    unlockC(n);
    push(n, ctx);
  };
  auto addFact = [&](uint32_t n, uint32_t s, uint32_t o, SolverCtx &ctx) {
    lockC(n);
    if (R[n][s].test(o)) { unlockC(n); return; }
    if (RB[n][s].test(o)) {
      RB[n][s].reset(o);
      R[n][s].set(o);
      dirtyBr[n][s].set(o);
      unlockC(n);
      push(n, ctx);
      return;
    }
    R[n][s].set(o);
    dirty[n][s].set(o);
    jdirty[n][s].set(o);
    dirtyBr[n][s].set(o);
    ctx.localFacts++;
    if (traceRoot >= 0 && o == (uint32_t)traceRoot) traceHit(n, s, false);
    unlockC(n);
    push(n, ctx);
  };
  // OR src as bridged: skipped where already known either way; bridged
  // bits run joins and a/f propagation but never dirtyBr.
  auto addBitsBridged = [&](uint32_t n, uint32_t s, const FactSet &src,
                            SolverCtx &ctx) {
    if (src.none()) return;
    FactSet &nb = ctx.nbB;
    lockC(n);
    nb.copyFrom(src);
    nb.subtract(RB[n][s]);
    nb.subtract(R[n][s]);
    if (nb.none()) { unlockC(n); return; }
    RB[n][s].unionWith(nb);
    dirty[n][s].unionWith(nb);
    jdirty[n][s].unionWith(nb);
    ctx.localFacts += nb.count();
    if (traceRoot >= 0 && nb.test((uint32_t)traceRoot))
      traceHit(n, s, true);
    unlockC(n);
    push(n, ctx);
  };
  size_t mergeCount = 0;
  std::vector<uint32_t> mergeHits(N, 0); // absorbed-class lineage per keeper
  // Cluster-transitivity audit: grammar M is per-witness, but union-find
  // closes clusters transitively (coarser-or-equal). keyCount tracks how
  // many cluster keys a class anchors; a join that merges a cell already
  // anchoring other keys coalesces key-clusters the grammar keeps apart.
  std::unique_ptr<std::atomic<uint32_t>[]> keyCount(
      new std::atomic<uint32_t>[solverCapN]);
  for (uint32_t i = 0; i < solverCapN; i++)
    keyCount[i].store(0, std::memory_order_relaxed);
  size_t transKeyMerges = 0;
  // Churn attribution: what triggers merges, how much join work is
  // merge-triggered re-offer, and which classes get re-popped — the data
  // that sizes the delta-precision fix and names summarization targets.
  size_t mergesFromJoin = 0, mergesFromSCC = 0, redundantJoins = 0;
  // --cfl-root-relevance: (root, keeper class) per join-triggered merge —
  // joins are the only consumer of individual root bits besides the final
  // icall answer read, so these witnesses + function roots form a
  // sufficient root set for reproducing this run's answers.
  std::vector<std::pair<uint32_t, uint32_t>> mergeWitness;
  uint64_t reofferedFacts = 0, sweepOffered = 0, sweepKept = 0;
  std::vector<uint32_t> popCount(N, 0);
  FactSet mnbS, mprS; // merge scratch (merge never nests inside itself)
  uint64_t cyMerge = 0;
  auto merge = [&](uint32_t a, uint32_t b) -> uint32_t {
    a = find(a); b = find(b);
    if (a == b) return a;
    struct MergeTimer {
      uint64_t &acc, t0;
      MergeTimer(uint64_t &a_) : acc(a_), t0(__builtin_ia32_rdtsc()) {}
      ~MergeTimer() { acc += __builtin_ia32_rdtsc() - t0; }
    } mt(cyMerge);
    // Keeper = union-by-rank. Deliberate keeper policies were tried
    // and measured NO BETTER on the kernel subset (2026-07-19):
    // by-fact-mass +22% (light-fact hubs became losers and the merged
    // planes were pushed along their huge edge lists), by-edge-list
    // +6%; rank implicitly keeps the veteran hub classes anyway. The
    // Lemma-3.4/small-to-large discipline from optimal bidirected Dyck
    // does not transfer: their merges carry no payload, ours push
    // planes along loser lists and re-sweep merged cell lists.
    if (ufrank[a] < ufrank[b]) std::swap(a, b);
    if (ufrank[a] == ufrank[b]) ufrank[a]++;
    ufp[b] = a;
    if (g_batchRecord)
      g_batchEvts.push_back({1, a, b, 0});
    mergeCount++;
    mergeHits[a] += 1 + mergeHits[b];
    keyCount[a].fetch_add(keyCount[b].load(std::memory_order_relaxed),
                          std::memory_order_relaxed);
    keyCount[b].store(0, std::memory_order_relaxed);
    isRoot[a] |= isRoot[b];
    tHow = "merge"; tFrom = b;
    for (uint32_t s = 0; s < NSHIFT; s++) {
      // Propagation delta: only facts genuinely new to the keeper. The
      // keeper's old facts reach the loser's former neighbors via the
      // one-time direct push below, NOT via a full re-dirty (that made
      // every merge re-offer the whole fact set on the whole edge list).
      if (R[b][s].any()) {
        FactSet &nb = mnbS;
        nb.copyFrom(R[b][s]);
        nb.subtract(R[a][s]);
        if (nb.any()) {
          // Split: bits only bridged at the keeper are promotions
          // (bridge-crossing newly allowed); the rest are fully new.
          FactSet &promoted = mprS;
          promoted.copyFrom(nb);
          promoted.intersectWith(RB[a][s]);
          RB[a][s].subtract(nb);
          nb.subtract(promoted);
          R[a][s].unionWith(nb);
          R[a][s].unionWith(promoted);
          dirty[a][s].unionWith(nb);
          dirtyBr[a][s].unionWith(nb);
          dirtyBr[a][s].unionWith(promoted);
        }
      }
      if (RB[b][s].any()) {
        FactSet &nb = mnbS;
        nb.copyFrom(RB[b][s]);
        nb.subtract(R[a][s]);
        nb.subtract(RB[a][s]);
        if (nb.any()) {
          RB[a][s].unionWith(nb);
          dirty[a][s].unionWith(nb);
        }
      }
      if (dirty[b][s].any()) dirty[a][s].unionWith(dirty[b][s]);
      if (dirtyBr[b][s].any()) dirtyBr[a][s].unionWith(dirtyBr[b][s]);
      R[b][s].release();
      RB[b][s].release();
      dirty[b][s].release();
      dirtyBr[b][s].release();
      // Join backlog: the merged cell list must be swept with every
      // fact not yet known-joined to all of it. Combine the joined
      // marks per the cell geometry above, then re-offer only the
      // difference — not the full fact set.
      joined[a][s].intersectWith(joined[b][s]);
      joined[b][s].release();
      // Re-offer the full fact set; the sweep filters through the
      // (now better-preserved) joined marks. Computing the precise
      // difference HERE was measured NEGATIVE on the kernel subset:
      // it streams the heavy merged plane 3-4 extra times per merge
      // while the multi-cluster cell lists keep the union case rare.
      jdirty[a][s].unionWith(R[a][s]);
      jdirty[a][s].unionWith(RB[a][s]);
      if (CFLSolverProfile)
        reofferedFacts += R[a][s].count() + RB[a][s].count();
      jdirty[b][s].release();
    }
    // One-time pushes along the loser's moved lists (keeper's old lists
    // only ever need deltas): merged facts along a/f edges (emission is
    // native — value flow launders provenance), natives across bridges.
    tHow = "merge-move-a"; tFrom = a;
    for (uint32_t t : outA[b]) {
      uint32_t tt = find(t);
      if (tt == a) continue;
      for (uint32_t s = 0; s < NSHIFT; s++) {
        if (R[a][s].any()) addBits(tt, s, R[a][s], ctx0);
        if (RB[a][s].any()) addBits(tt, s, RB[a][s], ctx0);
      }
    }
    tHow = "merge-move-f"; tFrom = a;
    for (auto [t, r] : outF[b]) {
      uint32_t tt = find(t);
      for (uint32_t s = 0; s < NSHIFT; s++) {
        uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + r) % NB;
        if (tt == a && s2 == s) continue;
        if (R[a][s].any()) addBits(tt, s2, R[a][s], ctx0);
        if (RB[a][s].any()) addBits(tt, s2, RB[a][s], ctx0);
      }
    }
    tHow = "merge-move-br"; tFrom = a;
    for (uint32_t br : bridgesOf[b]) {
      uint32_t bb = find(br);
      if (bb == a) continue;
      for (uint32_t s = 0; s < NSHIFT; s++)
        if (R[a][s].any()) addBitsBridged(bb, s, R[a][s], ctx0);
    }
    auto append = [](auto &dst, auto &src) {
      dst.insert(dst.end(), src.begin(), src.end());
      src.clear();
      src.shrink_to_fit();
    };
    append(outA[a], outA[b]);
    append(outF[a], outF[b]);
    append(cellsOf[a], cellsOf[b]);
    append(bridgesOf[a], bridgesOf[b]);
    // Wildcard status arriving with the loser retroactively projects the
    // keeper's existing facts onto the unknown-shift plane, per kind.
    if (NB > 0 && wflag[b] && !wflag[a])
      for (uint32_t s = 0; s < NB; s++) {
        if (R[a][s].any()) addBits(a, SHIFT_X, R[a][s], ctx0);
        if (RB[a][s].any()) addBitsBridged(a, SHIFT_X, RB[a][s], ctx0);
      }
    wflag[a] |= wflag[b];
    if (!nexusCls.empty())
      nexusCls[a] |= nexusCls[b]; // nexus typing survives unions
    if (!coneIn.empty())
      coneIn[a] |= coneIn[b]; // cone membership survives unions
    if (!ownedMask.empty()) {
      mergeEvents++;
      const uint64_t na2 = ownedMask[a] & ~ownedMask[b];
      const uint64_t nb2 = ownedMask[b] & ~ownedMask[a];
      if (na2 && nb2) {
        // true cross-subsystem weld: blame the shared join origin (the
        // object whose cell keyed this union) when available
        weldEvents++;
        std::string who = "ctx:" + std::string(blobCtx);
        if (blobCtxOrigin != UINT32_MAX &&
            blobCtxOrigin < rootClassOf.size()) {
          const Value *wv =
              NF.getValueForNode(toOrig[rootClassOf[blobCtxOrigin]]);
          if (wv && wv->hasName())
            who = wv->getName().str();
          else if (wv) {
            if (const auto *wi = dyn_cast<Instruction>(wv))
              who = (wi->getFunction()->getName() + "::" +
                     wi->getOpcodeName()).str();
          } else {
            who = "<synthetic>/" + std::string(blobCtx);
          }
        }
        auto &bl2 = weldBlame[who];
        bl2.first++;
        bl2.second |= ownedMask[a] | ownedMask[b];
        g_weldRepOf[who] = a; // post-merge rep (re-find at report)
      }
      ownedMask[a] |= ownedMask[b];
    }
    if (CFLProbeBlobFormation && blobEvents.size() < 60000) {
      const uint32_t sa = clsSize[a], sb = clsSize[b];
      // log when both sides are substantial, or a milestone is crossed
      if (std::min(sa, sb) >= 64 ||
          (sa + sb >= 4096 && sa < 4096) || (sa + sb >= 65536 && sa < 65536))
        blobEvents.push_back(
            {a, sa, sb, protBlameName(a), protBlameName(b), blobCtx,
             blobCtxOrigin == UINT32_MAX
                 ? std::string()
                 : protBlameName(find(rootClassOf[blobCtxOrigin]))});
    }
    clsSize[a] += clsSize[b];
    if (protOn) {
      if (protIn[b])
        protIn[a] = 1;
      auto rb = readerBridgedTo.find(b);
      if (rb != readerBridgedTo.end()) {
        auto &va = readerBridgedTo[a];
        va.append(rb->second.begin(), rb->second.end());
        readerBridgedTo.erase(rb);
      }
      if (protIn[a] && readerBridgedTo.count(a))
        protDemoteQ.push_back(a); // reader gained stores: demote later
      auto pa = protAnchor.find(b);
      if (pa != protAnchor.end()) {
        uint32_t n2 = (protAnchor[a] += pa->second);
        protAnchor.erase(b);
        if (n2 > PROT_ANCHOR_K && !protCollapsed.count(a))
          protCollapseQ.push_back(a); // no merge here: queue (reentrancy)
      }
      if (protCollapsed.count(b)) {
        protCollapsed.erase(b);
        protCollapsed.insert(a);
      }
    }
    push(a, ctx0);
    return a;
  };
  // Merged classes accumulate stale/duplicate edge and cell entries;
  // compact when a list has grown well past its last compacted size.
  std::vector<uint32_t> compactMark(N, 64);
  auto compactLists = [&](uint32_t n) {
    for (auto &t : outA[n]) t = find(t);
    std::sort(outA[n].begin(), outA[n].end());
    outA[n].erase(std::unique(outA[n].begin(), outA[n].end()), outA[n].end());
    outA[n].erase(std::remove(outA[n].begin(), outA[n].end(), n),
                  outA[n].end());
    for (auto &[t, r] : outF[n]) t = find(t);
    std::sort(outF[n].begin(), outF[n].end());
    outF[n].erase(std::unique(outF[n].begin(), outF[n].end()), outF[n].end());
    for (auto &c : cellsOf[n]) c = find(c);
    std::sort(cellsOf[n].begin(), cellsOf[n].end());
    cellsOf[n].erase(std::unique(cellsOf[n].begin(), cellsOf[n].end()),
                     cellsOf[n].end());
    for (auto &br : bridgesOf[n]) br = find(br);
    std::sort(bridgesOf[n].begin(), bridgesOf[n].end());
    bridgesOf[n].erase(
        std::unique(bridgesOf[n].begin(), bridgesOf[n].end()),
        bridgesOf[n].end());
    bridgesOf[n].erase(
        std::remove(bridgesOf[n].begin(), bridgesOf[n].end(), n),
        bridgesOf[n].end());
    compactMark[n] = (uint32_t)std::max<size_t>(
        64, 2 * (outA[n].size() + outF[n].size() + cellsOf[n].size() +
                 bridgesOf[n].size()));
  };
  // Cluster registry: fact (o, s) -> current representative class of the
  // merged cell cluster. Entries may go stale under merges; resolve with
  // find() on read. ONE flat map, deliberately: joins are sequential in
  // every shipped configuration, and the sharded variant (256 maps with
  // per-shard spinlocks, built for the deferred-join experiments) was
  // measured to TRIPLE the redundant-confirm probe cost at whole-kernel
  // scale — 272M probes walk shard headers scattered across 16KB
  // instead of one map header hot in L1 (join phase 358B -> 1072B
  // cycles, the 291->497 s/iter kernel regression).
  boost::unordered_flat_map<uint64_t, uint32_t> clusterRep;
  auto clusterFind = [&](uint64_t key) -> uint32_t { // UINT32_MAX = absent
    auto it = clusterRep.find(key);
    return it == clusterRep.end() ? UINT32_MAX : it->second;
  };
  auto clusterCount = [&]() { return clusterRep.size(); };
  std::unordered_map<uint32_t, std::vector<uint64_t>> shiftKeysOf;
  size_t bridgeCount = 0;
  // VX bridge: pairwise fact exchange between two cluster classes, native
  // facts crossing as bridged. NOT a merge — the grammar's VX is not
  // transitive across the X cluster.
  auto addBridge = [&](uint32_t x, uint32_t y) {
    x = find(x); y = find(y);
    if (x == y) return; // already one class; exchange is implicit
    bridgesOf[x].push_back(y);
    bridgesOf[y].push_back(x);
    bridgeCount++;
    tHow = "bridge-init"; tFrom = x;
    for (uint32_t s = 0; s < NSHIFT; s++) {
      if (R[x][s].any()) addBitsBridged(y, s, R[x][s], ctx0);
      if (R[y][s].any()) addBitsBridged(x, s, R[y][s], ctx0);
    }
  };
  // --cfl-probe-sink-ablate (MEASUREMENT-ONLY, UNSOUND): pretend cells
  // whose class contains an instruction from a matching function (or a
  // matching global) are write-only sinks — skip ALL their cluster
  // joins. Quantifies a channel's contribution to fusion/fact-mass/
  // answers and previews a reviewed sink model. Memoized per rep at
  // query time; merges can stale the memo — acceptable for a probe.
  SmallVector<StringRef, 8> sinkAblatePats;
  {
    StringRef spec(CFLProbeSinkAblate);
    while (!spec.empty()) {
      auto [head, rest] = spec.split(',');
      if (!head.empty())
        sinkAblatePats.push_back(head);
      spec = rest;
    }
    if (!sinkAblatePats.empty())
      WARNING("[MEASUREMENT-ONLY UNSOUND] sink-ablate active: "
              << CFLProbeSinkAblate << "\n");
  }
  auto classMatchesPats = [&](uint32_t cls, ArrayRef<StringRef> pats,
                              boost::unordered_flat_map<uint32_t, char>
                                  &memo) -> bool {
    auto it2 = memo.find(cls);
    if (it2 != memo.end())
      return it2->second;
    bool hit = false;
    auto nameHit = [&](const Value *V3) {
      if (!V3)
        return;
      StringRef nm;
      if (const auto *I3 = dyn_cast<Instruction>(V3))
        nm = I3->getFunction()->getName();
      else if (V3->hasName())
        nm = V3->getName();
      for (StringRef p : pats)
        if (!nm.empty() && nm.contains(p)) {
          hit = true;
          return;
        }
    };
    if (cls < toOrig.size()) {
      nameHit(NF.getValueForNode(toOrig[cls]));
      if (!hit) {
        auto mit2 = canonicalClassMembers.find(toOrig[cls]);
        if (mit2 != canonicalClassMembers.end())
          for (NodeIndex m3 : mit2->second) {
            nameHit(NF.getValueForNode(m3));
            if (hit)
              break;
          }
      }
    }
    memo[cls] = hit;
    return hit;
  };
  boost::unordered_flat_map<uint32_t, char> sinkAblateMemo;
  auto sinkAblateClass = [&](uint32_t cls) {
    return classMatchesPats(cls, sinkAblatePats, sinkAblateMemo);
  };
  // --cfl-sink-instr needs no code here: the opaque-arena model (task
  // #34 v3) is applied structurally at graph-build time (visitCallBase
  // binds payload-accessor returns to shared arena objects), so the
  // solve runs unmodified. Contract gating is enforced at planting.

  auto joinCluster = [&](uint32_t cell, uint32_t o, uint32_t s) {
    if (CFLProbeRodataJoins && o < rootRodata.size() && rootRodata[o]) {
      g_rodataJoinsSkipped++; // MEASUREMENT-ONLY over-removal (task #25)
      return;
    }
    if (!sinkAblatePats.empty() && sinkAblateClass(find(cell))) {
      g_sinkAblatedJoins++; // MEASUREMENT-ONLY UNSOUND channel removal
      return;
    }
    if (protOn && s == 0 && protRid.count(o)) {
      auto &ps = prot[o];
      if (ps.cell != UINT32_MAX)
        ps.cell = find(ps.cell);
      const uint32_t cr = find(cell);
      if (cr == ps.cell)
        return;
      if (protIn[cr]) {
        // writer (or mixed): merges into the cell, exactly as today
        protWriterBlame[protBlameName(cr)]++;
        auto ait = protAnchor.find(cr);
        if (ait != protAnchor.end() && ait->second > 0 &&
            (ps.cell == UINT32_MAX || find(ps.cell) != cr))
          { auto &bl = protCoalesceBlame[protBlameName(cr)];
            bl.first++; bl.second = cr; } // key-family fusion
        if (ps.cell == UINT32_MAX) {
          ps.cell = cr;
          uint32_t n2 = ++protAnchor[find(cr)];
          if (n2 > PROT_ANCHOR_K && !CFLJoinCone &&
              !protCollapsed.count(find(cr)))
            protCollapseQ.push_back(find(cr)); // join-cone: readers are
                                               // few (2% cone), allow
                                               // wide anchors
        } else {
          blobCtx = "prot-writer"; blobCtxOrigin = o;
          ps.cell = merge(ps.cell, cr);
        }
        protWriterMerges++;
        if (!ps.waiting.empty()) {
          auto pending = std::move(ps.waiting);
          ps.waiting.clear();
          for (uint32_t w : pending) {
            w = find(w);
            if (w == ps.cell)
              continue;
            addBridge(find(ps.cell), w);
            protWaitAttached++;
          }
          ps.cell = find(ps.cell);
        }
      } else if (ps.cell != UINT32_MAX &&
                 protCollapsed.count(find(ps.cell))) {
        // collapsed family: no discrimination left — pooled semantics,
        // and no per-reader plane copies
        blobCtx = "prot-pooled-reader"; blobCtxOrigin = o;
        ps.cell = merge(find(ps.cell), cr);
        protPooledReaders++;
      } else if (CFLJoinCone && (coneIn.empty() || !coneIn[cr])) {
        // join-cone mode, NON-cone reader: pooled semantics exactly as
        // without protection — the copy-out is reserved for cells in
        // the answer cone.
        blobCtx = "cone-pooled-reader"; blobCtxOrigin = o;
        ps.cell = ps.cell == UINT32_MAX ? cr : merge(find(ps.cell), cr);
        protPooledReaders++;
      } else {
        // reader: copy-out. Facts cross the bridge and re-emit native
        // along a-edges (value flow launders provenance), but never
        // re-cross another bridge — cells stay separate classes.
        auto &v = readerBridgedTo[cr];
        if (std::find(v.begin(), v.end(), o) != v.end())
          return; // already attached to this origin's cell
        v.push_back(o);
        if (ps.cell == UINT32_MAX) {
          ps.waiting.push_back(cr); // no writer yet: attach on arrival
        } else {
          addBridge(ps.cell, cr);
          protReaderBridges++;
        }
      }
      return;
    }
    const uint64_t key = (uint64_t)o * NSHIFT + s;
    auto [it, ins] = clusterRep.emplace(key, find(cell));
    if (!ins) {
      const uint32_t cellRep = find(cell);
      if (cellRep == find(it->second)) {
        redundantJoins++; // already one cluster: pure lookup, no work
      } else if (keyCount[cellRep].load(std::memory_order_relaxed) > 0) {
        transKeyMerges++; // cell anchors other keys: key-clusters coalesce
      }
      const size_t mc0 = mergeCount;
      blobCtx = "join"; blobCtxOrigin = o;
      it->second = merge(it->second, cell);
      if (mergeCount > mc0) {
        mergesFromJoin++;
        if (CFLRootRelevance)
          mergeWitness.emplace_back(o, find(it->second));
      }
      return;
    }
    keyCount[find(cell)].fetch_add(1, std::memory_order_relaxed);
    if (g_batchRecord)
      g_batchEvts.push_back({0, cell, o, s}); // first insert of this key
    if (NB == 0) return;
    // VX linking: bridge the (o, X) cluster with each exact cluster of o.
    if (s == SHIFT_X) {
      for (uint64_t ek : shiftKeysOf[o]) {
        const uint32_t er = clusterFind(ek);
        assert(er != UINT32_MAX && "shiftKeysOf names a missing cluster");
        addBridge(it->second, er);
      }
    } else {
      shiftKeysOf[o].push_back(key);
      const uint32_t xr = clusterFind((uint64_t)o * NSHIFT + SHIFT_X);
      if (xr != UINT32_MAX)
        addBridge(it->second, xr);
    }
  };
  // Demote bridged readers that gained an in-edge: stores landing in a
  // reader class cross its bridge once but never re-cross, so other
  // readers of the same cell would miss them — merge the reader into
  // EVERY cell it bridge-joined (collapses those cells together if it
  // joined several: exactly today's semantics, protection forfeited
  // for them). Sequential contexts only (join sweeps / wiring).
  auto processProtDemotions = [&]() {
    while (!protDemoteQ.empty()) {
      uint32_t c = find(protDemoteQ.back());
      protDemoteQ.pop_back();
      auto rb = readerBridgedTo.find(c);
      if (rb == readerBridgedTo.end())
        continue; // already handled (or folded away by a merge)
      auto rids = std::move(rb->second);
      readerBridgedTo.erase(rb);
      if (rids.size() > 1) {
        auto &bl = protCoalesceBlame["DEMOTE:" + protBlameName(c)];
        bl.first += rids.size() - 1;
        bl.second = c;
      }
      for (uint32_t o : rids) {
        auto &ps = prot[o];
        c = find(c);
        if (ps.cell == UINT32_MAX) {
          ps.cell = c; // waiting reader turned writer: it IS the cell
          uint32_t n2 = ++protAnchor[find(c)];
          if (n2 > PROT_ANCHOR_K && !protCollapsed.count(find(c)))
            protCollapseQ.push_back(find(c));
          continue;
        }
        ps.cell = find(ps.cell);
        if (ps.cell != c) {
          blobCtx = "prot-demote"; blobCtxOrigin = o;
          ps.cell = merge(ps.cell, c);
        }
        protDemotions++;
      }
    }
  };

  // Collapse over-anchored cells: merge every bridge partner back in
  // and mark the class so future readers merge too. Restores plain
  // pooled semantics for families whose writers already coalesced —
  // protection stops paying copy costs where it cannot discriminate.
  auto processProtCollapses = [&]() {
    while (!protCollapseQ.empty()) {
      uint32_t c = find(protCollapseQ.back());
      protCollapseQ.pop_back();
      if (protCollapsed.count(c))
        continue;
      protCollapsed.insert(c);
      protCollapses++;
      bool again = true;
      while (again) {
        again = false;
        for (uint32_t br : bridgesOf[c]) {
          uint32_t bb = find(br);
          if (bb != c) {
            blobCtx = "prot-collapse"; blobCtxOrigin = UINT32_MAX;
            uint32_t keeper = merge(c, bb);
            if (!protCollapsed.count(keeper)) {
              protCollapsed.erase(c);
              protCollapsed.insert(keeper);
            }
            c = find(keeper);
            again = true;
            break; // bridgesOf[c] mutated by the merge: restart scan
          }
        }
      }
    }
  };

  // Dynamic a-SCC collapse: classes mutually reachable over the current
  // (post-merge) shift-preserving edge graph — a-edges plus residue-0
  // f-edges — receive each other's every fact, so their planes are equal
  // at fixpoint; merging them is precision-neutral and both dedups the
  // entangled core's identical planes (stored once) and removes its
  // internal a-prop churn. Tarjan is O(N+E) (~ms); run periodically as
  // the graph coarsens (merges create new cycles).
  auto collapseSCCs = [&]() -> size_t {
    std::vector<uint32_t> low(N), dfn(N, 0);
    std::vector<uint32_t> tarjanStack;
    std::vector<std::pair<uint32_t, size_t>> callStack;
    std::vector<bool> onStk(N, false);
    std::vector<std::vector<uint32_t>> sccs;
    uint32_t timer = 1;
    auto edgeAt = [&](uint32_t u, size_t i) -> uint32_t {
      // Unified edge index: outA first, then residue-0 outF entries.
      if (i < outA[u].size()) return find(outA[u][i]);
      auto &[t, r] = outF[u][i - outA[u].size()];
      return r == 0 ? find(t) : UINT32_MAX;
    };
    for (uint32_t start = 0; start < N; start++) {
      if (find(start) != start || dfn[start]) continue;
      callStack.emplace_back(start, 0);
      dfn[start] = low[start] = timer++;
      tarjanStack.push_back(start);
      onStk[start] = true;
      while (!callStack.empty()) {
        auto &[u, ei] = callStack.back();
        if (ei < outA[u].size() + outF[u].size()) {
          uint32_t v = edgeAt(u, ei++);
          if (v == UINT32_MAX || v == u) continue;
          if (!dfn[v]) {
            dfn[v] = low[v] = timer++;
            tarjanStack.push_back(v);
            onStk[v] = true;
            callStack.emplace_back(v, 0);
          } else if (onStk[v]) {
            low[u] = std::min(low[u], dfn[v]);
          }
        } else {
          if (low[u] == dfn[u]) {
            std::vector<uint32_t> scc;
            while (true) {
              uint32_t w = tarjanStack.back();
              tarjanStack.pop_back();
              onStk[w] = false;
              scc.push_back(w);
              if (w == u) break;
            }
            if (scc.size() > 1) sccs.push_back(std::move(scc));
          }
          uint32_t uu = u;
          callStack.pop_back();
          if (!callStack.empty())
            low[callStack.back().first] =
                std::min(low[callStack.back().first], low[uu]);
        }
      }
    }
    size_t collapsed = 0;
    for (auto &scc : sccs) {
      uint32_t rep = find(scc[0]);
      blobCtx = "a-scc"; blobCtxOrigin = UINT32_MAX;
      for (size_t i = 1; i < scc.size(); i++) {
        rep = merge(rep, scc[i]);
        collapsed++;
      }
      compactLists(rep);
    }
    return collapsed;
  };
  tHow = "seed"; tFrom = UINT32_MAX;
  if (CFLBatchRoots == 0) {
    size_t exactMint = 0, wildMint = 0;
    for (auto [n, rid] : seeds) {
      const bool exact = !nexusGate || rootNexus[rid];
      addFact(find(n), exact ? 0 : SHIFT_X, rid, ctx0);
      (exact ? exactMint : wildMint)++;
    }
    if (nexusGate)
      CG_LOG("NexusFields: " << exactMint << " exact-minted roots (fn + "
             "nexus origins), " << wildMint << " wildcard-minted (FI)\n");
  } // batched mode seeds per batch inside the round driver (task #40)
  flushCtx(ctx0);

  // ---- Incremental cross-iteration wiring ----
  // The outer fixpoint used to re-solve from scratch after every round
  // of callee wiring (5 full solves on the kernel; iterations past the
  // first mostly re-derive the previous fixpoint). Facts are monotone
  // and resolution only ADDS edges, so instead: translate the EB edges
  // appended by the wiring into solver form, seed them from the planes
  // already computed, and continue draining from the previous fixpoint.
  std::vector<NodeIndex> newAllocNodes; // callsites turned AllocSites
  FactSet parkedRoots; // obsolete identity roots, masked out of seeding
  auto growTo = [&](uint32_t N2) {
    assert(N2 <= solverCapN &&
           "flows-to incremental wiring exceeded class headroom");
    if (N2 <= N) return;
    R.resize(N2); RB.resize(N2); dirty.resize(N2); jdirty.resize(N2);
    dirtyBr.resize(N2); joined.resize(N2);
    for (uint32_t i = N; i < N2; i++) {
      R[i].resize(NSHIFT); RB[i].resize(NSHIFT); dirty[i].resize(NSHIFT);
      jdirty[i].resize(NSHIFT); dirtyBr[i].resize(NSHIFT);
      joined[i].resize(NSHIFT);
    }
    outA.resize(N2); outF.resize(N2); cellsOf.resize(N2);
    bridgesOf.resize(N2);
    wflag.resize(N2, 0);
    hasIn.resize(N2, false);
    topoRank.resize(N2, 0); // rank is an order heuristic only
    ufp.resize(N2); ufrank.resize(N2, 0);
    for (uint32_t i = N; i < N2; i++) ufp[i] = i;
    compactMark.resize(N2, 64);
    popCount.resize(N2, 0);
    mergeHits.resize(N2, 0);
    isRoot.resize(N2, 0);
    if (!inSlice.empty()) inSlice.resize(N2, 1); // new wiring is never sliced
    if (!protIn.empty()) protIn.resize(N2, 0);
    // New wiring-era classes default non-nexus: a late-minted nexus
    // alloc degrades to FI for itself (sound, logged via mint tally).
    if (!nexusCls.empty()) nexusCls.resize(N2, 0);
    if (!coneIn.empty()) coneIn.resize(N2, 0);
    if (!ownedMask.empty()) ownedMask.resize(N2, 0);
    clsSize.resize(N2, 1);
    N = N2;
  };
  auto originBearing = [&](NodeIndex canon) {
    if (valueIsOrigin(canon)) return true;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m : mit->second)
        if (valueIsOrigin(m)) return true;
    return false;
  };
  auto mintRoot = [&](uint32_t cls) {
    uint32_t rep = find(cls);
    if (isRoot[rep]) return;
    isRoot[rep] = 1;
    uint32_t rid = nextRoot++;
    if (protOn)
      for (uint32_t pc : protCls)
        if (find(pc) == rep) {
          protRid.insert(rid); // container origin minted mid-fixpoint
          break;
        }
    FactSet::Universe = nextRoot; // widen BEFORE the first set of this bit
    rootClassOf.push_back(rep);
    rootParkable.push_back(!hasIn[rep] && !originBearing(toOrig[rep]));
    rootRodata.push_back(classIsRodata(toOrig[rep]));
    if (CFLRodataCopy && rootRodata.back())
      protRid.insert(rid); // rodata origin minted mid-fixpoint (task #25)
    if (CFLJoinCone)
      protRid.insert(rid); // join-cone: all origins eligible (task #38)
    if (!ownedMask.empty() && !funcOfCanon.count(toOrig[rep])) {
      const Value *ov2 = NF.getValueForNode(toOrig[rep]);
      const llvm::Module *om2 = nullptr;
      if (ov2) {
        if (const auto *oi2 = dyn_cast<Instruction>(ov2))
          om2 = oi2->getModule();
        else if (const auto *og2 = dyn_cast<GlobalValue>(ov2))
          om2 = og2->getParent();
      }
      ownedMask[rep] |= 1ull << subsysBitOf(om2);
    }
    if (nexusGate)
      rootNexus.push_back(nexusCls[rep] &&
                          (nexusIds || originBearing(toOrig[rep])));
    tHow = "inc-mint"; tFrom = rep;
    addFact(rep, (nexusGate && !rootNexus[rid]) ? SHIFT_X : 0, rid, ctx0);
  };
  auto wireIncremental = [&](size_t lo) {
    const uint32_t oldN = N;
    const uint32_t rootsBefore = nextRoot;
    // Phase 1: classify the appended EB edges (dense() grows the id
    // space; per-class arrays follow in growTo before any indexing).
    struct NewEdge { uint32_t kind, a, b, c; }; // 0=a 1=d 2=f 3=fx
    std::vector<NewEdge> batch;
    for (size_t i = lo; i < edges.size(); i++) {
      const auto &E = edges[i];
      NodeIndex cf = getCanonicalNode(E.from), ct = getCanonicalNode(E.to);
      if (E.label == la) {
        uint32_t x = dense(cf), y = dense(ct);
        if (x != y) batch.push_back({0, x, y, 0});
      } else if (E.label == ld) {
        batch.push_back({1, dense(cf), dense(ct), 0});
      } else if (NB > 0 && E.label == lfx) {
        batch.push_back({3, dense(cf), 0, 0});
      } else if (NB > 0) {
        auto bIt = bucketOfLabel.find(E.label);
        if (bIt != bucketOfLabel.end())
          batch.push_back({2, dense(cf), dense(ct), bIt->second});
      }
    }
    growTo((uint32_t)toOrig.size());
    // Park obsolete identity roots: any parkable root whose class is the
    // target of a new a/f edge is exactly a root the from-scratch
    // rebuild would stop minting. Its bit stays where drain 0 already
    // put it (joins made from it remain — sound over-approximation) but
    // is masked out of all further edge seeding.
    {
      boost::unordered_flat_set<uint32_t> tgtReps;
      for (const NewEdge &e : batch)
        if (e.kind == 0 || e.kind == 2) tgtReps.insert(find(e.b));
      size_t parked = 0;
      for (uint32_t rid = 0; rid < (uint32_t)rootClassOf.size(); rid++) {
        if (!rootParkable[rid] || parkedRoots.test(rid)) continue;
        if (tgtReps.count(find(rootClassOf[rid]))) {
          parkedRoots.set(rid);
          parked++;
        }
      }
      if (parked)
        CG_LOG("FlowsTo incremental: parked " << parked
               << " obsolete identity roots\n");
    }
    FactSet seedScratch;
    auto seedBits = [&](uint32_t tgt, uint32_t s2, const FactSet &plane) {
      if (plane.none()) return;
      if (parkedRoots.none()) { addBits(tgt, s2, plane, ctx0); return; }
      seedScratch.copyFrom(plane);
      seedScratch.subtract(parkedRoots);
      if (seedScratch.any()) addBits(tgt, s2, seedScratch, ctx0);
    };
    // Phase 2: apply. Edge lists live on the current rep (a merged-away
    // class's lists were already moved); targets stay raw and resolve
    // with find() at use, exactly like the initial build. Each new edge
    // is seeded with the source class's full current planes — the same
    // one-time push merge() does for moved edges.
    size_t nA = 0, nD = 0, nF = 0, nW = 0;
    for (const NewEdge &e : batch) {
      if (e.kind == 0) {
        hasIn[e.b] = true;
        if (protOn) {
          const uint32_t pb = find(e.b);
          if (!protIn[pb]) {
            protIn[pb] = 1;
            if (readerBridgedTo.count(pb))
              protDemoteQ.push_back(pb);
          }
        }
        uint32_t x = find(e.a), y = find(e.b);
        if (x == y) continue;
        outA[x].push_back(e.b);
        nA++;
        if (traceRoot >= 0) { tHow = "inc-wire-a"; tFrom = x; }
        for (uint32_t s = 0; s < NSHIFT; s++) {
          seedBits(y, s, R[x][s]);
          seedBits(y, s, RB[x][s]);
        }
      } else if (e.kind == 1) {
        uint32_t p = find(e.a);
        auto &cs = cellsOf[p];
        if (std::find(cs.begin(), cs.end(), e.b) == cs.end()) {
          cs.push_back(e.b);
          nD++;
          // A new cell invalidates the all-cells joined marks: re-offer
          // the class's full fact set; old cells re-confirm via the
          // one-lookup fast path.
          for (uint32_t s = 0; s < NSHIFT; s++) {
            joined[p][s].clear();
            if (R[p][s].any()) jdirty[p][s].unionWith(R[p][s]);
            if (RB[p][s].any()) jdirty[p][s].unionWith(RB[p][s]);
          }
          push(p, ctx0);
        }
      } else if (e.kind == 2) {
        hasIn[e.b] = true;
        if (protOn) {
          const uint32_t pb = find(e.b);
          if (!protIn[pb]) {
            protIn[pb] = 1;
            if (readerBridgedTo.count(pb))
              protDemoteQ.push_back(pb);
          }
        }
        uint32_t b = find(e.a);
        outF[b].emplace_back(e.b, e.c);
        nF++;
        if (traceRoot >= 0) { tHow = "inc-wire-f"; tFrom = b; }
        for (uint32_t s = 0; s < NSHIFT; s++) {
          uint32_t tt = find(e.b);
          uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + e.c) % NB;
          if (tt == b && s2 == s) continue;
          seedBits(tt, s2, R[b][s]);
          seedBits(tt, s2, RB[b][s]);
        }
      } else {
        uint32_t w = find(e.a);
        if (!wflag[w]) {
          wflag[w] = 1;
          nW++;
          if (traceRoot >= 0) { tHow = "inc-wire-fx"; tFrom = w; }
          for (uint32_t s = 0; s < NB; s++) {
            if (R[w][s].any()) addBits(w, SHIFT_X, R[w][s], ctx0);
            if (RB[w][s].any()) addBitsBridged(w, SHIFT_X, RB[w][s], ctx0);
          }
        }
      }
    }
    // Phase 3: mint identity roots — new classes by the initial-minting
    // criterion (heap objects, allocator callsite values, previously
    // edge-less formals), plus existing classes that just became
    // allocation sites (their identity was not origin-bearing when the
    // initial mint ran).
    for (uint32_t n2 = oldN; n2 < N; n2++)
      if (!hasIn[n2] || originBearing(toOrig[n2])) {
        // Lazy mode defers exactly like the initial mint: the
        // post-drain expansion admits the class if/when it enters A.
        if (CFLLazyMint) lazyDeferred.push_back(n2);
        else mintRoot(n2);
      }
    for (NodeIndex an : newAllocNodes) {
      auto dIt = toDense.find(getCanonicalNode(an));
      assert(dIt != toDense.end() &&
             "allocator callsite class missing from dense map");
      if (CFLLazyMint) lazyDeferred.push_back(dIt->second);
      else mintRoot(dIt->second);
    }
    newAllocNodes.clear();
    flushCtx(ctx0);
    CG_LOG("FlowsTo incremental: +" << (N - oldN) << " classes, +" << nA
           << " a / +" << nD << " d / +" << nF << " f / +" << nW
           << " fx edges, +" << (nextRoot - rootsBefore) << " roots ("
           << nextRoot << " total)\n");
  };

  // Lazy-mint expansion (task #21, rules 2+3): recompute A on the
  // CURRENT quotient — merges only coarsen it, so A only grows — and
  // mint every deferred candidate that entered it. Runs at each drain
  // fixpoint; a round that mints nothing means A and the root set are
  // stable (the restricted fixpoint). Seeding is monotone addFact —
  // the cheap direction of incrementality, no wiring involved.
  size_t lazyRounds = 0, lazyLateMints = 0;
  auto lazyExpand = [&]() -> size_t {
    if (lazyDeferred.empty()) return 0;
    auto tExp = std::chrono::steady_clock::now();
    std::vector<std::vector<uint32_t>> rin(N);
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue;
      for (uint32_t t : outA[n]) {
        uint32_t tt = find(t);
        if (tt != n) rin[tt].push_back(n);
      }
      for (auto [t, r] : outF[n]) {
        uint32_t tt = find(t);
        if (tt != n) rin[tt].push_back(n);
      }
      for (uint32_t c : cellsOf[n]) { // cell -> owner hop
        uint32_t cc = find(c);
        if (cc != n) rin[cc].push_back(n);
      }
    }
    std::vector<char> A(N, 0);
    std::vector<uint32_t> bfs;
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto dIt = toDense.find(getCanonicalNode(fn));
      if (dIt == toDense.end()) continue;
      uint32_t rep = find(dIt->second);
      if (!A[rep]) { A[rep] = 1; bfs.push_back(rep); }
    }
    while (!bfs.empty()) {
      uint32_t n = bfs.back();
      bfs.pop_back();
      for (uint32_t p : rin[n])
        if (!A[p]) { A[p] = 1; bfs.push_back(p); }
      for (uint32_t br : bridgesOf[n]) { // pairwise exchange: both ways
        uint32_t bb = find(br);
        if (!A[bb]) { A[bb] = 1; bfs.push_back(bb); }
      }
    }
    size_t minted = 0;
    std::vector<uint32_t> still;
    still.reserve(lazyDeferred.size());
    for (uint32_t n : lazyDeferred) {
      uint32_t rep = find(n);
      if (isRoot[rep]) continue; // merged into a minted identity
      if (A[rep]) {
        mintRoot(rep);
        minted++;
      } else {
        still.push_back(n);
      }
    }
    lazyDeferred.swap(still);
    lazyRounds++;
    lazyLateMints += minted;
    if (minted) flushCtx(ctx0);
    CG_LOG("LazyMint: round " << lazyRounds << " minted +" << minted
           << " roots (" << lazyLateMints << " late total, "
           << lazyDeferred.size() << " still deferred), "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tExp).count()
           << " ms\n");
    return minted;
  };

  // --cfl-solver-profile: rdtsc phase accounting inside the wave phases,
  // accumulated per thread and summed at the end. Attribution: join =
  // jdirty filter incl. cluster lookups plus the sequential apply
  // (merges); bridge = dirtyBr crossings; scan = guard checks on clean
  // shifts; wflag/aprop/fprop = delta emission (addBits cost lands in
  // its calling phase).
  const bool prof = CFLSolverProfile;
  auto rd = [&]() -> uint64_t { return prof ? __builtin_ia32_rdtsc() : 0; };
  // Phase A — join filter (parallel-safe: union-find frozen, cluster
  // registry read-only, only n's own planes/lists mutated). Cell join
  // (M ::= -d V d | -d VX d): sweep the join backlog — facts never yet
  // pushed to this class's full cell list — against the per-fact
  // clusters. Facts whose (o, s) cluster already equals the class's
  // single deduped cell rep are confirmed here (the overwhelming
  // majority: merge re-offers re-confirming an existing cluster); the
  // rest become requests for the sequential apply step, which performs
  // the actual cluster inserts, VX bridging and merges.
  // Join sweep (M ::= -d V d | -d VX d): drain the join backlog against
  // the class's cells via the per-fact clusters. ALWAYS sequential —
  // joins merge union-find classes and move planes, which cannot overlap
  // the frozen parallel phases. At T>1 the driver runs this as its own
  // sequential sub-phase right after each block's parallel propagation,
  // while the block's planes are still warm; deferring per-fact requests
  // instead (tried) re-touched every first-offer fact cold at ~5x the
  // cycles and lost on kernel-shaped merge churn. A merge can absorb n
  // itself: stop; the keeper inherits the backlog and is re-queued.
  auto joinSweep = [&](uint32_t n, SolverCtx &ctx) {
    if (protOn && !protDemoteQ.empty())
      processProtDemotions();
    if (protOn && !protCollapseQ.empty())
      processProtCollapses();
    if (find(n) != n) return; // merged away; keeper carries the state
    for (uint32_t s = 0; s < NSHIFT; s++) {
      if (jdirty[n][s].none()) continue;
      uint64_t tp0 = rd();
      FactSet &todo = ctx.todoS;
      todo.copyFrom(jdirty[n][s]);
      jdirty[n][s].clear();
      if (cellsOf[n].empty()) { ctx.cyJoin += rd() - tp0; continue; }
      // Dedup stale cell entries to live union-find reps: after the
      // FIRST fact of a shift joins the cells they all share one rep,
      // so each further fact needs one lookup, not |list| (dropping
      // this was the original 95%-of-solve-time mistake). Dedup once up
      // front (prior sweeps' merges), and again after the first fact.
      auto &cs = cellsOf[n];
      auto dedupCells = [&]() {
        for (auto &c : cs) c = find(c);
        std::sort(cs.begin(), cs.end());
        cs.erase(std::unique(cs.begin(), cs.end()), cs.end());
      };
      dedupCells();
      if (prof) ctx.sweepOffered += todo.count();
      todo.subtract(joined[n][s]);
      if (prof) ctx.sweepKept += todo.count();
      // Snapshot: joinCluster can merge and mutate backing state.
      ctx.sweepElems.clear();
      todo.forEach([&](uint32_t o) { ctx.sweepElems.push_back(o); });
      bool firstFact = true;
      for (uint32_t o : ctx.sweepElems) {
        bool aborted = false;
        for (size_t ci = 0; ci < cellsOf[n].size(); ci++) {
          ctx.nJoinLk++;
          joinCluster(cellsOf[n][ci], o, s);
          if (find(n) != n) { aborted = true; break; }
        }
        if (aborted) break;
        if (firstFact) { dedupCells(); firstFact = false; }
        // Cells appended mid-loop were covered (the inner bound
        // re-reads cellsOf[n].size()).
        joined[n][s].set(o);
      }
      ctx.cyJoin += rd() - tp0;
      if (find(n) != n) return;
    }
  };
  // unique_ptr: in batch-worker mode the parent's pool has T=1 (no
  // live threads — fork-safe); each forked worker rebuilds its own
  // pool with its share of the cores.
  auto poolPtr = std::make_unique<WavePool>(solverThreads);
  uint64_t seqJoinCy = 0; // T>1: cycles in the sequential join sub-phase
  // Phase B — bridge crossings, wildcard projection and a/f delta
  // propagation. Parallel-safe under the lock discipline: the owner
  // snapshots and clears its own delta planes under its lock; every
  // write to another class's planes goes through addBits/addBitsBridged
  // which lock the target. No merges here.
  auto propagate = [&](uint32_t n, SolverCtx &ctx) {
    if (find(n) != n) return; // merged away; keeper carries the state
    ctx.pops++;
    popCount[n]++;
    if (outA[n].size() + outF[n].size() + cellsOf[n].size() +
            bridgesOf[n].size() >
        compactMark[n])
      compactLists(n);
    // Sequential run: join fused into the same class visit — the wave
    // scheduler's win is ONE streaming pass over the hot planes per
    // wave. At T>1 the driver runs the joins as a sequential sub-phase
    // after this block's parallel propagation instead.
    if (solverThreads == 1) {
      joinSweep(n, ctx);
      if (find(n) != n) return; // absorbed by an in-sweep join
    }
    for (uint32_t s = 0; s < NSHIFT; s++) {
      uint64_t tp1 = rd();
      // Snapshot and clear this shift's delta planes under n's lock:
      // concurrent addBits from other classes' owners mutate these same
      // planes under the same lock, so even the emptiness peeks must be
      // inside it (a torn sparse-vector read is a crash, not staleness).
      FactSet &db = ctx.dbS;
      FactSet &d = ctx.d;
      const bool wproj = NB > 0 && wflag[n] && s != SHIFT_X;
      lockC(n);
      const bool doBr = dirtyBr[n][s].any() && !bridgesOf[n].empty();
      if (doBr) db.copyFrom(dirtyBr[n][s]);
      dirtyBr[n][s].clear();
      const bool hasD = dirty[n][s].any();
      if (hasD) {
        d.copyFrom(dirty[n][s]);
        dirty[n][s].clear();
        if (wproj) {
          // Wildcard (fx self-loop): new facts also hold at unknown
          // shift, kind preserved (retroactive projection on wflag gain
          // is in merge). Split by kind under the same lock as the
          // snapshot so the R/RB reads are coherent.
          ctx.dNatS.copyFrom(d);
          ctx.dNatS.intersectWith(R[n][s]);
          ctx.dBrS.copyFrom(d);
          ctx.dBrS.intersectWith(RB[n][s]);
        }
      }
      unlockC(n);
      // Bridge crossings: native backlog only, arriving bridged.
      if (doBr) {
        if (traceRoot >= 0) { tHow = "bridge"; tFrom = n; }
        for (uint32_t br : bridgesOf[n]) {
          uint32_t bb = find(br);
          if (bb != n) addBitsBridged(bb, s, db, ctx);
        }
      }
      uint64_t tp2 = rd();
      ctx.cyBridge += tp2 - tp1;
      if (!hasD) { ctx.cyScan += rd() - tp2; continue; }
      uint64_t tp3 = rd();
      if (wproj) {
        if (traceRoot >= 0) { tHow = "wflag"; tFrom = n; }
        if (ctx.dNatS.any()) addBits(n, SHIFT_X, ctx.dNatS, ctx);
        if (ctx.dBrS.any()) addBitsBridged(n, SHIFT_X, ctx.dBrS, ctx);
      }
      uint64_t tp4 = rd();
      ctx.cyW += tp4 - tp3;
      // Propagate the delta: whole-plane OR along a-edges, plane-rotated
      // OR along f-edges (X absorbs). Emission is native — value flow
      // launders bridge provenance, exactly like the grammar (M-hops
      // are separated by a-steps in every V derivation).
      if (traceRoot >= 0) { tHow = "a-prop"; tFrom = n; }
      for (uint32_t t : outA[n]) {
        uint32_t tt = find(t);
        if (tt != n) { ctx.nAOr++; addBits(tt, s, d, ctx); }
      }
      uint64_t tp5 = rd();
      ctx.cyA += tp5 - tp4;
      if (prof) ctx.orWords += (uint64_t)d.count() * outA[n].size();
      if (traceRoot >= 0) { tHow = "f-prop"; tFrom = n; }
      for (auto [t, r] : outF[n]) {
        uint32_t tt = find(t);
        uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + r) % NB;
        if (tt != n || s2 != s) { ctx.nFOr++; addBits(tt, s2, d, ctx); }
      }
      ctx.cyF += rd() - tp5;
    }
  };
  // Drain in rank-sorted waves, each wave in rank-contiguous blocks:
  // per block, phase A (join filter) runs data-parallel over classes,
  // the deferred joins apply sequentially, then phase B (bridge/
  // wildcard/a/f propagation) runs data-parallel. Cross-block pushes
  // inside a wave still land downhill — later blocks pick up the
  // accumulated deltas — preserving the wave scheduler's one-touch-per-
  // wave locality; only intra-block forwarding defers to the next wave.
  const uint32_t blockSz = std::max(1u, (unsigned)CFLSolverBlock);
  constexpr uint32_t kGrain = 16;
  std::vector<uint32_t> waveBuf;
  size_t waveCount = 0;
  uint64_t nextSCC = 1u << 18, nextProg = 1u << 20;
  size_t edgesConsumed = edges.size();
  int fpIter = 0;
  // Outer resolution fixpoint: drain -> resolve -> wire the new callee
  // edges incrementally -> drain again from the reached fixpoint. The
  // heavy diagnostics run once, after convergence.
  // Drain to fixpoint: rank-sorted waves until the worklist is empty.
  // Factored out so the origin-batched driver (task #40) can run it
  // once per batch.
  auto drainWaves = [&]() {
  while (true) {
    for (auto &c : ctxs) flushCtx(c);
    if (worklist.empty()) break;
    waveBuf.clear();
    waveBuf.swap(worklist);
    std::sort(waveBuf.begin(), waveBuf.end(),
              [&](uint32_t x, uint32_t y) {
                return topoRank[x] < topoRank[y];
              });
    for (uint32_t n : waveBuf)
      inWL[n].store(0, std::memory_order_relaxed);
    waveCount++;
    for (size_t b0 = 0; b0 < waveBuf.size(); b0 += blockSz) {
      const uint32_t lo = (uint32_t)b0;
      const uint32_t hi =
          (uint32_t)std::min(waveBuf.size(), b0 + (size_t)blockSz);
      std::atomic<uint32_t> cursor{lo};
      auto runPhase = [&](auto &&body) {
        cursor.store(lo, std::memory_order_relaxed);
        parallelPhase = solverThreads > 1;
        poolPtr->run([&](unsigned tid) {
          SolverCtx &ctx = ctxs[tid];
          while (true) {
            uint32_t i = cursor.fetch_add(kGrain, std::memory_order_relaxed);
            if (i >= hi) break;
            const uint32_t e = std::min(i + kGrain, hi);
            for (; i < e; i++) body(waveBuf[i], ctx);
          }
        });
        parallelPhase = false;
      };
      runPhase(propagate); // bridge/wildcard/a/f prop (+joins at T==1)
      if (solverThreads > 1) {
        // Sequential join sub-phase for this block, while its planes
        // are still warm; workers idle here — joins mutate the
        // union-find and move planes, which the frozen parallel phases
        // cannot tolerate. Parallel joins are a future, separate lever.
        uint64_t tj0 = rd();
        for (size_t i = b0; i < (size_t)hi; i++)
          joinSweep(waveBuf[i], ctx0);
        seqJoinCy += rd() - tj0;
      }
      for (auto &c : ctxs) flushCtx(c);
      if (iterations >= nextSCC) {
        nextSCC += 1u << 18;
        size_t collapsed = collapseSCCs();
        mergesFromSCC += collapsed;
        if (collapsed)
          CG_LOG("FlowsTo: a-SCC collapse merged " << collapsed
                 << " classes at " << iterations << " pops\n");
        flushCtx(ctx0);
      }
      if (iterations >= nextProg) {
        nextProg += 1u << 20;
        CG_LOG("FlowsTo progress: " << iterations << " pops, " << factCount
               << " facts, " << clusterCount() << " clusters, "
               << mergeCount << " merges, "
               << std::chrono::duration_cast<std::chrono::milliseconds>(
                      std::chrono::steady_clock::now() - tStart).count()
               << " ms\n");
      }
    }
  }
  };
  // ---- Origin-batched solving (task #40, --cfl-batch-roots=K) ----
  // Fact planes are pure DERIVED state; the only cross-origin coupling
  // is the union-find quotient + clusterRep join keys + bridges, all
  // retained across batches. Per batch: release every plane, seed K
  // roots, drain to fixpoint, harvest the answer-plane bits at fptr
  // classes. Outer rounds repeat until a full pass adds no merges —
  // merges are monotone and bounded, so this terminates at the same
  // closure (lazy-mint catch-up argument family); the stable round's
  // harvest is complete under the final quotient. Memory = graph + one
  // batch's planes; round count measures the modularity thesis.
  auto clearPlanes = [&]() {
    for (uint32_t n = 0; n < N; n++) {
      for (uint32_t s = 0; s < NSHIFT; s++) {
        R[n][s].release();
        RB[n][s].release();
        dirty[n][s].release();
        jdirty[n][s].release();
        dirtyBr[n][s].release();
        joined[n][s].release();
      }
      popCount[n] = 0;
    }
  };
  // Accumulated answer-plane bits per fptr-class rep (batched mode):
  // resolution reads these instead of the (released) live planes.
  std::vector<uint32_t> fptrClsList;
  boost::unordered_flat_map<uint32_t, FactSet> fptrAcc;
  if (CFLBatchRoots) {
    boost::unordered_flat_set<uint32_t> seenF;
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex)
        continue;
      auto dIt = toDense.find(getCanonicalNode(fn));
      if (dIt != toDense.end() && seenF.insert(dIt->second).second)
        fptrClsList.push_back(dIt->second);
    }
    CG_LOG("BatchRoots: K=" << CFLBatchRoots << ", " << fptrClsList.size()
           << " fptr classes tracked\n");
  }
  for (;;) {
  if (CFLBatchRoots == 0) {
  do { // lazy-mint: drain, expand deferred roots, drain again to stability
    drainWaves();
  // At every drain fixpoint, re-admit deferred roots whose classes
  // entered A on the merge-coarsened quotient, then drain the new
  // identity bits; stable A + empty backlog = restricted fixpoint.
  } while (lazyExpand() > 0);
  } else {
    const uint32_t K = CFLBatchRoots;
    const unsigned P = std::max(1u, (unsigned)CFLBatchWorkers);
    size_t round = 0;
    // One batch: release planes, seed rids [blo, bhi), drain.
    auto runBatch = [&](uint32_t blo, uint32_t bhi) {
      clearPlanes();
      tHow = "batch-seed"; tFrom = UINT32_MAX;
      for (uint32_t rid = blo; rid < bhi; rid++) {
        if (parkedRoots.test(rid))
          continue;
        const bool exact =
            !nexusGate || (rid < rootNexus.size() && rootNexus[rid]);
        addFact(find(rootClassOf[rid]), exact ? 0 : SHIFT_X, rid, ctx0);
      }
      flushCtx(ctx0);
      drainWaves();
    };
    for (;;) {
      const size_t mc0 = mergeCount;
      const uint32_t nR = nextRoot;
      for (auto &kv : fptrAcc) kv.second.release();
      fptrAcc.clear();
      if (P > 1) {
        // Process-parallel round (task #41): fork W workers — the graph
        // and quotient arrive copy-on-write, so memory is graph(shared)
        // + W live batch plane-sets. Workers drain single-threaded,
        // record effectual events + harvest bits to scratch files, and
        // _exit without LLVM teardown. The parent replays the streams
        // in worker order: replayed first-inserts recreate keys and VX
        // bridges, cross-worker key collisions become the cross-batch
        // merges, and recorded merges cover SCC collapses.
        const uint32_t nB = (nR + K - 1) / K;
        const unsigned W = std::min((unsigned)nB, P);
        char scratch[] = "/tmp/ka-batch-XXXXXX";
        if (!mkdtemp(scratch))
          report_fatal_error("BatchWorkers: mkdtemp failed");
        std::vector<pid_t> kids(W, -1);
        fflush(nullptr);
        for (unsigned w = 0; w < W; w++) {
          const pid_t pid = fork();
          if (pid < 0)
            report_fatal_error("BatchWorkers: fork failed");
          if (pid == 0) {
            // Claim this worker's share of the cores: fork carried no
            // pool threads, so build a fresh pool and enough ctxs (the
            // deque grows without invalidating ctx0).
            const unsigned wT = std::max(
                1u, std::thread::hardware_concurrency() / W);
            if (wT > 1) {
              solverThreads = wT;
              while (ctxs.size() < wT)
                ctxs.emplace_back();
              poolPtr = std::make_unique<WavePool>(wT);
            }
            g_batchRecord = true;
            g_batchEvts.clear();
            boost::unordered_flat_map<uint32_t, FactSet> hv;
            for (uint32_t bi = w; bi < nB; bi += W) {
              runBatch(bi * K, std::min(nR, (bi + 1) * K));
              for (uint32_t fc : fptrClsList) {
                const uint32_t rep = find(fc);
                FactSet &acc = hv[fc];
                acc.unionWith(R[rep][0]);
                acc.unionWith(RB[rep][0]);
                if (NB > 0) {
                  acc.unionWith(R[rep][SHIFT_X]);
                  acc.unionWith(RB[rep][SHIFT_X]);
                }
              }
            }
            const std::string base =
                std::string(scratch) + "/" + std::to_string(w);
            FILE *fe = fopen((base + ".evt").c_str(), "wb");
            if (!fe)
              _exit(3);
            const uint64_t ne = g_batchEvts.size();
            if (fwrite(&ne, 8, 1, fe) != 1 ||
                (ne && fwrite(g_batchEvts.data(), sizeof(BatchEvt), ne,
                              fe) != ne))
              _exit(3);
            fclose(fe);
            FILE *fh = fopen((base + ".hv").c_str(), "wb");
            if (!fh)
              _exit(3);
            const uint64_t nh = hv.size();
            if (fwrite(&nh, 8, 1, fh) != 1)
              _exit(3);
            std::vector<uint32_t> bits;
            for (auto &kv : hv) {
              bits.clear();
              kv.second.forEach([&](uint32_t o) { bits.push_back(o); });
              const uint32_t id = kv.first;
              const uint64_t nb2 = bits.size();
              if (fwrite(&id, 4, 1, fh) != 1 ||
                  fwrite(&nb2, 8, 1, fh) != 1 ||
                  (nb2 && fwrite(bits.data(), 4, nb2, fh) != nb2))
                _exit(3);
            }
            fclose(fh);
            _exit(0);
          }
          kids[w] = pid;
        }
        for (unsigned w = 0; w < W; w++) {
          int st = 0;
          if (waitpid(kids[w], &st, 0) != kids[w] || !WIFEXITED(st) ||
              WEXITSTATUS(st) != 0)
            report_fatal_error("BatchWorkers: worker failed");
        }
        // Replay in worker order — deterministic, and equivalent to a
        // sequential schedule of the same derivations.
        size_t evReplayed = 0;
        for (unsigned w = 0; w < W; w++) {
          const std::string base =
              std::string(scratch) + "/" + std::to_string(w);
          FILE *fe = fopen((base + ".evt").c_str(), "rb");
          if (!fe)
            report_fatal_error("BatchWorkers: missing event file");
          uint64_t ne = 0;
          if (fread(&ne, 8, 1, fe) != 1)
            report_fatal_error("BatchWorkers: bad event file");
          std::vector<BatchEvt> evs(ne);
          if (ne && fread(evs.data(), sizeof(BatchEvt), ne, fe) != ne)
            report_fatal_error("BatchWorkers: truncated event file");
          fclose(fe);
          unlink((base + ".evt").c_str());
          blobCtx = "batch-replay"; blobCtxOrigin = UINT32_MAX;
          for (const BatchEvt &e : evs) {
            if (e.kind == 0) {
              joinCluster(e.a, e.b, e.c);
            } else {
              const uint32_t x = find(e.a), y = find(e.b);
              if (x != y)
                merge(x, y);
            }
          }
          evReplayed += ne;
          FILE *fh = fopen((base + ".hv").c_str(), "rb");
          if (!fh)
            report_fatal_error("BatchWorkers: missing harvest file");
          uint64_t nh = 0;
          if (fread(&nh, 8, 1, fh) != 1)
            report_fatal_error("BatchWorkers: bad harvest file");
          for (uint64_t i = 0; i < nh; i++) {
            uint32_t id = 0;
            uint64_t nb2 = 0;
            if (fread(&id, 4, 1, fh) != 1 || fread(&nb2, 8, 1, fh) != 1)
              report_fatal_error("BatchWorkers: truncated harvest file");
            std::vector<uint32_t> bits(nb2);
            if (nb2 && fread(bits.data(), 4, nb2, fh) != nb2)
              report_fatal_error("BatchWorkers: truncated harvest bits");
            FactSet &acc = fptrAcc[id];
            for (uint32_t o : bits)
              acc.set(o);
          }
          fclose(fh);
          unlink((base + ".hv").c_str());
        }
        flushCtx(ctx0);
        rmdir(scratch);
        CG_LOG("BatchWorkers: " << W << " workers, " << evReplayed
               << " events replayed\n");
      } else {
      for (uint32_t blo = 0; blo < nR; blo += K) {
        runBatch(blo, std::min(nR, blo + K));
        // Harvest under the current quotient; only the stable round's
        // accumulation (no rep movement) is consumed by resolution.
        // Keyed by the STATIC fptr class id so worker-local reps never
        // leak across process boundaries.
        for (uint32_t fc : fptrClsList) {
          const uint32_t rep = find(fc);
          FactSet &acc = fptrAcc[fc];
          acc.unionWith(R[rep][0]);
          acc.unionWith(RB[rep][0]);
          if (NB > 0) {
            acc.unionWith(R[rep][SHIFT_X]);
            acc.unionWith(RB[rep][SHIFT_X]);
          }
        }
      }
      } // sequential-batch path
      round++;
      const size_t dm = mergeCount - mc0;
      CG_LOG("BatchRoots: round " << round << ": " << dm << " new merges, "
             << (nextRoot - nR) << " late mints, "
             << ((nR + K - 1) / K) << " batches\n");
      if (dm == 0 && nextRoot == nR)
        break; // quotient stable: this round's harvest is valid
    }
  }
  // --cfl-verify-closure: certify the fixpoint. One full non-delta scan of
  // every rule; any rule that would still fire is a violation. This checks
  // the closure property the delta/backlog machinery must maintain — the
  // Lean SolverModel's central assumption, and the layer where the
  // historical solver bugs (joined-marking, merge cascades) lived.
  if (CFLVerifyClosure) {
    uint64_t viol = 0;
    auto report = [&](const char *rule, uint32_t n, uint32_t s,
                      uint32_t extra) {
      if (viol++ < 20)
        errs() << "CLOSURE " << rule << " violation: c" << n << " s" << s
               << " (-> " << extra << ")\n";
    };
    FactSet uniS, tgtS;
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue;
      // dedup cells once for the join check
      if (!cellsOf[n].empty()) {
        auto &cs = cellsOf[n];
        for (auto &c : cs) c = find(c);
        std::sort(cs.begin(), cs.end());
        cs.erase(std::unique(cs.begin(), cs.end()), cs.end());
      }
      for (uint32_t s = 0; s < NSHIFT; s++) {
        // C0: all delta backlogs drained.
        if (dirty[n][s].any()) report("C0-dirty", n, s, 0);
        if (jdirty[n][s].any() && !cellsOf[n].empty())
          report("C0-jdirty", n, s, 0);
        if (dirtyBr[n][s].any() && !bridgesOf[n].empty())
          report("C0-dirtyBr", n, s, 0);
        if (R[n][s].none() && RB[n][s].none()) continue;
        uniS.copyFrom(R[n][s]);
        uniS.unionWith(RB[n][s]);
        auto subsetViol = [&](const FactSet &a, const FactSet &b) {
          bool bad = false;
          a.forEach([&](uint32_t o) {
            // Parked identity roots are exempt: they are deliberately
            // masked out of incremental edge seeding (retired by the
            // equivalent from-scratch rebuild).
            if (parkedRoots.test(o)) return;
            if (!b.test(o)) bad = true;
          });
          return bad;
        };
        // C1: a-edges emit native at same shift.
        for (uint32_t t : outA[n]) {
          uint32_t tt = find(t);
          if (tt == n) continue;
          if (subsetViol(uniS, R[tt][s])) report("C1-a", n, s, tt);
        }
        // C2: f-edges emit native at rotated shift (X absorbs).
        for (auto [t, r] : outF[n]) {
          uint32_t tt = find(t);
          uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + r) % NB;
          if (tt == n && s2 == s) continue;
          if (subsetViol(uniS, R[tt][s2])) report("C2-f", n, s, tt);
        }
        // C3: wildcard projection onto the X plane, kind-preserving.
        if (NB > 0 && wflag[n] && s != SHIFT_X) {
          if (subsetViol(R[n][s], R[n][SHIFT_X])) report("C3-wR", n, s, n);
          tgtS.copyFrom(R[n][SHIFT_X]);
          tgtS.unionWith(RB[n][SHIFT_X]);
          if (subsetViol(RB[n][s], tgtS)) report("C3-wB", n, s, n);
        }
        // C5: native facts crossed every bridge (arriving as either kind).
        if (!bridgesOf[n].empty() && R[n][s].any()) {
          for (uint32_t br : bridgesOf[n]) {
            uint32_t bb = find(br);
            if (bb == n) continue;
            tgtS.copyFrom(R[bb][s]);
            tgtS.unionWith(RB[bb][s]);
            if (subsetViol(R[n][s], tgtS)) report("C5-br", n, s, bb);
          }
        }
        // C4: every fact joined every cell of its class: the (o, s)
        // cluster exists and contains all the cells.
        if (!cellsOf[n].empty()) {
          uniS.forEach([&](uint32_t o) {
            const uint32_t cr = clusterFind((uint64_t)o * NSHIFT + s);
            if (cr == UINT32_MAX) { report("C4-key", n, s, o); return; }
            uint32_t rep = find(cr);
            for (uint32_t c : cellsOf[n])
              if (find(c) != rep) { report("C4-cell", n, s, o); return; }
          });
        }
      }
    }
    if (viol) {
      errs() << "CLOSURE: " << viol << " violations — fixpoint NOT closed\n";
      assert(false && "flows-to fixpoint failed closure verification");
    } else {
      CG_LOG("Closure verified: all rules saturated (0 violations)\n");
    }
  }

  uint64_t totalR = 0, totalRB = 0;
  uint32_t liveClasses = 0;
  for (uint32_t n = 0; n < N; n++) {
    if (find(n) != n) continue;
    liveClasses++;
    for (uint32_t s = 0; s < NSHIFT; s++) {
      totalR += R[n][s].count();
      totalRB += RB[n][s].count();
    }
  }
  CG_LOG("FlowsTo: " << N << " classes (" << liveClasses << " after "
         << mergeCount << " merges), " << nextRoot << " roots, "
         << totalR << " native + " << totalRB << " bridged facts "
         << "(vs pairwise V), " << clusterCount() << " cell clusters, "
         << bridgeCount << " VX bridges, " << waveCount << " waves, "
         << iterations << " worklist pops, "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tStart).count() << " ms\n");

  // Resolution: origins at the fptr class whose shift is zero or unknown
  // (an exact nonzero shift is a provably misaligned pointer, not a call
  // target), intersected with function roots, then the standard filters.
  // Newly discovered pairs are wired (arg/ret flows via handleCall, same
  // as the saturation fixpoint) and force another outer iteration —
  // a resolved callee's flows can enable further resolutions.
  size_t resolved = 0, totalTargets = 0, newPairs = 0, topOnlyPairs = 0;
  // Per-filter pruning tallies: every rejection is potential unsoundness
  // exposure and, symmetrically, the filter's precision contribution —
  // the retirement criterion once CFL-side precision drives them to zero.
  size_t filtCandidates = 0, filtTypeRej = 0, filtFieldRej = 0;
  // --cfl-probe-origin-split (task #29): per-icall, the counterfactual
  // origin-indexed answer — targets attributable to the merged cluster
  // classes of the container origins the fptr was LOADED from — vs the
  // pooled class answer. D = distinct merged cluster classes among
  // those origins: D>1 means per-origin binding splits the answer from
  // the FINAL state already; D==1 means the clusters merged (hub) and
  // splitting needs witness provenance / unmerging. Measurement-only.
  size_t osIcalls = 0, osPooled = 0, osSplit = 0, osD1 = 0, osD24 = 0,
         osDbig = 0, osNoLoad = 0, osNoOrigin = 0;
  std::vector<std::tuple<size_t, const CallBase *, size_t, size_t, size_t>>
      osTop; // (excess, CS, |A|, |Asplit|, D)
  // --cfl-probe-ops-mono (task #30): per two-level dispatch site, is
  // the resolved target set contained in ONE ops-global's member set?
  // Derives the kernel-modularity invariant from the sound analysis
  // instead of assuming it: mono sites certify per-ops pairing; poly
  // sites are the violation/imprecision ledger. Measurement-only.
  std::unordered_map<const GlobalVariable *, FuncSet> opsMembers;
  std::unordered_map<const Function *, SmallVector<const GlobalVariable *, 2>>
      opsMemberOf;
  size_t omSites = 0, omMono = 0, omNear = 0, omPoly = 0, omNoOps = 0;
  std::map<const GlobalVariable *, size_t> omMonoByG;
  std::vector<std::pair<const CallBase *, size_t>> omPolySample;
  if (CFLProbeOpsMono) {
    std::function<void(const Constant *, FuncSet &)> collectFns =
        [&](const Constant *C, FuncSet &out) {
          if (const auto *F2 = dyn_cast<Function>(C->stripPointerCasts())) {
            out.insert(getFuncDef(const_cast<Function *>(F2)));
            return;
          }
          if (isa<ConstantAggregate>(C))
            for (const Use &Op : C->operands())
              if (const auto *CO = dyn_cast<Constant>(Op.get()))
                collectFns(CO, out);
        };
    for (auto &mp2 : Ctx->Modules)
      for (const GlobalVariable &GV : mp2.first->globals()) {
        if (!GV.hasInitializer()) continue;
        FuncSet ms;
        collectFns(GV.getInitializer(), ms);
        if (ms.size() < 2) continue; // singleton "ops" add no partition
        auto &slot = opsMembers[&GV];
        slot = std::move(ms);
        for (const Function *F2 : slot) opsMemberOf[F2].push_back(&GV);
      }
  }
  // Ops-table channel (task #36): resolve the pendings recorded at
  // __static_call_update sites against every same-typed global
  // initializer, once. zeroinitializer tables contribute nothing
  // (their field elements are null, not functions).
  if (CFLStaticOpsTables && !g_sctTableBuilt) {
    g_sctTableBuilt = true;
    boost::unordered_flat_map<std::string,
                              std::vector<const GlobalVariable *>>
        byType;
    for (auto &mp : Ctx->Modules)
      for (const GlobalVariable &GVt : mp.first->globals()) {
        if (!GVt.hasInitializer())
          continue;
        const auto *STt = dyn_cast<StructType>(GVt.getValueType());
        if (STt && STt->hasName())
          byType[sctCanonStructName(STt->getName()).str()].push_back(&GVt);
      }
    for (const auto &P : g_sctPendings) {
      auto tIt = byType.find(P.structName);
      bool any = false;
      if (tIt != byType.end())
        for (const GlobalVariable *T : tIt->second) {
          g_sctTablesScanned++;
          const Constant *E =
              T->getInitializer()->getAggregateElement(P.fieldIdx);
          if (!E)
            continue;
          if (const auto *TF =
                  dyn_cast<Function>(E->stripPointerCasts())) {
            g_sctKeyTable[P.keyName].insert(
                getFuncDef(const_cast<Function *>(TF)));
            any = true;
          }
        }
      if (!any)
        g_sctPendingNoTable++;
    }
    CG_LOG("StaticOpsTables: " << g_sctPendings.size()
           << " load-shaped updates resolved against " << g_sctTablesScanned
           << " table scans; " << g_sctKeyTable.size() << " keys tabled ("
           << g_sctUpdConst << " const + " << g_sctUpdLoad
           << " load updates, " << g_sctUpdNonconform << " non-conforming"
           << " -> " << g_sctKeyUntabled.size() << " untabled keys, "
           << g_sctPendingNoTable << " pendings with no fn source)\n");
  }

  // --cfl-census-icall-shape (task #37): classify every FAT answer site
  // (>=100 targets) by the IR shape of its fptr chain and by whether its
  // operand class is THE giant — separates "resolved to the quotient"
  // from "genuinely unresolved" and names the families for the next
  // answer-level campaigns. Measurement only.
  struct IcallShapeFam { size_t sites = 0, pairs = 0, giantSites = 0;
                         std::string exemplar; };
  std::map<std::string, IcallShapeFam> shapeFams;
  uint32_t censusGiantRep = UINT32_MAX;
  if (CFLCensusIcallShape) {
    uint32_t best = 0;
    for (uint32_t n2 = 0; n2 < N; n2++)
      if (find(n2) == n2 && clsSize[n2] > best) {
        best = clsSize[n2];
        censusGiantRep = n2;
      }
  }

  for (auto *CS : Ctx->IndirectCallInsts) {
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    NodeIndex fn = NF.getValueNodeFor(fptr);
    if (fn == AndersNodeFactory::InvalidIndex) continue;
    if (getCanonicalNode(fn) == NF.getUniversalPtrNode())
      g_uniFptrIcalls++; // fptr IS unknown extern memory — boundary
    auto dIt = toDense.find(getCanonicalNode(fn));
    if (dIt == toDense.end()) continue;
    std::string csStruct; unsigned csField = 0;
    bool hasKey = getCallSiteFieldKey(fptr, csStruct, csField);
    FuncSet targets;
    const uint32_t rep = find(dIt->second);
    if (!CFLTraceFptr.empty() &&
        CS->getFunction()->getName().contains(CFLTraceFptr)) {
      // Backward slice over the post-merge graph: reverse a/f edges plus
      // bridges. The has-root boundary is the severed link.
      errs() << "TRACE-BWD icall in " << CS->getFunction()->getName()
             << " fptr c" << rep << "\n";
      std::unordered_map<uint32_t, std::vector<std::string>> inEdges;
      for (uint32_t n2 = 0; n2 < N; n2++) {
        if (find(n2) != n2) continue;
        for (uint32_t t : outA[n2])
          inEdges[find(t)].push_back("a<-c" + std::to_string(n2));
        for (auto [t, r] : outF[n2])
          inEdges[find(t)].push_back("f" + std::to_string(r) + "<-c" +
                                     std::to_string(n2));
        for (uint32_t br : bridgesOf[n2])
          inEdges[find(br)].push_back("br<-c" + std::to_string(n2));
      }
      auto nameOfClass = [&](uint32_t cls) -> std::string {
        const Value *V2 = cls < N ? NF.getValueForNode(toOrig[cls]) : nullptr;
        if (!V2) return "<synthetic>";
        if (V2->hasName()) return V2->getName().str();
        if (const auto *I2 = dyn_cast<Instruction>(V2))
          return (I2->getFunction()->getName() + "::" + I2->getOpcodeName())
              .str();
        return "<unnamed>";
      };
      size_t ckShown = 0;
      for (auto &[key, crep] : clusterRep) {
        if (find(crep) != rep || ckShown++ > 40) continue;
        uint32_t o2 = (uint32_t)(key / NSHIFT), s2 = (uint32_t)(key % NSHIFT);
        errs() << "TRACE-BWD   cluster-key origin=r" << o2 << " (c"
               << rootClassOf[o2] << " " << nameOfClass(rootClassOf[o2])
               << ") shift=" << s2 << " origin-in:[";
        uint32_t oc = find(rootClassOf[o2]);
        auto oie = inEdges.find(oc);
        size_t oShown = 0;
        if (oie != inEdges.end())
          for (auto &e : oie->second) {
            if (oShown++ > 8) { errs() << " ..."; break; }
            errs() << " " << e;
            uint32_t sc = (uint32_t)std::stoul(e.substr(e.find("c") + 1));
            errs() << "(" << nameOfClass(sc).substr(0, 50) << ")";
          }
        errs() << " ]\n";
        // Members of the origin class: what merged into this orphan?
        NodeIndex ocanon = toOrig[rootClassOf[o2]];
        auto mIt = canonicalClassMembers.find(ocanon);
        if (mIt != canonicalClassMembers.end()) {
          size_t mShown = 0;
          for (NodeIndex m : mIt->second) {
            if (mShown++ > 15) { errs() << "TRACE-BWD     ...more members\n"; break; }
            const Value *MV = NF.getValueForNode(m);
            errs() << "TRACE-BWD     member n" << m << " ";
            if (MV && MV->hasName()) errs() << MV->getName().substr(0, 70);
            else if (MV) {
              if (const auto *MI = dyn_cast<Instruction>(MV))
                errs() << MI->getFunction()->getName().substr(0, 46) << "::"
                       << *MI;
            } else {
              errs() << (NF.isObjectNode(m) ? "<obj/cell>" : "<synthetic>");
            }
            errs() << "\n";
          }
        } else {
          errs() << "TRACE-BWD     (singleton class)\n";
        }
      }
      // Where did the traced function's stores land? Its class's cells and
      // their cluster keys.
      if (traceRoot >= 0) {
        for (auto &[key, crep] : clusterRep) {
          uint32_t cr = find(crep);
          bool hasTr = false;
          for (uint32_t s3 = 0; s3 < NSHIFT && !hasTr; s3++)
            hasTr = R[cr][s3].test((uint32_t)traceRoot);
          if (!hasTr) continue;
          uint32_t o2 = (uint32_t)(key / NSHIFT), s2 = (uint32_t)(key % NSHIFT);
          static size_t trShown = 0;
          if (trShown++ > 60) break;
          errs() << "TRACE-BWD   root-in-cluster c" << cr << " key=(r" << o2
                 << " " << nameOfClass(rootClassOf[o2]).substr(0, 50) << ", s"
                 << s2 << ")\n";
        }
      }
      std::vector<uint32_t> q{rep};
      boost::unordered_flat_set<uint32_t> vis{rep};
      size_t printed = 0;
      for (size_t qi = 0; qi < q.size() && printed < 300; qi++) {
        uint32_t v = q[qi];
        bool has = false;
        for (uint32_t s = 0; s < NSHIFT && !has; s++)
          has = R[v][s].test((uint32_t)traceRoot) ||
                RB[v][s].test((uint32_t)traceRoot);
        errs() << "TRACE-BWD c" << v << " root=" << has << " ";
        const Value *VV = v < N ? NF.getValueForNode(toOrig[v]) : nullptr;
        if (VV && VV->hasName()) errs() << VV->getName().substr(0, 60);
        else if (VV) {
          if (const auto *II = dyn_cast<Instruction>(VV))
            errs() << II->getFunction()->getName().substr(0, 40) << "::"
                   << II->getOpcodeName();
        }
        errs() << " in:[";
        auto ie = inEdges.find(v);
        size_t shownE = 0;
        if (ie != inEdges.end())
          for (auto &e : ie->second) {
            if (shownE++ > 200) { errs() << " ..."; break; }
            errs() << " " << e;
            uint32_t src2 = (uint32_t)std::stoul(e.substr(e.find("c") + 1));
            if (vis.insert(src2).second && q.size() < 3000) q.push_back(src2);
          }
        errs() << " ]\n";
        printed++;
      }
    }
    if (traceRoot >= 0) {
      bool has = false;
      for (uint32_t s = 0; s < NSHIFT && !has; s++)
        has = R[rep][s].test((uint32_t)traceRoot) ||
              RB[rep][s].test((uint32_t)traceRoot);
      errs() << "TRACE icall " << CS->getFunction()->getName() << " fptr c"
             << rep << " has-root=" << has << "\n";
    }
    auto collect = [&](const FactSet &plane) {
      plane.forEach([&](uint32_t o) {
        auto rIt = funcRootOf.find(o);
        if (rIt == funcRootOf.end()) return;
        Function *F = getFuncDef(const_cast<Function *>(rIt->second));
        // static_call sites are direct-form icalls: the trampoline's
        // own root is the dispatch point, not a callee. Compare by
        // GUID, not pointer: __SCT__ symbols have no IR definition, so
        // funcRootOf holds an arbitrary per-TU declaration object
        // (pointer-ordered container iteration) — pointer equality
        // fired nondeterministically across runs (1-pair dump flap,
        // full7 vs lazy2) and missed 2547 trampoline-self pairs.
        if (Function *called = CS->getCalledFunction())
          if (F == called || F->getGUID() == called->getGUID())
            return;
        filtCandidates++;
        if (!isCompatible(CS, F)) { filtTypeRej++; return; }
        if (hasKey && !fieldFilterAccepts(F, csStruct, csField)) {
          filtFieldRej++;
          return;
        }
        targets.insert(F);
      });
    };
    // Tracepoint keyed dispatch (task #35 v3): answer-level primitive.
    // The graph cannot carry per-key fn channels — probe VALUE classes
    // are V-merged into the giant, so scanning R[operand-class] returns
    // the pool no matter how the channel is wired. For __traceiter
    // sites the census-complete registration table IS the answer; the
    // wiring below (Callees insert + callee-flow wiring) is unchanged.
    bool tpModelOwned = false;
    if (CFLTracepointKeys) {
      auto tpIt = g_tpIterIcallKey.find(CS);
      if (tpIt != g_tpIterIcallKey.end()) {
        if (!g_tpKeyHasDynProbe.count(tpIt->second)) {
          tpModelOwned = true;
          g_tpKeyModelAnswered++;
          auto pIt = g_tpKeyProbes.find(tpIt->second);
          if (pIt != g_tpKeyProbes.end())
            for (const Function *PF : pIt->second) {
              if (!isCompatible(CS, PF)) {
                g_tpKeyTypeRej++;
                if (g_tpKeyTypeRej <= 40)
                  WARNING("TracepointKeys: type-rejected probe "
                          << PF->getName() << " at "
                          << CS->getFunction()->getName() << "\n");
                continue;
              }
              targets.insert(PF);
            }
        } else {
          g_tpKeyFallbackSites++; // LOUD: table incomplete for this key
        }
      }
    }
    // Ops-table channel (task #36): a __SCT__ site whose key is tabled
    // takes its targets from the table — the graph answer at these
    // sites is the type fallback (the update's fn argument is a
    // dynamic ops-struct load the graph never resolves). Untabled or
    // non-conforming keys keep graph behavior, counted.
    bool sctModelOwned = false;
    if (CFLStaticOpsTables && !tpModelOwned) {
      Function *SCTF = CS->getCalledFunction();
      if (SCTF && SCTF->getName().starts_with("__SCT__")) {
        std::string keyName =
            ("__SCK__" + SCTF->getName().drop_front(7)).str();
        auto kIt = g_sctKeyTable.find(keyName);
        if (kIt != g_sctKeyTable.end() &&
            !g_sctKeyUntabled.count(keyName)) {
          sctModelOwned = true;
          g_sctSitesModelAnswered++;
          for (const Function *TF : kIt->second) {
            // The table is AUTHORITATIVE: it lists exactly what update
            // sites patch into this key, so a type mismatch (e.g.
            // __static_call_return0's long(void) at a typed site) is a
            // REAL runtime target the type filter would wrongly drop.
            // Counted + warned for review, never filtered.
            if (!isCompatible(CS, TF)) {
              g_sctTypeRej++;
              if (g_sctTypeRej <= 20)
                WARNING("StaticOpsTables: type-mismatched table entry "
                        << TF->getName() << " at "
                        << CS->getFunction()->getName()
                        << " (kept)\n");
            }
            targets.insert(TF);
          }
        } else {
          g_sctSitesUntabled++;
        }
      }
    }
    if (!tpModelOwned && !sctModelOwned && CFLBatchRoots) {
      // Batched mode: live planes hold only the last batch — read the
      // stable round's accumulated answer bits (static-id keyed).
      auto aIt = fptrAcc.find(dIt->second);
      if (aIt != fptrAcc.end())
        collect(aIt->second);
    }
    if (!tpModelOwned && !sctModelOwned && !CFLBatchRoots) {
      collect(R[rep][0]);
      collect(RB[rep][0]);
    }
    const size_t exactTargets = targets.size();
    if (!tpModelOwned && !sctModelOwned && !CFLBatchRoots && NB > 0) {
      collect(R[rep][SHIFT_X]);
      collect(RB[rep][SHIFT_X]);
    }
    topOnlyPairs += targets.size() - exactTargets;
    if (CFLCensusIcallShape && targets.size() >= 100) {
      auto shapeOf = [&]() -> std::string {
        const Value *co = CS->getCalledOperand()->stripPointerCasts();
        if (const auto *A = dyn_cast<Argument>(co))
          return ("formal " + A->getParent()->getName() + "#" +
                  std::to_string(A->getArgNo()))
              .str();
        const auto *LI = dyn_cast<LoadInst>(co);
        if (!LI) {
          if (isa<PHINode>(co)) return "phi";
          if (isa<SelectInst>(co)) return "select";
          const auto *IC = dyn_cast<Instruction>(co);
          return std::string("other:") +
                 (IC ? IC->getOpcodeName() : "non-inst");
        }
        const Value *P = LI->getPointerOperand()->stripPointerCasts();
        if (const auto *GO = dyn_cast<GEPOperator>(P)) {
          const auto *ST3 =
              dyn_cast<StructType>(GO->getSourceElementType());
          std::string fld = "?";
          if (GO->getNumIndices() == 2)
            if (const auto *ci = dyn_cast<ConstantInt>(GO->getOperand(2)))
              fld = std::to_string(ci->getZExtValue());
          const Value *B = GO->getPointerOperand()->stripPointerCasts();
          std::string base = isa<LoadInst>(B)      ? " [2level]"
                             : isa<Argument>(B)    ? " [parambase]"
                             : isa<GlobalVariable>(B) ? " [globalbase]"
                                                      : "";
          if (ST3 && ST3->hasName())
            return ("load " + sctCanonStructName(ST3->getName()) + "." +
                    fld + base)
                .str();
          return "load gep-untyped" + base;
        }
        if (isa<GlobalVariable>(P))
          return ("load @" + P->getName()).str();
        if (isa<Argument>(P)) return "load *param";
        if (isa<PHINode>(P)) return "load phi-ptr";
        if (isa<LoadInst>(P)) return "load **indirect";
        return "load other";
      };
      auto &fam = shapeFams[shapeOf()];
      fam.sites++;
      fam.pairs += targets.size();
      if (rep == censusGiantRep) fam.giantSites++;
      if (fam.exemplar.empty())
        fam.exemplar = (CS->getFunction()->getName() + " (" +
                        std::to_string(targets.size()) + " tgts, cls " +
                        std::to_string(clsSize[rep]) + ", R " +
                        std::to_string(R[rep][0].count()) + ")")
                           .str();
    }
    if (CFLProbeOriginSplit && !targets.empty()) {
      const auto *LI = dyn_cast<LoadInst>(fptr);
      if (!LI) {
        osNoLoad++;
      } else {
        NodeIndex pn = NF.getValueNodeFor(LI->getPointerOperand());
        auto pIt = pn == AndersNodeFactory::InvalidIndex
                       ? toDense.end()
                       : toDense.find(getCanonicalNode(pn));
        if (pIt == toDense.end()) {
          osNoOrigin++;
        } else {
          const uint32_t prep = find(pIt->second);
          std::set<uint32_t> clsSet;
          auto scanO = [&](const FactSet &pl) {
            pl.forEach([&](uint32_t o) {
              if (funcRootOf.count(o)) return; // container origins only
              for (uint32_t sh = 0; sh < NSHIFT; sh++) {
                uint32_t c = clusterFind((uint64_t)o * NSHIFT + sh);
                if (c != UINT32_MAX) clsSet.insert(find(c));
              }
            });
          };
          scanO(R[prep][0]);
          scanO(RB[prep][0]);
          if (clsSet.empty()) {
            osNoOrigin++;
          } else {
            FuncSet split;
            for (uint32_t c : clsSet) {
              auto scanF = [&](const FactSet &pl) {
                pl.forEach([&](uint32_t o) {
                  auto rIt = funcRootOf.find(o);
                  if (rIt == funcRootOf.end()) return;
                  Function *F =
                      getFuncDef(const_cast<Function *>(rIt->second));
                  if (targets.count(F)) split.insert(F);
                });
              };
              scanF(R[c][0]);
              scanF(RB[c][0]);
            }
            osIcalls++;
            osPooled += targets.size();
            osSplit += split.size();
            const size_t D = clsSet.size();
            if (D == 1) osD1++;
            else if (D <= 4) osD24++;
            else osDbig++;
            if (targets.size() > split.size())
              osTop.emplace_back(targets.size() - split.size(), CS,
                                 targets.size(), split.size(), D);
          }
        }
      }
    }
    if (CFLProbeOpsMono && !targets.empty()) {
      const auto *LI2 = dyn_cast<LoadInst>(fptr);
      const LoadInst *L1 = nullptr;
      if (LI2) {
        const Value *B = LI2->getPointerOperand()->stripPointerCasts();
        while (const auto *G = dyn_cast<GEPOperator>(B))
          B = G->getPointerOperand()->stripPointerCasts();
        L1 = dyn_cast<LoadInst>(B);
      }
      if (L1) { // two-level dispatch site
        omSites++;
        std::map<const GlobalVariable *, size_t> cover;
        size_t withOps = 0;
        for (const Function *F2 : targets) {
          auto mIt = opsMemberOf.find(F2);
          if (mIt == opsMemberOf.end()) continue;
          withOps++;
          for (const GlobalVariable *G : mIt->second) cover[G]++;
        }
        size_t best = 0;
        const GlobalVariable *bestG = nullptr;
        for (auto &[G, N] : cover)
          if (N > best) { best = N; bestG = G; }
        if (withOps == 0) {
          omNoOps++;
        } else if (best == targets.size()) {
          omMono++;
          omMonoByG[bestG]++;
        } else if (best + 2 >= targets.size()) {
          omNear++;
        } else {
          omPoly++;
          if (omPolySample.size() < 12)
            omPolySample.emplace_back(CS, targets.size());
        }
      }
    }
    if (!targets.empty()) { resolved++; totalTargets += targets.size(); }
    // ops-pairs step 2 (task #30): at a two-level dispatch site
    // (obj->ops then ops->fn), the receiver base object is the value
    // whose pooled actual->formal edge we can replace per-pair.
    const Value *opsRecv = nullptr;
    if (CFLOpsPairs && !opsPairs.empty() && !targets.empty()) {
      if (const auto *L2 = dyn_cast<LoadInst>(fptr)) {
        const Value *B = L2->getPointerOperand()->stripPointerCasts();
        while (const auto *G2 = dyn_cast<GEPOperator>(B))
          B = G2->getPointerOperand()->stripPointerCasts();
        if (const auto *L1 = dyn_cast<LoadInst>(B)) {
          const Value *RB = L1->getPointerOperand()->stripPointerCasts();
          while (const auto *G3 = dyn_cast<GEPOperator>(RB))
            RB = G3->getPointerOperand()->stripPointerCasts();
          opsRecv = RB;
        }
      }
    }
    for (const Function *F : targets) {
      if (!Ctx->Callees[CS].insert(F).second)
        continue; // wired in an earlier iteration
      newPairs++;
      // Wire the callee's flows exactly as the saturation fixpoint does;
      // the new edges enter the NEXT iteration's solve.
      Function *CF = const_cast<Function *>(F);
      if (Ctx->AllocFuncs.count(CF)) {
        Ctx->AllocSites.insert(CS);
        NodeIndex callNode = getRepNodeForValue(CS);
        if (callNode == AndersNodeFactory::InvalidIndex) {
          // Allocator resolved at a callsite with no value node (result
          // unused or non-pointer-typed, e.g. type-compat match on a
          // void callsite): create on demand, as handleCall does.
          callNode = getCanonicalNode(NF.createValueNode(CS));
        }
        AllocSites.insert(callNode);
        newAllocNodes.push_back(callNode);
        NodeIndex heapObj = NF.createOpaqueObjectNode(CS, true);
        EB.addDereferenceEdges(callNode, heapObj);
        auto sit = Ctx->FuncSummaries.find(CF);
        if (sit != Ctx->FuncSummaries.end() &&
            applySummaryAtoms(CS, *sit->second))
          wireCallArgs(CS, CF); // dynamic-fn INVOKE: feed the body pool
      } else if (Ctx->ContainerFuncs.count(CF)) {
        handleContainerCall(CS, CF);
      } else {
        int k = -1;
        if (opsRecv && opsFnTightenable(F)) {
          // receiver position: the callsite arg that IS the base object
          for (unsigned ai = 0;
               ai < CS->arg_size() && ai < CF->arg_size(); ai++)
            if (CS->getArgOperand(ai)->stripPointerCasts() == opsRecv) {
              k = (int)ai;
              break;
            }
        }
        if (k >= 0) {
          g_opsTightSites++;
          if (opsPairWired.insert({F, k}).second) {
            // per-pair binding: F's receiver formal <- every certified
            // container of every table F belongs to (all certified, by
            // opsFnTightenable)
            Value *farg = CF->getArg(k);
            NodeIndex fk = getRepNodeForValue(farg);
            if (fk == AndersNodeFactory::InvalidIndex)
              fk = NF.createValueNode(farg);
            fk = getCanonicalNode(fk);
            for (auto &kv : opsPairs) {
              if (!kv.second.members.count(CF))
                continue;
              for (const Value *C2 : kv.second.containers) {
                NodeIndex cn = getRepNodeForValue(C2);
                if (cn == AndersNodeFactory::InvalidIndex)
                  cn = NF.createValueNode(const_cast<Value *>(C2));
                addAssignmentEdge(getCanonicalNode(cn), fk);
              }
            }
          }
          handleCall(CS, CF, k);
        } else {
          if (opsRecv)
            g_opsTightRej++;
          handleCall(CS, CF);
        }
      }
    }
  }
  if (CFLOpsPairs && (g_opsTightSites || g_opsTightRej))
    CG_LOG("OpsPairs LEDGER: tightened " << g_opsTightSites
           << " (callee,site) wirings so far, " << g_opsTightRej
           << " two-level rejections (untightenable/no-recv-arg)\n");
  if (protOn) {
    size_t cells = 0, waiting = 0;
    boost::unordered_flat_set<uint32_t> live;
    for (auto &kv : prot) {
      if (kv.second.cell != UINT32_MAX) {
        cells++;
        live.insert(find(kv.second.cell));
      }
      waiting += kv.second.waiting.size();
    }
    CG_LOG("ProtCells LEDGER: " << protRid.size() << " protected origins, "
           << cells << " cells materialized (" << live.size()
           << " distinct classes), " << protWriterMerges << " writer merges, "
           << protReaderBridges << " reader bridges (+" << protWaitAttached
           << " wait-attached), " << waiting << " readers still waiting, "
           << protDemotions << " demotions, " << protCollapses
           << " over-anchored cells collapsed (" << protPooledReaders
           << " readers pooled)\n");
  if (g_strataAblated)
    errs() << "StrataAblate: " << g_strataAblated
           << " phys-stratum inttoptr bridges severed "
              "[MEASUREMENT-ONLY UNSOUND]\n";
  if (protOn && !protWriterBlame.empty()) {
    std::vector<std::pair<size_t, const std::string *>> wr2;
    size_t wtot = 0;
    for (auto &kv : protWriterBlame) {
      wr2.emplace_back(kv.second, &kv.first);
      wtot += kv.second;
    }
    std::sort(wr2.begin(), wr2.end(), std::greater<>());
    errs() << "ProtWriters: " << wtot << " writer merges via "
           << protWriterBlame.size() << " distinct pre-merge identities\n";
    for (size_t i = 0; i < std::min<size_t>(40, wr2.size()); i++)
      errs() << "ProtWriters: " << wr2[i].first << "x " << *wr2[i].second
             << "\n";
  }
  if (protOn && !protCoalesceBlame.empty()) {
    std::vector<std::pair<size_t, const std::string *>> br2;
    size_t total2 = 0;
    for (auto &kv : protCoalesceBlame) {
      br2.emplace_back(kv.second.first, &kv.first);
      total2 += kv.second.first;
    }
    std::sort(br2.begin(), br2.end(), std::greater<>());
    errs() << "ProtCoalesce: " << total2 << " key-family fusions via "
           << protCoalesceBlame.size() << " distinct writer classes\n";
    for (size_t i = 0; i < std::min<size_t>(30, br2.size()); i++) {
      uint32_t bc = find(protCoalesceBlame[*br2[i].second].second);
      size_t facts = 0, bfacts = 0;
      for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
        facts += R[bc][s2].count();
        bfacts += RB[bc][s2].count();
      }
      size_t mem2 = 0;
      if (bc < toOrig.size()) {
        auto mit2 = canonicalClassMembers.find(toOrig[bc]);
        if (mit2 != canonicalClassMembers.end())
          mem2 = mit2->second.size();
      }
      auto aIt2 = protAnchor.find(bc);
      errs() << "ProtCoalesce: " << br2[i].first << "x " << *br2[i].second
             << "  [class c" << bc << ": members=" << mem2
             << " facts=" << facts << "+" << bfacts << "br outA="
             << outA[bc].size() << " cells=" << cellsOf[bc].size()
             << " keysAnchored="
             << (aIt2 == protAnchor.end() ? 0 : aIt2->second)
             << (protCollapsed.count(bc) ? " COLLAPSED" : "") << "]\n";
    }
  }
  }
  if (CFLProbeUserCopyAblate)
    errs() << "UserCopyAblate: " << g_userCopyAsmSevered
           << " copy-body + " << g_userGetAsmSevered
           << " get_user asm memory closures severed ("
           << g_userCopyDerefsSevered
           << " raw-ptr derefs) [MEASUREMENT-ONLY UNSOUND]\n";
  // NOTE probe/model LEDGER prints must live HERE, after the protOn
  // block closes — anything inside it only prints when protection is
  // active (the ops-pairs config), which the canonical config is not.
  if (NB > 0 && g_tagRoundTrips)
    CG_LOG("TagRoundTrip: " << g_tagRoundTrips
           << " ptrtoint wildcards suppressed (tag-bit-only closures)\n");
  if (g_sinkAblatedJoins)
    errs() << "SinkAblate: " << g_sinkAblatedJoins
           << " cluster joins skipped [MEASUREMENT-ONLY UNSOUND]\n";
  if (CFLSinkInstr) {
    assert(g_sinkContractChecked &&
           "sink arena ran without the read-back contract check");
    errs() << "SinkInstr: " << g_sinkArenaSites
           << " accessor callsites bound to opaque payload arenas (contract: "
           << g_sinkSitesConfirmed << " confirmed / " << g_sinkSitesEscaped
           << " escape / " << g_sinkSitesViolated << " violation)\n";
  }
  if (CFLCensusCouplers && !ownedMask.empty()) {
    errs() << "Couplers: " << weldEvents << " cross-subsystem welds / "
           << mergeEvents << " merges; subsystems: " << g_subsysNames.size()
           << "\n";
    std::vector<std::pair<uint64_t, const std::string *>> wb;
    for (auto &kv : weldBlame)
      wb.emplace_back(kv.second.first, &kv.first);
    std::sort(wb.begin(), wb.end(), std::greater<>());
    for (size_t i2 = 0; i2 < std::min<size_t>(30, wb.size()); i2++) {
      auto &e2 = weldBlame[*wb[i2].second];
      errs() << "Couplers: x" << e2.first << " ("
             << __builtin_popcountll(e2.second) << " subsys) "
             << *wb[i2].second << "\n";
      if (i2 < 6) {
        errs() << "Couplers:   subsystems:";
        for (unsigned b3 = 0; b3 < 63 && b3 < g_subsysNames.size(); b3++)
          if (e2.second & (1ull << b3))
            errs() << " " << g_subsysNames[b3];
        errs() << "\n";
        // sample the welded class's owned origins, one per subsystem
        auto rIt2 = g_weldRepOf.find(*wb[i2].second);
        if (rIt2 != g_weldRepOf.end()) {
          const uint32_t wrep = find(rIt2->second);
          uint64_t seen3 = 0;
          size_t shown3 = 0;
          for (uint32_t rid3 = 0; rid3 < nextRoot && shown3 < 14; rid3++) {
            if (funcRootOf.count(rid3)) continue;
            if (find(rootClassOf[rid3]) != wrep) continue;
            const Value *ov3 =
                NF.getValueForNode(toOrig[rootClassOf[rid3]]);
            const llvm::Module *om3 = nullptr;
            std::string on3 = "<synthetic>";
            if (ov3) {
              if (const auto *oi3 = dyn_cast<Instruction>(ov3)) {
                om3 = oi3->getModule();
                on3 = (oi3->getFunction()->getName() + "::" +
                       oi3->getOpcodeName()).str();
              } else if (const auto *og3 = dyn_cast<GlobalValue>(ov3)) {
                om3 = og3->getParent();
                on3 = og3->getName().str();
              }
            }
            uint8_t sb3 = subsysBitOf(om3);
            if (seen3 & (1ull << sb3)) continue;
            seen3 |= 1ull << sb3;
            shown3++;
            errs() << "Couplers:   origin[" << (om3 ? g_subsysNames[sb3]
                    : std::string("?")) << "] " << on3 << "\n";
          }
        }
      }
    }
    // Answer-side diversity: how many subsystems' DATA objects does
    // each icall operand class see at fixpoint?
    size_t h[9] = {0};
    for (auto *CS3 : Ctx->IndirectCallInsts) {
      NodeIndex fn3 = NF.getValueNodeFor(
          CS3->getCalledOperand()->stripPointerCastsAndAliases());
      if (fn3 == AndersNodeFactory::InvalidIndex) continue;
      auto dIt3 = toDense.find(getCanonicalNode(fn3));
      if (dIt3 == toDense.end()) continue;
      const uint32_t rep3 = find(dIt3->second);
      uint64_t m3 = 0;
      auto accum = [&](const FactSet &pl) {
        pl.forEach([&](uint32_t o3) {
          if (funcRootOf.count(o3)) return;
          const Value *ov3 = o3 < rootClassOf.size()
              ? NF.getValueForNode(toOrig[rootClassOf[o3]]) : nullptr;
          const llvm::Module *om3 = nullptr;
          if (ov3) {
            if (const auto *oi3 = dyn_cast<Instruction>(ov3))
              om3 = oi3->getModule();
            else if (const auto *og3 = dyn_cast<GlobalValue>(ov3))
              om3 = og3->getParent();
          }
          m3 |= 1ull << subsysBitOf(om3);
        });
      };
      accum(R[rep3][0]);
      accum(RB[rep3][0]);
      int pc3 = __builtin_popcountll(m3);
      h[pc3 >= 8 ? 8 : pc3]++;
    }
    errs() << "Couplers: icall-operand data-subsystem diversity:";
    for (int i3 = 0; i3 < 9; i3++)
      errs() << " [" << i3 << (i3 == 8 ? "+" : "") << "]=" << h[i3];
    errs() << "\n";
    for (size_t i3 = 0; i3 < g_subsysNames.size() && i3 < 40; i3++)
      errs() << "Couplers: subsys " << i3 << " = " << g_subsysNames[i3]
             << "\n";
  }
  if (CFLTracepointKeys) {
    errs() << "TracepointKeys: " << g_tpKeyConstBinds << " const binds + "
           << g_tpKeyMediatorBinds << " walker pairs ("
           << g_tpWalkerKeys.size() << " keys, "
           << g_tpKeyMediatorDataPools << " mediator data pools), "
           << g_tpKeyDispatchWires << " __traceiter dispatches wired, "
           << g_tpKeyIterLoadsSevered << " iterator funcs-loads severed, "
           << g_tpKeyModelAnswered << " sites model-answered ("
           << g_tpKeyTypeRej << " type-rejected probes); "
           << "UNCLASSIFIED reg sites " << g_tpKeyUnclassified
           << ", keyless iters " << g_tpKeyKeylessIter << ", unmapped keys "
           << g_tpKeyUnmapped << ", dyn-probe keys " << g_tpKeyDynProbe
           << " -> " << g_tpKeyFallbackSites
           << " fallback sites (all must be 0 for the severed model to "
           << "be complete)\n";
  }
  if (CFLStaticOpsTables) {
    errs() << "StaticOpsTables: " << g_sctKeyTable.size() << " keys tabled ("
           << g_sctUpdConst << " const + " << g_sctUpdLoad
           << " load-shaped updates), " << g_sctSitesModelAnswered
           << " __SCT__ sites model-answered (" << g_sctTypeRej
           << " type-mismatched entries KEPT); " << g_sctUpdNonconform
           << " non-conforming updates -> " << g_sctKeyUntabled.size()
           << " untabled keys, " << g_sctSitesUntabled
           << " sites kept graph behavior, " << g_sctPendingNoTable
           << " pendings without a fn source\n";
  }
  if (CFLProbeBlobFormation) {
    uint32_t giant = 0;
    for (uint32_t n2 = 0; n2 < N; n2++)
      if (find(n2) == n2 && clsSize[n2] > clsSize[giant])
        giant = n2;
    errs() << "BlobForm: FINAL giant class c" << giant
           << " size=" << clsSize[giant] << " (" << blobEvents.size()
           << " events logged)\n";
    std::map<std::string, std::pair<size_t, uint64_t>> byCtx; // n, mass
    std::map<std::string, uint64_t> byFeeder;                 // absorbed
    size_t shown = 0, giantEvents = 0;
    for (const BlobEv &ev : blobEvents) {
      if (find(ev.keeper) != giant)
        continue;
      giantEvents++;
      std::string ck = ev.ctx;
      if (!ev.origin.empty())
        ck += ":" + ev.origin;
      auto &ce = byCtx[ck];
      ce.first++;
      ce.second += std::min(ev.szA, ev.szB);
      byFeeder[ev.szA < ev.szB ? ev.nA : ev.nB] +=
          std::min(ev.szA, ev.szB);
      if (shown < 60) {
        shown++;
        errs() << "BlobForm: EV " << ev.ctx
               << (ev.origin.empty() ? "" : (" origin=" + ev.origin))
               << " " << ev.szA << "<" << ev.nA.substr(0, 50) << "> + "
               << ev.szB << "<" << ev.nB.substr(0, 50) << ">\n";
      }
    }
    errs() << "BlobForm: " << giantEvents
           << " logged events fed the giant; by channel:\n";
    std::vector<std::pair<uint64_t, const std::string *>> cr2;
    for (auto &kv : byCtx)
      cr2.emplace_back(kv.second.second, &kv.first);
    std::sort(cr2.begin(), cr2.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(25, cr2.size()); i++)
      errs() << "BlobForm: channel " << *cr2[i].second << " events="
             << byCtx[*cr2[i].second].first << " absorbed-mass=" << cr2[i].first
             << "\n";
    std::vector<std::pair<uint64_t, const std::string *>> fr2;
    for (auto &kv : byFeeder)
      fr2.emplace_back(kv.second, &kv.first);
    std::sort(fr2.begin(), fr2.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(25, fr2.size()); i++)
      errs() << "BlobForm: feeder " << *fr2[i].second << " absorbed="
             << fr2[i].first << "\n";
  }
  if (CFLCertUserCopy) {
    // Match cert rids by their MINTED class (pre-merge): post-merge
    // matching would blame every foreign root whose class later merged
    // with a U class. rootClassOf holds the class at mint time, and
    // the U objects are minted before any solve-time union.
    boost::unordered_flat_map<uint32_t, std::vector<const std::string *>>
        certMintSites; // minted dense class -> site labels
    for (auto &p : g_userCertObjs) {
      auto dIt = toDense.find(getCanonicalNode(p.first));
      if (dIt == toDense.end()) continue;
      certMintSites[dIt->second].push_back(&p.second);
    }
    std::vector<std::pair<uint32_t, uint32_t>> certRids; // (rid, mint cls)
    size_t certMergedAway = 0;
    for (uint32_t rid = 0; rid < nextRoot; rid++) {
      auto cIt = certMintSites.find(rootClassOf[rid]);
      if (cIt == certMintSites.end()) continue;
      certRids.emplace_back(rid, rootClassOf[rid]);
      // A U class merged into a bigger class means its rid now rides
      // that class's whole downstream — inventory becomes coarse.
      if (find(rootClassOf[rid]) != rootClassOf[rid] ||
          clsSize[find(rootClassOf[rid])] > 1)
        certMergedAway++;
    }
    size_t crossIcalls = 0, checkedIcalls = 0, shown = 0;
    std::map<std::string, size_t> crossBySite; // site label -> icall count
    for (auto *CS2 : Ctx->IndirectCallInsts) {
      Value *fp2 = CS2->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn2 = NF.getValueNodeFor(fp2);
      if (fn2 == AndersNodeFactory::InvalidIndex) continue;
      auto dIt2 = toDense.find(getCanonicalNode(fn2));
      if (dIt2 == toDense.end()) continue;
      const uint32_t rep2 = find(dIt2->second);
      checkedIcalls++;
      bool hit = false;
      for (auto [rid, mc] : certRids) {
        bool has = false;
        for (uint32_t s2 = 0; s2 < NSHIFT && !has; s2++)
          has = R[rep2][s2].test(rid) || RB[rep2][s2].test(rid);
        if (!has) continue;
        hit = true;
        for (const std::string *sd : certMintSites[mc]) {
          crossBySite[*sd]++;
          if (shown < 40) {
            shown++;
            errs() << "UserCert: CROSSING icall in "
                   << CS2->getFunction()->getName() << " <- " << *sd << "\n";
          }
        }
      }
      if (hit) crossIcalls++;
    }
    errs() << "UserCert: " << g_userCertCopySites << " copy-body + "
           << g_userCertGetSites << " get_user sites tagged, "
           << certRids.size() << " cert roots live";
    if (certMergedAway)
      errs() << " (" << certMergedAway
             << " U classes merged into bigger classes — coarse blame)";
    errs() << "; " << crossIcalls << "/" << checkedIcalls
           << " icall fptr operands carry user bytes\n";
    size_t siteShown = 0;
    for (auto &kv : crossBySite) {
      if (siteShown++ >= 30) {
        errs() << "UserCert: ... " << (crossBySite.size() - 30)
               << " more sites\n";
        break;
      }
      errs() << "UserCert: site " << kv.first << " reaches " << kv.second
             << " icalls\n";
    }
  }
  if (CFLProbeOpsMono && omSites) {
    errs() << "OpsMono: " << omSites << " two-level dispatch sites: "
           << omMono << " mono (targets inside ONE ops global), " << omNear
           << " near (<=2 extras), " << omPoly << " polymorphic, "
           << omNoOps << " no-ops-member; " << opsMembers.size()
           << " ops globals (>=2 fns)\n";
    std::vector<std::pair<size_t, const GlobalVariable *>> gr;
    for (auto &[G, N] : omMonoByG) gr.emplace_back(N, G);
    std::sort(gr.begin(), gr.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(15, gr.size()); i++)
      errs() << "OpsMono: mono-certified " << gr[i].second->getName()
             << " sites=" << gr[i].first << " members="
             << opsMembers[gr[i].second].size() << "\n";
    for (auto &[cs2, n] : omPolySample)
      errs() << "OpsMono: POLY |T|=" << n << " at "
             << cs2->getFunction()->getName() << "\n";
  }
  if (CFLProbeOriginSplit) {
    std::sort(osTop.begin(), osTop.end(),
              [](auto &a, auto &b) { return std::get<0>(a) > std::get<0>(b); });
    errs() << "OriginSplit: " << osIcalls << " load-shaped icalls probed ("
           << osNoLoad << " non-load fptr, " << osNoOrigin
           << " no container origin); pooled pairs " << osPooled
           << " vs origin-indexed " << osSplit << " ("
           << (osPooled ? 100.0 * (osPooled - osSplit) / osPooled : 0.0)
           << "% excess); cluster diversity D==1: " << osD1
           << ", 2-4: " << osD24 << ", >4: " << osDbig << "\n";
    for (size_t i = 0; i < std::min<size_t>(15, osTop.size()); i++) {
      auto &[ex, cs2, a, sp, d] = osTop[i];
      errs() << "OriginSplit: excess=" << ex << " |A|=" << a << " split="
             << sp << " D=" << d << " at "
             << cs2->getFunction()->getName() << "\n";
    }
  }
  if (CFLCensusIcallShape && !shapeFams.empty()) {
    std::vector<std::pair<size_t, const std::string *>> fr;
    size_t totP = 0, totS = 0;
    for (auto &kv : shapeFams) {
      fr.emplace_back(kv.second.pairs, &kv.first);
      totP += kv.second.pairs;
      totS += kv.second.sites;
    }
    std::sort(fr.begin(), fr.end(), std::greater<>());
    errs() << "IcallShape: " << totS << " fat sites (>=100 tgts) / "
           << totP << " pairs in " << shapeFams.size() << " families\n";
    for (size_t i2 = 0; i2 < std::min<size_t>(40, fr.size()); i2++) {
      auto &fam = shapeFams[*fr[i2].second];
      errs() << "IcallShape: " << fam.pairs << " pairs / " << fam.sites
             << " sites (" << fam.giantSites << " giant-cls) "
             << *fr[i2].second << "  e.g. " << fam.exemplar << "\n";
    }
    // Giant anatomy (task #38): fn identity is destroyed by TWO distinct
    // mechanisms — fn value CLASSES union-find-merged into the giant
    // (class-identity destruction) vs fn ROOTS accumulated into
    // R[giant] by fact propagation (every real flow into any cell the
    // giant absorbed). The forensics and the injection points differ,
    // so count them separately.
    if (censusGiantRep != UINT32_MAX) {
      const uint32_t gr = find(censusGiantRep);
      size_t fnClasses = 0, fnClassesInGiant = 0;
      std::vector<StringRef> ex;
      for (auto &kv : funcOfCanon) {
        auto dIt2 = toDense.find(kv.first);
        if (dIt2 == toDense.end())
          continue;
        fnClasses++;
        if (find(dIt2->second) == gr) {
          fnClassesInGiant++;
          if (ex.size() < 12)
            ex.push_back(kv.second->getName());
        }
      }
      size_t rootsInGiant = 0, fnRootsInGiant = 0;
      R[gr][0].forEach([&](uint32_t o) {
        rootsInGiant++;
        if (funcRootOf.count(o))
          fnRootsInGiant++;
      });
      errs() << "GiantAnatomy: rep c" << gr << " members " << clsSize[gr]
             << "; fn CLASSES merged in " << fnClassesInGiant << "/"
             << fnClasses << " address-taken; R[giant] roots "
             << rootsInGiant << " of which " << fnRootsInGiant
             << " are fn roots\n";
      for (StringRef n2 : ex)
        errs() << "GiantAnatomy: merged-fn-class " << n2 << "\n";
      // Entry-cell histogram: fn identities reach the giant through
      // their FIRST-HOP a-edge targets (exemplar acct_pin_kill: one
      // store into the fs_pin cell chain, already giant-merged). Count
      // the DISTINCT giant-member entry classes over all fn roots —
      // few nameable channels => targeted guards; thousands => the
      // full provenance-cells redesign.
      {
        boost::unordered_flat_set<uint32_t> fnDense;
        for (auto &kv : funcOfCanon) {
          auto dIt3 = toDense.find(kv.first);
          if (dIt3 != toDense.end())
            fnDense.insert(dIt3->second);
        }
        boost::unordered_flat_map<uint32_t, uint32_t> entryFnCount;
        size_t fnEdges = 0, fnEdgesToGiant = 0;
        for (auto [s2, t2] : aEdges) {
          if (!fnDense.count(s2))
            continue;
          fnEdges++;
          if (find(t2) != gr)
            continue;
          fnEdgesToGiant++;
          entryFnCount[t2]++;
        }
        auto entryName = [&](uint32_t cls) -> std::string {
          const Value *V2 =
              cls < toOrig.size() ? NF.getValueForNode(toOrig[cls]) : nullptr;
          if (!V2)
            return "<synthetic>";
          if (V2->hasName())
            return V2->getName().str();
          if (const auto *I3 = dyn_cast<Instruction>(V2))
            return (I3->getFunction()->getName() + "::" +
                    I3->getOpcodeName())
                .str();
          return "<unnamed>";
        };
        std::vector<std::pair<uint32_t, uint32_t>> top;
        for (auto &kv : entryFnCount)
          top.emplace_back(kv.second, kv.first);
        std::sort(top.begin(), top.end(), std::greater<>());
        errs() << "GiantAnatomy: fn out-a edges " << fnEdges << ", into "
               << "giant " << fnEdgesToGiant << " via "
               << entryFnCount.size() << " distinct entry classes\n";
        for (size_t i3 = 0; i3 < std::min<size_t>(30, top.size()); i3++)
          errs() << "GiantAnatomy: entry x" << top[i3].first << " c"
                 << top[i3].second << " " << entryName(top[i3].second)
                 << "\n";
      }
    }
  }
  CG_LOG("FlowsTo: resolved " << resolved << " icalls, "
         << totalTargets << " targets (" << newPairs << " new pairs wired, "
         << topOnlyPairs << " via wildcard plane only), iteration "
         << (iteration + fpIter) << "\n");
  if (CFLProbeRodataJoins)
    CG_LOG("RodataProbe: " << g_rodataJoinsSkipped
           << " joins skipped for rodata-bearing witness classes "
           << "(MEASUREMENT-ONLY over-removal)\n");
  CG_LOG("FilterStats: " << filtCandidates << " CFL candidates, "
         << filtTypeRej << " type-rejected, " << filtFieldRej
         << " field-rejected (each rejection = unsoundness exposure; "
         << "zero = filter retirable)\n");
  if (newPairs == 0) {
    // Lazy-mint catch-up: the A-loop cannot admit CYCLIC witness
    // dependences — e.g. circular list_head chains, where each node's
    // join needs the neighbor's merge for its consequence path to
    // reach an fptr (whole-kernel evidence: tcp_ulp/9p-transport ops
    // registration lists, -5737 pairs without this). At convergence,
    // mint EVERY still-deferred root and drain to the closure over
    // the full root set — by confluence of the monotone rules this is
    // exactly the eager fixpoint, so answers are identical by
    // construction; the restricted middle iterations keep their win.
    if (!lazyDeferred.empty()) {
      const size_t nDef = lazyDeferred.size();
      size_t minted = 0;
      for (uint32_t c : lazyDeferred) {
        uint32_t rep = find(c);
        if (!isRoot[rep]) { mintRoot(rep); minted++; }
      }
      lazyDeferred.clear();
      flushCtx(ctx0);
      CG_LOG("LazyMint: CATCH-UP minted " << minted << "/" << nDef
             << " deferred roots at convergence (cyclic witness "
             << "dependences are unreachable by the A-loop); draining "
             << "to the full closure\n");
      fpIter++;
      continue; // re-drain with the full root set, then re-resolve
    }
    break; // converged: no callee flows were added
  }
  if (iteration + fpIter + 1 >= (int)CFLFlowsToMaxIters) {
    WARNING("[UNSOUND-RISK] FlowsTo fixpoint hit iteration cap ("
            << CFLFlowsToMaxIters.getValue() << ") with " << newPairs
            << " newly wired pairs unprocessed; results may miss flows "
            << "through those callees\n");
    break;
  }
  if (!CFLFlowsToIncremental)
    return true; // from-scratch mode: driver rebuilds and re-solves
  wireIncremental(edgesConsumed);
  edgesConsumed = edges.size();
  fpIter++;
  } // outer resolution fixpoint

  // Reduce per-thread counters into the reporting totals.
  uint64_t cyJoin = 0, cyBridge = 0, cyScan = 0, cyW = 0, cyA = 0, cyF = 0;
  uint64_t nJoinLk = 0, nAOr = 0, nFOr = 0, orWords = 0;
  for (auto &c : ctxs) {
    cyJoin += c.cyJoin; cyBridge += c.cyBridge; cyScan += c.cyScan;
    cyW += c.cyW; cyA += c.cyA; cyF += c.cyF;
    nJoinLk += c.nJoinLk; nAOr += c.nAOr; nFOr += c.nFOr;
    orWords += c.orWords;
    sweepOffered += c.sweepOffered;
    sweepKept += c.sweepKept;
  }
  if (prof) {
    const uint64_t cyTot = cyJoin + cyBridge + cyScan + cyW + cyA + cyF;
    auto pct = [&](uint64_t c) { return cyTot ? (double)c * 100.0 / cyTot : 0.0; };
    errs() << "SolverProf: total " << cyTot << " cycles in pop loop\n";
    errs() << "SolverProf: join   " << cyJoin << " (" << pct(cyJoin)
           << "%), lookups " << nJoinLk << " (seq sub-phase " << seqJoinCy
           << ", merge " << cyMerge << " cycles)\n";
    errs() << "SolverProf: bridge " << cyBridge << " (" << pct(cyBridge) << "%)\n";
    errs() << "SolverProf: scan   " << cyScan << " (" << pct(cyScan) << "%)\n";
    errs() << "SolverProf: wflag  " << cyW << " (" << pct(cyW) << "%)\n";
    errs() << "SolverProf: a-prop " << cyA << " (" << pct(cyA)
           << "%), ORs " << nAOr << "\n";
    errs() << "SolverProf: f-prop " << cyF << " (" << pct(cyF)
           << "%), ORs " << nFOr << ", a-plane words " << orWords << "\n";
  }

  // Name the hub/web culprits: widest classes (fact volume, fan-out
  // amplifiers like void* container formals and allocator returns) and
  // merge-churn centers (container webs whose cluster coalescing drives
  // the convergence tail).
  if (VerboseLevel >= 2) {
    std::vector<uint32_t> memberCnt(N, 0);
    for (uint32_t i = 0; i < N; i++) memberCnt[find(i)]++;
    auto describe = [&](uint32_t n) {
      const Value *V = NF.getValueForNode(toOrig[n]);
      if (const auto *Arg = dyn_cast_or_null<Argument>(V))
        errs() << Arg->getParent()->getName().substr(0, 60) << "::arg"
               << Arg->getArgNo();
      else if (V && V->hasName())
        errs() << V->getName().substr(0, 70);
      else if (const auto *I = dyn_cast_or_null<Instruction>(V))
        errs() << I->getFunction()->getName().substr(0, 50) << "::"
               << I->getOpcodeName();
      else
        errs() << (NF.isObjectNode(toOrig[n]) ? "<obj/cell>" : "<synthetic>");
    };
    auto dumpTop = [&](const char *tag, auto keyOf) {
      std::vector<std::pair<uint64_t, uint32_t>> ranked;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n) continue;
        uint64_t k = keyOf(n);
        if (k) ranked.emplace_back(k, n);
      }
      size_t K = std::min<size_t>(20, ranked.size());
      std::partial_sort(ranked.begin(), ranked.begin() + K, ranked.end(),
                        std::greater<>());
      for (size_t i = 0; i < K; i++) {
        auto [k, n] = ranked[i];
        uint64_t f = 0;
        for (uint32_t s = 0; s < NSHIFT; s++)
          f += R[n][s].count() + RB[n][s].count();
        errs() << tag << ": c" << n << " facts=" << f
               << " merges=" << mergeHits[n] << " members=" << memberCnt[n]
               << " cells=" << cellsOf[n].size()
               << " outA=" << outA[n].size()
               << (wflag[n] ? " wflag " : " ");
        describe(n);
        errs() << "\n";
      }
    };
    dumpTop("TopClass", [&](uint32_t n) {
      uint64_t f = 0;
      for (uint32_t s = 0; s < NSHIFT; s++)
        f += R[n][s].count() + RB[n][s].count();
      return f;
    });
    dumpTop("TopMerge", [&](uint32_t n) { return (uint64_t)mergeHits[n]; });
    dumpTop("TopPop", [&](uint32_t n) { return (uint64_t)popCount[n]; });
    // Sample absorbed members of the top merge-churn classes: these name
    // the web constructs (list helpers, registries, alloc wrappers) that
    // ContainerFuncs/AllocFuncs coverage should summarize away.
    {
      std::vector<std::pair<uint64_t, uint32_t>> byMerge;
      for (uint32_t n = 0; n < N; n++)
        if (find(n) == n && mergeHits[n])
          byMerge.emplace_back(mergeHits[n], n);
      size_t K = std::min<size_t>(8, byMerge.size());
      std::partial_sort(byMerge.begin(), byMerge.begin() + K, byMerge.end(),
                        std::greater<>());
      std::unordered_map<uint32_t, std::vector<uint32_t>> samples;
      for (size_t i = 0; i < K; i++) samples[byMerge[i].second] = {};
      for (uint32_t i = 0; i < N && !samples.empty(); i++) {
        uint32_t r = find(i);
        if (r == i) continue;
        auto sIt = samples.find(r);
        if (sIt != samples.end() && sIt->second.size() < 4)
          sIt->second.push_back(i);
      }
      for (size_t i = 0; i < K; i++) {
        uint32_t n = byMerge[i].second;
        errs() << "MergeMembers c" << n << " (" << mergeHits[n] << "):";
        for (uint32_t m : samples[n]) {
          errs() << "  [";
          describe(m);
          errs() << "]";
        }
        errs() << "\n";
      }
    }
    // Cluster-transitivity audit: union-find clusters are coarser-or-equal
    // vs the grammar's per-witness M; multi-key clusters and transitive
    // key-coalescing merges bound the over-approximation (Lean gap F3).
    {
      std::unordered_map<uint32_t, uint32_t> keysPer;
      for (auto &[k, rep] : clusterRep) keysPer[find(rep)]++;
      uint64_t multi = 0, maxK = 0;
      for (auto &[cls, kc] : keysPer) {
        if (kc > 1) multi++;
        maxK = std::max<uint64_t>(maxK, kc);
      }
      errs() << "ClusterTrans: " << clusterCount() << " keys in "
             << keysPer.size() << " clusters, multi-key clusters " << multi
             << ", max keys/cluster " << maxK
             << ", transitive key-coalescing merges " << transKeyMerges
             << "\n";
    }
    errs() << "ChurnStats: merges join=" << mergesFromJoin
           << " scc=" << mergesFromSCC
           << ", redundant join lookups " << redundantJoins
           << ", merge-reoffered " << reofferedFacts
           << " facts, sweeps offered " << sweepOffered << " kept "
           << sweepKept
           << " (volume fields need --cfl-solver-profile)\n";
  }

  if (traceRoot >= 0) {
    errs() << "TRACE final reach of root " << traceRoot << " ("
           << traceEvents << " events):\n";
    unsigned shown = 0;
    for (uint32_t n = 0; n < N && shown < 100000; n++) {
      if (find(n) != n) continue;
      for (uint32_t s = 0; s < NSHIFT; s++) {
        bool inR = R[n][s].test((uint32_t)traceRoot);
        bool inB = RB[n][s].test((uint32_t)traceRoot);
        if (!inR && !inB) continue;
        errs() << "TRACE reach c" << n << " s" << s << (inB ? " [br]" : "")
               << " ";
        const Value *V = NF.getValueForNode(toOrig[n]);
        if (V && V->hasName()) errs() << V->getName();
        else if (V) {
          if (const auto *I = dyn_cast<Instruction>(V))
            errs() << I->getFunction()->getName() << "::" << I->getOpcodeName();
        }
        errs() << "\n";
        shown++;
      }
    }
  }

  if (!CFLTraceValue.empty()) {
    for (auto &Mpair : Ctx->Modules) {
      for (Function &F2 : *Mpair.first) {
        if (!F2.getName().contains(CFLTraceValue) || F2.isDeclaration())
          continue;
        errs() << "TRACE-VAL fn " << F2.getName() << "\n";
        auto dumpV = [&](const Value *V3, const char *tag) {
          NodeIndex vn = NF.getValueNodeFor(V3);
          if (vn == AndersNodeFactory::InvalidIndex) return;
          auto dIt2 = toDense.find(getCanonicalNode(vn));
          if (dIt2 == toDense.end()) { errs() << "TRACE-VAL  " << tag
              << " <not-in-graph>\n"; return; }
          uint32_t cl2 = find(dIt2->second);
          errs() << "TRACE-VAL  " << tag << " c" << cl2 << " facts:";
          size_t fShown = 0;
          for (uint32_t s4 = 0; s4 < NSHIFT && fShown <= 10; s4++) {
            R[cl2][s4].forEach([&](uint32_t o4) {
              if (fShown > 10) return;
              if (fShown++ == 10) { errs() << " ..."; return; }
              errs() << " (r" << o4 << ",s" << s4 << ")";
            });
          }
          bool hasTr2 = false;
          if (traceRoot >= 0)
            for (uint32_t s4 = 0; s4 < NSHIFT && !hasTr2; s4++)
              hasTr2 = R[cl2][s4].test((uint32_t)traceRoot) ||
                       RB[cl2][s4].test((uint32_t)traceRoot);
          errs() << " traced=" << hasTr2 << " cells:" << cellsOf[cl2].size()
                 << "\n";
        };
        for (const Argument &A3 : F2.args()) {
          if (!A3.getType()->isPointerTy()) continue;
          std::string as = ("arg" + std::to_string(A3.getArgNo()));
          dumpV(&A3, as.c_str());
        }
        for (const Instruction &I3 : instructions(F2)) {
          if (!containsPointerType(I3.getType())) continue;
          std::string is;
          llvm::raw_string_ostream oss(is);
          oss << I3;
          dumpV(&I3, is.substr(0, 90).c_str());
        }
      }
    }
  }

  // --cfl-cotravel-stats: bound the root-bundling win. Roots whose
  // (class, shift) incidence columns are identical could share one plane
  // bit; classes whose fact sets are identical could share plane storage.
  // Hashes are Zobrist-style (XOR of mixed cell keys) — set-equality up
  // to 64-bit collisions, adequate for a sizing diagnostic. R only; RB
  // (bridged) planes are excluded.
  // --cfl-root-relevance: how many of the minted roots does the ANSWER
  // actually need? A root matters only as (a) a function root read at an
  // icall fptr plane, or (b) a merge witness whose merged class lies on a
  // backward flow path (reverse a/f edges + bridges over the final
  // quotient graph) from some fptr class. {all function roots} union
  // {ancestor merge witnesses} is a sufficient set to reproduce this
  // run's resolution — the demand-driven-roots upper bound.
  if (CFLRootRelevance) {
    // Backward-reachable (ancestor) classes from all icall fptr classes.
    std::vector<std::vector<uint32_t>> rin(N);
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue;
      for (uint32_t t : outA[n]) {
        uint32_t tt = find(t);
        if (tt != n) rin[tt].push_back(n);
      }
      for (auto [t, r] : outF[n]) {
        uint32_t tt = find(t);
        if (tt != n) rin[tt].push_back(n);
      }
    }
    std::vector<char> anc(N, 0);
    std::vector<uint32_t> bfs;
    size_t fptrClasses = 0;
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto dIt = toDense.find(getCanonicalNode(fn));
      if (dIt == toDense.end()) continue;
      uint32_t rep = find(dIt->second);
      if (!anc[rep]) { anc[rep] = 1; bfs.push_back(rep); fptrClasses++; }
    }
    while (!bfs.empty()) {
      uint32_t n = bfs.back();
      bfs.pop_back();
      for (uint32_t p2 : rin[n])
        if (!anc[p2]) { anc[p2] = 1; bfs.push_back(p2); }
      for (uint32_t br : bridgesOf[n]) { // pairwise exchange: both ways
        uint32_t bb = find(br);
        if (!anc[bb]) { anc[bb] = 1; bfs.push_back(bb); }
      }
    }
    size_t ancClasses = 0, liveCls = 0;
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue;
      liveCls++;
      if (anc[n]) ancClasses++;
    }
    // Answer roots: function roots present at some fptr class's answer
    // planes (shift 0 and X, native or bridged) — what resolution reads.
    std::vector<char> isAns(nextRoot, 0), isWitAny(nextRoot, 0),
        isWitAnc(nextRoot, 0);
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n || !anc[n]) continue; // fptr classes are ancestors
      // (only fptr classes need scanning, but ancestor scan is cheap and
      // fptr membership is a subset; restrict via a second mark instead)
    }
    for (auto *CS : Ctx->IndirectCallInsts) {
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto dIt = toDense.find(getCanonicalNode(fn));
      if (dIt == toDense.end()) continue;
      uint32_t rep = find(dIt->second);
      auto mark = [&](const FactSet &pl) {
        pl.forEach([&](uint32_t o) {
          if (funcRootOf.count(o)) isAns[o] = 1;
        });
      };
      mark(R[rep][0]);
      mark(RB[rep][0]);
      if (NB > 0) {
        mark(R[rep][SHIFT_X]);
        mark(RB[rep][SHIFT_X]);
      }
    }
    for (auto &[o, keeper] : mergeWitness) {
      isWitAny[o] = 1;
      if (anc[find(keeper)]) isWitAnc[o] = 1;
    }
    // Fact mass per category over the final planes.
    std::vector<char> inSuff(nextRoot, 0);
    for (auto &[rid, F] : funcRootOf) inSuff[rid] = 1;
    size_t funcRoots = funcRootOf.size();
    for (uint32_t o = 0; o < nextRoot; o++)
      if (isWitAnc[o]) inSuff[o] = 1;
    uint64_t factsTotal = 0, factsSuff = 0;
    size_t nAns = 0, nWitAny = 0, nWitAnc = 0, nSuff = 0;
    for (uint32_t o = 0; o < nextRoot; o++) {
      nAns += isAns[o];
      nWitAny += isWitAny[o];
      nWitAnc += isWitAnc[o];
      nSuff += inSuff[o];
    }
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue;
      for (uint32_t s = 0; s < NSHIFT; s++) {
        auto tally = [&](const FactSet &pl) {
          pl.forEach([&](uint32_t o) {
            factsTotal++;
            if (inSuff[o]) factsSuff++;
          });
        };
        tally(R[n][s]);
        tally(RB[n][s]);
      }
    }
    errs() << "RootRel: " << nextRoot << " roots minted; " << funcRoots
           << " function, " << nAns << " read at icall planes\n";
    errs() << "RootRel: fptr-ancestor classes " << ancClasses << "/"
           << liveCls << " live (" << fptrClasses << " fptr classes)\n";
    errs() << "RootRel: merge witnesses " << nWitAny << " any, " << nWitAnc
           << " on fptr-ancestor classes (of " << mergeWitness.size()
           << " witnessed merges)\n";
    errs() << "RootRel: SUFFICIENT SET " << nSuff << "/" << nextRoot
           << " roots (" << (nextRoot ? 100.0 * nSuff / nextRoot : 0.0)
           << "%), fact mass " << factsSuff << "/" << factsTotal << " ("
           << (factsTotal ? 100.0 * factsSuff / factsTotal : 0.0)
           << "%) — demand-driven upper bound\n";
  }

  // --cfl-conflation-report: rank FUNCTIONS (not classes) as candidates
  // for the summary/clone pipeline (task #17). Two tables:
  //  Conflate:    shared-formal conflation — callers x facts resident in
  //               a pointer-formal's class. This product is what a
  //               per-callsite summary or clone would de-mix (the
  //               sort/__static_call_update/kmemdup channel). Facts are
  //               counted on the formal's MERGED class, so they are an
  //               upper bound for the formal itself — fine for ranking.
  //  AllocSpread: identity spread of each allocation-site root — how
  //               many live classes carry it, attributed to the wrapper
  //               function owning the callsite and its caller count
  //               (one internal site serving many callers = the
  //               t_allocinit/kmemdup conflation shape).
  // The report is the input queue for the offline proposer+confirmer
  // loop: symptomatic AND summary-confirmable -> summarize; symptomatic
  // and not -> clone candidate (#17); neither -> leave the body alone.
  if (CFLConflationReport) {
    auto tConf = std::chrono::steady_clock::now();
    std::unordered_map<const Function *, uint32_t> callerCnt;
    for (auto &ce : Ctx->Callees)
      for (const Function *tf : ce.second) callerCnt[tf]++;
    auto classFacts = [&](uint32_t rep) {
      uint64_t f = 0;
      for (uint32_t s = 0; s < NSHIFT; s++)
        f += R[rep][s].count() + RB[rep][s].count();
      return f;
    };
    auto denseRepOf = [&](NodeIndex v) -> int64_t {
      if (v == AndersNodeFactory::InvalidIndex) return -1;
      auto dIt = toDense.find(getCanonicalNode(v));
      if (dIt == toDense.end()) return -1;
      return (int64_t)find(dIt->second);
    };
    // Table 1: shared-formal conflation, GROUPED BY CLASS — hub classes
    // absorb thousands of formals, so per-function rows would print one
    // mega-class fifty times. Each row = one class: its fact mass, total
    // caller weight of the functions whose formals live in it, and the
    // top member functions (the de-mix targets).
    struct HubRow {
      uint64_t facts = 0, callerWeight = 0;
      std::vector<std::pair<uint32_t, const Function *>> members; // callers
    };
    std::unordered_map<uint32_t, HubRow> hubs;
    size_t fnRows = 0;
    for (auto &cc : callerCnt) {
      const Function *F2 = cc.first;
      if (!F2 || F2->isDeclaration()) continue;
      int64_t best = -1;
      uint64_t bestF = 0;
      for (const Argument &A2 : F2->args()) {
        if (!A2.getType()->isPointerTy()) continue;
        int64_t rep = denseRepOf(NF.getValueNodeFor(&A2));
        if (rep < 0) continue;
        uint64_t f = classFacts((uint32_t)rep);
        if (f > bestF) { bestF = f; best = rep; }
      }
      {
        int64_t rep = denseRepOf(NF.getReturnNodeFor(F2));
        if (rep >= 0) {
          uint64_t f = classFacts((uint32_t)rep);
          if (f > bestF) { bestF = f; best = rep; }
        }
      }
      if (best < 0 || bestF == 0) continue;
      fnRows++;
      HubRow &h = hubs[(uint32_t)best];
      h.facts = bestF;
      h.callerWeight += cc.second;
      h.members.emplace_back(cc.second, F2);
    }
    std::vector<std::pair<uint64_t, uint32_t>> hubRank;
    for (auto &hv : hubs)
      hubRank.emplace_back(hv.second.facts * hv.second.callerWeight,
                           hv.first);
    size_t K1 = std::min<size_t>(25, hubRank.size());
    std::partial_sort(hubRank.begin(), hubRank.begin() + K1, hubRank.end(),
                      std::greater<>());
    errs() << "Conflate: " << fnRows << " called+defined functions with "
           << "fact-bearing pointer formals/ret in " << hubs.size()
           << " classes; top " << K1 << " classes by facts x callerWeight:\n";
    for (size_t i = 0; i < K1; i++) {
      HubRow &h = hubs[hubRank[i].second];
      std::sort(h.members.begin(), h.members.end(),
                [](auto &a, auto &b) { return a.first > b.first; });
      errs() << "Conflate: c" << hubRank[i].second << " facts=" << h.facts
             << " memberFns=" << h.members.size() << " callerWeight="
             << h.callerWeight << " top:";
      for (size_t j = 0; j < std::min<size_t>(6, h.members.size()); j++)
        errs() << " " << h.members[j].second->getName() << "("
               << h.members[j].first << ")";
      errs() << "\n";
    }
    // Hub decomposition: for the top classes, histogram the member
    // values by CONTAINING FUNCTION and kind. The functions whose
    // instructions/cells dominate a hub's membership are the GLUERS —
    // the tiny utilities whose formals/loads bridged thousands of
    // otherwise-unrelated formals into one class (the sort/
    // __static_call_update channel). They, plus any global-variable
    // members, are the first summary/clone targets.
    for (size_t hi2 = 0; hi2 < std::min<size_t>(3, hubRank.size()); hi2++) {
      const uint32_t hubRep = find(hubRank[hi2].second);
      struct GlueRow { uint32_t vals = 0, formals = 0, insts = 0; };
      std::map<const Function *, GlueRow> byFn;
      size_t mFormals = 0, mInsts = 0, mGlobals = 0, mObjCell = 0,
             mSynth = 0, mDense = 0, mExpanded = 0;
      std::vector<std::string> globalNames;
      auto classify = [&](const Value *V, NodeIndex orig) {
        mExpanded++;
        if (const auto *Arg = dyn_cast_or_null<Argument>(V)) {
          mFormals++;
          auto &g = byFn[Arg->getParent()];
          g.vals++;
          g.formals++;
        } else if (const auto *I2 = dyn_cast_or_null<Instruction>(V)) {
          mInsts++;
          auto &g = byFn[I2->getFunction()];
          g.vals++;
          g.insts++;
        } else if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) {
          mGlobals++;
          if (globalNames.size() < 12)
            globalNames.push_back(GV->getName().str());
        } else {
          (NF.isObjectNode(orig) ? mObjCell : mSynth)++;
        }
      };
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != hubRep) continue;
        mDense++;
        NodeIndex orig = toOrig[n];
        classify(NF.getValueForNode(orig), orig);
        auto mit = canonicalClassMembers.find(orig);
        if (mit != canonicalClassMembers.end())
          for (NodeIndex m2 : mit->second)
            classify(NF.getValueForNode(m2), m2);
      }
      errs() << "HubMembers: c" << hubRank[hi2].second << " dense="
             << mDense << " values=" << mExpanded << " (formals="
             << mFormals << " insts=" << mInsts << " globals=" << mGlobals
             << " obj/cell=" << mObjCell << " synth=" << mSynth << ")\n";
      if (!globalNames.empty()) {
        errs() << "HubMembers: c" << hubRank[hi2].second << " globals:";
        for (auto &gn : globalNames) errs() << " " << gn;
        errs() << "\n";
      }
      std::vector<std::pair<uint32_t, const Function *>> glue;
      for (auto &bf : byFn) glue.emplace_back(bf.second.vals, bf.first);
      size_t KG = std::min<size_t>(20, glue.size());
      std::partial_sort(glue.begin(), glue.begin() + KG, glue.end(),
                        std::greater<>());
      errs() << "HubGlue: c" << hubRank[hi2].second << " " << byFn.size()
             << " functions contribute members; top " << KG
             << " by member count (fn totalVals/formals/insts):\n";
      for (size_t j = 0; j < KG; j++) {
        const GlueRow &g = byFn[glue[j].second];
        errs() << "HubGlue: " << glue[j].second->getName() << " "
               << g.vals << "/" << g.formals << "/" << g.insts << "\n";
      }
      // Merge provenance: the joins that BUILT this class, keyed by
      // witness origin (a-SCC collapses carry no witness — their share
      // is the remainder). Residency histograms proved non-causal
      // (bpf/slab/lockdep ablations: null); witnesses are causal by
      // construction — each entry is a merge that actually fired keyed
      // by that origin.
      std::unordered_map<uint32_t, uint32_t> witHits;
      size_t hubJoins = 0;
      for (auto &mw : mergeWitness)
        if ((uint32_t)find(mw.second) == hubRep) {
          witHits[mw.first]++;
          hubJoins++;
        }
      auto ridName = [&](uint32_t rid) -> std::string {
        auto fit2 = funcRootOf.find(rid);
        if (fit2 != funcRootOf.end())
          return ("fn:" + fit2->second->getName()).str();
        uint32_t cls = rootClassOf[rid];
        const Value *V2 = NF.getValueForNode(toOrig[cls]);
        if (!V2) return "<synthetic c" + std::to_string(cls) + ">";
        if (V2->hasName()) return V2->getName().str();
        if (const auto *I2 = dyn_cast<Instruction>(V2))
          return (I2->getFunction()->getName().str() + "::" +
                  I2->getOpcodeName());
        return "<anon>";
      };
      std::vector<std::pair<uint32_t, uint32_t>> witRank; // (count, rid)
      for (auto &wh : witHits) witRank.emplace_back(wh.second, wh.first);
      size_t KW = std::min<size_t>(20, witRank.size());
      std::partial_sort(witRank.begin(), witRank.begin() + KW, witRank.end(),
                        std::greater<>());
      errs() << "HubMerge: c" << hubRank[hi2].second << " " << hubJoins
             << " witnessed joins into this class by " << witHits.size()
             << " distinct witnesses (run totals: " << mergeCount
             << " merges, " << mergesFromSCC << " from a-SCC collapse); "
             << "top witnesses:\n";
      for (size_t j = 0; j < KW; j++)
        errs() << "HubMerge: x" << witRank[j].first << " "
               << ridName(witRank[j].second) << "\n";
      // Top-witness class anatomy: the printed name is only the CANONICAL
      // representative of the minted class — presolve merges can fold a
      // load result together with real origins. Dump the member-kind
      // tally so "guc_wq_item_append::load"-style labels can be read as
      // what the class actually contains.
      for (size_t j = 0; j < std::min<size_t>(5, KW); j++) {
        uint32_t rid = witRank[j].second;
        uint32_t cls = rootClassOf[rid];
        NodeIndex canon = toOrig[cls];
        size_t mAlloca = 0, mGlob = 0, mCall = 0, mLoad = 0, mArg = 0,
               mOther = 0;
        std::vector<std::string> gnames;
        auto tally = [&](NodeIndex m2) {
          const Value *V2 = NF.getValueForNode(m2);
          if (!V2) { mOther++; return; }
          if (isa<AllocaInst>(V2)) mAlloca++;
          else if (const auto *GV = dyn_cast<GlobalVariable>(V2)) {
            mGlob++;
            if (gnames.size() < 8) gnames.push_back(GV->getName().str());
          } else if (isa<CallBase>(V2)) mCall++;
          else if (isa<LoadInst>(V2)) mLoad++;
          else if (isa<Argument>(V2)) mArg++;
          else mOther++;
        };
        tally(canon);
        auto mit2 = canonicalClassMembers.find(canon);
        if (mit2 != canonicalClassMembers.end())
          for (NodeIndex m2 : mit2->second) tally(m2);
        errs() << "HubWitness: x" << witRank[j].first << " "
               << ridName(rid) << " class-members: alloca=" << mAlloca
               << " global=" << mGlob << " call=" << mCall << " load="
               << mLoad << " arg=" << mArg << " other=" << mOther;
        if (!gnames.empty()) {
          errs() << " globals:[";
          for (auto &g2 : gnames) errs() << " " << g2;
          errs() << " ]";
        }
        errs() << "\n";
      }
    }

    // Table 2: allocation-site identity spread. One sweep accumulates,
    // per root id, the number of live classes whose planes carry it.
    std::vector<uint32_t> spreadOf(nextRoot, 0);
    {
      FactSet uni;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n) continue;
        bool any = false;
        for (uint32_t s = 0; s < NSHIFT; s++) {
          if (R[n][s].none() && RB[n][s].none()) continue;
          if (!any) { uni.copyFrom(R[n][s]); any = true; }
          else uni.unionWith(R[n][s]);
          uni.unionWith(RB[n][s]);
        }
        if (any) uni.forEach([&](uint32_t o) { spreadOf[o]++; });
      }
    }
    std::unordered_map<uint32_t, uint32_t> ridOfRep;
    for (uint32_t rid = 0; rid < (uint32_t)rootClassOf.size(); rid++)
      ridOfRep[find(rootClassOf[rid])] = rid; // merged classes: one rid wins
    struct ARow {
      const Function *wrapper;
      uint32_t rid, spread, wcallers;
    };
    std::vector<ARow> arows;
    for (NodeIndex an : AllocSites) {
      int64_t rep = denseRepOf(an);
      if (rep < 0) continue;
      auto rit = ridOfRep.find((uint32_t)rep);
      if (rit == ridOfRep.end()) continue; // unminted (lazy) or merged away
      const Value *v = NF.getValueForNode(toOrig[(uint32_t)rep]);
      const auto *inst = v ? dyn_cast<Instruction>(v) : nullptr;
      const Function *wrapper = inst ? inst->getFunction() : nullptr;
      uint32_t wc = 0;
      if (wrapper) {
        auto wit = callerCnt.find(wrapper);
        if (wit != callerCnt.end()) wc = wit->second;
      }
      arows.push_back({wrapper, rit->second, spreadOf[rit->second], wc});
    }
    size_t K2 = std::min<size_t>(50, arows.size());
    std::partial_sort(arows.begin(), arows.begin() + K2, arows.end(),
                      [](const ARow &a, const ARow &b) {
                        return (uint64_t)a.spread * (a.wcallers + 1) >
                               (uint64_t)b.spread * (b.wcallers + 1);
                      });
    errs() << "AllocSpread: " << arows.size() << " allocation-site roots; "
           << "top " << K2 << " by spread x (wrapperCallers+1):\n";
    for (size_t i = 0; i < K2; i++) {
      const ARow &a2 = arows[i];
      errs() << "AllocSpread: "
             << (a2.wrapper ? a2.wrapper->getName() : StringRef("<none>"))
             << " rid=" << a2.rid << " spread=" << a2.spread
             << " classes, wrapperCallers=" << a2.wcallers << "\n";
    }
    errs() << "ConflationReport: done in "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tConf).count()
           << " ms\n";
  }

  if (CFLCoTravelStats) {
    auto mix64 = [](uint64_t x) {
      x += 0x9E3779B97F4A7C15ULL;
      x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
      x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
      return x ^ (x >> 31);
    };
    std::vector<uint64_t> colHash(nextRoot, 0), colCnt(nextRoot, 0);
    std::unordered_map<uint64_t, uint64_t> rowSigCount; // sig -> classes
    uint64_t totalFacts = 0, rowsWithFacts = 0;
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue;
      uint64_t rowHash = 0;
      bool any = false;
      for (uint32_t s = 0; s < NSHIFT; s++) {
        const uint64_t cellKey = (uint64_t)n * NSHIFT + s;
        R[n][s].forEach([&](uint32_t r) {
          colHash[r] ^= mix64(cellKey);
          colCnt[r]++;
          rowHash ^= mix64(((uint64_t)r << 8) | s);
          any = true;
          totalFacts++;
        });
      }
      if (any) { rowsWithFacts++; rowSigCount[rowHash]++; }
    }
    // Distinct columns keyed by (hash, count) to guard weak collisions.
    std::unordered_map<uint64_t, std::pair<uint64_t, uint64_t>>
        bundles; // key -> (root count, column size)
    uint64_t activeRoots = 0;
    for (uint32_t r = 0; r < nextRoot; r++) {
      if (!colCnt[r]) continue;
      activeRoots++;
      auto &b = bundles[mix64(colHash[r]) ^ mix64(colCnt[r])];
      b.first++;
      b.second = colCnt[r];
    }
    uint64_t compressedFacts = 0, maxBundle = 0;
    for (auto &[k, b] : bundles) {
      compressedFacts += b.second;
      maxBundle = std::max(maxBundle, b.first);
    }
    uint64_t sharedRows = 0;
    for (auto &[sig, cnt] : rowSigCount) sharedRows += cnt - 1;
    errs() << "CoTravel: facts " << totalFacts
           << ", active roots " << activeRoots
           << ", distinct columns (bundles) " << bundles.size()
           << ", root ratio "
           << (bundles.empty() ? 0.0
                               : (double)activeRoots / bundles.size())
           << ", max bundle " << maxBundle << "\n";
    errs() << "CoTravel: bundled facts " << compressedFacts
           << ", fact compression "
           << (compressedFacts ? (double)totalFacts / compressedFacts : 0.0)
           << "x\n";
    errs() << "CoTravel: classes with facts " << rowsWithFacts
           << ", distinct row signatures " << rowSigCount.size()
           << ", rows sharable " << sharedRows << "\n";
    // Dynamic a-SCC census: classes mutually reachable over the POST-MERGE
    // a-graph have provably equal fact planes at fixpoint, so they are
    // mergeable with the existing merge() machinery — plane dedup and
    // removal of SCC-internal a-prop churn without a new representation.
    {
      std::vector<uint32_t> comp(N, UINT32_MAX), low(N), dfn(N, 0);
      std::vector<uint32_t> stk, tarjanStack;
      std::vector<std::pair<uint32_t, size_t>> callStack;
      std::vector<bool> onStk(N, false);
      uint32_t timer = 1, nComp = 0;
      std::unordered_map<uint32_t, uint64_t> compSize;
      for (uint32_t start = 0; start < N; start++) {
        if (find(start) != start || dfn[start]) continue;
        callStack.emplace_back(start, 0);
        dfn[start] = low[start] = timer++;
        tarjanStack.push_back(start);
        onStk[start] = true;
        while (!callStack.empty()) {
          auto &[u, ei] = callStack.back();
          if (ei < outA[u].size()) {
            uint32_t v = find(outA[u][ei++]);
            if (v == u) continue;
            if (!dfn[v]) {
              dfn[v] = low[v] = timer++;
              tarjanStack.push_back(v);
              onStk[v] = true;
              callStack.emplace_back(v, 0);
            } else if (onStk[v]) {
              low[u] = std::min(low[u], dfn[v]);
            }
          } else {
            if (low[u] == dfn[u]) {
              uint32_t c = nComp++;
              uint64_t sz = 0;
              while (true) {
                uint32_t w = tarjanStack.back();
                tarjanStack.pop_back();
                onStk[w] = false;
                comp[w] = c;
                sz++;
                if (w == u) break;
              }
              compSize[c] = sz;
            }
            uint32_t uu = u;
            callStack.pop_back();
            if (!callStack.empty())
              low[callStack.back().first] =
                  std::min(low[callStack.back().first], low[uu]);
          }
        }
      }
      uint64_t nontrivial = 0, collapsible = 0, maxScc = 0;
      for (auto &[c, sz] : compSize) {
        if (sz > 1) { nontrivial++; collapsible += sz - 1; }
        maxScc = std::max(maxScc, sz);
      }
      uint64_t intraEdges = 0, totalEdges = 0;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n) continue;
        for (uint32_t t : outA[n]) {
          uint32_t tt = find(t);
          if (tt == n) continue;
          totalEdges++;
          if (comp[tt] == comp[n]) intraEdges++;
        }
      }
      errs() << "CoTravel: dynamic a-SCCs — nontrivial " << nontrivial
             << ", max size " << maxScc << ", collapsible classes "
             << collapsible << ", intra-SCC a-edges " << intraEdges << "/"
             << totalEdges << "\n";
    }
  }

  return false; // fixpoint reached (or cap warned) — driver runs once
}

void CallGraphPass::ensureConstGEPFieldEdges(const ConstantExpr *CE) {
  const auto *GEP = dyn_cast<GEPOperator>(CE);
  if (!GEP)
    return;
  NodeIndex node = NF.getValueNodeFor(CE);
  if (node == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex canon = getCanonicalNode(node);
  if (!moduleConstGEPFieldDone.insert(canon).second)
    return;

  const Value *base = GEP->getPointerOperand()->stripPointerCasts();
  NodeIndex baseNode = getRepNodeForValue(base); // recurses into nested CEs
  if (baseNode == AndersNodeFactory::InvalidIndex)
    return;
  if (canon == getCanonicalNode(baseNode))
    return; // field-0 GEPs canonicalize to the base node itself

  if (!EB.hasFieldLabels() || !curDL) {
    // Field-insensitive: a non-zero-field constexpr GEP gets its own
    // node (NodeFactory gepMap) — without the grammar's plain
    // GetElementPtr edge (base -> result a) that node floats and every
    // store/load through gep(@G, field) is silently severed from the
    // global's cell (found by t_ops.c, task #30).
    addAssignmentEdge(baseNode, node);
    return;
  }

  SmallVector<int64_t, 4> levels;
  if (!decomposeGEPLevels(GEP, *curDL, levels)) {
    applyFieldFallback(baseNode, node, "constexpr-gep-variable");
    return;
  }
  if (levels.empty())
    addAssignmentEdge(baseNode, node);
  else
    addFieldChainEdges(baseNode, node, levels);
}

// laundering witnesses (defined with the int-provenance machinery below)
static bool mayCarryPtrProvenance(const llvm::Value *V, unsigned depth,
                                  bool &declined);
static bool mayBecomePointer(const llvm::Value *V, unsigned depth,
                             bool &declined);
static bool isPtrWidthInt(const llvm::Type *T, const llvm::DataLayout &DL);

// inline-asm interface-closure ledger (census: 17,804 ptr-capable
// sites / 171 templates; the families modeled here are percpu ptr
// slots, asm atomics on ptr-width ints, raw-ptr register throughs)
static size_t g_staticCallWired = 0, g_staticCallNoKey = 0,
              g_staticCallUpdates = 0, g_staticCallDynUpdate = 0,
              g_tracepointProbes = 0, g_staticCallTpIter = 0;

static size_t g_asmSlotLoads = 0, g_asmSlotStores = 0,
              g_asmWidthWitnessed = 0, g_asmLaunderDeclined = 0,
              g_asmRegLoads = 0, g_asmRegStores = 0, g_asmRegCopies = 0;

void CallGraphPass::handleInlineAsm(CallBase &CS) {
  auto *IA = cast<InlineAsm>(CS.getCalledOperand());
  auto Constraints = InlineAsm::ParseConstraints(IA->getConstraintString());
  CG_DEBUG("InlineAsm: processing \"" << IA->getAsmString()
           << "\" with " << Constraints.size() << " constraints\n");


  // Build constraint-to-arg and constraint-to-ret mappings.
  // hasArg() is true for inputs and indirect outputs (they consume a CallBase arg).
  // Non-indirect outputs produce part of the return aggregate.
  unsigned argIdx = 0, retIdx = 0;
  std::vector<int> cToArg(Constraints.size(), -1);
  std::vector<int> cToRet(Constraints.size(), -1);
  for (unsigned i = 0; i < Constraints.size(); i++) {
    auto &CI = Constraints[i];
    if (CI.Type == InlineAsm::isClobber
#if LLVM_VERSION_MAJOR >= 15
        || CI.Type == InlineAsm::isLabel
#endif
    )
      continue;
    if (CI.hasArg())
      cToArg[i] = argIdx++;
    if (CI.Type == InlineAsm::isOutput && !CI.isIndirect)
      cToRet[i] = retIdx++;
  }

  // 1. Tied constraints -> copy edges.
  // If output constraint i has MatchingInput == j, the output gets the same
  // value as the tied input. Only create edges for pointer-typed operands.
  for (unsigned i = 0; i < Constraints.size(); i++) {
    auto &CI = Constraints[i];
    if (CI.Type != InlineAsm::isOutput || CI.MatchingInput < 0)
      continue;
    unsigned tied = CI.MatchingInput;
    int srcArgIdx = cToArg[tied];
    if (srcArgIdx < 0 || (unsigned)srcArgIdx >= CS.arg_size())
      continue;
    Value *srcVal = CS.getArgOperand(srcArgIdx);
    if (!srcVal->getType()->isPointerTy())
      continue;

    NodeIndex srcNode = getRepNodeForValue(srcVal);
    if (srcNode == AndersNodeFactory::InvalidIndex)
      continue;

    NodeIndex dstNode;
    if (CI.isIndirect) {
      // Indirect output: asm writes to *arg, so the destination is the arg pointer
      int dstArgIdx = cToArg[i];
      if (dstArgIdx < 0)
        continue;
      dstNode = getRepNodeForValue(CS.getArgOperand(dstArgIdx));
    } else {
      // Register output: result flows to the CallBase instruction itself
      dstNode = getRepNodeForValue(&CS);
    }
    if (dstNode == AndersNodeFactory::InvalidIndex)
      continue;

    CG_DEBUG("InlineAsm: tied copy edge from arg " << srcArgIdx
             << " to " << (CI.isIndirect ? "indirect output" : "result") << "\n");
    addAssignmentEdge(srcNode, dstNode);
  }

  // 2. Indirect memory operands with pointer elementtype.
  // =*m (output, indirect): asm writes to *arg. Conservatively, any pointer-typed
  //   direct input could be stored there.
  // *m (input, indirect): asm reads from *arg. Loaded value could flow to
  //   pointer-typed outputs.
  for (unsigned i = 0; i < Constraints.size(); i++) {
    auto &CI = Constraints[i];
    if (!CI.isIndirect)
      continue;
    int aIdx = cToArg[i];
    if (aIdx < 0 || (unsigned)aIdx >= CS.arg_size())
      continue;

#if LLVM_VERSION_MAJOR >= 15
    Type *ET = CS.getParamElementType(aIdx);
#else
    Type *ET = CS.getArgOperand(aIdx)->getType()->isPointerTy()
      ? CS.getArgOperand(aIdx)->getType()->getPointerElementType()
      : nullptr;
#endif
    // ptr-typed slot, or a ptr-WIDTH int slot (asm atomics on i64 —
    // xchgq/lock cmpxchgq — launder fptrs exactly like the IR-level
    // _Atomic lowering; same witness discipline as visitLoad/StoreInst)
    bool ptrSlot = ET && containsPointerType(ET);
    bool widthSlot = !ptrSlot && ET && curDL &&
                     isPtrWidthInt(ET->getScalarType(), *curDL);
    if (!ptrSlot && !widthSlot)
      continue;

    NodeIndex ptrNode = getRepNodeForValue(CS.getArgOperand(aIdx));
    if (ptrNode == AndersNodeFactory::InvalidIndex)
      continue;
    NodeIndex derefNode = getRepDerefNode(ptrNode);

    if (CI.Type == InlineAsm::isOutput) {
      // store to *ptr — any ptr-typed direct input, or witnessed
      // ptr-width int input, could be what the asm stores
      for (unsigned j = 0; j < Constraints.size(); j++) {
        if (Constraints[j].Type != InlineAsm::isInput)
          continue;
        int sIdx = cToArg[j];
        if (sIdx < 0 || (unsigned)sIdx >= CS.arg_size())
          continue;
        Value *srcVal = CS.getArgOperand(sIdx);
        if (Constraints[j].isIndirect)
          continue;
        // laundered constants arrive as ptrtoint CEs whose i64 type
        // resolves to the shared ConstantInt node — unwrap to the
        // underlying pointer so the edge carries the real identity
        if (auto *PTI = dyn_cast<PtrToIntOperator>(srcVal))
          srcVal = PTI->getPointerOperand();
        bool ok = srcVal->getType()->isPointerTy();
        if (!ok && widthSlot && curDL &&
            isPtrWidthInt(srcVal->getType(), *curDL)) {
          bool declined = false;
          ok = mayCarryPtrProvenance(srcVal, 8, declined);
          if (ok) g_asmWidthWitnessed++;
          else if (declined) g_asmLaunderDeclined++;
        }
        if (!ok)
          continue;
        NodeIndex srcNode = getRepNodeForValue(srcVal);
        if (srcNode == AndersNodeFactory::InvalidIndex ||
            NF.isSpecialNode(srcNode))
          continue;
        CG_DEBUG("InlineAsm: indirect store edge from input arg " << sIdx
                 << " to deref of output arg " << aIdx << "\n");
        addAssignmentEdge(srcNode, derefNode);
        g_asmSlotStores++;
      }
    } else if (CI.Type == InlineAsm::isInput) {
      // load from *ptr — flows to the result if it is ptr-typed, or
      // ptr-width and witnessed to become a pointer downstream
      bool ok = CS.getType()->isPointerTy() ||
                containsPointerType(CS.getType());
      if (!ok && curDL && isPtrWidthInt(CS.getType(), *curDL)) {
        bool declined = false;
        ok = mayBecomePointer(&CS, 8, declined);
        if (ok) g_asmWidthWitnessed++;
        else if (declined) g_asmLaunderDeclined++;
      }
      if (ok) {
        NodeIndex dstNode = getRepNodeForValue(&CS);
        if (dstNode == AndersNodeFactory::InvalidIndex)
          dstNode = getCanonicalNode(NF.createValueNode(&CS)); // i64 result
        CG_DEBUG("InlineAsm: indirect load edge from deref of input arg "
                 << aIdx << " to result\n");
        addAssignmentEdge(derefNode, dstNode);
        g_asmSlotLoads++;
      }
    }
  }

  // 2b. Raw pointer register/address inputs ("p"/"r" constraints with
  // pointer-typed args): the asm may READ through them regardless of
  // clobbers (percpu this_cpu_read_stable), and WRITE through them
  // when it declares memory effects (memory clobber or any indirect
  // output) — rep movs/stos, uaccess bodies. Immediate-constraint
  // pointers (metadata symbols) are excluded like the census does.
  {
    bool memClobber = false, anyIndirectOut = false;
    for (auto &CI : Constraints) {
      if (CI.Type == InlineAsm::isClobber) {
        for (const std::string &Code : CI.Codes)
          if (StringRef(Code).contains("memory")) memClobber = true;
      } else if (CI.Type == InlineAsm::isOutput && CI.isIndirect) {
        anyIndirectOut = true;
      }
    }
    bool resPtrCapable = CS.getType()->isPointerTy() ||
                         containsPointerType(CS.getType());
    if (!resPtrCapable && !CS.getType()->isVoidTy() && curDL &&
        isPtrWidthInt(CS.getType(), *curDL)) {
      bool declined = false;
      resPtrCapable = mayBecomePointer(&CS, 8, declined);
      if (declined) g_asmLaunderDeclined++;
    }
    SmallVector<NodeIndex, 4> rawPtrDerefs;
    SmallVector<Value *, 4> valueInputs;
    for (unsigned i = 0; i < Constraints.size(); i++) {
      auto &CI = Constraints[i];
      if (CI.Type != InlineAsm::isInput || CI.isIndirect)
        continue;
      int aIdx = cToArg[i];
      if (aIdx < 0 || (unsigned)aIdx >= CS.arg_size())
        continue;
      Value *A = CS.getArgOperand(aIdx);
      valueInputs.push_back(A);
      if (!A->getType()->isPointerTy())
        continue;
      bool allImm = !CI.Codes.empty();
      for (const std::string &Code : CI.Codes)
        allImm &= (Code == "i" || Code == "s" || Code == "n" || Code == "X");
      if (allImm)
        continue; // link-time symbol, no runtime access through it
      NodeIndex pNode = getRepNodeForValue(A);
      if (pNode == AndersNodeFactory::InvalidIndex)
        continue;
      rawPtrDerefs.push_back(getRepDerefNode(pNode));
    }
    // MEASUREMENT-ONLY UNSOUND (task #32 usercopy ablation): if this asm
    // is a from-user uaccess memory access — a bulk-copy body (rep movsb)
    // or a caller-side `call __get_user_N` scalar read — drop its entire
    // raw-ptr memory closure: the load/store/alias edges that carry user
    // bytes into (and around) the destination. The separation test then
    // checks the indirect-call graph is unchanged.
    if (CFLProbeUserCopyAblate && !rawPtrDerefs.empty()) {
      const bool copyBody =
          CS.getFunction() && isUserCopyFromFn(CS.getFunction()->getName());
      const bool getUser = StringRef(IA->getAsmString()).contains("__get_user");
      if (copyBody || getUser) {
        if (copyBody)
          g_userCopyAsmSevered++;
        else
          g_userGetAsmSevered++;
        g_userCopyDerefsSevered += rawPtrDerefs.size();
        rawPtrDerefs.clear();
      }
    }
    // MEASUREMENT-ONLY (task #32 usercopy certificate): tag the same
    // two ingress shapes with a synthetic origin object flowing into
    // the asm's memory cells — the solver then tracks "user bytes" as
    // a root and the resolution pass inventories which icall operands
    // they reach.
    if (CFLCertUserCopy && !rawPtrDerefs.empty()) {
      const bool copyBody =
          CS.getFunction() && isUserCopyFromFn(CS.getFunction()->getName());
      const bool getUser = StringRef(IA->getAsmString()).contains("__get_user");
      if (copyBody || getUser) {
        NodeIndex U = NF.createOpaqueObjectNode(&CS, true);
        for (NodeIndex derefP : rawPtrDerefs)
          addAssignmentEdge(U, derefP);
        if (copyBody)
          g_userCertCopySites++;
        else
          g_userCertGetSites++;
        g_userCertObjs.emplace_back(
            U, (CS.getFunction()->getName() +
                (copyBody ? "::copy-body" : "::get_user"))
                   .str());
      }
    }
    for (NodeIndex derefP : rawPtrDerefs) {
      if (resPtrCapable) {
        NodeIndex dstNode = getRepNodeForValue(&CS);
        if (dstNode == AndersNodeFactory::InvalidIndex)
          dstNode = getCanonicalNode(NF.createValueNode(&CS)); // i64 result
        addAssignmentEdge(derefP, dstNode);
        g_asmRegLoads++;
      }
      if (memClobber || anyIndirectOut) {
        for (Value *V : valueInputs) {
          if (auto *PTI = dyn_cast<PtrToIntOperator>(V))
            V = PTI->getPointerOperand();
          bool ok = V->getType()->isPointerTy();
          if (!ok && curDL && isPtrWidthInt(V->getType(), *curDL)) {
            bool declined = false;
            ok = mayCarryPtrProvenance(V, 8, declined);
            if (!ok && declined) g_asmLaunderDeclined++;
          }
          if (!ok)
            continue;
          NodeIndex srcNode = getRepNodeForValue(V);
          if (srcNode == AndersNodeFactory::InvalidIndex ||
              NF.isSpecialNode(srcNode))
            continue;
          addAssignmentEdge(srcNode, derefP);
          g_asmRegStores++;
        }
        for (NodeIndex derefQ : rawPtrDerefs)
          if (derefQ != derefP) {
            addAssignmentEdge(derefQ, derefP);
            g_asmRegCopies++;
          }
      }
    }
  }

  // 3. Call detection in asm text.
  // Match "call[q] <funcname>" patterns and look up targets in Ctx->Funcs.
  StringRef asmStr = IA->getAsmString();
  size_t pos = 0;
  while (pos < asmStr.size()) {
    // Find "call" keyword
    size_t callPos = asmStr.find("call", pos);
    if (callPos == StringRef::npos)
      break;

    // Skip the "call" keyword and optional suffix (callq, etc.)
    size_t cur = callPos + 4;
    while (cur < asmStr.size() && isalpha(asmStr[cur]))
      cur++;
    // Skip whitespace
    while (cur < asmStr.size() && (asmStr[cur] == ' ' || asmStr[cur] == '\t'))
      cur++;
    if (cur >= asmStr.size()) break;

    // Skip optional '*' (indirect call indicator) — we can't resolve those
    if (asmStr[cur] == '*' || asmStr[cur] == '%' || asmStr[cur] == '$') {
      pos = cur + 1;
      continue;
    }

    // Extract function name (alphanumeric + underscore + dot).
    // Also handle ${N:P} operand substitutions by stripping them — these are
    // LLVM asm operand placeholders (e.g., "call __put_user_${4:P}" where
    // ${4:P} expands to a size suffix like "1", "2", "4", "8").
    std::string funcName;
    size_t nameStart = cur;
    while (cur < asmStr.size()) {
      if (isalnum(asmStr[cur]) || asmStr[cur] == '_' || asmStr[cur] == '.') {
        funcName += asmStr[cur++];
      } else if (asmStr[cur] == '$' && cur + 1 < asmStr.size() && asmStr[cur + 1] == '{') {
        // Skip ${...} substitution
        size_t end = asmStr.find('}', cur + 2);
        if (end == StringRef::npos) break;
        cur = end + 1;
      } else {
        break;
      }
    }

    if (!funcName.empty()) {
      // Try the exact name first, then also try common size-suffixed variants
      // (e.g., __put_user_1, __put_user_2, __put_user_4, __put_user_8)
      bool found = false;
      uint64_t guid = GlobalValue::getGUID(funcName);
      auto it = Ctx->Funcs.find(guid);
      if (it != Ctx->Funcs.end()) {
        CG_LOG("InlineAsm: detected call to " << funcName << " in asm text\n");
        handleCall(&CS, it->second);
        found = true;
      } else {
        // Census the unresolved residue loudly: static_call trampolines
        // (__SCT__* — needs the __SCK__<name>.func icall model, task
        // pending) and targets defined only in .S assembly (no IR body,
        // e.g. __get_user_N) land here.
        WARNING("InlineAsm: embedded call target \"" << funcName
                << "\" has no IR definition (unmodeled) in "
                << CS.getFunction()->getName() << "\n");
      }
      // If the name ended with a ${...} substitution (stripped above),
      // try common numeric suffixes for size-parameterized kernel helpers.
      if (!found && cur > nameStart &&
          cur <= asmStr.size() && nameStart < cur) {
        for (const char *suffix : {"1", "2", "4", "8"}) {
          std::string variant = funcName + suffix;
          guid = GlobalValue::getGUID(variant);
          it = Ctx->Funcs.find(guid);
          if (it != Ctx->Funcs.end()) {
            CG_LOG("InlineAsm: detected call to " << variant << " in asm text\n");
            handleCall(&CS, it->second);
          }
        }
      }
    }
    pos = cur;
  }
}

bool CallGraphPass::isSummarizableAlloca(const AllocaInst *AI) const {
  if (!AI || !AI->getAllocatedType()->isPointerTy())
    return false;

  std::vector<const Value *> worklist;
  std::unordered_set<const Value *> seen;
  worklist.push_back(AI);
  seen.insert(AI);

  while (!worklist.empty()) {
    const Value *cur = worklist.back();
    worklist.pop_back();

    for (const User *U : cur->users()) {
      const Instruction *I = dyn_cast<Instruction>(U);
      if (I && I->getFunction() != AI->getFunction())
        return false;

      if (const auto *BC = dyn_cast<BitCastInst>(U)) {
        if (BC->getOperand(0) != cur)
          return false;
        if (seen.insert(BC).second)
          worklist.push_back(BC);
        continue;
      }

      if (const auto *ASC = dyn_cast<AddrSpaceCastInst>(U)) {
        if (ASC->getOperand(0) != cur)
          return false;
        if (seen.insert(ASC).second)
          worklist.push_back(ASC);
        continue;
      }

      if (const auto *GEP = dyn_cast<GetElementPtrInst>(U)) {
        if (GEP->getPointerOperand() != cur || !isZeroOffsetGEP(GEP))
          return false;
        if (seen.insert(GEP).second)
          worklist.push_back(GEP);
        continue;
      }

      if (const auto *LI = dyn_cast<LoadInst>(U)) {
        if (LI->getPointerOperand() != cur)
          return false;
        if (LI->isVolatile() || !LI->getType()->isPointerTy())
          return false;
        continue;
      }

      if (const auto *SI = dyn_cast<StoreInst>(U)) {
        if (SI->getPointerOperand() == cur) {
          if (SI->isVolatile())
            return false;
          const Value *stored = SI->getValueOperand();
          if (!stored->getType()->isPointerTy() && !shouldSkipValue(stored))
            return false;
          continue;
        }
        if (SI->getValueOperand() == cur)
          return false; // alloca address escapes
        return false;
      }

      if (const auto *CB = dyn_cast<CallBase>(U)) {
        if (isIgnorableAllocaIntrinsic(CB))
          continue;
        return false;
      }

      // Any other use is conservatively treated as escape/unmodeled behavior.
      return false;
    }
  }

  return true;
}

void CallGraphPass::collectLocalAllocaSummaries(const Function *F) {
  localSummarizedAllocaSlots.clear();
  localAllocaStoreVals.clear();
  localAllocaLoadVals.clear();

  if (!F)
    return;

  for (const Instruction &I : instructions(F)) {
    const auto *AI = dyn_cast<AllocaInst>(&I);
    if (!AI || !isSummarizableAlloca(AI))
      continue;
    NodeIndex slotRep = getRepNodeForValue(AI);
    if (slotRep == AndersNodeFactory::InvalidIndex)
      continue;
    localSummarizedAllocaSlots.insert(slotRep);
  }

  if (!localSummarizedAllocaSlots.empty()) {
    CG_DEBUG("Local alloca summaries in " << F->getName() << ": "
             << localSummarizedAllocaSlots.size() << "\n");
  }
}

bool CallGraphPass::resolveSummarizedAllocaSlot(const Value *Ptr, NodeIndex &slotRep) {
  slotRep = AndersNodeFactory::InvalidIndex;
  if (localSummarizedAllocaSlots.empty() || !Ptr)
    return false;

  const Value *base = stripAllocaAliasBase(Ptr);
  if (!isa<AllocaInst>(base))
    return false;

  NodeIndex node = getRepNodeForValue(base);
  if (node == AndersNodeFactory::InvalidIndex)
    return false;

  if (!localSummarizedAllocaSlots.count(node))
    return false;

  slotRep = node;
  return true;
}

void CallGraphPass::emitLocalAllocaSummaryEdges() {
  for (NodeIndex slot : localSummarizedAllocaSlots) {
    auto storesIt = localAllocaStoreVals.find(slot);
    auto loadsIt = localAllocaLoadVals.find(slot);
    if (storesIt == localAllocaStoreVals.end() || loadsIt == localAllocaLoadVals.end())
      continue;

    const auto &stores = storesIt->second;
    const auto &loads = loadsIt->second;
    if (stores.empty() || loads.empty())
      continue;

    std::unordered_set<NodeIndex> uniqueStores(stores.begin(), stores.end());
    std::unordered_set<NodeIndex> uniqueLoads(loads.begin(), loads.end());

    for (NodeIndex s : uniqueStores) {
      for (NodeIndex l : uniqueLoads)
        addAssignmentEdge(s, l);
    }
  }
}

bool CallGraphPass::runOnFunction(Function *F) {

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

  // --cfl-ablate-funcs: MEASUREMENT-ONLY UNSOUND PROBE. Skip body-edge
  // emission for the named functions (exact name, or name up to a '.'
  // uniquification suffix) to attribute hub-class gluing causally
  // (conflation report). The function stays a call target — callers
  // still wire actuals to its formals — but its body contributes no
  // flows, exactly "treat as opaque". Never use for real analysis.
  if (!CFLAblateFuncs.empty()) {
    static size_t g_ablated = 0;
    StringRef fname = F->getName();
    StringRef base = fname.take_front(fname.find('.'));
    StringRef spec(CFLAblateFuncs);
    while (!spec.empty()) {
      auto [head, rest] = spec.split(',');
      if (!head.empty() && (fname == head || base == head)) {
        WARNING("[MEASUREMENT-ONLY UNSOUND] ablating body of "
                << fname << " (" << ++g_ablated << " ablations)\n");
        return false;
      }
      spec = rest;
    }
  }

  // Per-instruction node creation is idempotent (already done in doInitialization
  // when CFLGlobalDedup is active), but we still need it for the non-dedup path.
  for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
    const Instruction *I = &*itr;
    if (containsPointerType(I->getType())) {
      NF.createValueNode(I);
    }
    if (const ReturnInst *RI = dyn_cast<ReturnInst>(I))
      Ctx->RetSites[F] = RI;

    if (const CallBase *CB = dyn_cast<CallBase>(I)) {
      if (const Function *CF = CB->getCalledFunction()) {
        if (Ctx->AllocFuncs.count(CF))
          Ctx->AllocSites.insert(CB);
      }
    }
  }

  bool allocaSummaryActive = CFLLocalAllocaSummary;
  if (allocaSummaryActive) {
    collectLocalAllocaSummaries(F);
  }

  // Use InstVisitor to handle instructions.
  InstHandler visitor(*this, F);
  visitor.visit(F);

  if (allocaSummaryActive) {
    emitLocalAllocaSummaryEdges();
  }
  // Clear alloca tracking structures
  localSummarizedAllocaSlots.clear();
  localAllocaStoreVals.clear();
  localAllocaLoadVals.clear();

  return false;
}

// Implementation of InstHandler visitor methods
void CallGraphPass::InstHandler::visitReturnInst(ReturnInst &I) {
  if (I.getNumOperands() > 0) {
    Value *rv = I.getOperand(0);
    if (!containsPointerType(rv->getType())) {
      // XXX only consider pointer type
      return;
    }

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(rv)) {
      CG_DEBUG("Skipping return value: " << *rv << "\n");
      return;
    }

    NodeIndex rvNode = CGP.getRepNodeForValue(rv);
    assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
    NodeIndex RT = CGP.NF.getReturnNodeFor(F);
    assert(RT != AndersNodeFactory::InvalidIndex && "Return node not found!");
    CGP.addAssignmentEdge(rvNode, RT);
  }
}

void CallGraphPass::InstHandler::visitCallBase(CallBase &CS) {
  if (CS.isInlineAsm()) {
    CGP.handleInlineAsm(CS);
    return;
  }
  if (CGP.Ctx->AllocSites.count(&CS)) {
    // record allocation sites and create heap object node
    NodeIndex valNode = CGP.getRepNodeForValue(&CS);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      // Allocator returns non-pointer type (e.g. unsigned long for
      // __get_free_pages); create a value node on demand.
      valNode = CGP.NF.createValueNode(&CS);
      valNode = CGP.getCanonicalNode(valNode);
    }
    CGP.AllocSites.insert(valNode);
    NodeIndex heapObj = CGP.NF.createOpaqueObjectNode(&CS, true);
    CGP.EB.addDereferenceEdges(valNode, heapObj);
    // Keep allocator return-node flow active for compositional promotion:
    // known allocator return symbols must stay reachable even when alloc
    // callsites are short-circuited as explicit AllocSites.
    if (Function *CF = CS.getCalledFunction()) {
      // Record call edge so allocator calls appear in the callgraph export.
      auto RCF = CGP.getFuncDef(CF);
      CGP.Ctx->Callees[&CS].insert(RCF);
      auto sit = CGP.Ctx->FuncSummaries.find(RCF);
      if (sit == CGP.Ctx->FuncSummaries.end())
        sit = CGP.Ctx->FuncSummaries.find(CF);
      if (sit != CGP.Ctx->FuncSummaries.end()) {
        // Summarized allocator: the callsite's identity IS the fresh
        // object; the shared return-node edge is exactly the measured
        // cross-caller conflation channel (~470 witnessed joins at km)
        // — suppress it, then apply the remaining atoms (CPY for the
        // dup family restores the copy the skipped body drops).
        if (CGP.applySummaryAtoms(&CS, *sit->second))
          CGP.wireCallArgs(&CS, RCF); // dynamic-fn INVOKE: feed the body pool
      } else if (CF->getReturnType()->isPointerTy()) {
        NodeIndex retNode = CGP.NF.getReturnNodeFor(RCF);
        if (retNode == AndersNodeFactory::InvalidIndex)
          retNode = CGP.NF.createReturnNode(RCF);
        retNode = CGP.getCanonicalNode(retNode);
        CGP.addAssignmentEdge(retNode, valNode);
      }
    }
    CG_DEBUG("Create heap obj node " << heapObj << " for " << CS << "\n");
    return; // skip allocation sites
  }

  // --cfl-sink-instr (task #34 v3): OPAQUE-ARENA model at the payload
  // accessor boundary. The accessor's return is bound to ONE shared
  // opaque object per accessor (NOT per callsite — write-side and
  // read-side callsites must share the origin so payload write->read
  // flow through the arena cells is preserved), replacing the ret
  // binding into ring-buffer internals. Args still feed the real body
  // (out-params, side effects). Gated on the read-back contract
  // confirmer, which runs before any instruction visiting.
  if (CFLSinkInstr) {
    const Function *AF = dyn_cast<Function>(
        CS.getCalledOperand()->stripPointerCasts());
    if (AF && isSinkPayloadAccessor(AF->getName())) {
      assert(g_sinkContractChecked &&
             "arena planting reached before the contract check");
      NodeIndex valNode = CGP.getRepNodeForValue(&CS);
      if (valNode == AndersNodeFactory::InvalidIndex)
        valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&CS));
      NodeIndex &arena =
          g_sinkArenaObj[AF->getName() == "perf_trace_buf_alloc"];
      if (arena == AndersNodeFactory::InvalidIndex)
        arena = CGP.NF.createOpaqueObjectNode(&CS, true);
      CGP.EB.addDereferenceEdges(valNode, arena);
      Function *RCF = CGP.getFuncDef(const_cast<Function *>(AF));
      CGP.Ctx->Callees[&CS].insert(RCF);
      CGP.wireCallArgs(&CS, RCF);
      g_sinkArenaSites++;
      return; // the arena IS the return identity; skip normal ret binding
    }
  }

  // Check for function pointer cycles
  if (!CS.getCalledFunction()) {
    Value *CO = CS.getCalledOperand()->stripPointerCastsAndAliases();
    if (auto *Load = dyn_cast<LoadInst>(CO)) {
      CG_DEBUG("Indirect call through loaded function pointer: " << *Load->getPointerOperand() << "\n");
    }
  }

  // static_call updater as a MODELED PRIMITIVE (task #14): letting the
  // generic actual-to-formal wiring run on __static_call_update
  // conflates EVERY key through the shared 'key' parameter (k->func =
  // func on the param unions all keys' planes: km subset showed
  // __SCT__cond_resched "resolving" to alloc_insn_page). Per-callsite
  // wiring func -> deref(key-global) is exact and covers the body's
  // only pointer effect; non-global keys fall through to the generic
  // path + LEDGER.
  if (CFLStaticCall) {
    Function *UF = CS.getCalledFunction();
    if (UF && UF->getName() == "__static_call_update" &&
        CS.arg_size() >= 3) {
      Value *KeyV = CS.getArgOperand(0)->stripPointerCasts();
      if (auto *KeyG = dyn_cast<GlobalVariable>(KeyV)) {
        // Ops-table channel (task #36): record what this update binds.
        // Const fn -> direct table entry; load gep(%struct.X, base,
        // 0, N) -> pending (resolved against all %struct.X global
        // initializers at resolution); anything else UNTABLES the key.
        if (CFLStaticOpsTables) {
          std::string keyName = KeyG->getName().str();
          // Recursive fn-source classifier: const fn / null / ops-table
          // load, composed through select/phi (the OPTIONAL_RET0 macro
          // emits `load ?: __static_call_return0` as a select). EVERY
          // leaf must conform or the key is untabled.
          std::function<bool(const Value *, unsigned)> classify =
              [&](const Value *FV, unsigned depth) -> bool {
            if (depth > 4)
              return false;
            FV = FV->stripPointerCasts();
            if (const auto *TF = dyn_cast<Function>(FV)) {
              g_sctKeyTable[keyName].insert(
                  CGP.getFuncDef(const_cast<Function *>(TF)));
              g_sctUpdConst++;
              return true;
            }
            if (isa<ConstantPointerNull>(FV)) {
              g_sctKeyTable.try_emplace(keyName); // known key, no target
              return true;
            }
            if (const auto *LI2 = dyn_cast<LoadInst>(FV)) {
              const Value *PB =
                  LI2->getPointerOperand()->stripPointerCasts();
              // (a) base strips to a struct-typed GLOBAL (the singleton
              // pattern: @kvm_pmu_ops field 0 has NO gep, later fields
              // are canonical i8 byte-geps): map the constant byte
              // offset to a field via DataLayout.
              const Value *Base = PB;
              APInt Off(64, 0);
              bool constOff = true;
              if (const auto *GO0 = dyn_cast<GEPOperator>(PB)) {
                constOff =
                    CGP.curDL && GO0->accumulateConstantOffset(*CGP.curDL,
                                                               Off);
                Base = GO0->getPointerOperand()->stripPointerCasts();
              }
              if (const auto *BG = dyn_cast<GlobalVariable>(Base)) {
                const auto *BST =
                    dyn_cast<StructType>(BG->getValueType());
                if (constOff && BST && BST->hasName() && CGP.curDL) {
                  const StructLayout *SL = CGP.curDL->getStructLayout(
                      const_cast<StructType *>(BST));
                  uint64_t o = Off.getZExtValue();
                  if (o < SL->getSizeInBytes()) {
                    g_sctKeyTable.try_emplace(keyName);
                    g_sctPendings.push_back(
                        {keyName,
                         sctCanonStructName(BST->getName()).str(),
                         SL->getElementContainingOffset(o)});
                    g_sctUpdLoad++;
                    return true;
                  }
                }
                return false;
              }
              // (b) dynamic base: struct-typed gep with constant field
              // index (trace_event_reg / apic->f shape)
              const auto *GO = dyn_cast<GEPOperator>(PB);
              const StructType *ST2 =
                  GO ? dyn_cast<StructType>(GO->getSourceElementType())
                     : nullptr;
              const auto *Zero =
                  GO && GO->getNumIndices() == 2
                      ? dyn_cast<ConstantInt>(GO->getOperand(1))
                      : nullptr;
              const auto *FieldC =
                  Zero && Zero->isZero()
                      ? dyn_cast<ConstantInt>(GO->getOperand(2))
                      : nullptr;
              if (!ST2 || !ST2->hasName() || !FieldC)
                return false;
              g_sctKeyTable.try_emplace(keyName);
              g_sctPendings.push_back(
                  {keyName, sctCanonStructName(ST2->getName()).str(),
                   (unsigned)FieldC->getZExtValue()});
              g_sctUpdLoad++;
              return true;
            }
            if (const auto *SEL = dyn_cast<SelectInst>(FV)) {
              bool a = classify(SEL->getTrueValue(), depth + 1);
              bool b = classify(SEL->getFalseValue(), depth + 1);
              return a && b;
            }
            if (const auto *PHI2 = dyn_cast<PHINode>(FV)) {
              bool ok = true;
              for (const Value *IV : PHI2->incoming_values())
                ok &= classify(IV, depth + 1);
              return ok;
            }
            return false;
          };
          if (!classify(CS.getArgOperand(2), 0)) {
            g_sctKeyUntabled.insert(keyName);
            g_sctUpdNonconform++;
          }
        }
        NodeIndex keyNode = CGP.getRepNodeForValue(KeyG);
        NodeIndex funcNode =
            CGP.getRepNodeForValue(CS.getArgOperand(2)->stripPointerCasts());
        if (keyNode != AndersNodeFactory::InvalidIndex &&
            funcNode != AndersNodeFactory::InvalidIndex &&
            !CGP.NF.isSpecialNode(funcNode)) {
          CGP.addAssignmentEdge(
              funcNode, CGP.getRepDerefNode(CGP.getCanonicalNode(keyNode)));
          auto RUF = CGP.getFuncDef(UF);
          CGP.Ctx->Callees[&CS].insert(RUF); // keep the export edge
          g_staticCallUpdates++;
          return; // primitive modeled; skip generic arg wiring
        }
      }
      // dynamic key (tracepoint_update_call, bpf dispatcher): the
      // generic actual-to-formal wiring would conflate EVERY key
      // through the shared param — suppress it and LEDGER. The
      // tracepoint family (the dominant user) is covered exactly by
      // the tracepoint_probe_register primitive below; anything else
      // is an explicit, counted boundary assumption.
      g_staticCallDynUpdate++;
      CG_DEBUG("StaticCall: dynamic-key update suppressed at "
               << F->getName() << "\n");
      auto RUF = CGP.getFuncDef(UF);
      CGP.Ctx->Callees[&CS].insert(RUF);
      return;
    }
    // tracepoint registration primitive: register_trace_X(probe) calls
    // tracepoint_probe_register*(&__tracepoint_X, probe, data). The
    // probe becomes a target of the paired static call
    // __SCT__tp_func_X (via tracepoint_update_call's dynamic-key
    // update, suppressed above) — wire probe -> deref(__SCK__tp_func_X)
    // per callsite. Normal handleCall still runs: tp->funcs flows keep
    // feeding the __traceiter_X iterator path.
    if (UF && UF->getName().starts_with("tracepoint_probe_register") &&
        CS.arg_size() >= 2) {
      if (auto *TP = dyn_cast<GlobalVariable>(
              CS.getArgOperand(0)->stripPointerCasts())) {
        if (TP->getName().starts_with("__tracepoint_")) {
          std::string sckName =
              ("__SCK__tp_func_" + TP->getName().drop_front(13)).str();
          GlobalValue *Key = F->getParent()->getNamedValue(sckName);
          if (!Key || Key->isDeclaration()) {
            auto git = CGP.Ctx->Gobjs.find(GlobalValue::getGUID(sckName));
            if (git != CGP.Ctx->Gobjs.end())
              Key = const_cast<GlobalVariable *>(git->second);
          }
          NodeIndex probeNode = CGP.getRepNodeForValue(
              CS.getArgOperand(1)->stripPointerCasts());
          if (Key && !Key->isDeclaration() &&
              probeNode != AndersNodeFactory::InvalidIndex &&
              !CGP.NF.isSpecialNode(probeNode)) {
            NodeIndex keyNode = CGP.getRepNodeForValue(Key);
            if (keyNode != AndersNodeFactory::InvalidIndex) {
              CGP.addAssignmentEdge(
                  probeNode,
                  CGP.getRepDerefNode(CGP.getCanonicalNode(keyNode)));
              g_tracepointProbes++;
            }
          }
        }
      }
    }
  }

  // Tracepoint keyed channels (task #35): the register family's shared
  // tp formal is THE channel that pools every tracepoint's probes into
  // every __traceiter_* dispatch (pin: 964 sites x ~1,561 targets =
  // 17.9% of the kernel answer set). Sever every classifiable family
  // callsite from the generic body and bind per key instead: CONST
  // keys here; the two struct-mediated registrars are covered by the
  // initializer walker, and their dynamic data argument is pooled into
  // the walker keys' data cells (data was globally pooled before this
  // model too — only the fn plane gains keying). Unclassifiable sites
  // keep generic wiring, counted LOUDLY (census: zero at kernel scale).
  if (CFLTracepointKeys) {
    const Function *RF = dyn_cast<Function>(
        CS.getCalledOperand()->stripPointerCasts());
    if (RF && isTracepointRegFn(RF->getName()) && CS.arg_size() >= 3) {
      const Value *tpArg = CS.getArgOperand(0)->stripPointerCasts();
      const auto *TPG = dyn_cast<GlobalVariable>(tpArg);
      const bool constKey =
          TPG && TPG->getName().starts_with("__tracepoint_");
      const bool knownMediator = F->getName() == "trace_event_reg" ||
                                 F->getName() == "bpf_probe_register" ||
                                 F->getName() == "bpf_probe_unregister";
      if (constKey || knownMediator) {
        const bool unreg =
            RF->getName() == "tracepoint_probe_unregister";
        if (constKey && !unreg)
          CGP.bindTracepointProbe(TPG,
                                  CS.getArgOperand(1)->stripPointerCasts(),
                                  CS.getArgOperand(2),
                                  /*fromWalker=*/false);
        if (!constKey && !unreg) {
          // mediator data pool: this callsite's dynamic data actual
          // feeds every walker-bound key's data cell
          NodeIndex dataN =
              CGP.getRepNodeForValue(CS.getArgOperand(2));
          if (dataN != AndersNodeFactory::InvalidIndex &&
              !CGP.NF.isSpecialNode(dataN)) {
            for (const GlobalVariable *K : g_tpWalkerKeys)
              CGP.addAssignmentEdge(dataN,
                                    CGP.tracepointJunctions(K).second);
            g_tpKeyMediatorDataPools++;
          }
        }
        CGP.Ctx->Callees[&CS].insert(
            CGP.getFuncDef(const_cast<Function *>(RF)));
        return; // severed: the shared tp formal never sees this key
      }
      g_tpKeyUnclassified++; // LOUD: generic wiring kept, pool re-forms
    }
  }

  // static_call (task #14): a direct call to the undefined __SCT__X
  // trampoline dispatches through __SCK__X's func slot — the key is a
  // real IR global whose initializer (DEFINE_STATIC_CALL) and updates
  // (__static_call_update stores key->func in-corpus) are already
  // modeled. Wire deref(key) -> value(trampoline) and treat the site
  // as an icall so standard resolution + arg/ret wiring apply.
  {
    Function *SCT = CS.getCalledFunction();
    if (!SCT)
      SCT = dyn_cast<Function>(
          CS.getCalledOperand()->stripPointerCastsAndAliases());
    if (CFLStaticCall && SCT && SCT->isDeclaration() &&
        SCT->getName().starts_with("__SCT__")) {
      StringRef Suffix = SCT->getName().drop_front(7);
      // Tracepoint static calls dispatch to __traceiter_X or a probe
      // registered on X; probes are transitively reachable through the
      // iterator's own indirect call over tp->funcs, so the syntactic
      // edge SCT -> __traceiter_X is callgraph-sound AND avoids reading
      // the key plane (tp keys route through tracepoint structs that
      // live in the type-erased hub — reading them imported the whole
      // hub: km showed __SCT__tp_func_sched_wakeup "resolving" to
      // array_map ops).
      if (Suffix.starts_with("tp_func_")) {
        std::string iterName =
            ("__traceiter_" + Suffix.drop_front(8)).str();
        Function *Iter = F->getParent()->getFunction(iterName);
        if (!Iter || Iter->isDeclaration()) {
          auto fit = CGP.Ctx->Funcs.find(GlobalValue::getGUID(iterName));
          if (fit != CGP.Ctx->Funcs.end()) Iter = fit->second;
        }
        if (Iter) {
          auto RIter = CGP.getFuncDef(Iter);
          CGP.Ctx->Callees[&CS].insert(RIter);
          if (Function *RSCT = CS.getCalledFunction())
            CGP.Ctx->Callees[&CS].insert(CGP.getFuncDef(RSCT));
          g_staticCallTpIter++;
          return; // probes covered transitively via the iterator icall
        }
        g_staticCallNoKey++; // LEDGER: tp_func without visible iterator
        // fall through to the key-based path as backstop
      }
      std::string sckName = ("__SCK__" + Suffix).str();
      GlobalValue *Key = F->getParent()->getNamedValue(sckName);
      if (!Key || Key->isDeclaration()) {
        auto git = CGP.Ctx->Gobjs.find(GlobalValue::getGUID(sckName));
        if (git != CGP.Ctx->Gobjs.end())
          Key = const_cast<GlobalVariable *>(git->second);
      }
      if (Key && !Key->isDeclaration()) {
        NodeIndex keyNode = CGP.getRepNodeForValue(Key);
        NodeIndex sctNode = CGP.NF.getValueNodeFor(SCT);
        if (sctNode == AndersNodeFactory::InvalidIndex)
          sctNode = CGP.NF.createValueNode(SCT);
        if (keyNode != AndersNodeFactory::InvalidIndex) {
          CGP.addAssignmentEdge(
              CGP.getRepDerefNode(CGP.getCanonicalNode(keyNode)),
              CGP.getCanonicalNode(sctNode));
          CGP.Ctx->IndirectCallInsts.insert(&CS);
          CGP.moduleIndirectCallInsts[F->getParent()].insert(&CS);
          if (!CS.getMetadata("ka.icall.id")) {
            std::string id =
                getScopeName(F) + "#" + std::to_string(icallCounter++);
            CS.setMetadata("ka.icall.id",
                           MDNode::get(CS.getContext(),
                                       {MDString::get(CS.getContext(), id)}));
          }
          g_staticCallWired++;
          return; // resolved via flows-to, not as an opaque extern call
        }
      }
      g_staticCallNoKey++; // LEDGER: trampoline without visible key
    }
  }

  if (Function *CF = CS.getCalledFunction()) {
    // direct call
    auto RCF = CGP.getFuncDef(CF);
    CGP.Ctx->Callees[&CS].insert(RCF);
    if (CGP.Ctx->ContainerFuncs.count(RCF))
      CGP.handleContainerCall(&CS, RCF);
    else
      CGP.handleCall(&CS, RCF);
  } else {
    // indirect call (or direct call through alias/bitcast)
    Value *CO = CS.getCalledOperand()->stripPointerCastsAndAliases();
    // resolve constant expr
    if (auto *CE = dyn_cast<ConstantExpr>(CO)) {
      switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: {
          GEPOperator* GEP = dyn_cast<GEPOperator>(CE);
          CO = GEP->getPointerOperand()->stripPointerCastsAndAliases();
          break;
        }
        case Instruction::BitCast: {
          CO = CE->getOperand(0);
          break;
        }
        default:
          WARNING("Unhandled constant expression call target: " << *CE << "\n");
      }
    }
    if (Function *CF = dyn_cast<Function>(CO)) {
      // direct call through bitcast/alias
      auto RCF = CGP.getFuncDef(CF);
      CGP.Ctx->Callees[&CS].insert(RCF);
      if (CGP.Ctx->ContainerFuncs.count(RCF))
        CGP.handleContainerCall(&CS, RCF);
      else
        CGP.handleCall(&CS, RCF);
    } else if (auto *IF = dyn_cast<GlobalIFunc>(CO)) {
      auto it = CGP.IFuncTargets.find(IF);
      if (it != CGP.IFuncTargets.end()) {
        for (const Function *CF : it->second) {
          CGP.Ctx->Callees[&CS].insert(CF);
          if (CGP.Ctx->ContainerFuncs.count(CF))
            CGP.handleContainerCall(&CS, CF);
          else
            CGP.handleCall(&CS, CF);
          CG_LOG("IFunc call: " << IF->getName() << " -> " << CF->getName() << "\n");
        }
      } else {
        CG_DEBUG("IFunc call: " << IF->getName() << " has no resolved targets\n");
      }
    } else {
      // Tracepoint keyed dispatch (task #35): a __traceiter_X icall
      // reads its own key's channel cells. The generic funcs-load
      // chain stays wired but carries nothing once every registration
      // callsite is severed above — this edge pair IS the resolution.
      if (CFLTracepointKeys &&
          F->getName().starts_with("__traceiter_")) {
        if (const GlobalVariable *KeyGV = traceiterKeyOf(F)) {
          auto [fnJ, dataJ] = CGP.tracepointJunctions(KeyGV);
          (void)fnJ; // v3: answers come from the binding table
          NodeIndex keyN = CGP.getRepNodeForValue(KeyGV);
          if (keyN != AndersNodeFactory::InvalidIndex) {
            keyN = CGP.getCanonicalNode(keyN);
            g_tpIterIcallKey[&CS] = keyN;
            // The no-probe default stub is dispatched on the
            // static-call fast path; include it defensively.
            std::string stubName =
                ("__probestub_" + KeyGV->getName().drop_front(13)).str();
            Function *Stub = F->getParent()->getFunction(stubName);
            if (!Stub || Stub->isDeclaration()) {
              auto fit2 =
                  CGP.Ctx->Funcs.find(GlobalValue::getGUID(stubName));
              if (fit2 != CGP.Ctx->Funcs.end())
                Stub = fit2->second;
            }
            if (Stub)
              g_tpKeyProbes[keyN].insert(CGP.getFuncDef(Stub));
            if (CS.arg_size() >= 1) {
              NodeIndex dArg =
                  CGP.getRepNodeForValue(CS.getArgOperand(0));
              if (dArg != AndersNodeFactory::InvalidIndex)
                CGP.addAssignmentEdge(dataJ, dArg);
            }
            g_tpKeyDispatchWires++;
          }
        } else {
          g_tpKeyKeylessIter++; // LOUD: census says this is empty
        }
      }
      CGP.Ctx->IndirectCallInsts.insert(&CS);
      CGP.moduleIndirectCallInsts[F->getParent()].insert(&CS);
      // Attach deterministic icall ID as LLVM metadata.
      // Use scoped caller name for uniqueness across TUs.
      std::string id;
      id = getScopeName(F) + "#" + std::to_string(icallCounter++);
      CS.setMetadata("ka.icall.id",
          MDNode::get(CS.getContext(),
                      {MDString::get(CS.getContext(), id)}));
    }
  }
}

void CallGraphPass::InstHandler::visitAllocaInst(AllocaInst &I) {
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(&I, slotRep))
    return;

  // Create a deref node eagerly only for pointer-bearing allocas. Cells of
  // scalar allocas (bool/int out-params etc.) can never hold a function
  // pointer under tracked (pointer-typed) accesses; creating them eagerly
  // manufactured O(n^2) M-facts over empty cells (harfbuzz sanitize class).
  // A pointer-typed access through such an alloca still creates the deref
  // lazily in visitLoadInst/visitStoreInst, so this stays sound.
  if (!containsPointerType(I.getAllocatedType()))
    return;
  NodeIndex ptrNode = CGP.getRepNodeForValue(&I);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find alloca node");
  (void)CGP.getRepDerefNode(ptrNode);
}

// ---- integer-laundered pointer provenance through MEMORY ----
// ptrtoint/inttoptr/binop visitors track provenance while it stays in
// SSA registers, but the load/store guards skip integer types, so
// provenance dies at memory. Clang lowers _Atomic function pointers to
// exactly this shape (atomicrmw/cmpxchg on i64 with ptrtoint constants,
// inttoptr on the way out — see test/t_atomicptr.c), and long-carried
// pointers hit it too. Witness-based repair: a pointer-width integer
// store/load emits deref edges when a bounded def/use scan finds
// pointer provenance; the interprocedural cases the scan declines
// (int arguments, int call results, escapes via ret/call) are COUNTED
// as explicit ledger entries, never dropped silently.
static size_t g_intProvStores = 0, g_intProvLoads = 0;
static size_t g_intStoreUnmodeled = 0, g_intLoadUnmodeled = 0;

static bool constantHasPtrToInt(const Constant *C, unsigned depth) {
  if (depth == 0) return true; // bail conservative
  if (const auto *CE = dyn_cast<ConstantExpr>(C)) {
    if (CE->getOpcode() == Instruction::PtrToInt) return true;
    for (const Use &U : CE->operands())
      if (const auto *OC = dyn_cast<Constant>(U.get()))
        if (constantHasPtrToInt(OC, depth - 1)) return true;
  }
  return false;
}

// Def-side witness: could this integer value carry pointer provenance?
static bool mayCarryPtrProvenance(const Value *V, unsigned depth,
                                  bool &declined) {
  if (depth == 0) return true; // depth exhaustion: conservative yes
  if (isa<PtrToIntInst>(V)) return true;
  if (const auto *C = dyn_cast<Constant>(V)) {
    if (isa<ConstantInt>(C) || isa<ConstantData>(C)) return false;
    return constantHasPtrToInt(C, 6);
  }
  if (isa<LoadInst>(V)) return true; // slot-to-slot int copies stay live
  if (isa<Argument>(V)) { declined = true; return false; } // ledger
  if (const auto *CB2 = dyn_cast<CallBase>(V)) {
    (void)CB2;
    declined = true; // int-returning call may launder a pointer: ledger
    return false;
  }
  if (const auto *I = dyn_cast<Instruction>(V)) {
    if (isa<BinaryOperator>(I) || isa<CastInst>(I) || isa<PHINode>(I) ||
        isa<SelectInst>(I) || isa<FreezeInst>(I)) {
      for (const Use &U : I->operands())
        if (U->getType()->isIntegerTy() || U->getType()->isPointerTy())
          if (mayCarryPtrProvenance(U.get(), depth - 1, declined))
            return true;
      return false;
    }
  }
  return false;
}

// Use-side witness: could this loaded integer become a pointer again?
static bool mayBecomePointer(const Value *V, unsigned depth, bool &declined) {
  if (depth == 0) return true;
  for (const User *U : V->users()) {
    if (isa<IntToPtrInst>(U)) return true;
    if (const auto *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getValueOperand() == V) return true; // flows onward via memory
      continue;
    }
    if (isa<ReturnInst>(U) || isa<CallBase>(U)) { declined = true; continue; }
    if (isa<BinaryOperator>(U) || isa<CastInst>(U) || isa<PHINode>(U) ||
        isa<SelectInst>(U) || isa<FreezeInst>(U) || isa<ExtractValueInst>(U))
      if (mayBecomePointer(U, depth - 1, declined))
        return true;
  }
  return false;
}

static bool isPtrWidthInt(const Type *T, const DataLayout &DL) {
  return T->isIntegerTy() &&
         T->getIntegerBitWidth() >= DL.getPointerSizeInBits();
}

void CallGraphPass::InstHandler::visitLoadInst(LoadInst &I) {
  // Tracepoint keyed dispatch (task #35): inside __traceiter_X, the
  // funcs-head load reads cells that the kernel-scale giant absorbs —
  // the keyed channel replaces this read entirely (sound: the census
  // completeness counters prove every registration is channel-bound),
  // so the generic wiring is severed here to keep the pool from
  // riding back in beside the exact channel.
  if (CFLTracepointKeys) {
    const Function *LF = I.getFunction();
    if (LF && LF->getName().starts_with("__traceiter_")) {
      const Value *P = I.getPointerOperand();
      if (const auto *CE = dyn_cast<ConstantExpr>(P))
        if (CE->getOpcode() == Instruction::GetElementPtr)
          P = CE->getOperand(0);
      if (const auto *GV = dyn_cast<GlobalVariable>(P->stripPointerCasts()))
        if (GV->getName().starts_with("__tracepoint_")) {
          g_tpKeyIterLoadsSevered++;
          return;
        }
    }
  }
  if (!containsPointerType(I.getType())) {
    // Integer-laundered provenance: a pointer-width int load whose value
    // can become a pointer again (inttoptr downstream, or stored onward)
    // must read the cell.
    bool declined = false;
    if (CGP.curDL && isPtrWidthInt(I.getType(), *CGP.curDL)) {
      if (mayBecomePointer(&I, 8, declined)) {
        NodeIndex valNode = CGP.getRepNodeForValue(&I);
        if (valNode == AndersNodeFactory::InvalidIndex)
          valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
        Value *lp = I.getOperand(0);
        NodeIndex slotRep;
        if (CGP.resolveSummarizedAllocaSlot(lp, slotRep)) {
          CGP.localAllocaLoadVals[slotRep].push_back(valNode);
        } else {
          NodeIndex pN = CGP.getRepNodeForValue(lp);
          if (pN != AndersNodeFactory::InvalidIndex)
            CGP.addAssignmentEdge(CGP.getRepDerefNode(pN), valNode);
        }
        g_intProvLoads++;
      } else if (declined) {
        g_intLoadUnmodeled++; // ledger
      }
    }
    return;
  }
  NodeIndex valNode = CGP.getRepNodeForValue(&I);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find load value node");

  Value *ptr = I.getOperand(0);
  // Frontends often lower va_arg to __va_list_tag memory accesses (no VAArgInst).
  // Connect such pointer loads to the function's vararg summary node.
  if (Function *F = I.getFunction()) {
    NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
    if (varargNode != AndersNodeFactory::InvalidIndex &&
        derivesFromLoweredVAList(ptr)) {
      CGP.addAssignmentEdge(varargNode, valNode);
      CG_DEBUG("LoweredVAArg: " << F->getName() << ": vararg node " << varargNode
               << " -> val node " << valNode << " for " << I << "\n");
    }
  }

  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaLoadVals[slotRep].push_back(valNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find load ptr node");

  // Aggregate loads read every field: pull every residue cell into the
  // aggregate SSA value (residue 0 via the normal deref edge below). No
  // pointer wildcard — that smeared every access through this pointer's
  // aliases, not just this load.
  if (CGP.EB.hasFieldLabels() && I.getType()->isAggregateType()) {
    if (CFLResidueCopies && CFLFlowsTo) {
      const unsigned P = CGP.EB.getNumFieldBuckets();
      for (unsigned r = 1; r < P; r++) {
        NodeIndex pF = CGP.getFieldPtrNode(ptrNode, (int64_t)r);
        CGP.EB.addFieldEdges(ptrNode, CGP.getCanonicalNode(pF), (int)r);
        CGP.addAssignmentEdge(CGP.getRepDerefNode(CGP.getCanonicalNode(pF)),
                              valNode);
      }
    } else {
      CGP.addFieldWildcardLoop(ptrNode, "aggregate-load");
    }
  }

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  CGP.addAssignmentEdge(derefNode, valNode);
}

void CallGraphPass::InstHandler::visitStoreInst(StoreInst &I) {
  Value *val = I.getOperand(0);
  if (!containsPointerType(val->getType())) {
    // Integer-laundered provenance: a pointer-width int store with a
    // def-side witness (ptrtoint upstream) still moves a pointer.
    bool declined = false;
    if (CGP.curDL && isPtrWidthInt(val->getType(), *CGP.curDL) &&
        !shouldSkipValue(val)) {
      if (mayCarryPtrProvenance(val, 8, declined)) {
        NodeIndex valNode = CGP.getRepNodeForValue(val);
        if (valNode == AndersNodeFactory::InvalidIndex)
          valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(val));
        if (auto *CE = dyn_cast<ConstantExpr>(val))
          if (CE->getOpcode() == Instruction::PtrToInt) {
            NodeIndex srcN = CGP.getRepNodeForValue(CE->getOperand(0));
            if (srcN != AndersNodeFactory::InvalidIndex)
              CGP.addAssignmentEdge(srcN, valNode);
          }
        Value *sp = I.getOperand(1);
        NodeIndex slotRep;
        if (CGP.resolveSummarizedAllocaSlot(sp, slotRep)) {
          CGP.localAllocaStoreVals[slotRep].push_back(valNode);
        } else {
          NodeIndex pN = CGP.getRepNodeForValue(sp);
          if (pN != AndersNodeFactory::InvalidIndex)
            CGP.addAssignmentEdge(valNode, CGP.getRepDerefNode(pN));
        }
        g_intProvStores++;
      } else if (declined) {
        g_intStoreUnmodeled++; // ledger: interprocedural int provenance
      }
    }
    return;
  }

  // Skip nullptr and compiler-introduced values
  if (shouldSkipValue(val)) {
    CG_DEBUG("Skipping value in Store: " << *val << "\n");
    return;
  }

  // Check for potential linked data structure patterns
  if (auto *GEP = dyn_cast<GetElementPtrInst>(val)) {
    auto *ptrOp = GEP->getPointerOperand();
    if (auto *Load = dyn_cast<LoadInst>(ptrOp)) {
      // Pattern: store GEP(load(ptr)), ptr - typical linked list cycle
      CG_DEBUG("Potential linked structure cycle: store GEP(load(" << *Load->getPointerOperand()
               << ")), " << *I.getPointerOperand() << "\n");
    }
  }

  NodeIndex valNode = CGP.getRepNodeForValue(val);
  // assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find store value node");
  if (valNode == AndersNodeFactory::InvalidIndex) {
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(val));
    CG_DEBUG("Create value node " << valNode << " for store " << *val << "\n");
  }

  Value *ptr = I.getOperand(1);
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaStoreVals[slotRep].push_back(valNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find store ptr node");

  // Aggregate stores write every field: push the aggregate SSA value into
  // every residue cell (residue 0 via the normal deref edge below).
  if (CGP.EB.hasFieldLabels() && val->getType()->isAggregateType()) {
    if (CFLResidueCopies && CFLFlowsTo) {
      const unsigned P = CGP.EB.getNumFieldBuckets();
      for (unsigned r = 1; r < P; r++) {
        NodeIndex pF = CGP.getFieldPtrNode(ptrNode, (int64_t)r);
        CGP.EB.addFieldEdges(ptrNode, CGP.getCanonicalNode(pF), (int)r);
        CGP.addAssignmentEdge(valNode,
                              CGP.getRepDerefNode(CGP.getCanonicalNode(pF)));
      }
    } else {
      CGP.addFieldWildcardLoop(ptrNode, "aggregate-store");
    }
  }

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  CGP.addAssignmentEdge(valNode, derefNode);
}

void CallGraphPass::InstHandler::visitGetElementPtrInst(GetElementPtrInst &GEP) {
  Value *ptr = GEP.getPointerOperand();

  // Only handle GEPs on pointer or vector-of-pointer types
  if (!containsPointerType(ptr->getType()))
    return;

  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  if (ptrNode == AndersNodeFactory::InvalidIndex) {
    // On-the-fly node creation for unhandled operands (e.g., constant vectors)
    ptrNode = CGP.getCanonicalNode(CGP.NF.createValueNode(ptr));
    CG_DEBUG("Create value node " << ptrNode << " for GEP ptr " << *ptr << "\n");
  }
  NodeIndex valNode = CGP.getRepNodeForValue(&GEP);
  if (valNode == AndersNodeFactory::InvalidIndex) {
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&GEP));
    CG_DEBUG("Create value node " << valNode << " for GEP result " << GEP << "\n");
  }

  if (CGP.EB.hasFieldLabels()) {
    SmallVector<int64_t, 4> levels;
    const DataLayout &DL = GEP.getModule()->getDataLayout();
    if (!CGP.decomposeGEPLevels(cast<GEPOperator>(&GEP), DL, levels))
      CGP.applyFieldFallback(ptrNode, valNode, "gep-variable-offset");
    else if (levels.empty())
      CGP.addAssignmentEdge(ptrNode, valNode);
    else
      CGP.addFieldChainEdges(ptrNode, valNode, levels);
    return;
  }

  CGP.addAssignmentEdge(ptrNode, valNode);
}

void CallGraphPass::InstHandler::visitBitCastInst(BitCastInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    srcNode = CGP.getCanonicalNode(CGP.NF.createValueNode(I.getOperand(0)));
    CG_DEBUG("Create value node " << srcNode << " for bitcast src " << *(I.getOperand(0)) << "\n");
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
    WARNING("Create value node " << dstNode << " for bitcast dst " << I << "\n");
  }
  CGP.addAssignmentEdge(srcNode, dstNode);
}

// freeze forwards its operand unchanged (poison stopper) — a plain copy
// for pointer-carrying values. Census: kernel 106 freezes, 2 on pointer
// paths; silently dropped before this visitor existed.
void CallGraphPass::InstHandler::visitFreezeInst(FreezeInst &I) {
  if (!containsPointerType(I.getType()))
    return;
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex)
    srcNode = CGP.getCanonicalNode(CGP.NF.createValueNode(I.getOperand(0)));
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  CGP.addAssignmentEdge(srcNode, dstNode);
}

// addrspacecast is ptr->ptr value flow; visitBitCastInst does not catch
// it (distinct opcode). Zero instances in current corpora — defensive.
void CallGraphPass::InstHandler::visitAddrSpaceCastInst(AddrSpaceCastInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex)
    srcNode = CGP.getCanonicalNode(CGP.NF.createValueNode(I.getOperand(0)));
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  CGP.addAssignmentEdge(srcNode, dstNode);
}

// atomicrmw on a pointer slot (xchg — the lockless fptr-swap idiom) is a
// fused store+load: new value into the cell, old value out to the result.
void CallGraphPass::InstHandler::visitAtomicRMWInst(AtomicRMWInst &I) {
  Value *val = I.getValOperand();
  if (!containsPointerType(val->getType())) {
    // _Atomic fptr slots lower to i64 xchg with ptrtoint/inttoptr —
    // accept when either side carries a provenance witness.
    bool dv = false, du = false;
    if (!(CGP.curDL && isPtrWidthInt(val->getType(), *CGP.curDL)))
      return;
    if (!mayCarryPtrProvenance(val, 8, dv) && !mayBecomePointer(&I, 8, du)) {
      if (dv || du) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex valNode = CGP.getRepNodeForValue(val);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(val));
  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  if (auto *CE = dyn_cast<ConstantExpr>(val))
    if (CE->getOpcode() == Instruction::PtrToInt) {
      NodeIndex srcN = CGP.getRepNodeForValue(CE->getOperand(0));
      if (srcN != AndersNodeFactory::InvalidIndex)
        CGP.addAssignmentEdge(srcN, valNode);
    }
  Value *ptr = I.getPointerOperand();
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaStoreVals[slotRep].push_back(valNode);
    CGP.localAllocaLoadVals[slotRep].push_back(resNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex &&
         "Failed to find atomicrmw ptr node");
  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);
  CGP.addAssignmentEdge(valNode, derefNode);
  CGP.addAssignmentEdge(derefNode, resNode);
}

// cmpxchg on a pointer slot: conditional store of the new value plus the
// old value loaded into the {old, i1} aggregate result (extractvalue
// projects it — sound to wire both directions unconditionally).
void CallGraphPass::InstHandler::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  Value *nv = I.getNewValOperand();
  if (!containsPointerType(nv->getType())) {
    bool dv = false, du = false;
    if (!(CGP.curDL && isPtrWidthInt(nv->getType(), *CGP.curDL)))
      return;
    if (!mayCarryPtrProvenance(nv, 8, dv) && !mayBecomePointer(&I, 8, du)) {
      if (dv || du) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex valNode = CGP.getRepNodeForValue(nv);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(nv));
  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  if (auto *CE = dyn_cast<ConstantExpr>(nv))
    if (CE->getOpcode() == Instruction::PtrToInt) {
      NodeIndex srcN = CGP.getRepNodeForValue(CE->getOperand(0));
      if (srcN != AndersNodeFactory::InvalidIndex)
        CGP.addAssignmentEdge(srcN, valNode);
    }
  Value *ptr = I.getPointerOperand();
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaStoreVals[slotRep].push_back(valNode);
    CGP.localAllocaLoadVals[slotRep].push_back(resNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex &&
         "Failed to find cmpxchg ptr node");
  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);
  CGP.addAssignmentEdge(valNode, derefNode);
  CGP.addAssignmentEdge(derefNode, resNode);
}

static bool ptrToIntTagRoundTripOnly(const Value *PTI); // defined below

// phi/select of PTR-WIDTH INTS can carry pointer provenance — clang
// folds `flag ? (ulong)&a : (ulong)&b` into a select whose operands
// are ptrtoint CONSTANT EXPRESSIONS (found by test/t_maskwalk.c:
// the whole chain silently dropped and the downstream icall resolved
// to NOTHING). Same laundering guards as the atomic handlers above;
// a CE ptrtoint contributes its pointer operand, plus — under field
// mode — the same escape-wildcard discipline visitPtrToIntInst
// applies to the instruction form (a CE never passes through that
// visitor, so this is its only wildcard site).
void CallGraphPass::InstHandler::visitPHINode(PHINode &PHI) {
  if (!containsPointerType(PHI.getType())) {
    if (!(CGP.curDL && isPtrWidthInt(PHI.getType(), *CGP.curDL)))
      return;
    bool d = false, prov = mayBecomePointer(&PHI, 8, d);
    for (unsigned i = 0, e = PHI.getNumIncomingValues(); !prov && i != e;
         ++i) {
      bool d2 = false;
      prov = mayCarryPtrProvenance(PHI.getIncomingValue(i), 8, d2);
      d |= d2;
    }
    if (!prov) {
      if (d) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&PHI);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&PHI));
  auto wireIncoming = [&](Value *src) {
    // A ptrtoint CONSTANT EXPRESSION maps to a special node (constant
    // pool), which would silently absorb the flow — unwrap to the
    // pointer operand instead.
    const auto *CE = dyn_cast<ConstantExpr>(src);
    const bool ceP2I = CE && CE->getOpcode() == Instruction::PtrToInt;
    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    if (srcNode != AndersNodeFactory::InvalidIndex &&
        !(ceP2I && CGP.NF.isSpecialNode(srcNode))) {
      CGP.addAssignmentEdge(srcNode, dstNode);
      return;
    }
    if (!ceP2I)
      return; // plain int constant: no provenance
    NodeIndex ptrN = CGP.getRepNodeForValue(CE->getOperand(0));
    if (ptrN == AndersNodeFactory::InvalidIndex || CGP.NF.isSpecialNode(ptrN))
      return;
    if (CGP.EB.hasFieldLabels() && !ptrToIntTagRoundTripOnly(CE))
      CGP.addFieldWildcardLoop(ptrN, "ptrtoint-escape-ce");
    else if (CGP.EB.hasFieldLabels())
      g_tagRoundTrips++;
    CGP.addAssignmentEdge(ptrN, dstNode);
  };
  for (unsigned i = 0, e = PHI.getNumIncomingValues(); i != e; ++i) {
    Value *src = PHI.getIncomingValue(i);
    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in PHI: " << *src << "\n");
      continue;
    }
    wireIncoming(src);
  }
}

void CallGraphPass::InstHandler::visitSelectInst(SelectInst &I) {
  if (!containsPointerType(I.getType())) {
    if (!(CGP.curDL && isPtrWidthInt(I.getType(), *CGP.curDL)))
      return;
    bool d = false, prov = mayBecomePointer(&I, 8, d);
    for (unsigned i = 1; !prov && i < I.getNumOperands(); i++) {
      bool d2 = false;
      prov = mayCarryPtrProvenance(I.getOperand(i), 8, d2);
      d |= d2;
    }
    if (!prov) {
      if (d) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  auto wireIncoming = [&](Value *src) {
    // A ptrtoint CONSTANT EXPRESSION maps to a special node (constant
    // pool), which would silently absorb the flow — unwrap to the
    // pointer operand instead.
    const auto *CE = dyn_cast<ConstantExpr>(src);
    const bool ceP2I = CE && CE->getOpcode() == Instruction::PtrToInt;
    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    if (srcNode != AndersNodeFactory::InvalidIndex &&
        !(ceP2I && CGP.NF.isSpecialNode(srcNode))) {
      CGP.addAssignmentEdge(srcNode, dstNode);
      return;
    }
    if (!ceP2I)
      return; // plain int constant: no provenance
    NodeIndex ptrN = CGP.getRepNodeForValue(CE->getOperand(0));
    if (ptrN == AndersNodeFactory::InvalidIndex || CGP.NF.isSpecialNode(ptrN))
      return;
    if (CGP.EB.hasFieldLabels() && !ptrToIntTagRoundTripOnly(CE))
      CGP.addFieldWildcardLoop(ptrN, "ptrtoint-escape-ce");
    else if (CGP.EB.hasFieldLabels())
      g_tagRoundTrips++;
    CGP.addAssignmentEdge(ptrN, dstNode);
  };
  for (unsigned i = 1; i < I.getNumOperands(); i++) {
    Value *src = I.getOperand(i);
    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in Select: " << *src << "\n");
      continue;
    }
    wireIncoming(src);
  }
}

void CallGraphPass::InstHandler::visitExtractValueInst(ExtractValueInst &EVI) {
  bool resultIsPtr = EVI.getType()->isPointerTy();

  // Check if the aggregate operand already has tracked pointer content.
  // Skip constants (undef, zeroinitializer, etc.) — they map to ConstantIntIndex
  // which doesn't carry useful pointer information.
  Value *agg = EVI.getAggregateOperand();
  NodeIndex aggNode = AndersNodeFactory::InvalidIndex;
  if (!isa<Constant>(agg))
    aggNode = CGP.NF.getValueNodeFor(agg);

  // Nothing to track if the result isn't a pointer and the aggregate
  // has no tracked pointer content to propagate through nested extracts
  if (!resultIsPtr && aggNode == AndersNodeFactory::InvalidIndex)
    return;

  // field insensitive, just connect the aggregate
  NodeIndex valNode = CGP.NF.getValueNodeFor(&EVI);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.NF.createValueNode(&EVI);
  valNode = CGP.getCanonicalNode(valNode);

  if (aggNode != AndersNodeFactory::InvalidIndex)
    CGP.addAssignmentEdge(aggNode, valNode);
}

void CallGraphPass::InstHandler::visitInsertValueInst(InsertValueInst &IVI) {
  // field insensitive, just connect the aggregate
  Value *val = IVI.getInsertedValueOperand();
  bool valIsPtr = val->getType()->isPointerTy();

  // Check if the aggregate operand already has tracked pointer content
  // (e.g., from a prior insertvalue that inserted a pointer).
  // Skip constants (undef, zeroinitializer, etc.) — they map to ConstantIntIndex
  // which doesn't carry useful pointer information.
  Value *agg = IVI.getAggregateOperand();
  NodeIndex aggNode = AndersNodeFactory::InvalidIndex;
  if (!isa<Constant>(agg))
    aggNode = CGP.NF.getValueNodeFor(agg);

  // Nothing to track if the inserted value isn't a pointer and the aggregate
  // has no tracked pointer content
  if (!valIsPtr && aggNode == AndersNodeFactory::InvalidIndex)
    return;

  NodeIndex resNode = CGP.NF.getValueNodeFor(&IVI);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.NF.createValueNode(&IVI);
  resNode = CGP.getCanonicalNode(resNode);

  // Propagate aggregate's pointer content to result
  if (aggNode != AndersNodeFactory::InvalidIndex)
    CGP.addAssignmentEdge(aggNode, resNode);

  // Propagate inserted value if it's a pointer
  if (valIsPtr) {
    NodeIndex valNode = CGP.NF.getValueNodeFor(val);
    assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find insertvalue val node");
    CGP.addAssignmentEdge(valNode, resNode);
  }
}

void CallGraphPass::InstHandler::visitIntToPtrInst(IntToPtrInst &I) {
  if (!CFLProbeStratumAblate.empty() &&
      [&] {
        StrataBucket b = strataClassify(I.getOperand(0), I.getFunction());
        StringRef sel(CFLProbeStratumAblate);
        if (sel == "phys")
          return strataIsPhys(b); // legacy: all four buckets
        // bucket-selective: comma list of directmap,vmemmap,kernelmap,
        // mmfn — struct page descriptors are TYPED KERNEL OBJECTS
        // (vmemmap = metadata stratum), only the direct map exposes
        // page CONTENTS; the separation test severs contents access.
        if (b == STRATA_DIRECTMAP && sel.contains("directmap"))
          return true;
        if (b == STRATA_VMEMMAP && sel.contains("vmemmap"))
          return true;
        if (b == STRATA_KERNELMAP && sel.contains("kernelmap"))
          return true;
        if (b == STRATA_MMFN && sel.contains("mmfn"))
          return true;
        return false;
      }()) {
    // MEASUREMENT-ONLY UNSOUND: sever the phys-stratum bridge — the
    // result becomes an opaque identity (no in-edge -> its own root),
    // as if phys<->virt conversions returned a fresh stratum handle.
    g_strataAblated++;
    return;
  }
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    WARNING("IntToPtr: src node not found: " << I << "\n");
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    WARNING("IntToPtr: dst node not found: " << I << "\n");
    return;
  }
  CG_DEBUG("IntToPtr: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.addAssignmentEdge(srcNode, dstNode);

  // offset_to_ptr rule: inttoptr(add/sub-chain containing ptrtoint p)
  // computes a pointer FROM an array entry — semantically a read of
  // the array (kernel PREL32 idiom: initcalls, pci_fixup, __ksymtab).
  // Pull deref(p) into the result so members wired store-like into the
  // array reach exactly these consumers and no one else. Bounded walk
  // through the integer-arithmetic chain; every ptrtoint leaf counts.
  {
    SmallVector<const Value *, 8> stack{I.getOperand(0)};
    SmallPtrSet<const Value *, 8> seen;
    SmallVector<const PtrToIntOperator *, 4> ptiLeaves;
    SmallVector<const LoadInst *, 4> loadLeaves;
    unsigned steps = 0;
    while (!stack.empty() && steps++ < 16) {
      const Value *V = stack.pop_back_val();
      if (!seen.insert(V).second) continue;
      if (const auto *PTI = dyn_cast<PtrToIntOperator>(V)) {
        ptiLeaves.push_back(PTI);
        continue;
      }
      if (const auto *LI = dyn_cast<LoadInst>(V)) {
        loadLeaves.push_back(LI);
        continue;
      }
      if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
        unsigned op = BO->getOpcode();
        if (op == Instruction::Add || op == Instruction::Sub ||
            op == Instruction::Or) {
          stack.push_back(BO->getOperand(0));
          stack.push_back(BO->getOperand(1));
        }
        continue;
      }
      if (const auto *CI2 = dyn_cast<CastInst>(V)) {
        stack.push_back(CI2->getOperand(0));
        continue;
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        for (const Value *IV : PN->incoming_values()) stack.push_back(IV);
        continue;
      }
    }
    // The pull applies only to the self-relative read p + *p: some
    // load in the chain must read THROUGH the same pointer that was
    // ptrtoint'ed (same value class). Without this the rule fires on
    // percpu rebasing (inttoptr(add(ptrtoint &var, cpu_offset))) where
    // the offset comes from another object and the array pull is
    // noise (subset: value-leak removed but pairs flat until gated).
    for (const PtrToIntOperator *PTI : ptiLeaves) {
      NodeIndex base = CGP.getRepNodeForValue(PTI->getPointerOperand());
      if (base == AndersNodeFactory::InvalidIndex ||
          CGP.NF.isSpecialNode(base))
        continue;
      bool selfRead = false;
      for (const LoadInst *LI : loadLeaves) {
        NodeIndex lp = CGP.getRepNodeForValue(
            LI->getPointerOperand()->stripPointerCasts());
        if (lp != AndersNodeFactory::InvalidIndex &&
            CGP.getCanonicalNode(lp) == CGP.getCanonicalNode(base)) {
          selfRead = true;
          break;
        }
      }
      if (selfRead)
        CGP.addAssignmentEdge(
            CGP.getRepDerefNode(CGP.getCanonicalNode(base)), dstNode);
    }
  }
}

// Kernel code tags ALIGNED pointers in their low bits (p|1 to mark,
// p&~1 to clear, v&7 to extract the tag). Sub-alignment constant
// bit-twiddling never changes the field offset, so a ptrtoint whose
// COMPLETE local use-closure is tag ops + compares + tag extraction +
// inttoptr round trips is not a field escape: the plain a-edges
// already model it exactly (shift 0) and the fx wildcard would only
// smear. Any other use — store/call/ret (downstream rebasing through
// memory is covered ONLY by the source wildcard), offset-destroying
// masks (& ~0xfff), variable or non-tag arithmetic — keeps the
// wildcard. Bounded walk; on cap, keep the wildcard (sound default).
static bool ptrToIntTagRoundTripOnly(const Value *PTI) {
  SmallVector<const Value *, 16> wl{PTI};
  SmallPtrSet<const Value *, 32> seen{PTI};
  unsigned steps = 0;
  while (!wl.empty()) {
    if (++steps > 128)
      return false;
    const Value *V = wl.pop_back_val();
    for (const User *U : V->users()) {
      if (isa<IntToPtrInst>(U) || isa<ICmpInst>(U) || isa<SwitchInst>(U))
        continue; // round trip at offset 0 / compare: exact
      if (const auto *BO = dyn_cast<BinaryOperator>(U)) {
        const auto *CI = dyn_cast<ConstantInt>(
            BO->getOperand(BO->getOperand(0) == V ? 1 : 0));
        if (!CI)
          return false;
        const uint64_t c = CI->getZExtValue();
        switch (BO->getOpcode()) {
        case Instruction::Or:
        case Instruction::Xor:
          if (c >= 8)
            return false; // beyond sub-alignment bits
          break;
        case Instruction::And:
          if (c < 8)
            continue; // tag EXTRACTION: result carries no pointer
          if (~c >= 8)
            return false; // offset-destroying mask (& ~0xfff et al.)
          break; // tag clear (& ~7 and finer)
        default:
          return false;
        }
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      if (isa<ZExtInst>(U) || isa<BitCastInst>(U) || isa<FreezeInst>(U) ||
          isa<PHINode>(U) || isa<SelectInst>(U)) {
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      return false;
    }
  }
  return true;
}

void CallGraphPass::InstHandler::visitPtrToIntInst(PtrToIntInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    WARNING("PtrToInt: src node not found: " << I << "\n");
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
    CG_DEBUG("PtrToInt: created value node " << dstNode << " for " << I << "\n");
  }
  CG_DEBUG("PtrToInt: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  // Field mode: integer arithmetic on the escaped pointer can rebase it to
  // any field (disguised GEP); absorb with the wildcard loop at the source
  // — EXCEPT proven tag-bit round trips, which are exact at shift 0.
  if (CGP.EB.hasFieldLabels()) {
    if (ptrToIntTagRoundTripOnly(&I))
      g_tagRoundTrips++;
    else
      CGP.addFieldWildcardLoop(srcNode, "ptrtoint-escape");
  }
  CGP.addAssignmentEdge(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitBinaryOperator(BinaryOperator &I) {
  if (!I.getType()->isIntegerTy())
    return;

  // Emit a-edges from EVERY pointer-derived operand to the result, per
  // the encoding spec (operand_i -> result). The previous "other
  // operand must be constant" guard WARNed-and-dropped exactly the
  // offset_to_ptr / PREL32 consumer shape the kernel uses for
  // initcalls and pci_fixup: fn = add(ptrtoint base, sext(*entry)).
  NodeIndex dstNode = AndersNodeFactory::InvalidIndex;
  for (unsigned i = 0; i < 2; i++) {
    NodeIndex n = CGP.getRepNodeForValue(I.getOperand(i));
    if (n == AndersNodeFactory::InvalidIndex || CGP.NF.isSpecialNode(n))
      continue;
    if (dstNode == AndersNodeFactory::InvalidIndex) {
      dstNode = CGP.getRepNodeForValue(&I);
      if (dstNode == AndersNodeFactory::InvalidIndex) {
        dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
        CG_DEBUG("BinOp: created value node " << dstNode << " for " << I << "\n");
      }
    }
    CG_DEBUG("BinOp: " << n << " -> " << dstNode << " for " << I << "\n");
    CGP.addAssignmentEdge(n, dstNode);
  }
}

void CallGraphPass::InstHandler::visitVAArgInst(VAArgInst &I) {
  if (!I.getType()->isPointerTy())
    return;

  NodeIndex valNode = CGP.NF.getValueNodeFor(&I);
  if (valNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: result node not found: " << I << "\n");
    return;
  }

  Function *F = I.getParent()->getParent();
  NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
  if (varargNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: vararg node not found for function: " << F->getName() << "\n");
    return;
  }

  CG_DEBUG("VAArg: " << F->getName() << ": vararg node " << varargNode
           << " -> val node " << valNode << " for " << I << "\n");
  CGP.addAssignmentEdge(varargNode, valNode);
}

void CallGraphPass::InstHandler::visitMemTransferInst(MemTransferInst &I) {
  // MemTransferInst covers memcpy and memmove intrinsics
  CGP.handleMemcpy(&I);
  // Record call graph edge for the intrinsic
  if (Function *CF = I.getCalledFunction())
    CGP.Ctx->Callees[&I].insert(CF);
}

void CallGraphPass::InstHandler::visitMemSetInst(MemSetInst &I) {
  // MemSetInst covers memset intrinsics
  // For pointer analysis, memset doesn't transfer pointers, so we can ignore it
  CG_DEBUG("MemSet instruction (ignored for pointer analysis): " << I << "\n");
  // Record call graph edge for the intrinsic
  if (Function *CF = I.getCalledFunction())
    CGP.Ctx->Callees[&I].insert(CF);
}

void CallGraphPass::InstHandler::visitExtractElementInst(ExtractElementInst &I) {
  // Only when extracting a pointer from <N x ptr>
  if (!I.getType()->isPointerTy())
    return;

  Value *vec = I.getVectorOperand();
  NodeIndex vecNode = CGP.getRepNodeForValue(vec);
  if (vecNode == AndersNodeFactory::InvalidIndex) {
    CG_DEBUG("ExtractElement: vec node not found for " << *vec << "\n");
    return;
  }
  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex) {
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  }
  CGP.addAssignmentEdge(vecNode, resNode);
}

void CallGraphPass::InstHandler::visitInsertElementInst(InsertElementInst &I) {
  if (!containsPointerType(I.getType()))
    return;

  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex) {
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  }

  // Propagate the scalar pointer element into the vector
  Value *elt = I.getOperand(1);
  if (containsPointerType(elt->getType())) {
    NodeIndex eltNode = CGP.getRepNodeForValue(elt);
    if (eltNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(eltNode, resNode);
  }

  // Propagate existing elements from the source vector
  Value *vec = I.getOperand(0);
  if (!isa<UndefValue>(vec)) {
    NodeIndex vecNode = CGP.getRepNodeForValue(vec);
    if (vecNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(vecNode, resNode);
  }
}

void CallGraphPass::InstHandler::visitShuffleVectorInst(ShuffleVectorInst &I) {
  if (!containsPointerType(I.getType()))
    return;

  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex) {
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  }

  for (unsigned i = 0; i < 2; i++) {
    Value *vec = I.getOperand(i);
    if (isa<UndefValue>(vec))
      continue;
    NodeIndex vecNode = CGP.getRepNodeForValue(vec);
    if (vecNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(vecNode, resNode);
  }
}

// Process global variable initializer. Field-insensitive by default: every
// pointer in the initializer assigns into `ptrNode` (the global's deref cell).
// In field mode (`addrNode` valid), struct elements are routed into per-field
// cells reached through matched f-edges from the global's address node, so
// initializer contents stay field-separated like runtime stores.
void CallGraphPass::processInitializer(NodeIndex ptrNode, Constant *init,
                                        const std::string &enclosingStruct,
                                        int enclosingFieldIdx,
                                        NodeIndex addrNode) {
  if (!init)
    return;

  // Skip nullptr - don't create edges for null assignments
  if (isa<ConstantPointerNull>(init)) {
    CG_DEBUG("Skipping nullptr in initializer\n");
    return;
  }

  // Skip compiler-introduced values in initializers
  if (shouldSkipValue(init)) {
    CG_DEBUG("Skipping compiler value in initializer: " << *init << "\n");
    return;
  }

  // Aliases (e.g., aliased syscall wrappers) resolve to their aliasee so
  // function/global addresses stored through an alias are not dropped.
  if (auto *GA = dyn_cast<GlobalAlias>(init)) {
    auto *Aliasee = dyn_cast<Constant>(GA->getAliasee()->stripPointerCasts());
    assert(Aliasee && "GlobalAlias with non-constant aliasee in initializer");
    processInitializer(ptrNode, Aliasee, enclosingStruct, enclosingFieldIdx,
                       addrNode);
    return;
  }

  if (isa<GlobalVariable>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &globalvar: add assignment edges globalvar_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    CG_DEBUG("add CFL assignment edges for global variable " << cast<GlobalVariable>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (isa<Function>(init)) {
    auto *storedFunc = cast<Function>(init);
    Function *canonStoredFunc = getFuncDef(storedFunc);
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &function: add assignment edges function_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    // Record direct function store into struct field. A store WITHOUT a
    // derivable key (literal-struct initializer like sysctl tables, plain
    // global, top-level array) must mark the function evidence-incomplete:
    // otherwise named-struct evidence collected elsewhere would wrongly
    // reject callsites that load from the keyless location (the access
    // side may still see a named struct type, e.g. kern_table's literal
    // [38 x {ptr,...}] read through %struct.ctl_table geps).
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      funcFieldStores[canonStoredFunc].insert(
          {enclosingStruct, static_cast<unsigned>(enclosingFieldIdx)});
    else
      funcFieldStoresIncomplete.insert(canonStoredFunc);
    CG_DEBUG("add CFL assignment edges for function " << storedFunc->getName()
             << " -> " << ptrNode << "\n");
  } else if (ConstantArray *CA = dyn_cast<ConstantArray>(init)) {
    // Arrays are collapsed: all elements share the array's cell.
    for (unsigned i = 0; i != CA->getNumOperands(); ++i) {
      processInitializer(ptrNode, CA->getOperand(i), enclosingStruct,
                         enclosingFieldIdx, addrNode);
    }
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(init)) {
    StructType *STy = CS->getType();
    const bool isUnion = STy && STy->hasName() &&
                         LLVM_STRING_STARTS_WITH(STy->getStructName(), "union");
    const bool fieldMode = EB.hasFieldLabels() &&
                           addrNode != AndersNodeFactory::InvalidIndex &&
                           curDL && STy;
    const StructLayout *SL =
        (fieldMode && !isUnion) ? curDL->getStructLayout(STy) : nullptr;
    if (fieldMode && isUnion) {
      // Union members overlay; keep them in the parent cell and absorb any
      // deeper field access with the wildcard loop.
      addFieldWildcardLoop(addrNode, "union-initializer");
    }
    for (unsigned i = 0; i != CS->getNumOperands(); ++i) {
      std::string curStruct = enclosingStruct;
      int curField = enclosingFieldIdx;
      if (STy && !STy->isLiteral() && STy->hasName() && !isUnion) {
        curStruct = stripStructNameSuffix(STy->getStructName()).str();
        curField = i;
      }
      NodeIndex childCell = ptrNode;
      NodeIndex childAddr = addrNode;
      if (SL) {
        int64_t off = (int64_t)SL->getElementOffset(i);
        if (off != 0) {
          NodeIndex parentCanon = getCanonicalNode(addrNode);
          childAddr = getFieldPtrNode(parentCanon, off);
          EB.addFieldEdges(parentCanon, getCanonicalNode(childAddr),
                           fieldBucket(off));
        }
        childCell = getRepDerefNode(childAddr);
      }
      processInitializer(childCell, CS->getOperand(i), curStruct, curField,
                         childAddr);
    }
  } else if (ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(init)) {
    Type *Ty = CAZ->getType();
    if (isa<ArrayType>(Ty) || isa<VectorType>(Ty)) {
      processInitializer(ptrNode, CAZ->getSequentialElement(), enclosingStruct, enclosingFieldIdx);
    } else if (StructType *CSTy = dyn_cast<StructType>(Ty)) {
      for (unsigned i = 0; i != CSTy->getNumElements(); ++i) {
        std::string curStruct = enclosingStruct;
        int curField = enclosingFieldIdx;
        if (!CSTy->isLiteral() && CSTy->hasName() &&
            !LLVM_STRING_STARTS_WITH(CSTy->getStructName(), "union")) {
          curStruct = stripStructNameSuffix(CSTy->getStructName()).str();
          curField = i;
        }
        Constant *elem = CAZ->getStructElement(i);
        processInitializer(ptrNode, elem, curStruct, curField);
      }
    }
  } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(init)) {
    switch (CE->getOpcode()) {
      case Instruction::GetElementPtr: {
        // Field mode: store the canonical constant-GEP field pointer itself
        // (its f-edges from the base are ensured on lookup), keeping the
        // stored address field-precise.
        if (EB.hasFieldLabels()) {
          NodeIndex ceNode = getRepNodeForValue(CE);
          if (ceNode != AndersNodeFactory::InvalidIndex) {
            EB.addAssignmentEdges(ceNode, ptrNode);
            break;
          }
        }
        // Field-insensitive: get the base pointer with casts stripped
        const GEPOperator *GEPOp = cast<GEPOperator>(CE);
        const Value* basePtr = GEPOp->getPointerOperand()->stripPointerCasts();
        NodeIndex baseNode = NF.getValueNodeFor(basePtr);
        if (baseNode == AndersNodeFactory::InvalidIndex) {
          baseNode = NF.createValueNode(basePtr);
        }
        // ptr = base_ptr: add assignment edges base_ptr -> ptr
        EB.addAssignmentEdges(baseNode, ptrNode);
        break;
      }
      case Instruction::BitCast: {
        // BitCast: process the operand directly
        processInitializer(ptrNode, CE->getOperand(0), enclosingStruct, enclosingFieldIdx);
        break;
      }
      case Instruction::IntToPtr: {
        // ptr = (ptr)int: add assignment edges constantInt -> ptr
        // EB.addAssignmentEdges(NF.getConstantIntNode(), ptrNode);
        break;
      }
      default:
        CG_DEBUG("Unhandled constant expression: " << *init << "\n");
    }
  }
}

void CallGraphPass::processCtorsDtors(Module *M) {
  for (StringRef Name : {"llvm.global_ctors", "llvm.global_dtors"}) {
    GlobalVariable *GV = M->getGlobalVariable(Name);
    if (!GV || !GV->hasInitializer())
      continue;
    ConstantArray *CA = dyn_cast<ConstantArray>(GV->getInitializer());
    if (!CA)
      continue;
    for (auto &Op : CA->operands()) {
      if (isa<ConstantAggregateZero>(Op))
        continue;
      ConstantStruct *CS = cast<ConstantStruct>(Op);
      // Operand 1 is the function pointer
      if (Function *F = dyn_cast<Function>(CS->getOperand(1))) {
        auto *RF = getFuncDef(F);
        if (Ctx->CtorDtorFuncs.insert(RF).second)
          CG_LOG("CtorDtor: " << Name << " -> " << RF->getName() << "\n");
      }
    }
  }
}

void CallGraphPass::collectIFuncTargets(const GlobalIFunc *IF) {
  Function *Resolver = const_cast<GlobalIFunc*>(IF)->getResolverFunction();
  if (!Resolver || Resolver->isDeclaration()) {
    CG_DEBUG("IFunc: " << IF->getName() << " resolver not available\n");
    return;
  }
  FuncSet &Targets = IFuncTargets[IF];
  for (auto &BB : *Resolver) {
    if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
      if (!RI->getReturnValue())
        continue;
      Value *RV = RI->getReturnValue()->stripPointerCasts();
      if (auto *F = dyn_cast<Function>(RV)) {
        Targets.insert(getFuncDef(F));
      } else if (auto *LI = dyn_cast<LoadInst>(RV)) {
        // Handle pattern: store @func, %alloca; ... %rv = load %alloca; ret %rv
        Value *Ptr = LI->getPointerOperand();
        for (User *U : Ptr->users()) {
          if (auto *SI = dyn_cast<StoreInst>(U)) {
            if (SI->getPointerOperand() == Ptr) {
              if (auto *F = dyn_cast<Function>(SI->getValueOperand()->stripPointerCasts()))
                Targets.insert(getFuncDef(F));
            }
          }
        }
      }
    }
  }
  CG_LOG("IFunc: " << IF->getName() << " resolved via " << Resolver->getName()
         << " to " << Targets.size() << " target(s)\n");
  for (const Function *T : Targets)
    CG_LOG("  IFunc target: " << T->getName() << "\n");
}

// task #22 phase B: alias undefined linker-array bounds externs to their
// section members. The linker concatenates section-X items between
// __start_X/__stop_X; consumers iterate from the bounds symbol and
// either load members directly (ABS64 arrays: __param, .init.setup,
// _ftrace_events) or compute fn = entry + *entry (PREL32: initcalls,
// pci_fixup) — there the register-provenance chain (ptrtoint/add/
// inttoptr, all visited) carries the bounds symbol's VALUE to the
// consumer, so a-edges member -> bounds cover both shapes under the
// field-insensitive memory model.
// candidate section keys for a bounds symbol name; kernel bounds are
// either generic (__start_X/__stop_X <-> section X modulo _/. prefix)
// or hand-written in vmlinux.lds (the irregulars below)
static bool linkerBoundsSectionKeys(StringRef N, std::vector<std::string> &exact,
                                    std::vector<std::string> &prefix) {
    StringRef K;
    if (N.starts_with("__start_")) {
      K = N.drop_front(8);
    } else if (N.starts_with("__stop_")) {
      K = N.drop_front(7);
    } else if (N.starts_with("__") &&
               (N.ends_with("_start") || N.ends_with("_end"))) {
      K = N.drop_back(N.ends_with("_start") ? 6 : 4);
      exact.push_back(K.str()); // e.g. __governor_thermal_table
      K = K.drop_front(2);      // e.g. initcall5, setup, con_initcall
    } else {
      return false;
    }
    exact.push_back(K.str());         // __param, __tracepoints_ptrs
    exact.push_back(("_" + K).str()); // _ftrace_events
    exact.push_back(("." + K).str()); // .apicdrivers
    if (K.starts_with("initcall")) {
      // per-level bounds delimit a contiguous run of .initcallN.init
      // sections; the union of all levels over-approximates soundly
      prefix.push_back(".initcall");
    } else if (K == "setup") {
      exact.push_back(".init.setup");
    } else if (K == "con_initcall") {
      exact.push_back(".con_initcall.init");
    } else if (K == "_bpf_raw_tp") {
      exact.push_back("__bpf_raw_tp_map");
    } else if (K.starts_with("pci_fixups_")) {
      exact.push_back((".pci_fixup_" + K.drop_front(11)).str());
    } else if (K == "ftrace_eval_maps") {
      exact.push_back("_ftrace_eval_map");
    }
    return true;
}

// Families whose IN-CORPUS consumers treat entries as code/symbol
  // METADATA, not data-flow pointers: (a) patching machinery
  // (static_call, jump_label, extable fixups, mcount) — modeled as
  // control transforms, static_call = task #14; (b) loadable-module
  // linking (__ksymtab/__kcrctab) — resolve_symbol runs on out-of-
  // corpus modules; wiring would inject EVERY exported symbol into
  // the alias world; (c) pure string/metadata tables. Excluded and
// LEDGERed as explicit boundary assumptions.
static bool linkerExcludedFamily(StringRef K) {
    return K.contains("ksymtab") || K.contains("kcrctab") ||
           K.contains("static_call") || K.contains("jump_table") ||
           K.contains("ex_table") || K.contains("bug_table") ||
           K.contains("orc_") || K.contains("mcount") ||
           K.contains("tracepoint_str") || K.contains("bprintk") ||
           K.contains("dyndbg") || K.contains("modver") ||
           K.contains("kprobe_blacklist") || K.contains("notes");
}

// union of members over the bounds symbol's candidate sections; sets
// *unresolved when any matched section had symbol-looking module-asm
// entries that resolve to nothing (membership incomplete)
bool CallGraphPass::linkerArraySources(StringRef boundsName,
                                       std::set<const GlobalValue *> &inPlace,
                                       std::set<const GlobalValue *> &encoded,
                                       bool *unresolved) {
  if (unresolved) *unresolved = false;
  std::vector<std::string> exact, prefix;
  if (!linkerBoundsSectionKeys(boundsName, exact, prefix)) return false;
  auto take = [&](const std::string &sec) {
    auto ip = linkerSectionInPlace.find(sec);
    if (ip != linkerSectionInPlace.end())
      inPlace.insert(ip->second.begin(), ip->second.end());
    auto en = linkerSectionEncoded.find(sec);
    if (en != linkerSectionEncoded.end())
      encoded.insert(en->second.begin(), en->second.end());
    if (unresolved && linkerSectionUnresolved.count(sec))
      *unresolved = true;
  };
  auto takePrefix = [&](const std::string &p,
                        const std::map<std::string,
                                       std::set<const GlobalValue *>> &m) {
    for (auto it = m.lower_bound(p);
         it != m.end() && StringRef(it->first).starts_with(p); ++it)
      take(it->first);
  };
  for (const std::string &k : exact) take(k);
  for (const std::string &p : prefix) {
    takePrefix(p, linkerSectionInPlace);
    takePrefix(p, linkerSectionEncoded);
  }
  return true;
}

void CallGraphPass::wireLinkerSectionArrays() {
  if (!CFLLinkerArrays) return;
  size_t wired = 0, matched = 0, unmatched = 0, nodeless = 0;
  size_t excluded = 0, keptUniversal = 0;
  for (const auto &[guid, EGV] : Ctx->ExtGobjs) {
    StringRef N = EGV->getName();
    std::vector<std::string> exact, prefix;
    if (!linkerBoundsSectionKeys(N, exact, prefix)) continue;
    if (linkerExcludedFamily(N)) {
      excluded++;
      CG_DEBUG("LinkerArrays: bounds " << N
               << " excluded (metadata/patching/module-linking family)\n");
      continue;
    }
    bool unresolved = false;
    std::set<const GlobalValue *> inPlace, encoded;
    linkerArraySources(N, inPlace, encoded, &unresolved);
    if (unresolved) {
      // membership incomplete: symbol keeps the universal fallback,
      // which already over-approximates its reads — wiring would only
      // re-inject members into the universal hub
      keptUniversal++;
      CG_LOG("LinkerArrays: LEDGER bounds " << N
             << " kept universal (unresolved section entries)\n");
      continue;
    }
    if (inPlace.empty() && encoded.empty()) {
      // bounds over metadata sections (orc, bug/ex tables) or arrays
      // with no member in the corpus — ledgered, not silently dropped
      unmatched++;
      CG_DEBUG("LinkerArrays: bounds " << N
               << " has no IR-visible members\n");
      continue;
    }
    if (CFLCompositional && CompressedGraphInputs.empty()) {
      // Per-TU compositional mode cannot compose these flows: the
      // member->bounds edges are added once, after the last module,
      // and belong to no TU's graph, so no TU exports the bounds
      // symbol the compose-time boundary sanity check demands — the
      // composed solve is guaranteed to be rejected many minutes from
      // now. Fail here, at the first wireable bounds symbol.
      errs() << "wireLinkerSectionArrays: bounds symbol " << N
             << " has IR-visible members, but per-TU compositional mode "
                "cannot compose linker-section-array flows. Rerun with "
                "--cfl-compositional=false, or drop the flows explicitly "
                "with --cfl-linker-arrays=false (UNSOUND for kernel "
                "corpora).\n";
      exit(1);
    }
    NodeIndex eNode = NF.getValueNodeFor(EGV);
    assert(eNode != AndersNodeFactory::InvalidIndex &&
           "ExtGobj without value node");
    size_t before = wired;
    auto resolveNode = [&](const GlobalValue *S) -> NodeIndex {
      NodeIndex sNode = NF.getValueNodeFor(S);
      if (sNode == AndersNodeFactory::InvalidIndex) {
        if (auto *F = dyn_cast<Function>(S)) {
          // cross-module asm reference whose defining module was
          // initialized before the reference was seen — mint now
          sNode = NF.createValueNode(F);
          Ctx->AddressTakenFuncs.insert(F);
        } else {
          nodeless++; // skipped compiler global — ledgered
        }
      }
      return sNode;
    };
    // In-place members ARE the array elements: the bounds symbol
    // aliases their objects (value edges). Encoded (PREL32) members
    // live in deref(bounds), read out by the offset_to_ptr pull rule.
    // Precision rests on the bounds symbol having its OWN identity
    // (extGobjOverride) — wiring into the universal fallback leaked
    // every member into all unmodeled-extern reads (whole kernel
    // +2.7M pairs, 72% pci-quirk stubs at unrelated icalls).
    for (const GlobalValue *S : inPlace) {
      NodeIndex sNode = resolveNode(S);
      if (sNode == AndersNodeFactory::InvalidIndex) continue;
      addAssignmentEdge(sNode, eNode);
      wired++;
    }
    for (const GlobalValue *S : encoded) {
      NodeIndex sNode = resolveNode(S);
      if (sNode == AndersNodeFactory::InvalidIndex) continue;
      addAssignmentEdge(sNode, getRepDerefNode(getCanonicalNode(eNode)));
      wired++;
    }
    if (wired > before) matched++;
    CG_DEBUG("LinkerArrays: " << N << " <- " << (wired - before)
             << " members\n");
  }
  CG_LOG("LinkerArrays: " << matched << " bounds symbols wired, " << wired
         << " member flows; LEDGER " << unmatched
         << " bounds without IR-visible members, " << excluded
         << " excluded metadata/patching/module-linking bounds, "
         << keptUniversal << " kept universal (unresolved entries), "
         << nodeless << " nodeless members skipped\n");
}

// --cfl-confirm-fresh (task #17 step A): promote PURE-FRESH wrappers to
// allocator status by body confirmation, to fixpoint over wrapper
// chains. A promoted function's callers get per-callsite object
// identities (the discrimination/closure lever: fewer shared
// identities = fewer co-occurring join witnesses). Promotion implies
// the existing allocator treatment — body SKIPPED, ret edge suppressed
// via a fresh-only summary — so the criteria must make the skip sound:
//   R1 every returned value traces (phi/select/casts only; no GEP —
//      interior returns excluded) to calls of already-fresh functions,
//      null, constant inttoptr (ERR_PTR), or undef;
//   R2 the fresh callsite results are consumed only by that return
//      path plus null-checks (no stores, no escaping args, no
//      ptrtoint);
//   R3 no pointer side effects anywhere else: no store of a
//      pointer-typed value, no non-intrinsic call taking or returning
//      pointers unless the callee is itself fresh/allocator (its
//      formals are dead ends), intrinsics limited to the NOOP set +
//      memset. Rejections are tallied by reason (LEDGER).
static size_t g_freshPromoted = 0, g_freshRejRet = 0, g_freshRejEscape = 0,
              g_freshRejSide = 0, g_freshInit = 0, g_escapeSamples = 0,
              g_freshHelperComposed = 0;
static std::map<std::string, size_t> g_escapeBuckets;
static std::map<std::string, size_t> g_escapeCallees;
void CallGraphPass::confirmFreshWrappers() {
  static GlobalContext::FuncSummary pureFresh; // stable address for the map
  pureFresh.fresh = true;
  auto isNoopIntrinsic = [](const Function *IF) {
    if (!IF->isIntrinsic()) return false;
    StringRef n = IF->getName();
    return n.starts_with("llvm.dbg") || n.starts_with("llvm.lifetime") ||
           n.starts_with("llvm.assume") || n.starts_with("llvm.expect") ||
           n.starts_with("llvm.memset") || n.starts_with("llvm.experimental");
  };
  // Init-helper analysis (step B v2, the dominant call-escape bucket):
  // a helper is INIT-ONLY in pointer param j if param j is used solely
  // as a store base (through GEP/bitcast chains, plus null checks), and
  // every stored value is one of: the helper's own formal m (recorded
  // as a mapping), a non-pointer, null, or a param-j-derived pointer
  // (self-linkage, e.g. INIT_LIST_HEAD). No other pointer side effects
  // anywhere in the helper, all other ptr params unused for stores,
  // void-or-unused result. The wrapper then composes the helper's
  // stores through the callsite into its own ST atoms — one level of
  // summary composition, still zero graph duplication.
  struct InitInfo {
    bool valid = false;
    int objParam = -1;
    SmallVector<int, 4> srcFormals; // helper formal indices stored into obj
    SmallVector<const GlobalValue *, 4> srcGlobals; // globals stored into obj
    bool selfStore = false;         // obj-interior stored into obj
  };
  static std::map<const Function *, InitInfo> initCache;
  std::function<const InitInfo &(const Function *)> initOnlyInfoRef;
  initOnlyInfoRef = [&](const Function *C) -> const InitInfo & {
    auto it = initCache.find(C);
    if (it != initCache.end()) return it->second;
    InitInfo &inf = initCache[C];
    if (C->isDeclaration() || C->isVarArg()) return inf;
    if (!C->getReturnType()->isVoidTy()) return inf; // keep v1 strict
    // classify each pointer param's use graph
    int obj = -1;
    bool bad = false;
    SmallPtrSet<const Value *, 16> objGraph;
    SmallVector<int, 4> srcs;
    SmallVector<const GlobalValue *, 4> gsrcs;
    SmallPtrSet<const Instruction *, 4> nestedInit;
    bool self = false;
    for (const Argument &A2 : C->args()) {
      if (!A2.getType()->isPointerTy()) continue;
      // walk this param's derived-pointer graph
      SmallVector<const Value *, 8> w2{&A2};
      SmallPtrSet<const Value *, 16> g2;
      bool storedInto = false, escapes = false;
      SmallVector<int, 4> mySrcs;
      SmallVector<const GlobalValue *, 4> myGsrcs;
      SmallPtrSet<const Instruction *, 4> myNested;
      bool mySelf = false;
      while (!w2.empty() && !escapes) {
        const Value *v2 = w2.pop_back_val();
        if (!g2.insert(v2).second) continue;
        for (const User *U2 : v2->users()) {
          if (isa<ICmpInst>(U2)) continue;
          if (isa<GetElementPtrInst>(U2) || isa<BitCastInst>(U2)) {
            w2.push_back(cast<Value>(U2));
            continue;
          }
          if (const auto *SI2 = dyn_cast<StoreInst>(U2)) {
            if (SI2->getValueOperand() == v2) {
              // param-derived ptr stored: self-linkage iff the target
              // is also param-derived; a DIRECT formal stored into a
              // sibling param's memory is the init itself (recorded by
              // the sibling's walk as an Argument-source store-into);
              // any other target is an escape.
              const Value *tb = SI2->getPointerOperand()->stripPointerCasts();
              while (const auto *G3 = dyn_cast<GetElementPtrInst>(tb))
                tb = G3->getPointerOperand()->stripPointerCasts();
              if (g2.count(tb) || tb == &A2) { mySelf = true; storedInto = true; continue; }
              if (v2 == &A2) {
                if (const auto *TA = dyn_cast<Argument>(tb)) {
                  if (TA->getParent() == C && TA != &A2)
                    continue; // sibling records this as its init store
                }
              }
              escapes = true;
              break;
            }
            // store INTO param memory
            storedInto = true;
            const Value *sv2 = SI2->getValueOperand()->stripPointerCasts();
            if (!containsPointerType(sv2->getType())) continue;
            if (isa<ConstantPointerNull>(sv2)) continue;
            if (g2.count(sv2)) { mySelf = true; continue; }
            if (const auto *SA = dyn_cast<Argument>(sv2)) {
              if (SA->getParent() == C) { mySrcs.push_back((int)SA->getArgNo()); continue; }
            }
            if (const auto *SG = dyn_cast<GlobalValue>(sv2)) {
              myGsrcs.push_back(SG); // ops tables etc.
              continue;
            }
            escapes = true; // derived value: reject helper
            break;
          }
          if (const auto *NC = dyn_cast<CallBase>(U2)) {
            // nested init helper on this param (vma_init ->
            // vma_numab_state_init shape): recurse. The cache entry is
            // default-invalid while in flight, so cycles reject
            // naturally.
            const Function *C2 = NC->getCalledFunction();
            bool okNested = false;
            if (C2 && NC->getCalledOperand()->stripPointerCasts() != v2 &&
                NC->getType()->isVoidTy()) {
              const InitInfo &ni = initOnlyInfoRef(C2);
              bool pOk = ni.valid && ni.objParam < (int)NC->arg_size() &&
                         NC->getArgOperand(ni.objParam)
                                 ->stripPointerCasts() == v2;
              if (pOk)
                for (unsigned ai2 = 0; ai2 < NC->arg_size(); ai2++)
                  if ((int)ai2 != ni.objParam &&
                      NC->getArgOperand(ai2)->stripPointerCasts() == v2)
                    pOk = false;
              if (pOk) {
                okNested = true;
                for (int m3 : ni.srcFormals) {
                  if (m3 >= (int)NC->arg_size()) { okNested = false; break; }
                  const Value *av2 =
                      NC->getArgOperand(m3)->stripPointerCasts();
                  if (!containsPointerType(av2->getType())) continue;
                  if (isa<ConstantPointerNull>(av2)) continue;
                  if (g2.count(av2)) { mySelf = true; continue; }
                  if (const auto *NA = dyn_cast<Argument>(av2)) {
                    if (NA->getParent() == C) {
                      mySrcs.push_back((int)NA->getArgNo());
                      continue;
                    }
                  }
                  if (const auto *NG = dyn_cast<GlobalValue>(av2)) {
                    myGsrcs.push_back(NG);
                    continue;
                  }
                  okNested = false;
                  break;
                }
                if (okNested) {
                  for (const GlobalValue *NG2 : ni.srcGlobals)
                    myGsrcs.push_back(NG2);
                  if (ni.selfStore) mySelf = true;
                  storedInto = true;
                  myNested.insert(NC);
                }
              }
            }
            if (!okNested) { escapes = true; break; }
            continue;
          }
          escapes = true;
          break;
        }
      }
      if (escapes) { bad = true; break; }
      if (storedInto) {
        if (obj >= 0) { bad = true; break; } // one stored-into param only
        obj = (int)A2.getArgNo();
        objGraph = g2;
        srcs = mySrcs;
        gsrcs = myGsrcs;
        for (const Instruction *NI2 : myNested) nestedInit.insert(NI2);
        self = mySelf;
      }
    }
    if (bad || obj < 0) return inf;
    // no other pointer side effects in the helper body
    for (auto II2 = inst_begin(*C), IE2 = inst_end(*C); II2 != IE2; ++II2) {
      const Instruction *I3 = &*II2;
      if (const auto *SI3 = dyn_cast<StoreInst>(I3)) {
        const Value *pb3 = SI3->getPointerOperand()->stripPointerCasts();
        while (const auto *G4 = dyn_cast<GetElementPtrInst>(pb3))
          pb3 = G4->getPointerOperand()->stripPointerCasts();
        if (!objGraph.count(pb3) &&
            !(isa<Argument>(pb3) &&
              cast<Argument>(pb3)->getArgNo() == (unsigned)obj)) {
          if (containsPointerType(SI3->getValueOperand()->getType()))
            return inf;
        }
        continue;
      }
      if (const auto *CB3 = dyn_cast<CallBase>(I3)) {
        if (nestedInit.count(I3)) continue; // composed nested init
        const Function *CF3 = CB3->getCalledFunction();
        if (CF3 && isNoopIntrinsic(CF3)) continue;
        return inf; // any real call: reject helper (v1)
      }
      if (isa<PtrToIntInst>(I3) || isa<AtomicRMWInst>(I3) ||
          isa<AtomicCmpXchgInst>(I3) || isa<LoadInst>(I3))
        ; // loads are fine (reads don't move pointers outward)
    }
    inf.valid = true;
    inf.objParam = obj;
    inf.srcFormals = srcs;
    inf.srcGlobals = gsrcs;
    inf.selfStore = self;
    return inf;
  };
  auto &initOnlyInfo = initOnlyInfoRef;
  size_t round = 0;
  bool changed = true;
  while (changed) {
    changed = false;
    round++;
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
        if (!F.getReturnType()->isPointerTy()) continue;
        if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
          continue;
        if (Ctx->FuncSummaries.count(&F)) continue;
        auto calleeFresh = [&](const CallBase *CB) {
          const Function *CF = CB->getCalledFunction();
          return CF && Ctx->AllocFuncs.count(CF);
        };
        // R1: trace returns to fresh sources.
        SmallPtrSet<const Value *, 16> onRetPath;
        SmallVector<const Value *, 8> work;
        bool ok = true;
        for (auto &BB : F)
          if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
            if (RI->getReturnValue()) work.push_back(RI->getReturnValue());
        if (work.empty()) continue; // no pointer actually returned
        while (!work.empty() && ok) {
          const Value *v = work.pop_back_val();
          if (!onRetPath.insert(v).second) continue;
          if (isa<ConstantPointerNull>(v) || isa<UndefValue>(v)) continue;
          if (const auto *CE = dyn_cast<ConstantExpr>(v)) {
            if (CE->getOpcode() == Instruction::IntToPtr) continue; // ERR_PTR
            ok = false;
            continue;
          }
          if (const auto *CB = dyn_cast<CallBase>(v)) {
            if (!calleeFresh(CB)) ok = false;
            continue;
          }
          if (const auto *PN = dyn_cast<PHINode>(v)) {
            for (const Value *iv : PN->incoming_values()) work.push_back(iv);
            continue;
          }
          if (const auto *Sel = dyn_cast<SelectInst>(v)) {
            work.push_back(Sel->getTrueValue());
            work.push_back(Sel->getFalseValue());
            continue;
          }
          if (const auto *Cast = dyn_cast<CastInst>(v)) {
            if (Cast->getOpcode() == Instruction::BitCast ||
                Cast->getOpcode() == Instruction::AddrSpaceCast) {
              work.push_back(Cast->getOperand(0));
              continue;
            }
          }
          ok = false; // GEP, load, argument, anything else: not pure fresh
        }
        if (!ok) { g_freshRejRet++; continue; }
        // R2/B: classify every use of the fresh object graph. Allowed:
        // the return path, null checks, and — the STEP-B extension —
        // GEP chains off the fresh pointer whose leaves are stores of
        // FORMAL ARGUMENTS (or non-pointer values) into the object:
        // the alloc-init shape, expressible as ST(*ret <- argI) atoms
        // applied per callsite (an infinite clone with no graph
        // duplication). Anything else remains an escape.
        SmallPtrSet<const Value *, 16> freshGraph; // fresh ptr + GEPs
        SmallPtrSet<const Instruction *, 8> initStores;
        SmallPtrSet<const Instruction *, 4> initCalls; // composed helpers
        SmallVector<int, 4> initArgs;
        SmallVector<const GlobalValue *, 4> initGlobals;
        unsigned subAllocs = 0;
        bool selfStore = false;
        bool escaped = false, untracedInit = false;
        const char *rejWhy = nullptr; // escape-anatomy bucket
        {
          SmallVector<const Value *, 8> gwork;
          for (const Value *v : onRetPath)
            if (isa<CallBase>(v)) gwork.push_back(v);
          SmallPtrSet<const Value *, 16> seen;
          while (!gwork.empty() && !escaped) {
            const Value *v = gwork.pop_back_val();
            if (!seen.insert(v).second) continue;
            freshGraph.insert(v);
            for (const User *U : v->users()) {
              const Value *uv = cast<Value>(U);
              if (onRetPath.count(uv) || isa<ICmpInst>(U) ||
                  isa<ReturnInst>(U))
                continue;
              if (isa<GetElementPtrInst>(U) || isa<BitCastInst>(U)) {
                gwork.push_back(uv);
                continue;
              }
              if (const auto *SI = dyn_cast<StoreInst>(U)) {
                // store INTO the fresh graph is init; storing the fresh
                // pointer ITSELF somewhere else is an escape — bucket
                // it by where it lands.
                if (SI->getValueOperand() == v) {
                  const Value *pb =
                      SI->getPointerOperand()->stripPointerCasts();
                  while (const auto *G2 = dyn_cast<GetElementPtrInst>(pb))
                    pb = G2->getPointerOperand()->stripPointerCasts();
                  if (seen.count(pb) || freshGraph.count(pb)) {
                    // self-linkage (INIT_LIST_HEAD): object interior
                    // stored into the object itself
                    initStores.insert(SI);
                    selfStore = true;
                    continue;
                  }
                  if (const auto *PA = dyn_cast<Argument>(pb))
                    rejWhy = PA->getParent() == &F ? "outparam-store"
                                                   : "store-foreign-arg";
                  else if (isa<GlobalVariable>(pb))
                    rejWhy = "global-store";
                  else if (isa<LoadInst>(pb))
                    rejWhy = "store-into-loaded"; // list linkage shape
                  else
                    rejWhy = "store-other";
                  escaped = true;
                  break;
                }
                const Value *sv =
                    SI->getValueOperand()->stripPointerCasts();
                if (!containsPointerType(sv->getType())) {
                  initStores.insert(SI);
                  continue;
                }
                if (const auto *A2 = dyn_cast<Argument>(sv)) {
                  if (A2->getParent() == &F) {
                    initStores.insert(SI);
                    initArgs.push_back((int)A2->getArgNo());
                    continue;
                  }
                }
                if (isa<ConstantPointerNull>(sv)) {
                  initStores.insert(SI);
                  continue;
                }
                if (const auto *GVs = dyn_cast<GlobalValue>(sv)) {
                  initStores.insert(SI); // ops table / named fn into fresh
                  initGlobals.push_back(GVs);
                  continue;
                }
                if (const auto *SubCB = dyn_cast<CallBase>(sv)) {
                  // second allocation stored into the object
                  // (vm_area_alloc's vma_lock): FreshSub atom, provided
                  // the sub-result's other uses are only null checks
                  // and error-path frees
                  const Function *SubF = SubCB->getCalledFunction();
                  if (SubF && Ctx->AllocFuncs.count(SubF)) {
                    bool subOk = true;
                    for (const User *SU : SubCB->users()) {
                      if (SU == SI || isa<ICmpInst>(SU)) continue;
                      if (const auto *FC = dyn_cast<CallBase>(SU)) {
                        const Function *FF = FC->getCalledFunction();
                        if (FF && isFreeFn(FF->getName())) continue;
                      }
                      subOk = false;
                      break;
                    }
                    if (subOk) {
                      initStores.insert(SI);
                      subAllocs++;
                      continue;
                    }
                  }
                }
                untracedInit = true; // ptr from load/call: reject
                rejWhy = isa<GlobalValue>(sv)   ? "init-from-global"
                         : isa<LoadInst>(sv)    ? "init-from-load"
                         : isa<CallBase>(sv)    ? "init-from-call"
                         : isa<PHINode>(sv)     ? "init-from-phi"
                                                : "init-other";
                break;
              }
              if (const auto *CB2 = dyn_cast<CallBase>(U)) {
                const Function *EC = CB2->getCalledFunction();
                if (EC && (EC->getName().starts_with("llvm.memset") ||
                           EC->getName().starts_with("llvm.lifetime") ||
                           EC->getName().starts_with("llvm.dbg"))) {
                  continue; // zeroing/markers: no pointer content moved
                }
                // Curated benign-init callees: lock/waitqueue/completion
                // initializers store no program function pointers at
                // init time (lockdep names/keys are rodata metadata).
                // LEDGERed via the promotion log; extend deliberately.
                static const char *kBenignInit[] = {
                    "__raw_spin_lock_init", "lockdep_init_map_type",
                    "__init_waitqueue_head", "__mutex_init",
                    "init_completion", "__init_swait_queue_head",
                    "__init_rwsem", "seqcount_init", "__seqcount_init"};
                bool benign = false;
                if (EC)
                  for (const char *bn : kBenignInit)
                    if (EC->getName() == bn) { benign = true; break; }
                if (benign) {
                  initCalls.insert(CB2);
                  continue;
                }
                if (EC && isFreeFn(EC->getName())) {
                  // fresh freed on an error path: the object dies; the
                  // summary's fresh-object over-approximation is sound
                  initCalls.insert(CB2);
                  continue;
                }
                bool composed = false;
                if (EC && CB2->getCalledOperand()->stripPointerCasts() != v) {
                  const InitInfo &inf = initOnlyInfo(EC);
                  bool posOk = inf.valid &&
                               inf.objParam < (int)CB2->arg_size() &&
                               CB2->getArgOperand(inf.objParam)
                                       ->stripPointerCasts() == v;
                  if (posOk)
                    for (unsigned ai = 0; ai < CB2->arg_size(); ai++)
                      if ((int)ai != inf.objParam &&
                          CB2->getArgOperand(ai)->stripPointerCasts() == v)
                        posOk = false; // fresh escapes via a second slot
                  if (posOk) {
                    bool mapOk = true;
                    SmallVector<int, 4> mapped;
                    for (int m2 : inf.srcFormals) {
                      if (m2 >= (int)CB2->arg_size()) { mapOk = false; break; }
                      const Value *av =
                          CB2->getArgOperand(m2)->stripPointerCasts();
                      if (!containsPointerType(av->getType())) continue;
                      if (isa<ConstantPointerNull>(av)) continue;
                      if (const auto *AA = dyn_cast<Argument>(av)) {
                        if (AA->getParent() == &F) {
                          mapped.push_back((int)AA->getArgNo());
                          continue;
                        }
                      }
                      mapOk = false;
                      break;
                    }
                    if (mapOk) {
                      for (int g3 : mapped) initArgs.push_back(g3);
                      for (const GlobalValue *G5 : inf.srcGlobals)
                        initGlobals.push_back(G5);
                      if (inf.selfStore) selfStore = true;
                      initCalls.insert(CB2);
                      composed = true;
                      g_freshHelperComposed++;
                    }
                  }
                }
                if (!composed) {
                  rejWhy = EC ? "call-escape" : "icall-escape";
                  if (EC) g_escapeCallees[EC->getName().str()]++;
                  escaped = true;
                  break;
                }
                continue;
              }
              if (isa<PHINode>(U) || isa<SelectInst>(U)) {
                rejWhy = "phi-route";
                escaped = true;
                break;
              }
              if (isa<PtrToIntInst>(U)) rejWhy = "ptrtoint";
              else rejWhy = "other-use";
              escaped = true;
              break;
            }
          }
        }
        if (escaped || untracedInit) {
          g_freshRejEscape++;
          g_escapeBuckets[rejWhy ? rejWhy : "unknown"]++;
          if (g_escapeSamples < 40 && rejWhy) {
            g_escapeSamples++;
            CG_LOG("ConfirmFresh ESCAPE: " << F.getName() << " ["
                   << rejWhy << "]\n");
          }
          continue;
        }
        // R3: no pointer side effects elsewhere (classified init stores
        // are exempt — they become atoms).
        for (auto II = inst_begin(F), IE = inst_end(F); II != IE && ok;
             ++II) {
          const Instruction *I2 = &*II;
          if (const auto *SI = dyn_cast<StoreInst>(I2)) {
            if (initStores.count(I2)) continue;
            if (containsPointerType(SI->getValueOperand()->getType()))
              ok = false;
            continue;
          }
          if (const auto *CB = dyn_cast<CallBase>(I2)) {
            if (initCalls.count(I2)) continue; // composed init helper
            const Function *CF = CB->getCalledFunction();
            if (CF && (isNoopIntrinsic(CF) || Ctx->AllocFuncs.count(CF) ||
                       isFreeFn(CF->getName())))
              continue;
            bool ptrInvolved =
                containsPointerType(CB->getType()) && !onRetPath.count(CB);
            for (const Value *a2 : CB->args())
              if (containsPointerType(a2->getType())) ptrInvolved = true;
            if (!CF || ptrInvolved) ok = false; // indirect or ptr-carrying
            continue;
          }
          if (isa<PtrToIntInst>(I2) || isa<AtomicRMWInst>(I2) ||
              isa<AtomicCmpXchgInst>(I2))
            ok = false;
        }
        if (!ok) { g_freshRejSide++; continue; }
        // Promote. Pure fresh -> shared static summary; alloc-init ->
        // generated {FRESH, ST(*ret <- argI)...} summary (owned by Ctx).
        Ctx->AllocFuncs.insert(&F);
        if (initArgs.empty() && initGlobals.empty() && !selfStore &&
            subAllocs == 0) {
          Ctx->FuncSummaries[&F] = &pureFresh;
        } else {
          Ctx->OwnedSummaries.emplace_back();
          GlobalContext::FuncSummary &S = Ctx->OwnedSummaries.back();
          S.fresh = true;
          std::sort(initArgs.begin(), initArgs.end());
          initArgs.erase(std::unique(initArgs.begin(), initArgs.end()),
                         initArgs.end());
          for (int an : initArgs) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::Store;
            A.dst = -1; // *ret
            A.src = an;
            S.atoms.push_back(A);
          }
          if (selfStore) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::Store;
            A.dst = -1;
            A.src = -1; // object interior stored into itself
            S.atoms.push_back(A);
          }
          for (unsigned si2 = 0; si2 < subAllocs; si2++) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::FreshSub;
            A.dst = -1; // sub-object into *ret
            S.atoms.push_back(A);
          }
          {
            std::sort(initGlobals.begin(), initGlobals.end());
            initGlobals.erase(
                std::unique(initGlobals.begin(), initGlobals.end()),
                initGlobals.end());
            for (const GlobalValue *G5 : initGlobals) {
              GlobalContext::SummaryAtom A{};
              A.kind = GlobalContext::SummaryAtom::Store;
              A.dst = -1; // *ret
              A.gsrc = G5;
              S.atoms.push_back(A);
            }
          }
          Ctx->FuncSummaries[&F] = &S;
          g_freshInit++;
        }
        g_freshPromoted++;
        changed = true;
        if (g_freshPromoted <= 20)
          CG_LOG("ConfirmFresh: promoted " << F.getName()
                 << (initArgs.empty() ? "" : " [alloc-init]") << " (round "
                 << round << ")\n");
      }
    }
  }
  CG_LOG("ConfirmFresh: " << g_freshPromoted << " wrappers promoted ("
         << g_freshInit << " alloc-init with ST atoms) in " << round
         << " rounds; " << g_freshHelperComposed << " init-helper calls "
         << "composed; rejected " << g_freshRejRet << " ret-not-fresh, "
         << g_freshRejEscape << " escapes, " << g_freshRejSide
         << " ptr-side-effects\n");
  for (auto &eb : g_escapeBuckets)
    CG_LOG("ConfirmFresh escape-bucket[" << eb.first << "]: " << eb.second
           << "\n");
  {
    std::vector<std::pair<size_t, std::string>> ce;
    for (auto &kv : g_escapeCallees) ce.emplace_back(kv.second, kv.first);
    std::sort(ce.begin(), ce.end(), std::greater<>());
    size_t shown = 0;
    for (auto &kv : ce) {
      if (shown++ >= 25) break;
      CG_LOG("ConfirmFresh escape-callee x" << kv.first << " " << kv.second
             << "\n");
    }
  }
}

// --func-summaries: parse the transfer-summary file. Line format:
//   <name>[*] ATOM [ATOM...]   ('*' suffix = prefix match; '#' comments)
// Atoms: FRESH | NONE | CPY(ret<-argN) | CPY(argM<-argN) |
//        ALIAS(ret=argN) | ST(*argC<-argV) | LD(ret<-*argC)
// Ordered, first match wins (NONE entries carve exclusions out of a
// following prefix rule, mirroring the legacy isAllocFn ordering).
// Parse errors are FATAL: a silently dropped summary is a silent
// soundness/precision change.
static void loadFuncSummaries(GlobalContext *Ctx, const std::string &path) {
  std::ifstream in(path);
  if (!in) {
    errs() << "FuncSummary: cannot open " << path << "\n";
    assert(false && "--func-summaries file unreadable");
    return;
  }
  auto parseRef = [](StringRef tok, int &out) -> bool {
    if (tok == "ret") { out = -1; return true; }
    if (tok.consume_front("arg")) {
      unsigned v;
      if (!tok.getAsInteger(10, v)) { out = (int)v; return true; }
    }
    return false;
  };
  std::string line;
  size_t lineNo = 0, nFresh = 0, nCpy = 0, nAlias = 0, nSt = 0, nLd = 0,
         nNone = 0, nInv = 0, nChR = 0, nChC = 0;
  while (std::getline(in, line)) {
    lineNo++;
    StringRef L = StringRef(line).trim();
    if (L.empty() || L.starts_with("#")) continue;
    SmallVector<StringRef, 6> toks;
    L.split(toks, ' ', -1, false);
    GlobalContext::FuncSummary S;
    bool bad = toks.size() < 2;
    for (size_t i = 1; i < toks.size() && !bad; i++) {
      StringRef t = toks[i].trim();
      if (t.empty()) continue;
      GlobalContext::SummaryAtom A{};
      if (t == "FRESH") {
        A.kind = GlobalContext::SummaryAtom::Fresh;
        S.fresh = true;
        nFresh++;
      } else if (t == "NONE") {
        S.none = true;
        nNone++;
        continue;
      } else if (t.consume_front("CPY(") && t.consume_back(")")) {
        auto [d, s] = t.split("<-");
        A.kind = GlobalContext::SummaryAtom::Cpy;
        bad = !parseRef(d, A.dst) || !parseRef(s, A.src) || A.src < 0;
        nCpy++;
      } else if (t.consume_front("ALIAS(") && t.consume_back(")")) {
        auto [d, s] = t.split("=");
        A.kind = GlobalContext::SummaryAtom::Alias;
        bad = !parseRef(d, A.dst) || !parseRef(s, A.src) || A.src < 0;
        nAlias++;
      } else if (t.consume_front("ST(*") && t.consume_back(")")) {
        auto [c, v] = t.split("<-");
        A.kind = GlobalContext::SummaryAtom::Store;
        bad = !parseRef(c, A.dst) || !parseRef(v, A.src) || A.dst < 0;
        nSt++;
      } else if (t.consume_front("INVOKE(") && t.consume_back(")")) {
        auto [fnp, rest2] = t.split(":");
        A.kind = GlobalContext::SummaryAtom::Invoke;
        bad = !parseRef(fnp, A.dst) || A.dst < 0;
        if (!bad && rest2 == "ret") {
          // ret-transparency only: INVOKE(argF:ret). Args stay pooled
          // (no completeness claim); constant-fn callsites bind the
          // invoked fn's return to THIS callsite value instead of the
          // pooled HOF return (the ret-pooling hub channel).
          A.src = -1;
          A.aux = -1;
          A.off = 1;
        } else if (!bad) {
          auto [fk, dp] = rest2.split("<-");
          if (dp.consume_back(":ret"))
            A.off = 1; // data binding + ret-transparency
          bad = !parseRef(dp, A.src) || A.src < 0;
          unsigned fkv = 0;
          if (!bad) {
            StringRef fks = fk;
            bad = !fks.consume_front("f") || fks.getAsInteger(10, fkv);
            A.aux = (int)fkv;
          }
        }
        nInv++;
      } else if (t.consume_front("CHAINREG(") && t.consume_back(")")) {
        // CHAINREG(argK,*argB+OFF,fS): key at argK; callback at byte
        // OFF inside the block global at argB; block -> formal fS
        SmallVector<StringRef, 3> ps;
        t.split(ps, ',');
        A.kind = GlobalContext::SummaryAtom::ChainReg;
        bad = ps.size() != 3;
        if (!bad) {
          StringRef k = ps[0];
          if (k.consume_front("@")) {
            A.gsym = k.str(); // global-keyed variant (wrapper lift)
            bad = A.gsym.empty();
          } else {
            bad = !parseRef(k, A.dst) || A.dst < 0;
          }
        }
        if (!bad) {
          StringRef b = ps[1];
          bad = !b.consume_front("*");
          auto [ba, boff] = b.split('+');
          unsigned offv = 0, fkv = 0;
          bad = bad || !parseRef(ba, A.src) || A.src < 0 ||
                boff.getAsInteger(10, offv);
          StringRef fs = ps[2];
          bad = bad || !fs.consume_front("f") || fs.getAsInteger(10, fkv);
          A.off = (int)offv;
          A.fk = (int)fkv;
        }
        nChR++;
      } else if (t.consume_front("CHAINCALL(") && t.consume_back(")")) {
        // CHAINCALL(argK:fN<-argV): key at argK; dispatch value argV ->
        // each registered callback's formal fN
        auto [kp, rest2] = t.split(':');
        auto [fkp, vp] = rest2.split("<-");
        A.kind = GlobalContext::SummaryAtom::ChainCall;
        unsigned fkv = 0;
        StringRef fks = fkp;
        bad = !parseRef(kp, A.dst) || A.dst < 0 || !parseRef(vp, A.src) ||
              A.src < 0 || !fks.consume_front("f") ||
              fks.getAsInteger(10, fkv);
        A.fk = (int)fkv;
        nChC++;
      } else if (t.consume_front("LD(") && t.consume_back(")")) {
        auto [d, c] = t.split("<-*");
        A.kind = GlobalContext::SummaryAtom::Load;
        bad = !parseRef(d, A.dst) || !parseRef(c, A.src) || A.src < 0;
        nLd++;
      } else {
        bad = true;
      }
      if (!bad && !S.none) S.atoms.push_back(A);
    }
    if (bad) {
      errs() << "FuncSummary: parse error at " << path << ":" << lineNo
             << ": '" << line << "'\n";
      assert(false && "malformed func-summaries line");
      continue;
    }
    Ctx->SummarySpecs.emplace_back(toks[0].str(), std::move(S));
  }
  CG_LOG("FuncSummary: loaded " << Ctx->SummarySpecs.size() << " specs from "
         << path << " (" << nFresh << " FRESH, " << nCpy << " CPY, "
         << nAlias << " ALIAS, " << nSt << " ST, " << nLd << " LD, "
         << nInv << " INVOKE, " << nChR << " CHAINREG, " << nChC
         << " CHAINCALL, " << nNone << " NONE)\n");
}

// First-match-wins spec lookup ('*' suffix = prefix).
static const GlobalContext::FuncSummary *
summaryForName(GlobalContext *Ctx, StringRef name) {
  for (const auto &sp : Ctx->SummarySpecs) {
    StringRef pat(sp.first);
    bool hit = pat.consume_back("*") ? name.starts_with(pat) : name == pat;
    if (hit) return sp.second.none ? nullptr : &sp.second;
  }
  return nullptr;
}

// Apply the non-FRESH atoms of a summary at a callsite. FRESH itself is
// carried by the existing AllocFuncs machinery (per-callsite AllocSite +
// opaque heap object). Cell-copy edges are shift-preserving by
// construction (a-edge between deref nodes), which is exactly right for
// aligned whole-buffer dups (kmemdup family); prefix copies
// over-approximate soundly.
static size_t g_sumInvokeRet = 0; // INVOKE :ret bindings applied
static size_t g_sumCpy = 0, g_sumAlias = 0, g_sumSt = 0, g_sumLd = 0,
              g_sumSkipped = 0, g_sumFreshSub = 0, g_sumInvoke = 0,
              g_sumInvokeDyn = 0, g_chainReg = 0, g_chainRegDyn = 0,
              g_chainCall = 0, g_chainCallDyn = 0, g_chainLate = 0;
// Returns true when an Invoke atom's fn operand is not a constant
// function at this callsite — the caller must fall back to the pooled
// arg/ret wiring for soundness (LEDGERed).
// Chain keys must be canonical across TUs: external-linkage heads have
// per-TU declaration copies; map through Gobjs/ExtGobjs by GUID.
const GlobalValue *CallGraphPass::canonChainKey(const GlobalValue *G) {
  if (!G || G->hasLocalLinkage()) return G;
  auto git = Ctx->Gobjs.find(G->getGUID());
  if (git != Ctx->Gobjs.end() && git->second) return git->second;
  auto eit = Ctx->ExtGobjs.find(G->getGUID());
  if (eit != Ctx->ExtGobjs.end() && eit->second) return eit->second;
  return G;
}

bool CallGraphPass::applySummaryAtoms(const CallBase *CS,
                                      const GlobalContext::FuncSummary &S,
                                      bool *retBound) {
  bool needPooled = false;
  auto nodeForRef = [&](int ref, bool create) -> NodeIndex {
    const Value *v =
        ref < 0 ? (const Value *)CS
                : ((unsigned)ref < CS->arg_size() ? CS->getArgOperand(ref)
                                                  : nullptr);
    if (!v) { g_sumSkipped++; return AndersNodeFactory::InvalidIndex; }
    NodeIndex n = getRepNodeForValue(v);
    if (n == AndersNodeFactory::InvalidIndex && create)
      n = getCanonicalNode(NF.createValueNode(v));
    if (n == AndersNodeFactory::InvalidIndex) g_sumSkipped++;
    return n;
  };
  for (const auto &A : S.atoms) {
    switch (A.kind) {
    case GlobalContext::SummaryAtom::Fresh:
      break; // AllocFuncs path owns object creation
    case GlobalContext::SummaryAtom::Cpy: {
      NodeIndex d = nodeForRef(A.dst, true), s = nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          s == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(getRepDerefNode(getCanonicalNode(s)),
                        getRepDerefNode(getCanonicalNode(d)));
      g_sumCpy++;
      break;
    }
    case GlobalContext::SummaryAtom::Alias: {
      NodeIndex d = nodeForRef(A.dst, true), s = nodeForRef(A.src, false);
      if (d == AndersNodeFactory::InvalidIndex ||
          s == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(getCanonicalNode(s), getCanonicalNode(d));
      g_sumAlias++;
      break;
    }
    case GlobalContext::SummaryAtom::Store: {
      NodeIndex c = nodeForRef(A.dst, true);
      NodeIndex v = A.gsrc ? getRepNodeForValue(A.gsrc)
                           : nodeForRef(A.src, false);
      if (A.gsrc && v == AndersNodeFactory::InvalidIndex)
        v = getCanonicalNode(NF.createValueNode(A.gsrc));
      if (c == AndersNodeFactory::InvalidIndex ||
          v == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(getCanonicalNode(v),
                        getRepDerefNode(getCanonicalNode(c)));
      g_sumSt++;
      break;
    }
    case GlobalContext::SummaryAtom::Invoke: {
      // pair-correlated dispatch: bind data to the registered fn's
      // formal directly and re-attribute the invocation to this
      // registration site (Callees export edge). The pooled container
      // path drains because the summarized registration no longer
      // feeds it. A.off==1 adds RET-TRANSPARENCY: the callsite value
      // receives (only) the invoked fn's return — severs the
      // ret-pooling hub channel (fwnode devcon family, task #31).
      if ((unsigned)A.dst >= CS->arg_size() ||
          (A.src >= 0 && (unsigned)A.src >= CS->arg_size())) {
        g_sumSkipped++;
        break;
      }
      const Value *fv = CS->getArgOperand(A.dst)->stripPointerCasts();
      if (isa<ConstantPointerNull>(fv))
        break; // null fn: never invoked, nothing to bind
      const auto *RF = dyn_cast<Function>(fv);
      if (!RF) {
        // dynamic fn: cannot bind statically — signal pooled fallback
        // (ret included: the pooled return edge stays)
        g_sumInvokeDyn++;
        needPooled = true;
        break;
      }
      Function *DF = getFuncDef(const_cast<Function *>(RF));
      if (A.src >= 0 && (unsigned)A.aux < DF->arg_size()) {
        NodeIndex dn = nodeForRef(A.src, false);
        NodeIndex fn2 = getRepNodeForValue(DF->getArg(A.aux));
        if (fn2 == AndersNodeFactory::InvalidIndex)
          fn2 = getCanonicalNode(NF.createValueNode(DF->getArg(A.aux)));
        if (dn != AndersNodeFactory::InvalidIndex) {
          addAssignmentEdge(getCanonicalNode(dn), getCanonicalNode(fn2));
          g_sumInvoke++;
        }
      }
      if (A.off == 1) {
        if (containsPointerType(DF->getReturnType())) {
          NodeIndex rn = NF.getReturnNodeFor(DF);
          if (rn == AndersNodeFactory::InvalidIndex ||
              rn == NF.getUniversalPtrNode())
            rn = NF.createReturnNode(DF);
          NodeIndex cn = nodeForRef(-1, true);
          if (cn != AndersNodeFactory::InvalidIndex)
            addAssignmentEdge(getCanonicalNode(rn), getCanonicalNode(cn));
        }
        if (retBound)
          *retBound = true; // suppress the pooled HOF return edge
        if (A.src < 0)
          needPooled = true; // pure-ret: no claim about the args
        g_sumInvokeRet++;
      }
      Ctx->Callees[CS].insert(DF); // re-attributed callgraph edge
      break;
    }
    case GlobalContext::SummaryAtom::ChainReg: {
      if ((unsigned)A.src >= CS->arg_size() ||
          (A.dst >= 0 && (unsigned)A.dst >= CS->arg_size())) {
        g_sumSkipped++;
        break;
      }
      if (chainFinalized) { g_chainLate++; needPooled = true; break; }
      const GlobalValue *key = nullptr;
      if (A.gsrc) {
        key = A.gsrc; // derived (composition lift): already canonical
      } else if (!A.gsym.empty()) {
        // resolve by GUID against the global maps: the callsite TU
        // usually does NOT declare the chain head (the wrapper hides
        // it) -- getNamedValue there returned null and 1,889 wrapper
        // registrations fell back pooled (kernel-adopt2 identity check)
        const uint64_t g = llvm::GlobalValue::getGUID(A.gsym);
        auto git = Ctx->Gobjs.find(g);
        if (git != Ctx->Gobjs.end() && git->second) {
          key = git->second;
        } else {
          auto eit = Ctx->ExtGobjs.find(g);
          if (eit != Ctx->ExtGobjs.end() && eit->second) {
            key = eit->second;
          } else {
            // STATIC chain heads (pm_chain_head, oom_notify_list, ...)
            // are in no global map and not visible from callers' TUs.
            // Resolve by a one-time corpus scan of local-linkage
            // globals; only a UNIQUE name match binds (ambiguous or
            // absent -> dyn fallback, LEDGERed by the caller path).
            static std::unordered_map<std::string, const GlobalValue *>
                localByName; // nullptr sentinel = ambiguous
            static bool scanned = false;
            if (!scanned) {
              scanned = true;
              for (auto &mp2 : Ctx->Modules)
                for (const GlobalVariable &GV2 : mp2.first->globals()) {
                  if (!GV2.hasLocalLinkage() || !GV2.hasName()) continue;
                  auto [it2, ins2] =
                      localByName.emplace(GV2.getName().str(), &GV2);
                  if (!ins2) it2->second = nullptr; // ambiguous
                }
            }
            auto lit = localByName.find(A.gsym);
            if (lit != localByName.end() && lit->second)
              key = lit->second;
            else
              key = canonChainKey(CS->getModule()->getNamedValue(A.gsym));
          }
        }
      } else if (A.dst >= 0) {
        key = canonChainKey(dyn_cast<GlobalValue>(
            CS->getArgOperand(A.dst)->stripPointerCasts()));
      }
      const auto *blk = dyn_cast<GlobalVariable>(
          CS->getArgOperand(A.src)->stripPointerCasts());
      Function *fn = nullptr;
      if (blk && blk->hasInitializer()) {
        // walk the constant initializer to the fn at byte offset A.off
        const DataLayout &DL = blk->getParent()->getDataLayout();
        const Constant *C = blk->getInitializer();
        uint64_t off = (uint64_t)A.off;
        while (C) {
          if (const auto *CSt = dyn_cast<ConstantStruct>(C)) {
            const StructLayout *SL = DL.getStructLayout(CSt->getType());
            unsigned e = SL->getElementContainingOffset(off);
            off -= SL->getElementOffset(e);
            C = CSt->getOperand(e);
          } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
            uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
            if (!es) { C = nullptr; break; }
            C = CA->getOperand(off / es);
            off %= es;
          } else {
            break;
          }
        }
        if (C && off == 0)
          fn = const_cast<Function *>(
              dyn_cast<Function>(C->stripPointerCasts()));
      }
      if (!key || !blk || !fn) {
        // dynamic key/block or runtime-installed callback: keep the
        // container fed (pooled) — sound, LEDGERed
        g_chainRegDyn++;
        needPooled = true;
        break;
      }
      chainRegs.push_back({key, blk, getFuncDef(fn), A.fk, CS});
      g_chainReg++;
      break;
    }
    case GlobalContext::SummaryAtom::ChainCall: {
      if ((unsigned)A.dst >= CS->arg_size() ||
          (unsigned)A.src >= CS->arg_size()) { g_sumSkipped++; break; }
      if (chainFinalized) { g_chainLate++; needPooled = true; break; }
      const GlobalValue *key = canonChainKey(dyn_cast<GlobalValue>(
          CS->getArgOperand(A.dst)->stripPointerCasts()));
      if (!key) { g_chainCallDyn++; needPooled = true; break; }
      if (!chainDispatches.empty() && chainDispatches.back().cs == CS &&
          chainDispatches.back().key == key) {
        chainDispatches.back().binds.push_back({A.fk, A.src});
      } else {
        ChainDispatchRec r{CS, key, {}};
        r.binds.push_back({A.fk, A.src});
        chainDispatches.push_back(std::move(r));
        g_chainCall++;
      }
      // The dispatch site ALWAYS keeps pooled wiring: pooled-fallback
      // registrations and manual chain links flow through the body,
      // and its icall must still resolve them (the paired subset is
      // additional). Draining here severed t_chain2's fallback reg.
      needPooled = true;
      break;
    }
    case GlobalContext::SummaryAtom::FreshSub: {
      NodeIndex d = nodeForRef(A.dst, true);
      if (d == AndersNodeFactory::InvalidIndex) break;
      NodeIndex subVal = getCanonicalNode(NF.createValueNode());
      NodeIndex subObj = NF.createOpaqueObjectNode(nullptr, true);
      EB.addDereferenceEdges(subVal, subObj);
      AllocSites.insert(subVal); // origin identity for the mint loop
      addAssignmentEdge(subVal, getRepDerefNode(getCanonicalNode(d)));
      g_sumFreshSub++;
      break;
    }
    case GlobalContext::SummaryAtom::Load: {
      NodeIndex d = nodeForRef(A.dst, true), c = nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(getRepDerefNode(getCanonicalNode(c)),
                        getCanonicalNode(d));
      g_sumLd++;
      break;
    }
    }
  }
  return needPooled;
}

// --cfl-census-fields (task #29): MEASUREMENT-ONLY census of the
// family-2/3 store-side registration channels. A channel is a
// (struct,byte-offset) field key with constant-Function STORES on the
// registration side and field-LOAD-fed icalls on the dispatch side
// (INIT_WORK/timer/hrtimer/notifier shape: the fn is not a call
// parameter, it is written into a container the dispatcher reads
// back). Also counts paired sibling stores ((fn,data) written into
// the same object in the same function — the correlation a
// same-origin binding could exploit) and ops-struct pointer stores
// (family 3). Adds no edges.
void CallGraphPass::runFieldChannelCensus() {
  struct Chan {
    size_t fnStores = 0, dynStores = 0, opsStores = 0, icallLoads = 0;
    size_t paired = 0;
    std::set<std::string> fnSample;
    std::string loadSample;
  };
  std::map<std::string, Chan> chans;
  // family-3: "<opsFieldKey> ->fn <fnFieldKey>" -> (dispatchSites,
  // receiver-passing sites)
  std::map<std::string, std::pair<size_t, size_t>> twoLevel;
  std::map<const Value *, size_t> opsGlobalFanout; // ops global -> stores
  auto fieldKey = [&](const Value *P, const DataLayout &DL,
                      bool &varIdx) -> std::pair<std::string, const Value *> {
    APInt Off(64, 0);
    std::string SName;
    varIdx = false;
    P = P->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(P)) {
      if (!G->accumulateConstantOffset(DL, Off))
        varIdx = true;
      if (SName.empty())
        if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName())
            SName = stripStructNameSuffix(ST->getStructName()).str();
      P = G->getPointerOperand()->stripPointerCasts();
    }
    std::string Key = (SName.empty() ? std::string("?") : SName) + "+" +
                      (varIdx ? std::string("var")
                              : std::to_string(Off.getSExtValue()));
    return {Key, P};
  };
  auto isOpsGlobal = [](const Value *V) {
    const auto *GV = dyn_cast<GlobalVariable>(V);
    if (!GV || !GV->hasInitializer()) return false;
    const auto *CS = dyn_cast<ConstantStruct>(GV->getInitializer());
    if (!CS) return false;
    for (const Use &Op : CS->operands())
      if (isa<Function>(Op->stripPointerCasts())) return true;
    return false;
  };
  size_t totalFnStores = 0, totalIcallLoads = 0;
  for (auto &mp : Ctx->Modules) {
    const DataLayout &DL = mp.first->getDataLayout();
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
      if (shouldSkipFunction(&F)) continue;
      // per-base sibling stores within this function: fn-offset keys
      // and data-ptr stores keyed by base object
      std::map<const Value *, std::vector<std::string>> baseFnKeys;
      std::map<const Value *, size_t> baseDataStores;
      for (const Instruction &I : instructions(F)) {
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          const Value *V = SI->getValueOperand()->stripPointerCasts();
          bool varIdx = false;
          auto [Key, Base] = fieldKey(SI->getPointerOperand(), DL, varIdx);
          if (const auto *Fn = dyn_cast<Function>(V)) {
            Chan &C = chans[Key];
            C.fnStores++;
            totalFnStores++;
            if (C.fnSample.size() < 4) C.fnSample.insert(Fn->getName().str());
            baseFnKeys[Base].push_back(Key);
          } else if (isOpsGlobal(V)) {
            chans[Key].opsStores++;
            opsGlobalFanout[V]++;
          } else if (containsPointerType(V->getType())) {
            baseDataStores[Base]++;
            // dynamic fn store? count under the key only if the value
            // could be a function — unknowable under opaque ptrs; the
            // dyn tally lives on channels that ALSO see constant fns
            if (chans.count(Key)) chans[Key].dynStores++;
          }
        } else if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          const CallBase *fedCB = nullptr;
          for (const User *U : LI->users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (CB && !CB->isInlineAsm() &&
                CB->getCalledOperand()->stripPointerCasts() == LI)
              fedCB = CB;
          }
          if (!fedCB) continue;
          bool varIdx = false;
          auto [Key, Base] = fieldKey(LI->getPointerOperand(), DL, varIdx);
          Chan &C = chans[Key];
          C.icallLoads++;
          totalIcallLoads++;
          if (C.loadSample.empty())
            C.loadSample = F.getName().str();
          // family-3 two-level dispatch: the fn load's base is ITSELF
          // a loaded pointer (obj->ops then ops->fn). Record the outer
          // (ops-field) key and whether the icall passes the receiver
          // (the inner load's base object) as an argument.
          if (const auto *L1 = dyn_cast<LoadInst>(Base)) {
            bool v2 = false;
            auto [OKey, OBase] = fieldKey(L1->getPointerOperand(), DL, v2);
            bool recv = false;
            for (const Use &A2 : fedCB->args())
              if (A2->stripPointerCasts() == OBase) recv = true;
            auto &T = twoLevel[OKey + " ->fn " + Key];
            T.first++;
            if (recv) T.second++;
          }
        }
      }
      for (auto &[Base, Keys] : baseFnKeys)
        if (baseDataStores.count(Base))
          for (const std::string &K : Keys) chans[K].paired++;
    }
  }
  // Rank two-sided channels (registration AND dispatch observed).
  std::vector<std::pair<const std::string *, const Chan *>> ranked;
  size_t oneSidedStores = 0, oneSidedLoads = 0;
  for (auto &[K, C] : chans) {
    if (C.fnStores && C.icallLoads) ranked.push_back({&K, &C});
    else if (C.fnStores) oneSidedStores++;
    else if (C.icallLoads) oneSidedLoads++;
  }
  std::sort(ranked.begin(), ranked.end(), [](auto &A, auto &B) {
    return A.second->fnStores * A.second->icallLoads >
           B.second->fnStores * B.second->icallLoads;
  });
  errs() << "FieldChannels: " << chans.size() << " field keys; "
         << ranked.size() << " two-sided channels (" << oneSidedStores
         << " store-only, " << oneSidedLoads << " load-only); "
         << totalFnStores << " constant-fn stores, " << totalIcallLoads
         << " field-load icalls total\n";
  size_t shown = 0;
  for (auto &[K, C] : ranked) {
    if (shown++ >= 40) break;
    errs() << "FieldChannels: " << *K << " fnStores=" << C->fnStores
           << " paired=" << C->paired << " dynStores=" << C->dynStores
           << " opsStores=" << C->opsStores
           << " icallLoads=" << C->icallLoads << " dispatch@"
           << C->loadSample << " fns:";
    for (const auto &N : C->fnSample) errs() << " " << N;
    errs() << "\n";
  }
  // family-3 report: two-level dispatch channels + ops-global fan-out
  std::vector<std::pair<size_t, const std::string *>> tlRank;
  size_t recvTotal = 0, tlTotal = 0;
  for (auto &[K, V] : twoLevel) {
    tlRank.emplace_back(V.first, &K);
    tlTotal += V.first;
    recvTotal += V.second;
  }
  std::sort(tlRank.begin(), tlRank.end(), std::greater<>());
  errs() << "OpsChannels: " << twoLevel.size()
         << " two-level dispatch channels, " << tlTotal << " sites, "
         << recvTotal << " pass the receiver; " << opsGlobalFanout.size()
         << " distinct ops globals stored\n";
  for (size_t i = 0; i < std::min<size_t>(25, tlRank.size()); i++) {
    auto &V = twoLevel[*tlRank[i].second];
    errs() << "OpsChannels: " << *tlRank[i].second << " sites=" << V.first
           << " recv=" << V.second << "\n";
  }
  std::vector<std::pair<size_t, const Value *>> ogRank;
  for (auto &[G, N] : opsGlobalFanout) ogRank.emplace_back(N, G);
  std::sort(ogRank.begin(), ogRank.end(), std::greater<>());
  for (size_t i = 0; i < std::min<size_t>(10, ogRank.size()); i++)
    errs() << "OpsChannels: opsGlobal " << ogRank[i].second->getName()
           << " stored at " << ogRank[i].first << " sites\n";
}

// --cfl-confirm-invoke (task #28 tier 2): auto-confirm INVOKE summaries
// where the proof is LOCAL, under the #17 completeness discipline — a
// summary replaces callsite arg/ret wiring, so every pointer formal
// must be fully accounted by the atoms or provably benign; anything
// else rejects to the LEDGER.
//   DIRECT   the fn formal is invoked synchronously in the body with
//            other formals as arguments -> INVOKE atoms verbatim.
//   PASSTHRU formals are forwarded into an already-summarized INVOKE
//            callee -> the wrapper inherits translated atoms (+FRESH
//            when it returns the callee's fresh result). Fixpoint over
//            wrapper chains.
// Deferred shapes (FIELD/COSTORE) are NOT auto-confirmed: their
// dispatcher lives elsewhere; the census reports them for review.
static size_t g_invConfirmed = 0, g_invConfirmedPass = 0, g_invRejEscape = 0,
              g_invRejPtrRet = 0, g_invRejNoBinding = 0, g_invRejShape = 0,
              g_invConfirmedChain = 0;
// --cfl-census-ptrtoint (task #33): sizes the int-provenance residue
// design. Every ptrtoint under field mode currently pays an fx
// wildcard on its source ("ptrtoint-escape", the top wildcard family
// at km) — but a chain that is only constant add/sub back into
// inttoptr is a GEP in disguise (residue-encodable: f<C mod P>), and
// a compare-only use needs no wildcard at all. Classify every
// ptrtoint instruction by the worst thing its forward use-chains do:
//   ESCAPE   — stored / call arg / returned (leaves local analysis)
//   OTHER    — mul/shift/trunc/gep-index/unknown use
//   VARIABLE — add/sub/or with a non-constant operand (percpu, stride)
//   MASK     — and/or with a constant (alignment, low-bit tags)
//   CONST    — every terminal is inttoptr at an exact nonzero offset
//   CONST0   — exact offset-0 round trips only (plain 'a' already right)
//   CMP      — compares/switches only
//   DEAD     — no users
// CONST + CONST0 + CMP = the wildcard-suppressible population.
void CallGraphPass::runPtrToIntCensus() {
  enum Sev {
    DEAD, CMP, CONST0, TAG, CONST, MASK, VARIABLE, OTHER, ESCAPE, NSEV
  };
  static const char *sname[NSEV] = {"DEAD",  "CMP",      "CONST0",
                                    "TAG",   "CONST",    "MASK",
                                    "VARIABLE", "OTHER", "ESCAPE"};
  size_t tally[NSEV] = {0};
  size_t total = 0, inexactI2P = 0;
  std::map<int64_t, size_t> constOffsets;
  std::map<std::string, size_t> fnBySev[NSEV];
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      for (Instruction &I : instructions(F)) {
        auto *PTI = dyn_cast<PtrToIntInst>(&I);
        if (!PTI)
          continue;
        total++;
        // Forward BFS over the int computation. State = accumulated
        // constant offset while it stays exact.
        struct WI {
          const Value *v;
          int64_t off;
          bool exact;
        };
        SmallVector<WI, 16> wl{{PTI, 0, true}};
        SmallPtrSet<const Value *, 32> seen{PTI};
        bool fEsc = false, fOther = false, fVar = false, fMask = false,
             fConst = false, fZero = false, fCmp = false, fTag = false;
        unsigned steps = 0;
        while (!wl.empty() && steps++ < 256) {
          WI w = wl.pop_back_val();
          for (const User *U : w.v->users()) {
            auto push = [&](int64_t off, bool exact) {
              if (seen.insert(U).second)
                wl.push_back({cast<Value>(U), off, exact});
            };
            if (isa<IntToPtrInst>(U)) {
              if (w.exact) {
                if (w.off == 0)
                  fZero = true;
                else {
                  fConst = true;
                  constOffsets[w.off]++;
                }
              } else {
                inexactI2P++; // why-inexact already flagged en route
              }
              continue;
            }
            if (const auto *BO = dyn_cast<BinaryOperator>(U)) {
              const Value *other = BO->getOperand(BO->getOperand(0) == w.v
                                                      ? 1
                                                      : 0);
              const auto *CI2 = dyn_cast<ConstantInt>(other);
              switch (BO->getOpcode()) {
              case Instruction::Add:
                if (CI2)
                  push(w.off + CI2->getSExtValue(), w.exact);
                else {
                  fVar = true;
                  push(0, false);
                }
                break;
              case Instruction::Sub:
                if (CI2 && BO->getOperand(0) == w.v)
                  push(w.off - CI2->getSExtValue(), w.exact);
                else if (BO->getOperand(1) == w.v)
                  fOther = true; // negated provenance / ptr difference
                else {
                  fVar = true;
                  push(0, false);
                }
                break;
              case Instruction::And:
              case Instruction::Or:
              case Instruction::Xor:
                if (!CI2) {
                  fVar = true;
                  push(0, false);
                } else if (BO->getOpcode() == Instruction::And &&
                           CI2->getZExtValue() < 8) {
                  // tag EXTRACTION (v & 7): result is the flag bits,
                  // not a pointer — benign terminal
                } else if (BO->getOpcode() != Instruction::And
                               ? CI2->getZExtValue() < 8
                               : ~CI2->getZExtValue() < 8) {
                  // sub-alignment tag set/flip/clear: offset unchanged
                  fTag = true;
                  push(w.off, w.exact);
                } else {
                  fMask = true;
                  push(0, false);
                }
                break;
              default:
                fOther = true; // mul/shift/div: scaling, not an offset
                push(0, false);
                break;
              }
              continue;
            }
            if (isa<ZExtInst>(U) || isa<SExtInst>(U) ||
                isa<BitCastInst>(U) || isa<FreezeInst>(U)) {
              push(w.off, w.exact);
              continue;
            }
            if (isa<TruncInst>(U)) {
              fOther = true;
              push(0, false);
              continue;
            }
            if (isa<PHINode>(U) || isa<SelectInst>(U)) {
              push(0, false); // per-path offsets may differ
              continue;
            }
            if (isa<ICmpInst>(U) || isa<SwitchInst>(U)) {
              fCmp = true;
              continue;
            }
            if (const auto *SI = dyn_cast<StoreInst>(U)) {
              if (SI->getValueOperand() == w.v)
                fEsc = true;
              continue;
            }
            if (isa<CallBase>(U) || isa<ReturnInst>(U) ||
                isa<AtomicRMWInst>(U) || isa<AtomicCmpXchgInst>(U)) {
              fEsc = true;
              continue;
            }
            if (isa<GetElementPtrInst>(U)) {
              fOther = true; // laundered into another pointer's offset
              continue;
            }
            fOther = true;
          }
        }
        if (steps >= 256)
          fOther = true; // walk cap: never classify as suppressible
        Sev s = fEsc       ? ESCAPE
                : fOther   ? OTHER
                : fVar     ? VARIABLE
                : fMask    ? MASK
                : fConst   ? CONST
                : fTag     ? TAG
                : fZero    ? CONST0
                : fCmp     ? CMP
                           : DEAD;
        tally[s]++;
        fnBySev[s][F.getName().str()]++;
      }
    }
  }
  errs() << "PtrToIntCensus: " << total << " ptrtoint instructions\n";
  // TAG+CONST0+CMP+DEAD = what the shipped tag-round-trip rule
  // suppresses; CONST would additionally need f-edge emission.
  size_t suppressible = tally[TAG] + tally[CONST0] + tally[CMP] +
                        tally[DEAD];
  for (int s = 0; s < NSEV; s++)
    errs() << "PtrToIntCensus: " << sname[s] << " " << tally[s] << " ("
           << (total ? tally[s] * 100 / total : 0) << "%)\n";
  errs() << "PtrToIntCensus: tag-rule suppressible (TAG+CONST0+CMP+DEAD) "
         << suppressible << "/" << total << " ("
         << (total ? suppressible * 100 / total : 0) << "%), +CONST "
         << tally[CONST] << " residue-encodable, " << inexactI2P
         << " inexact inttoptr terminals\n";
  {
    std::vector<std::pair<size_t, int64_t>> or2;
    for (auto &kv : constOffsets)
      or2.emplace_back(kv.second, kv.first);
    std::sort(or2.begin(), or2.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(12, or2.size()); i++)
      errs() << "PtrToIntCensus: CONST offset " << or2[i].second << " x"
             << or2[i].first << "\n";
  }
  for (int s : {(int)TAG, (int)CONST, (int)ESCAPE, (int)VARIABLE,
                (int)MASK}) {
    std::vector<std::pair<size_t, const std::string *>> fr2;
    for (auto &kv : fnBySev[s])
      fr2.emplace_back(kv.second, &kv.first);
    std::sort(fr2.begin(), fr2.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(8, fr2.size()); i++)
      errs() << "PtrToIntCensus: " << sname[s] << "-fn " << fr2[i].first
             << "x " << *fr2[i].second << "\n";
  }
}

// --cfl-census-tracepoint (task #35): size the tracepoint keyed-channel
// design. The prize (pin-measured): 964 __traceiter_* callers carry
// 1,504,648 pairs = 17.9% of the 8.39M kernel answer set, because
// tracepoint_add_func's generic tp->funcs store pools every
// tracepoint's (probe, data) registrations into one channel. The model
// keys the channel by the @__tracepoint_* global — this census splits
// the registration sites by how the key is named there:
//   CONST  — tp argument IS a @__tracepoint_* global (the inlined
//            register_trace_<name> wrappers): directly keyable, the
//            static_call (#14) primitive shape.
//   LOAD   — tp loaded from memory (trace_event_reg's call->tp path):
//            needs the trace_event_call static-initializer pair
//            correlation (.tp co-resident with .probe/.perf_probe —
//            the #28 pair-atom shape).
//   FORMAL — tp is the enclosing function's parameter: in-family
//            plumbing (tracepoint_add_func etc.), not a channel entry.
// Dispatch side: every __traceiter_* body must name its key global at
// the funcs-head load (constexpr GEP on @__tracepoint_*) — keyless
// icalls would break the model, so they are counted loudly.
// --cfl-census-nexus (task #38): DISCOVER nexus structs instead of
// guessing them. A nexus struct is one whose objects many subsystems
// write pointers into — under FI its single cell transitively couples
// them all (task_struct = the exemplar found via the coupler census).
// Static signal: for every store whose address is a GEP into a named
// struct type, record (type <- writing subsystem); rank by subsystem
// diversity, splitting pointer-valued stores (the coupling carriers)
// from all stores.
void CallGraphPass::runNexusCensus() {
  struct TypeStat {
    uint64_t ptrWriters = 0, allWriters = 0, readers = 0;
    size_t ptrStores = 0;
  };
  std::map<std::string, TypeStat> byType;
  for (auto &mp : Ctx->Modules) {
    const uint8_t sb = subsysBitOf(mp.first);
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      for (Instruction &I : instructions(F)) {
        const Value *addr = nullptr;
        bool isStore = false, ptrVal = false;
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          addr = SI->getPointerOperand();
          isStore = true;
          ptrVal = SI->getValueOperand()->getType()->isPointerTy();
        } else if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          addr = LI->getPointerOperand();
          ptrVal = LI->getType()->isPointerTy();
        } else {
          continue;
        }
        const auto *GO =
            dyn_cast<GEPOperator>(addr->stripPointerCasts());
        const StructType *ST =
            GO ? dyn_cast<StructType>(GO->getSourceElementType()) : nullptr;
        if (!ST || !ST->hasName())
          continue;
        auto &t = byType[sctCanonStructName(ST->getName()).str()];
        if (isStore) {
          t.allWriters |= 1ull << sb;
          if (ptrVal) {
            t.ptrWriters |= 1ull << sb;
            t.ptrStores++;
          }
        } else if (ptrVal) {
          t.readers |= 1ull << sb;
        }
      }
    }
  }
  std::vector<std::pair<int, const std::string *>> rk;
  for (auto &kv : byType)
    rk.emplace_back(__builtin_popcountll(kv.second.ptrWriters), &kv.first);
  std::sort(rk.begin(), rk.end(), std::greater<>());
  errs() << "NexusCensus: " << byType.size() << " struct types with "
         << "field traffic\n";
  for (size_t i = 0; i < std::min<size_t>(30, rk.size()); i++) {
    auto &t = byType[*rk[i].second];
    errs() << "NexusCensus: ptr-writers " << rk[i].first << " subsys, "
           << "readers " << __builtin_popcountll(t.readers)
           << " subsys, " << t.ptrStores << " ptr-stores  "
           << *rk[i].second << "\n";
  }
}

void CallGraphPass::runTracepointCensus() {
  auto isRegFn = isTracepointRegFn;
  size_t nConst = 0, nConstPair = 0, nLoad = 0, nFormal = 0, nOther = 0;
  std::map<std::string, size_t> loadEnclosing, formalEnclosing,
      otherEnclosing;
  boost::unordered_flat_set<const GlobalVariable *> constKeys;
  boost::unordered_flat_set<const Function *> constProbes;
  size_t nTraceiter = 0, nTraceiterKeyless = 0, nIcallKeyed = 0,
         nIcallKeyless = 0;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      const bool isTraceiter = F.getName().starts_with("__traceiter_");
      const GlobalVariable *fnKey = nullptr;
      if (isTraceiter) {
        nTraceiter++;
        for (Instruction &I : instructions(F)) {
          const auto *LI = dyn_cast<LoadInst>(&I);
          if (!LI)
            continue;
          const Value *P = LI->getPointerOperand();
          if (const auto *CE = dyn_cast<ConstantExpr>(P))
            if (CE->getOpcode() == Instruction::GetElementPtr)
              P = CE->getOperand(0);
          if (const auto *GV =
                  dyn_cast<GlobalVariable>(P->stripPointerCasts()))
            if (GV->getName().starts_with("__tracepoint_")) {
              fnKey = GV;
              break;
            }
        }
        if (!fnKey)
          nTraceiterKeyless++;
      }
      for (Instruction &I : instructions(F)) {
        const auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->isInlineAsm())
          continue;
        const auto *CF = dyn_cast<Function>(
            CB->getCalledOperand()->stripPointerCasts());
        if (!CF) {
          if (isTraceiter) {
            if (fnKey)
              nIcallKeyed++;
            else
              nIcallKeyless++;
          }
          continue;
        }
        if (!isRegFn(CF->getName()) || CB->arg_size() < 2)
          continue;
        const Value *tp = CB->getArgOperand(0)->stripPointerCasts();
        if (const auto *GV = dyn_cast<GlobalVariable>(tp)) {
          if (GV->getName().starts_with("__tracepoint_")) {
            nConst++;
            constKeys.insert(GV);
            if (const auto *PF = dyn_cast<Function>(
                    CB->getArgOperand(1)->stripPointerCasts())) {
              nConstPair++;
              constProbes.insert(PF);
            }
          } else {
            nOther++;
            otherEnclosing[(F.getName() + " (gv " + GV->getName() + ")")
                               .str()]++;
          }
        } else if (isa<LoadInst>(tp)) {
          nLoad++;
          loadEnclosing[F.getName().str()]++;
        } else if (isa<Argument>(tp)) {
          nFormal++;
          formalEnclosing[F.getName().str()]++;
        } else {
          nOther++;
          otherEnclosing[
              (F.getName() + " (" +
               (isa<Instruction>(tp) ? cast<Instruction>(tp)->getOpcodeName()
                                     : "non-inst") +
               ")").str()]++;
        }
      }
    }
  }
  errs() << "TracepointCensus: register-family sites "
         << (nConst + nLoad + nFormal + nOther) << " = CONST " << nConst
         << " (" << nConstPair << " fully-static pairs, "
         << constKeys.size() << " distinct keys, " << constProbes.size()
         << " distinct probes) / LOAD " << nLoad << " / FORMAL " << nFormal
         << " / OTHER " << nOther << "\n";
  errs() << "TracepointCensus: dispatch __traceiter fns " << nTraceiter
         << " (" << nTraceiterKeyless << " KEYLESS), icalls keyed "
         << nIcallKeyed << " / keyless " << nIcallKeyless << "\n";
  auto dumpTop = [](const char *tag,
                    const std::map<std::string, size_t> &m) {
    std::vector<std::pair<size_t, const std::string *>> v;
    for (auto &kv : m)
      v.emplace_back(kv.second, &kv.first);
    std::sort(v.begin(), v.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(10, v.size()); i++)
      errs() << "TracepointCensus: " << tag << " x" << v[i].first << " "
             << *v[i].second << "\n";
  };
  dumpTop("load-site", loadEnclosing);
  dumpTop("formal-site", formalEnclosing);
  dumpTop("other-site", otherEnclosing);
}

// ---- Tracepoint keyed channels (task #35, --cfl-tracepoint-keys) ----
// Per-key channel = two synthetic JUNCTION value nodes (fn, data), NOT
// memory cells. v1 used fnCell = deref(@__tracepoint_X) and was
// byte-identical to the pin at kernel scale (-0/+59-flap): the tp
// structs' deref cells are inside the giant cluster there (tp pointers
// travel through the __tracepoint_ptrs section arrays and iterator
// formals, merging every tp's cells), so reading the channel imported
// the whole quotient even though the channel CONTENT was exact.
// Junction nodes are referenced by nothing but the model's own edges —
// no pointer ever names them, no cell join can absorb them. With the
// registration bodies and the iterator funcs-loads severed, plain
// a-edges probe -> J_X -> called-operand ARE the exact dispatch.
// Keyed by the key's CANONICAL NODE, not the GlobalVariable*: each TU
// has its own declaration object for an extern tracepoint, and all of
// them must land on one junction (getRepNodeForValue resolves decl ->
// def through the GUID linking).
static boost::unordered_flat_map<NodeIndex, std::pair<NodeIndex, NodeIndex>>
    g_tpKeyJunctionMap;

std::pair<NodeIndex, NodeIndex>
CallGraphPass::tracepointJunctions(const GlobalVariable *KeyGV) {
  NodeIndex keyN = getRepNodeForValue(KeyGV);
  if (keyN == AndersNodeFactory::InvalidIndex) {
    g_tpKeyUnmapped++; // LOUD in the LEDGER — census says this is empty
    keyN = getCanonicalNode(NF.createValueNode(KeyGV));
  } else {
    keyN = getCanonicalNode(keyN);
  }
  auto it = g_tpKeyJunctionMap.find(keyN);
  if (it != g_tpKeyJunctionMap.end())
    return it->second;
  NodeIndex fnJ = getCanonicalNode(NF.createValueNode(nullptr));
  NodeIndex dataJ = getCanonicalNode(NF.createValueNode(nullptr));
  auto p = std::make_pair(fnJ, dataJ);
  g_tpKeyJunctionMap.emplace(keyN, p);
  return p;
}

void CallGraphPass::bindTracepointProbe(const GlobalVariable *KeyGV,
                                        const Value *ProbeV,
                                        const Value *DataV,
                                        bool fromWalker) {
  auto [fnJ, dataJ] = tracepointJunctions(KeyGV);
  (void)fnJ; // v3: fn plane is answer-level, no graph edge (see above)
  NodeIndex keyN = getRepNodeForValue(KeyGV);
  keyN = keyN == AndersNodeFactory::InvalidIndex
             ? AndersNodeFactory::InvalidIndex
             : getCanonicalNode(keyN);
  if (const auto *PF = dyn_cast<Function>(ProbeV)) {
    if (keyN != AndersNodeFactory::InvalidIndex) {
      g_tpKeyProbes[keyN].insert(getFuncDef(const_cast<Function *>(PF)));
      (fromWalker ? g_tpKeyMediatorBinds : g_tpKeyConstBinds)++;
    }
  } else if (keyN != AndersNodeFactory::InvalidIndex) {
    // dynamic probe value: the table is incomplete for this key — its
    // dispatch sites fall back to the graph path, counted LOUDLY
    // (census: zero such registrations at kernel scale)
    g_tpKeyHasDynProbe.insert(keyN);
    g_tpKeyDynProbe++;
  }
  if (DataV && !shouldSkipValue(DataV)) {
    NodeIndex dataN = getRepNodeForValue(DataV);
    if (dataN != AndersNodeFactory::InvalidIndex &&
        !NF.isSpecialNode(dataN))
      addAssignmentEdge(dataN, dataJ);
  }
}

// Struct-mediated registrations: trace_event_reg registers
// call->class->probe / ->perf_probe on call->tp; bpf_probe_register
// registers btp->bpf_func on btp->tp. Both (key, probe) pairs exist
// as static-initializer co-residents — trace_event_call references
// its class (probe fns live in the class initializer) and its
// tracepoint; bpf_raw_event_map holds {tp, bpf_func} directly. The
// registrar callsites themselves are severed like every family site;
// the pairs bound here replace them. Probe-fn filters are the
// macro-generated prefixes; anything else in a class initializer is
// counted, not bound.
void CallGraphPass::bindTracepointMediatorPairs() {
  auto collectRefs = [](const Constant *Init,
                        SmallVectorImpl<const GlobalValue *> &out) {
    SmallVector<const Constant *, 16> wl{Init};
    SmallPtrSet<const Constant *, 32> seen;
    while (!wl.empty()) {
      const Constant *C = wl.pop_back_val();
      if (!seen.insert(C).second)
        continue;
      if (const auto *GVal = dyn_cast<GlobalValue>(C)) {
        out.push_back(GVal);
        continue;
      }
      for (const Use &U : C->operands())
        if (const auto *OC = dyn_cast<Constant>(U))
          wl.push_back(OC);
    }
  };
  boost::unordered_flat_set<const GlobalVariable *> keySet;
  for (auto &mp : Ctx->Modules) {
    for (const GlobalVariable &GV : mp.first->globals()) {
      if (!GV.hasInitializer())
        continue;
      // Only the two registrar-container shapes may bind pairs. Without
      // this, @llvm.used (which references every tracepoint, class and
      // probe in the TU) bound ALL of a TU's probes to whichever
      // tracepoint ref came first — wrong-proto cross-binds surfaced as
      // isCompatible rejections, same-template ones silently inflated
      // one key per TU.
      const auto *GVT = dyn_cast<StructType>(GV.getValueType());
      const bool isEventCall = GVT && GVT->hasName() &&
                               GVT->getName().contains("trace_event_call");
      // bpf maps are union-wrapped (%union.anon.N { %struct.bpf_raw_
      // event_map }) so the type name is invisible at the top level —
      // the placement section is the semantic anchor.
      const bool isBpfMap =
          GV.getSection() == "__bpf_raw_tp_map" ||
          (GVT && GVT->hasName() &&
           GVT->getName().contains("bpf_raw_event_map"));
      if (!isEventCall && !isBpfMap)
        continue;
      SmallVector<const GlobalValue *, 16> refs;
      collectRefs(GV.getInitializer(), refs);
      const GlobalVariable *tpKey = nullptr;
      for (const GlobalValue *R : refs)
        if (R->getName().starts_with("__tracepoint_")) {
          tpKey = dyn_cast<GlobalVariable>(R);
          break;
        }
      if (!tpKey)
        continue;
      bool bound = false;
      // bpf_raw_event_map shape: {tp, __bpf_trace_X} in one initializer
      if (isBpfMap)
        for (const GlobalValue *R : refs)
          if (const auto *PF = dyn_cast<Function>(R)) {
            if (PF->getName().starts_with("__bpf_trace_")) {
              bindTracepointProbe(tpKey, PF, nullptr, /*fromWalker=*/true);
              bound = true;
            } else {
              g_tpKeyClassFnSkipped++;
            }
          }
      // trace_event_call shape: class global carries the probe fns
      for (const GlobalValue *R : refs) {
        const auto *ClsGV = dyn_cast<GlobalVariable>(R);
        if (!ClsGV || ClsGV == &GV || ClsGV == tpKey ||
            !ClsGV->hasInitializer())
          continue;
        const auto *ST = dyn_cast<StructType>(ClsGV->getValueType());
        if (!ST || !ST->hasName() ||
            !ST->getName().contains("trace_event_class"))
          continue;
        SmallVector<const GlobalValue *, 16> crefs;
        collectRefs(ClsGV->getInitializer(), crefs);
        for (const GlobalValue *CR : crefs)
          if (const auto *PF = dyn_cast<Function>(CR)) {
            StringRef pn = PF->getName();
            if (pn.starts_with("trace_event_raw_event_") ||
                pn.starts_with("perf_trace_")) {
              bindTracepointProbe(tpKey, PF, nullptr, /*fromWalker=*/true);
              bound = true;
            } else if (pn != "trace_event_reg" &&
                       pn != "trace_event_raw_init") {
              g_tpKeyClassFnSkipped++;
            }
          }
      }
      if (bound && keySet.insert(tpKey).second)
        g_tpWalkerKeys.push_back(tpKey);
    }
  }
  CG_LOG("TracepointKeys: walker bound " << g_tpKeyMediatorBinds
         << " mediator (key,probe) pairs over " << g_tpWalkerKeys.size()
         << " keys (" << g_tpKeyClassFnSkipped
         << " non-probe initializer fns skipped, " << g_tpKeyUnmapped
         << " unmapped keys)\n");
}

// Trace-payload read-back contract confirmer (task #32, design recorded
// at task #31 close). The sink model (--cfl-sink-instr) seals cluster
// joins at trace-payload cells — sound ONLY if nothing loaded back out
// of a payload cell ever feeds an indirect call. This pass machine-
// checks that contract at every payload accessor callsite:
//   ring_buffer_event_data — THE payload pointer accessor, both the
//     write path (trace_event_buffer_reserve fills fbuffer->entry) and
//     the read path (trace output iterators);
//   perf_trace_buf_alloc — the perf-side raw_data payload buffer.
// The returned pointer is walked as PTR (payload address: GEP/cast
// chains, phi/select); loads through PTR yield VAL (payload content),
// walked through casts/phis/arithmetic — with inttoptr(VAL) laundering
// re-entering as PTR. Verdicts per site:
//   VIOLATION — a tracked value IS an indirect call's called operand.
//     Sealing REFUSES to run (hard error), never silently degrades.
//   ESCAPE — the value leaves the local walk (pointer stored, e.g.
//     fbuffer->entry / iter->ent; passed to a non-intrinsic callee;
//     returned; walk cap). Inventoried by sink name for the documented
//     review — the contract holds for these by review, not by machine.
//   CONFIRMED — every use is a write into the payload, comparison,
//     GEP index / branch condition (the certified benign control
//     channel: data-indexed selection, soundly over-approximated by
//     including all table entries), or other local non-dispatch use.
void CallGraphPass::runSinkConfirmer() {
  // Accessor list shared with the arena planting in visitCallBase — the
  // contract this confirms and the model it gates must key identically.
  auto isPayloadAccessor = isSinkPayloadAccessor;
  enum Kind : char { PTR, VAL };
  size_t sites = 0;
  std::vector<std::string> violations;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      for (Instruction &I : instructions(F)) {
        const auto *Root = dyn_cast<CallBase>(&I);
        if (!Root || Root->isInlineAsm())
          continue;
        const auto *AF = dyn_cast<Function>(
            Root->getCalledOperand()->stripPointerCasts());
        if (!AF || !isPayloadAccessor(AF->getName()))
          continue;
        sites++;
        // Bounded forward walk from the payload pointer.
        SmallVector<std::pair<const Value *, Kind>, 32> wl;
        SmallPtrSet<const Value *, 32> seenP, seenV;
        std::set<std::string> escapes;
        bool violated = false;
        wl.push_back({Root, PTR});
        seenP.insert(Root);
        size_t steps = 0;
        while (!wl.empty()) {
          if (++steps > 768) { // explicit cap, never silent
            escapes.insert("walk-cap");
            break;
          }
          auto [V, k] = wl.pop_back_val();
          auto push = [&](const Value *N2, Kind nk) {
            auto &seen = nk == PTR ? seenP : seenV;
            if (seen.insert(N2).second)
              wl.push_back({N2, nk});
          };
          for (const User *U : V->users()) {
            if (const auto *CB = dyn_cast<CallBase>(U)) {
              if (CB->getCalledOperand()->stripPointerCasts() == V) {
                violated = true; // payload-derived value dispatched
                violations.push_back(
                    (F.getName() + " (" + AF->getName() + " site)").str());
                continue;
              }
              const auto *CF2 = dyn_cast<Function>(
                  CB->getCalledOperand()->stripPointerCasts());
              if (CF2 && CF2->isIntrinsic()) {
                // mem-write INTO the payload is the sink's purpose;
                // memcpy OUT of it exports the bytes — review item.
                if (const auto *MT = dyn_cast<MemTransferInst>(CB)) {
                  if (MT->getRawSource()->stripPointerCasts() == V)
                    escapes.insert("memcpy-out");
                  continue;
                }
                continue; // memset/dbg/lifetime/assume: benign
              }
              escapes.insert(CF2 ? CF2->getName().str()
                                 : std::string("<indirect-arg>"));
              continue;
            }
            if (const auto *LI = dyn_cast<LoadInst>(U)) {
              if (k == PTR || LI->getPointerOperand() == V)
                push(LI, VAL); // content read-back (or read through a
                               // content-derived pointer: conservative)
              continue;
            }
            if (const auto *SI = dyn_cast<StoreInst>(U)) {
              if (SI->getValueOperand() == V)
                escapes.insert(k == PTR ? "ptr-stored" : "val-stored");
              continue; // store INTO tracked memory: benign write
            }
            if (isa<IntToPtrInst>(U)) {
              push(U, PTR); // laundering: content becomes a pointer
              continue;
            }
            if (const auto *G2 = dyn_cast<GEPOperator>(U)) {
              if (G2->getPointerOperand() == V)
                push(U, k); // address arithmetic keeps the kind
              // V as INDEX: data-selected offset — certified benign
              // control channel (all table entries stay included)
              continue;
            }
            if (isa<CastInst>(U)) {
              push(U, k);
              continue;
            }
            if (isa<PHINode>(U) || isa<SelectInst>(U)) {
              push(U, k);
              continue;
            }
            if (isa<BinaryOperator>(U)) {
              push(U, VAL); // arithmetic on content/address stays data
              continue;
            }
            if (isa<ICmpInst>(U) || isa<BranchInst>(U) ||
                isa<SwitchInst>(U))
              continue; // compare/branch: certified benign channel
            if (isa<ReturnInst>(U)) {
              escapes.insert(k == PTR ? "ret-ptr" : "ret-val");
              continue;
            }
            if (const auto *RMW = dyn_cast<AtomicRMWInst>(U)) {
              if (RMW->getPointerOperand() == V)
                push(U, VAL); // old value read back
              else
                escapes.insert("atomic-val");
              continue;
            }
            escapes.insert(std::string("use:") +
                           (isa<Instruction>(U)
                                ? cast<Instruction>(U)->getOpcodeName()
                                : "constexpr"));
          }
        }
        if (violated)
          g_sinkSitesViolated++;
        else if (!escapes.empty()) {
          g_sinkSitesEscaped++;
          for (const std::string &e : escapes)
            g_sinkEscapeSinks[e]++;
        } else {
          g_sinkSitesConfirmed++;
        }
      }
    }
  }
  g_sinkContractChecked = true;
  errs() << "SinkConfirm: " << sites << " payload accessor sites: "
         << g_sinkSitesConfirmed << " CONFIRMED, " << g_sinkSitesEscaped
         << " ESCAPE, " << g_sinkSitesViolated << " VIOLATION\n";
  size_t eShown = 0;
  for (auto &kv : g_sinkEscapeSinks) {
    if (eShown++ >= 40) {
      errs() << "SinkConfirm: ... " << (g_sinkEscapeSinks.size() - 40)
             << " more escape sinks\n";
      break;
    }
    errs() << "SinkConfirm: escape " << kv.first << " at " << kv.second
           << " sites\n";
  }
  for (size_t i = 0; i < std::min<size_t>(20, violations.size()); i++)
    errs() << "SinkConfirm: VIOLATION in " << violations[i] << "\n";
  if (CFLSinkInstr && g_sinkSitesViolated) {
    errs() << "ERROR: --cfl-sink-instr read-back contract VIOLATED at "
           << g_sinkSitesViolated
           << " sites — a payload-derived value feeds an indirect call; "
              "refusing to seal (see SinkConfirm: VIOLATION lines)\n";
    exit(1);
  }
}

void CallGraphPass::confirmInvokeSummaries() {
  // Benign transitive use of a pointer chain rooted at a formal:
  // address arithmetic and non-pointer reads/writes lose no pointer
  // flow when callsite wiring is dropped. PHIs/selects reject (v1).
  std::function<bool(const Value *)> benignChain = [&](const Value *V) {
    for (const User *U : V->users()) {
      if (isa<GEPOperator>(U) || isa<CastInst>(U)) {
        if (!benignChain(U)) return false;
      } else if (const auto *LI = dyn_cast<LoadInst>(U)) {
        if (containsPointerType(LI->getType())) return false;
      } else if (const auto *SI = dyn_cast<StoreInst>(U)) {
        if (SI->getValueOperand() == V) return false; // chain ptr escapes
        if (containsPointerType(SI->getValueOperand()->getType()))
          return false; // pointer written through the chain
      } else if (const auto *RMW = dyn_cast<AtomicRMWInst>(U)) {
        if (containsPointerType(RMW->getValOperand()->getType()))
          return false;
      } else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(U)) {
        if (containsPointerType(CX->getNewValOperand()->getType()))
          return false;
      } else if (isa<ICmpInst>(U)) {
        // ok
      } else {
        return false;
      }
    }
    return true;
  };
  auto isNoopIntrinsic = [](const Function *IF) {
    if (!IF || !IF->isIntrinsic()) return false;
    switch (IF->getIntrinsicID()) {
    case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
    case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
    case Intrinsic::assume: case Intrinsic::expect:
      return true;
    default: return false;
    }
  };
  size_t rounds = 0;
  bool changed = true;
  SmallPtrSet<const Function *, 16> rejected; // don't re-check/re-count
  while (changed && rounds++ < 16) {
    changed = false;
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
        if (F.isVarArg()) continue;
        if (shouldSkipFunction(&F)) continue;
        if (Ctx->FuncSummaries.count(&F)) continue;
        if (rejected.count(&F)) continue;
        if (F.arg_size() < 1) continue; // chain wrappers are single-arg
        auto formalIdx = [&](const Value *V) -> int {
          V = V->stripPointerCasts();
          for (const auto &A : F.args())
            if (&A == V) return (int)A.getArgNo();
          return -1;
        };
        // Locate the dispatch sites: icalls on ONE fn formal (DIRECT)
        // and/or calls into summarized-INVOKE callees (PASSTHRU).
        int fnFormal = -1;
        bool multiFn = false;
        SmallPtrSet<const CallBase *, 4> fnIcalls, passCalls,
            chainPassCalls;
        for (const Instruction &I : instructions(F)) {
          const auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || CB->isInlineAsm()) continue;
          if (const Function *IC = CB->getCalledFunction()) {
            auto sit = Ctx->FuncSummaries.find(
                getFuncDef(const_cast<Function *>(IC)));
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(IC);
            if (sit == Ctx->FuncSummaries.end()) continue;
            bool onlyInvFresh = true;
            for (const auto &A : sit->second->atoms) {
              if (A.kind == GlobalContext::SummaryAtom::Invoke) {
                if ((unsigned)A.dst < CB->arg_size() &&
                    formalIdx(CB->getArgOperand(A.dst)) >= 0)
                  passCalls.insert(CB);
              } else if (A.kind == GlobalContext::SummaryAtom::ChainReg) {
                // wrapper forwards its block formal into a CHAINREG
                // callee whose key is CONSTANT here -> liftable
                if ((unsigned)A.src < CB->arg_size() &&
                    formalIdx(CB->getArgOperand(A.src)) >= 0 &&
                    (A.gsrc || !A.gsym.empty() ||
                     (A.dst >= 0 && (unsigned)A.dst < CB->arg_size() &&
                      isa<GlobalValue>(CB->getArgOperand(A.dst)
                                           ->stripPointerCasts()))))
                  chainPassCalls.insert(CB);
              } else if (A.kind != GlobalContext::SummaryAtom::Fresh) {
                onlyInvFresh = false; // CPY/ST/... translation: v1 out
              }
            }
            if (!onlyInvFresh) {
              passCalls.erase(CB); // CPY/ST etc.: v1 out
              chainPassCalls.erase(CB);
            }
            continue;
          }
          int fi = formalIdx(CB->getCalledOperand());
          if (fi < 0) continue;
          if (fnFormal != -1 && fnFormal != fi) multiFn = true;
          fnFormal = fi;
          fnIcalls.insert(CB);
        }
        if (fnIcalls.empty() && passCalls.empty() && chainPassCalls.empty())
          continue;
        const int shapes = (!fnIcalls.empty()) + (!passCalls.empty()) +
                           (!chainPassCalls.empty());
        if (multiFn || shapes > 1) {
          g_invRejShape++;
          rejected.insert(&F);
          continue; // mixed/multi shapes: review territory (v1)
        }
        // Completeness sweep over every pointer formal.
        bool ok = true;
        const char *why = nullptr;
        std::set<std::pair<int, int>> bindings; // (callee formal k, data idx)
        bool wantFresh = false;
        for (const auto &Arg : F.args()) {
          if (!containsPointerType(Arg.getType())) continue;
          int ai = (int)Arg.getArgNo();
          for (const User *U : Arg.users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (CB && fnIcalls.count(CB)) {
              if (CB->getCalledOperand()->stripPointerCasts() == &Arg)
                continue; // the fn slot itself
              bool foundArg = false;
              for (unsigned k = 0; k < CB->arg_size(); k++)
                if (CB->getArgOperand(k)->stripPointerCasts() == &Arg) {
                  bindings.insert({(int)k, ai});
                  foundArg = true;
                }
              if (!foundArg) { ok = false; why = "esc-call"; }
              continue;
            }
            if (CB && (passCalls.count(CB) || chainPassCalls.count(CB)))
              continue; // callee summary is authoritative
            if (CB) {
              const Function *IC = CB->getCalledFunction();
              if (IC && (isNoopIntrinsic(IC) || isFreeFn(IC->getName())))
                continue;
              ok = false; why = "esc-call"; break;
            }
            if (isa<ICmpInst>(U)) continue;
            if (isa<GEPOperator>(U) || isa<CastInst>(U) ||
                isa<LoadInst>(U) || isa<StoreInst>(U) ||
                isa<AtomicRMWInst>(U) || isa<AtomicCmpXchgInst>(U)) {
              // treat as chain rooted here: store OF the formal rejects
              if (const auto *SI = dyn_cast<StoreInst>(U)) {
                if (SI->getValueOperand()->stripPointerCasts() == &Arg) {
                  ok = false; why = "esc-store"; break;
                }
                if (containsPointerType(SI->getValueOperand()->getType())) {
                  ok = false; why = "esc-store"; break;
                }
                continue;
              }
              if (const auto *LI = dyn_cast<LoadInst>(U)) {
                if (containsPointerType(LI->getType())) {
                  ok = false; why = "esc-load"; break;
                }
                continue;
              }
              if (!benignChain(U)) { ok = false; why = "esc-chain"; break; }
              continue;
            }
            ok = false; why = "esc-other"; break;
          }
          if (!ok) break;
        }
        // Return accounting.
        const CallBase *retPass = nullptr;
        if (ok && containsPointerType(F.getReturnType())) {
          if (!fnIcalls.empty() || !chainPassCalls.empty()) {
            ok = false; why = "ptr-ret"; // chain regs return int
          } else {
            for (const Instruction &I : instructions(F)) {
              const auto *RI = dyn_cast<ReturnInst>(&I);
              if (!RI) continue;
              const Value *RV = RI->getReturnValue()->stripPointerCasts();
              if (isa<ConstantPointerNull>(RV)) continue;
              const auto *RC = dyn_cast<CallBase>(RV);
              if (RC && passCalls.count(RC)) { retPass = RC; continue; }
              ok = false; why = "ptr-ret"; break;
            }
          }
        }
        if (!ok) {
          if (why && (!strcmp(why, "ptr-ret"))) g_invRejPtrRet++;
          else g_invRejEscape++;
          CG_LOG("ConfirmInvoke: REVIEW " << F.getName() << " ("
                 << (fnIcalls.empty() ? "PASSTHRU" : "DIRECT") << ", "
                 << (why ? why : "?") << ")\n");
          rejected.insert(&F);
          continue;
        }
        // Build atoms.
        GlobalContext::FuncSummary S;
        if (!chainPassCalls.empty()) {
          for (const CallBase *CB : chainPassCalls) {
            const Function *IC = getFuncDef(
                const_cast<Function *>(CB->getCalledFunction()));
            auto sit = Ctx->FuncSummaries.find(IC);
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(CB->getCalledFunction());
            for (const auto &A : sit->second->atoms) {
              if (A.kind != GlobalContext::SummaryAtom::ChainReg) continue;
              int wb = (unsigned)A.src < CB->arg_size()
                           ? formalIdx(CB->getArgOperand(A.src))
                           : -1;
              if (wb < 0) continue;
              const GlobalValue *key = nullptr;
              if (A.gsrc) key = A.gsrc;
              else if (!A.gsym.empty())
                key = canonChainKey(
                    CB->getModule()->getNamedValue(A.gsym));
              else if (A.dst >= 0 && (unsigned)A.dst < CB->arg_size())
                key = canonChainKey(dyn_cast<GlobalValue>(
                    CB->getArgOperand(A.dst)->stripPointerCasts()));
              if (!key) continue;
              GlobalContext::SummaryAtom NA;
              NA.kind = GlobalContext::SummaryAtom::ChainReg;
              NA.dst = -1;
              NA.src = wb;
              NA.off = A.off;
              NA.fk = A.fk;
              NA.gsrc = key;
              S.atoms.push_back(std::move(NA));
            }
          }
          if (!S.atoms.empty()) {
            Ctx->OwnedSummaries.push_back(std::move(S));
            Ctx->FuncSummaries[&F] = &Ctx->OwnedSummaries.back();
            g_invConfirmedChain++;
            changed = true;
            std::string line = F.getName().str();
            for (const auto &A : Ctx->OwnedSummaries.back().atoms)
              line += " CHAINREG(@" + A.gsrc->getName().str() + ",*arg" +
                      std::to_string(A.src) + "+" + std::to_string(A.off) +
                      ",f" + std::to_string(A.fk) + ")";
            errs() << "ConfirmInvoke: CONFIRMED CHAINLIFT " << line << "\n";
          } else {
            g_invRejNoBinding++;
            rejected.insert(&F);
          }
          continue;
        }
        if (!fnIcalls.empty()) {
          for (auto [k, d] : bindings)
            S.atoms.push_back({GlobalContext::SummaryAtom::Invoke,
                               fnFormal, d, k});
        } else {
          for (const CallBase *CB : passCalls) {
            const Function *IC = getFuncDef(
                const_cast<Function *>(CB->getCalledFunction()));
            auto sit = Ctx->FuncSummaries.find(IC);
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(CB->getCalledFunction());
            for (const auto &A : sit->second->atoms) {
              if (A.kind != GlobalContext::SummaryAtom::Invoke) continue;
              if ((unsigned)A.dst >= CB->arg_size() ||
                  (unsigned)A.src >= CB->arg_size())
                continue;
              int wf = formalIdx(CB->getArgOperand(A.dst));
              int wd = formalIdx(CB->getArgOperand(A.src));
              if (wf < 0 || wd < 0 || wf == wd) continue;
              S.atoms.push_back({GlobalContext::SummaryAtom::Invoke,
                                 wf, wd, A.aux});
            }
            if (retPass == CB && sit->second->fresh) wantFresh = true;
          }
        }
        if (S.atoms.empty()) {
          if (!fnIcalls.empty()) { g_invRejNoBinding++; rejected.insert(&F); }
          continue; // PASSTHRU may translate in a later round
        }
        S.fresh = wantFresh;
        Ctx->OwnedSummaries.push_back(std::move(S));
        Ctx->FuncSummaries[&F] = &Ctx->OwnedSummaries.back();
        if (wantFresh) Ctx->AllocFuncs.insert(&F);
        if (!fnIcalls.empty()) g_invConfirmed++; else g_invConfirmedPass++;
        changed = true;
        // file-format proposal line for review adoption
        std::string line = F.getName().str();
        for (const auto &A : Ctx->OwnedSummaries.back().atoms) {
          line += " INVOKE(arg" + std::to_string(A.dst) + ":f" +
                  std::to_string(A.aux) + "<-arg" + std::to_string(A.src) +
                  ")";
        }
        if (wantFresh) line += " FRESH";
        errs() << "ConfirmInvoke: CONFIRMED "
               << (fnIcalls.empty() ? "PASSTHRU " : "DIRECT ") << line
               << "\n";
      }
    }
  }
  CG_LOG("ConfirmInvoke LEDGER: " << g_invConfirmed << " DIRECT + "
         << g_invConfirmedPass << " PASSTHRU + " << g_invConfirmedChain
         << " CHAINLIFT confirmed ("
         << rounds << " rounds); rejected " << g_invRejEscape
         << " escape, " << g_invRejPtrRet << " ptr-ret, "
         << g_invRejNoBinding << " no-binding, " << g_invRejShape
         << " mixed-shape\n");
}

// Wire the keyed pair-channels: for each chain-head key, the cross
// product of registrations and dispatch sites — the callback becomes a
// callee OF THE DISPATCH SITE (real invocation attribution), its self
// formal receives the registration's block global, and each dispatch
// binding wires that site's value operand to the callback's formal.
// Registrations whose key has NO dispatch site fall back to pooled
// wiring (the container channel keeps them; nothing is severed).
void CallGraphPass::finalizeChainPairs() {
  chainFinalized = true;
  if (chainRegs.empty() && chainDispatches.empty()) return;
  if (CFLCompositional && CompressedGraphInputs.empty()) {
    errs() << "finalizeChainPairs: keyed pair-channels create cross-module "
              "edges after the last module; per-TU compositional mode "
              "cannot compose them. Rerun with --cfl-compositional=false.\n";
    exit(1);
  }
  std::map<const GlobalValue *, std::vector<size_t>> byKeyR, byKeyD;
  for (size_t i = 0; i < chainRegs.size(); i++)
    byKeyR[chainRegs[i].key].push_back(i);
  for (size_t i = 0; i < chainDispatches.size(); i++)
    byKeyD[chainDispatches[i].key].push_back(i);
  size_t pairs = 0, orphanRegs = 0, orphanDispatch = 0;
  auto formalNode = [&](Function *F, int k) -> NodeIndex {
    if (k < 0 || (unsigned)k >= F->arg_size())
      return AndersNodeFactory::InvalidIndex;
    NodeIndex n = getRepNodeForValue(F->getArg(k));
    if (n == AndersNodeFactory::InvalidIndex)
      n = NF.createValueNode(F->getArg(k));
    return getCanonicalNode(n);
  };
  for (auto &[key, regs] : byKeyR) {
    auto dIt = byKeyD.find(key);
    if (dIt == byKeyD.end()) {
      // no dispatch in corpus for this key: keep the pooled channel
      for (size_t ri : regs) {
        const ChainRegRec &r = chainRegs[ri];
        Function *CF = r.cs->getCalledFunction()
                           ? getFuncDef(r.cs->getCalledFunction())
                           : nullptr;
        if (CF && !CF->isDeclaration()) wireCallArgs(r.cs, CF);
        orphanRegs++;
      }
      continue;
    }
    for (size_t ri : regs) {
      const ChainRegRec &r = chainRegs[ri];
      NodeIndex blkNode = getRepNodeForValue(r.blk);
      if (blkNode == AndersNodeFactory::InvalidIndex)
        blkNode = NF.createValueNode(r.blk);
      NodeIndex selfN = formalNode(r.fn, r.selfFk);
      if (selfN != AndersNodeFactory::InvalidIndex)
        addAssignmentEdge(getCanonicalNode(blkNode), selfN);
      for (size_t di : dIt->second) {
        const ChainDispatchRec &d = chainDispatches[di];
        Ctx->Callees[d.cs].insert(r.fn);
        for (auto [fk, ai] : d.binds) {
          if ((unsigned)ai >= d.cs->arg_size()) continue;
          NodeIndex vN = getRepNodeForValue(d.cs->getArgOperand(ai));
          if (vN == AndersNodeFactory::InvalidIndex) continue;
          NodeIndex fN = formalNode(r.fn, fk);
          if (fN != AndersNodeFactory::InvalidIndex)
            addAssignmentEdge(getCanonicalNode(vN), fN);
        }
        pairs++;
      }
    }
  }
  for (auto &[key, ds] : byKeyD)
    if (!byKeyR.count(key)) orphanDispatch += ds.size();
  CG_LOG("ChainPairs LEDGER: " << chainRegs.size() << " const registrations"
         << " x " << chainDispatches.size() << " dispatch sites over "
         << byKeyR.size() << " keys -> " << pairs << " wired pairs; "
         << orphanRegs << " regs pooled (no dispatch), " << orphanDispatch
         << " dispatch sites without const regs; dyn fallbacks "
         << g_chainRegDyn << " reg / " << g_chainCallDyn << " call, "
         << g_chainLate << " post-finalize\n");
}

// --cfl-ops-pairs (task #30): certify the (ops-global, container)
// pair invariant per ops global, from IR use evidence (pre-merge, so
// falsification #6 does not apply). An ops global g is CERTIFIED when
// every use of g is classified:
//   - store of &g into a field: the store base (container value) is
//     captured as g's pair partner;
//   - embedding in another constant initializer: the embedding global
//     is the container;
//   - icmp/ptrtoint-for-compare: benign;
//   - anything else (escapes into calls, unanalyzable): INCOMPLETE ->
//     g keeps fully pooled behavior (nothing changes, LEDGERed).
// Certified pairs feed the step-2 receiver-formal tightening; this
// pass alone is measurement + table building.
static size_t g_opsCertified = 0, g_opsIncomplete = 0, g_opsContainers = 0,
              g_opsEmbedded = 0, g_opsReadOnly = 0, g_opsV2CallCert = 0,
              g_opsV2RetAlloc = 0, g_opsV2Level2 = 0, g_opsV2BaseUnres = 0,
              g_opsV2NoBody = 0, g_opsV2Other = 0;
// F is tightenable iff it belongs to >=1 certified table AND its
// address appears ONLY inside certified fn-table initializers (walked
// up constant chains), in direct calls, or in compares — any other
// escape (raw store of &F, &F as a call argument) means uncertified
// receivers could reach F, so it stays pooled.
bool CallGraphPass::opsFnTightenable(const Function *F) {
  auto it = opsTightCache.find(F);
  if (it != opsTightCache.end())
    return it->second;
  bool inTable = false;
  for (auto &kv : opsPairs)
    if (kv.second.members.count(const_cast<Function *>(F))) {
      inTable = true;
      break;
    }
  bool ok = inTable;
  if (ok) {
    for (const User *U : F->users()) {
      if (const auto *CB = dyn_cast<CallBase>(U)) {
        if (CB->getCalledOperand()->stripPointerCasts() == F)
          continue; // direct call
        ok = false; // &F passed as an argument
        break;
      }
      if (isa<ICmpInst>(U))
        continue;
      if (const auto *C = dyn_cast<Constant>(U)) {
        // climb constant chains to owning globals; each must be a
        // certified table
        bool cok = true;
        SmallVector<const Constant *, 8> cwl{C};
        SmallPtrSet<const Constant *, 8> cseen;
        while (!cwl.empty() && cok) {
          const Constant *CC = cwl.pop_back_val();
          if (!cseen.insert(CC).second)
            continue;
          if (const auto *PG = dyn_cast<GlobalVariable>(CC)) {
            if (!opsPairs.count(PG))
              cok = false;
            continue;
          }
          bool owned = false;
          for (const User *U2 : CC->users()) {
            if (const auto *PC = dyn_cast<Constant>(U2)) {
              owned = true;
              cwl.push_back(PC);
            } else {
              cok = false; // constant used by an instruction directly
              break;
            }
          }
          if (!owned)
            cok = false; // dangling constant use
        }
        if (!cok) {
          ok = false;
          break;
        }
        continue;
      }
      ok = false;
      break;
    }
  }
  opsTightCache[F] = ok;
  return ok;
}

void CallGraphPass::certifyOpsPairs() {
  auto collectFns = [&](const Constant *C, FuncSet &out,
                        auto &&self) -> void {
    if (const auto *F2 = dyn_cast<Function>(C->stripPointerCasts())) {
      out.insert(getFuncDef(const_cast<Function *>(F2)));
      return;
    }
    if (isa<ConstantAggregate>(C))
      for (const Use &Op : C->operands())
        if (const auto *CO = dyn_cast<Constant>(Op.get()))
          self(CO, out, self);
  };
  // Interior pointers (gep(&g, k!=0) as a VALUE): only member reads and
  // compares are benign. Anything else could store a derived pointer a
  // two-level site later dispatches through, bypassing the container
  // set -> the certificate must fail.
  auto interiorOK = [&](const Constant *C0) -> bool {
    SmallVector<const Constant *, 4> q{C0};
    SmallPtrSet<const Constant *, 4> qs;
    while (!q.empty()) {
      const Constant *C = q.pop_back_val();
      if (!qs.insert(C).second)
        continue;
      for (const User *U2 : C->users()) {
        if (isa<ICmpInst>(U2))
          continue;
        if (const auto *L2 = dyn_cast<LoadInst>(U2)) {
          if (L2->getPointerOperand()->stripPointerCasts() == C)
            continue;
          return false;
        }
        if (const auto *C2 = dyn_cast<ConstantExpr>(U2)) {
          q.push_back(C2);
          continue;
        }
        return false; // embedded in an initializer, call arg, store, ...
      }
    }
    return true;
  };
  // Walker v2: one-level recursion into a direct callee's formal. The
  // recipe classifies every use of formal [idx] (which holds &g at the
  // callsites we instantiate from):
  //   member reads / compares         -> benign
  //   store into a field of formal k  -> container = caller actual k
  //   store into a field of a global  -> container = that global
  //   store into a call-result local
  //     returned on every path        -> container = the callsite value
  //   anything else (second-level call, phi, unresolved base) -> FAIL
  struct FormalRecipe {
    bool ok = false;
    bool retAlloc = false;
    SmallVector<unsigned, 2> formalIdx;
    SmallVector<const GlobalVariable *, 2> globals;
  };
  std::map<std::pair<const Function *, unsigned>, FormalRecipe> recipeCache;
  std::set<const Function *> stCandidates; // --cfl-propose-ops-st
  auto walkFormal = [&](const Function *H0,
                        unsigned idx) -> const FormalRecipe & {
    auto key = std::make_pair(H0, idx);
    auto cit = recipeCache.find(key);
    if (cit != recipeCache.end())
      return cit->second;
    FormalRecipe &R2 = recipeCache[key];
    const Function *H = getFuncDef(const_cast<Function *>(H0));
    if (!H || H->empty() || idx >= H->arg_size()) {
      g_opsV2NoBody++;
      return R2;
    }
    const Argument *A = H->getArg(idx);
    bool ok = true;
    for (const User *U : A->users()) {
      if (isa<ICmpInst>(U))
        continue;
      if (const auto *LI = dyn_cast<LoadInst>(U)) {
        if (LI->getPointerOperand()->stripPointerCasts() == A)
          continue; // member read through the table pointer
        ok = false;
        g_opsV2Other++;
        break;
      }
      if (const auto *GI = dyn_cast<GetElementPtrInst>(U)) {
        if (GI->getPointerOperand()->stripPointerCasts() != A) {
          ok = false;
          g_opsV2Other++;
          break;
        }
        bool gok = true;
        for (const User *GU : GI->users()) {
          if (isa<ICmpInst>(GU))
            continue;
          const auto *GL = dyn_cast<LoadInst>(GU);
          if (GL && GL->getPointerOperand()->stripPointerCasts() == GI)
            continue;
          gok = false;
          break;
        }
        if (!gok) {
          ok = false;
          g_opsV2Other++;
          break;
        }
        continue;
      }
      if (const auto *SI = dyn_cast<StoreInst>(U)) {
        if (SI->getValueOperand()->stripPointerCasts() != A) {
          ok = false; // formal used as a store TARGET base
          g_opsV2Other++;
          break;
        }
        const Value *B = SI->getPointerOperand()->stripPointerCasts();
        while (const auto *G2 = dyn_cast<GEPOperator>(B))
          B = G2->getPointerOperand()->stripPointerCasts();
        if (const auto *BA = dyn_cast<Argument>(B)) {
          if (BA->getParent() == H) {
            R2.formalIdx.push_back(BA->getArgNo());
            continue;
          }
          ok = false;
          g_opsV2BaseUnres++;
          break;
        }
        if (const auto *BG = dyn_cast<GlobalVariable>(B)) {
          R2.globals.push_back(BG);
          continue;
        }
        if (const auto *BC = dyn_cast<CallBase>(B)) {
          // container allocated inside the helper: nameable at the
          // caller iff every return path yields it (or null)
          bool retOK = true, anyRet = false;
          for (const BasicBlock &BB : *H)
            if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
              anyRet = true;
              const Value *RV = RI->getReturnValue();
              if (!RV) {
                retOK = false;
                break;
              }
              RV = RV->stripPointerCasts();
              if (RV == BC || isa<ConstantPointerNull>(RV))
                continue;
              if (const auto *PH = dyn_cast<PHINode>(RV)) {
                // mem2reg null-check shape: ret phi [B, ...], [null, ...]
                bool phok = true;
                for (const Value *IV : PH->incoming_values()) {
                  const Value *IS = IV->stripPointerCasts();
                  if (IS == BC || isa<ConstantPointerNull>(IS))
                    continue;
                  phok = false;
                  break;
                }
                if (phok)
                  continue;
              }
              retOK = false;
              break;
            }
          if (retOK && anyRet) {
            R2.retAlloc = true;
            g_opsV2RetAlloc++;
            continue;
          }
          ok = false;
          g_opsV2BaseUnres++;
          break;
        }
        ok = false;
        g_opsV2BaseUnres++;
        break;
      }
      if (isa<CallBase>(U)) {
        ok = false; // second-level escape: one level only
        g_opsV2Level2++;
        break;
      }
      ok = false;
      g_opsV2Other++;
      break;
    }
    R2.ok = ok;
    return R2;
  };
  for (auto &mp : Ctx->Modules) {
    for (const GlobalVariable &GV : mp.first->globals()) {
      if (!GV.hasInitializer() || !GV.isConstant()) continue;
      FuncSet ms;
      collectFns(GV.getInitializer(), ms, collectFns);
      if (ms.size() < 2) continue;
      // walk every use of g; the worklist carries the exact &g alias
      // value so call-argument positions can be matched
      bool complete = true;
      std::vector<const Value *> containers;
      SmallVector<const User *, 16> wl(GV.user_begin(), GV.user_end());
      SmallPtrSet<const User *, 16> seen;
      while (!wl.empty() && complete) {
        const User *U = wl.pop_back_val();
        if (!seen.insert(U).second) continue;
        if (const auto *CE = dyn_cast<ConstantExpr>(U)) {
          if (CE->stripPointerCasts() == &GV) {
            for (const User *U2 : CE->users()) wl.push_back(U2);
          } else if (!interiorOK(CE)) {
            complete = false; // interior pointer escapes
          }
          continue;
        }
        if (const auto *CA = dyn_cast<Constant>(U)) {
          // embedded in another global's initializer: find the global
          bool foundG = false;
          SmallVector<const User *, 8> cwl(CA->user_begin(), CA->user_end());
          SmallPtrSet<const User *, 8> cseen;
          while (!cwl.empty()) {
            const User *CU = cwl.pop_back_val();
            if (!cseen.insert(CU).second) continue;
            if (const auto *PG = dyn_cast<GlobalVariable>(CU)) {
              containers.push_back(PG);
              foundG = true;
              g_opsEmbedded++;
            } else if (isa<Constant>(CU)) {
              for (const User *CU2 : CU->users()) cwl.push_back(CU2);
            } else {
              complete = false; // constant used by an instruction we
                                // did not classify at this level
            }
          }
          if (!foundG && cseen.empty()) complete = false;
          continue;
        }
        if (const auto *SI = dyn_cast<StoreInst>(U)) {
          if (SI->getValueOperand()->stripPointerCasts() != &GV) {
            complete = false; // g's address used as a store TARGET base?
            continue;
          }
          const Value *B = SI->getPointerOperand()->stripPointerCasts();
          while (const auto *G2 = dyn_cast<GEPOperator>(B))
            B = G2->getPointerOperand()->stripPointerCasts();
          containers.push_back(B);
          continue;
        }
        if (isa<ICmpInst>(U)) continue;
        if (const auto *LI = dyn_cast<LoadInst>(U)) {
          if (LI->getPointerOperand()->stripPointerCasts() == &GV)
            continue; // direct member read (v2: was counted an escape)
          complete = false;
          continue;
        }
        if (const auto *GI = dyn_cast<GetElementPtrInst>(U)) {
          bool gok = GI->getPointerOperand()->stripPointerCasts() == &GV;
          if (gok)
            for (const User *GU : GI->users()) {
              if (isa<ICmpInst>(GU)) continue;
              const auto *GL = dyn_cast<LoadInst>(GU);
              if (GL && GL->getPointerOperand()->stripPointerCasts() == GI)
                continue;
              gok = false;
              break;
            }
          if (!gok) complete = false;
          continue;
        }
        if (const auto *CB = dyn_cast<CallBase>(U)) {
          // v2: &g escapes into a direct call — recurse one level into
          // the callee's formal and instantiate the recipe per callsite
          const auto *H =
              dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
          if (!H || CB->isInlineAsm()) {
            complete = false; // indirect/asm callee: cannot follow
            continue;
          }
          bool any = false, allok = true;
          for (unsigned ai = 0; ai < CB->arg_size() && allok; ai++) {
            if (CB->getArgOperand(ai)->stripPointerCasts() != &GV)
              continue;
            any = true;
            const FormalRecipe &R2 = walkFormal(H, ai);
            if (!R2.ok) {
              allok = false;
              break;
            }
            for (unsigned k : R2.formalIdx) {
              if (k >= CB->arg_size()) {
                allok = false;
                break;
              }
              containers.push_back(CB->getArgOperand(k)->stripPointerCasts());
            }
            for (const GlobalVariable *BG : R2.globals)
              containers.push_back(BG);
            if (R2.retAlloc)
              containers.push_back(CB);
          }
          if (!any || !allok)
            complete = false;
          else {
            g_opsV2CallCert++;
            if (CFLProposeOpsSt)
              for (unsigned ai = 0; ai < CB->arg_size(); ai++)
                if (CB->getArgOperand(ai)->stripPointerCasts() == &GV) {
                  const auto &R2 = walkFormal(H, ai);
                  if (R2.ok && !R2.formalIdx.empty())
                    stCandidates.insert(getFuncDef(const_cast<Function *>(H)));
                }
          }
          continue;
        }
        complete = false; // phi / select / ptrtoint / anything else
      }
      if (!complete) {
        g_opsIncomplete++;
        continue;
      }
      if (containers.empty()) {
        // read-only table: never stored anywhere, so it can never sit
        // behind a two-level receiver — certifying it (with an empty
        // container set) is sound and unblocks opsFnTightenable for
        // members shared with stored tables.
        g_opsReadOnly++;
      }
      g_opsCertified++;
      g_opsContainers += containers.size();
      auto &rec = opsPairs[&GV];
      rec.members = std::move(ms);
      rec.containers = std::move(containers);
    }
  }
  // --cfl-propose-ops-st: whole-body qualifier for registration-setter
  // helpers. A helper is proposable iff EVERY instruction is
  // replicable per callsite: stores with a formal (GEP-walked) base
  // and formal/null/small-constant values; non-pointer reads;
  // pointer loads only feeding null-checks; no call touching a
  // formal-derived pointer; no pointer phi/select/alloca/atomics; ret
  // void, non-pointer, constant, or a plain formal (-> ALIAS atom).
  // Output lines are directly adoptable func_summaries.txt syntax, and
  // PROPOSALS ONLY — reviewed before adoption, never auto-applied.
  if (CFLProposeOpsSt) {
    auto baseOfV = [](const Value *V) -> const Value * {
      V = V->stripPointerCasts();
      while (const auto *G2 = dyn_cast<GEPOperator>(V))
        V = G2->getPointerOperand()->stripPointerCasts();
      return V;
    };
    std::vector<std::string> lines;
    for (const Function *H : stCandidates) {
      if (!H || H->empty() || H->isVarArg())
        continue;
      std::set<std::string> atoms; // dedup repeated identical stores
      std::string retAtom;
      bool ok = true;
      for (const BasicBlock &BB : *H) {
        for (const Instruction &I : BB) {
          if (!ok)
            break;
          if (const auto *SI = dyn_cast<StoreInst>(&I)) {
            const Value *B = baseOfV(SI->getPointerOperand());
            const auto *BA = dyn_cast<Argument>(B);
            if (!BA || BA->getParent() != H) {
              ok = false;
              break;
            }
            const Value *V = SI->getValueOperand()->stripPointerCasts();
            if (const auto *VA = dyn_cast<Argument>(V)) {
              if (VA->getParent() != H) {
                ok = false;
                break;
              }
              // scalar formals (enum/flags) need no atom — only pointer
              // identity must be replicated per callsite
              if (containsPointerType(VA->getType()))
                atoms.insert("ST(*arg" + std::to_string(BA->getArgNo()) +
                             "<-arg" + std::to_string(VA->getArgNo()) + ")");
              continue;
            }
            if (isa<ConstantPointerNull>(V))
              continue; // null init: no pointer flow
            if (const auto *CI = dyn_cast<ConstantInt>(V)) {
              (void)CI;
              continue; // constant scalar init
            }
            if (V->getType()->isPointerTy()) {
              ok = false; // fn ptr / global / computed pointer value
              break;
            }
            // non-constant scalar: reject ptr-width ints (possible
            // laundered provenance), allow narrow scalars
            if (curDL && V->getType()->isIntegerTy() &&
                V->getType()->getIntegerBitWidth() >= 64) {
              ok = false;
              break;
            }
            continue;
          }
          if (const auto *LI = dyn_cast<LoadInst>(&I)) {
            if (!containsPointerType(LI->getType()))
              continue; // scalar read
            bool nullChk = true;
            for (const User *LU : LI->users())
              if (!isa<ICmpInst>(LU)) {
                nullChk = false;
                break;
              }
            if (!nullChk) {
              ok = false;
              break;
            }
            continue;
          }
          if (const auto *CB2 = dyn_cast<CallBase>(&I)) {
            if (const auto *II = dyn_cast<IntrinsicInst>(CB2))
              if (II->isAssumeLikeIntrinsic() ||
                  isa<DbgInfoIntrinsic>(II))
                continue;
            for (const Use &Op : CB2->args()) {
              const Value *B = baseOfV(Op.get());
              if (isa<Argument>(B) || isa<PHINode>(B) || isa<SelectInst>(B) ||
                  isa<LoadInst>(B)) {
                ok = false; // formal-derived (or unresolvable) escape
                break;
              }
            }
            if (!ok)
              break;
            continue;
          }
          if (const auto *RI = dyn_cast<ReturnInst>(&I)) {
            const Value *RV = RI->getReturnValue();
            if (!RV || !RV->getType()->isPointerTy())
              continue;
            RV = RV->stripPointerCasts();
            if (const auto *RA = dyn_cast<Argument>(RV)) {
              std::string a =
                  "ALIAS(ret=arg" + std::to_string(RA->getArgNo()) + ")";
              if (retAtom.empty() || retAtom == a) {
                retAtom = a;
                continue;
              }
            }
            if (isa<ConstantPointerNull>(RV) || isa<UndefValue>(RV))
              continue;
            ok = false;
            break;
          }
          if (isa<GetElementPtrInst>(I) || isa<ICmpInst>(I) ||
              isa<BranchInst>(I) || isa<SwitchInst>(I) ||
              isa<UnreachableInst>(I) || isa<FenceInst>(I))
            continue;
          if (const auto *CI2 = dyn_cast<CastInst>(&I)) {
            if (isa<IntToPtrInst>(CI2) || isa<PtrToIntInst>(CI2)) {
              ok = false;
              break;
            }
            continue;
          }
          if (isa<BinaryOperator>(I))
            continue;
          if (isa<PHINode>(I) || isa<SelectInst>(I)) {
            if (I.getType()->isPointerTy()) {
              ok = false;
              break;
            }
            continue;
          }
          ok = false; // alloca / atomics / aggregates / anything else
          break;
        }
        if (!ok)
          break;
      }
      if (!ok || atoms.empty() || atoms.size() > 6)
        continue;
      std::string line = H->getName().str();
      for (const std::string &a : atoms)
        line += " " + a;
      if (!retAtom.empty())
        line += " " + retAtom;
      lines.push_back(line);
    }
    std::sort(lines.begin(), lines.end());
    for (const std::string &L : lines)
      errs() << "OpsST PROPOSAL: " << L << "\n";
    errs() << "OpsST PROPOSAL: " << lines.size() << " of "
           << stCandidates.size() << " escape helpers qualified\n";
  }

  CG_LOG("OpsPairs LEDGER: " << g_opsCertified << " ops globals CERTIFIED ("
         << g_opsContainers << " containers, " << g_opsEmbedded
         << " via initializer embedding, " << g_opsReadOnly
         << " read-only), " << g_opsIncomplete << " incomplete -> pooled; v2: "
         << g_opsV2CallCert << " call-escapes certified ("
         << g_opsV2RetAlloc << " ret-alloc), rejections: " << g_opsV2Level2
         << " second-level, " << g_opsV2BaseUnres << " base-unresolved, "
         << g_opsV2NoBody << " no-body/vararg, " << g_opsV2Other
         << " other\n");
}
// --cfl-census-strata (task #32): stratum-bridge census. The phys/page
// stratum re-enters the typed-object universe through inlined
// phys<->virt conversions — under KASLR these load the NAMED base
// globals (page_offset_base, vmemmap_base, phys_base), so the bridge
// sites are robustly detectable. Classify every inttoptr/ptrtoint by
// a depth-limited backward walk of its int computation, plus census
// the user-boundary copy interfaces. Measurement only.

void CallGraphPass::runStrataCensus() {
  static const char *bname[STRATA_NBUCK] = {
      "directmap", "vmemmap", "kernelmap", "mm-fn", "trace", "OTHER"};
  size_t i2p[STRATA_NBUCK] = {0}, p2i[STRATA_NBUCK] = {0};
  std::map<std::string, size_t> bridgeFns[2]; // [0]=phys buckets, [1]=OTHER
  std::map<std::string, size_t> userCopy;
  size_t userCopySites = 0;
  auto classify = [&](const Value *V0, const Function *F) -> StrataBucket {
    return strataClassify(V0, F);
  };
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (const auto *IP = dyn_cast<IntToPtrInst>(&I)) {
            StrataBucket b = classify(IP->getOperand(0), &F);
            i2p[b]++;
            bridgeFns[b == STRATA_OTHER][F.getName().str()]++;
          } else if (const auto *PI = dyn_cast<PtrToIntInst>(&I)) {
            p2i[classify(PI, &F)]++;
          } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
            const auto *H = dyn_cast<Function>(
                CB->getCalledOperand()->stripPointerCasts());
            if (!H)
              continue;
            StringRef n = H->getName();
            if (n == "copy_from_user" || n == "_copy_from_user" ||
                n == "__copy_from_user" || n == "strncpy_from_user" ||
                n == "strndup_user" || n == "memdup_user" ||
                n == "vmemdup_user" || n == "copy_from_user_nofault" ||
                n == "__copy_from_user_inatomic" || n == "memdup_user_nul") {
              userCopy[n.str()]++;
              userCopySites++;
            }
          }
        }
      }
    }
  }
  size_t ti = 0, tp = 0;
  for (int b = 0; b < STRATA_NBUCK; b++) {
    ti += i2p[b];
    tp += p2i[b];
  }
  errs() << "Strata: " << ti << " inttoptr / " << tp
         << " ptrtoint sites classified\n";
  for (int b = 0; b < STRATA_NBUCK; b++)
    errs() << "Strata: bucket " << bname[b] << " inttoptr=" << i2p[b]
           << " ptrtoint=" << p2i[b] << "\n";
  for (int h = 0; h < 2; h++) {
    std::vector<std::pair<size_t, const std::string *>> r;
    for (auto &kv : bridgeFns[h])
      r.emplace_back(kv.second, &kv.first);
    std::sort(r.begin(), r.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(15, r.size()); i++)
      errs() << "Strata: " << (h ? "OTHER-fn " : "phys-bridge-fn ")
             << r[i].first << "x " << *r[i].second << "\n";
  }
  errs() << "Strata: " << userCopySites << " user-copy sites:";
  for (auto &kv : userCopy)
    errs() << " " << kv.first << "=" << kv.second;
  errs() << "\n";
}

// An INVOKE-bearing FRESH summary keeps its body analyzed: the body IS
// the pooled container channel (create-struct stores -> dispatcher) that
// dynamic-fn registration callsites still feed. Constant-fn callsites
// don't wire actuals into it (drained by design), so the body carries
// exactly the dynamic residual. Without this, FRESH routes the function
// through the allocator body-skip and dynamic registrations are silently
// severed (caught by the kernel smpboot_thread_fn zero-target diff;
// micro: t_pairs2.c).
static bool summaryInvokeKeepsBody(GlobalContext *Ctx,
                                   const llvm::Function *F) {
  auto it = Ctx->FuncSummaries.find(F);
  if (it == Ctx->FuncSummaries.end()) return false;
  for (const auto &A : it->second->atoms)
    if (A.kind == GlobalContext::SummaryAtom::Invoke) return true;
  return false;
}

bool CallGraphPass::doInitialization(Module *M) {
  if (iteration == 0 && M == Ctx->Modules.front().first) {
    if (!FuncSummaryFile.empty() && Ctx->SummarySpecs.empty())
      loadFuncSummaries(Ctx, FuncSummaryFile);
    canonicalNodeMap.clear();
    canonicalClassMembers.clear();
    moduleIndirectCallInsts.clear();
    fieldAliasMap.clear();
    linkerSectionInPlace.clear();
    linkerSectionEncoded.clear();
    linkerSectionUnresolved.clear();
  }

  // Linker-mediated arrays (task #22): module-level asm places PREL32
  // entries (.long fn - .) into linker-gathered sections (initcalls,
  // pci_fixup, tracepoints_ptrs). The referenced functions ARE
  // address-taken — the linker embeds their address — even though no
  // IR user exists, and they are members of the section array consumed
  // via __start_X/__stop_X (wireLinkerSectionArrays).
  std::set<const Function *> asmTaken;
  if (CFLLinkerArrays && !M->getModuleInlineAsm().empty()) {
    cflWalkModuleAsm(
        M->getModuleInlineAsm(), [&](StringRef sec, StringRef sym) {
          if (sym.empty()) return;
          GlobalValue *GVal = M->getNamedValue(sym);
          if (!GVal) {
            char c0 = sym.front();
            if (isalpha((unsigned char)c0) || c0 == '_' || c0 == '$')
              linkerSectionUnresolved[sec.str()]++;
            return; // local labels / literal operands
          }
          if (auto *GA = dyn_cast<GlobalAlias>(GVal))
            GVal = dyn_cast_or_null<GlobalValue>(
                GA->getAliasee()->stripPointerCasts());
          if (!GVal) return;
          if (auto *F = dyn_cast<Function>(GVal)) {
            if (F->isIntrinsic()) return;
            asmTaken.insert(F);
            linkerSectionEncoded[sec.str()].insert(getFuncDef(F));
          } else if (auto *G = dyn_cast<GlobalVariable>(GVal)) {
            if (!G->isDeclaration())
              linkerSectionEncoded[sec.str()].insert(G);
          }
        });
  }

  for (auto &GV : M->globals()) {
    if (Ctx->ExtGobjs.find(GV.getGUID()) != Ctx->ExtGobjs.end())
      continue;
    if (GV.isDeclaration())
      continue;

    // Skip compiler-introduced globals
    if (shouldSkipValue(&GV)) {
      CG_DEBUG("Skipping compiler-introduced global: " << GV.getName() << "\n");
      continue;
    }

    NF.createValueNode(&GV);

    // section-attributed globals are linker-array members (__param,
    // .init.setup, _ftrace_events, __tracepoints, ...)
    if (CFLLinkerArrays && GV.hasSection()) {
      StringRef sec = GV.getSection();
      if (!sec.starts_with(".discard.") && sec != "llvm.metadata")
        linkerSectionInPlace[cflNormalizeSection(sec)].insert(&GV);
    }
  }

  for (Function &F : *M) {
    // initialize callers
    auto RF = getFuncDef(&F);
    CallInstSet &CIS = Ctx->Callers[RF]; // use RF to retrieve callers
    for (User *U : F.users()) {
      if (CallInst *CI = dyn_cast<CallInst>(U)) {
        if (CI->getCalledFunction() == &F)
          CIS.insert(CI);
      }
    }

    // collect address-taken functions (module-asm references count:
    // the linker materializes their address into a section array)
    if (F.hasAddressTaken() || asmTaken.count(&F)) {
      Ctx->AddressTakenFuncs.insert(&F);

      // only add fval -> fobj edge in call graph analysis?
      // create a value node for function pointer
      NodeIndex valNode = NF.createValueNode(&F);
      (void)valNode;
    }

    // Populate AllocFuncs. When --func-summaries is loaded, the file is
    // AUTHORITATIVE (FRESH entries drive all existing allocator paths;
    // the legacy hardcoded isAllocFn table is not consulted). Without
    // it, legacy behavior is unchanged.
    if (!Ctx->SummarySpecs.empty()) {
      if (const auto *S = summaryForName(Ctx, F.getName())) {
        Ctx->FuncSummaries[&F] = S;
        if (S->fresh) Ctx->AllocFuncs.insert(&F);
      }
    } else {
      int size = 0, flag = 0;
      if (isAllocFn(F.getName(), &size, &flag))
        Ctx->AllocFuncs.insert(&F);
    }

    if (!F.isDeclaration() && !F.isIntrinsic() && !F.empty()) {
      // create nodes for function arguments and return value
      if (F.getFunctionType()->isVarArg())
        NF.createVarargNode(&F);
      for (auto &arg : F.args()) {
        NF.createValueNode(&arg);
      }
      if (!F.getReturnType()->isVoidTy()) {
        NF.createReturnNode(&F);
      }

      // Create per-instruction value nodes early (for global dedup).
      // Skip alloc/container functions to match doModulePass filtering.
      if (CFLGlobalDedup &&
          !Ctx->AllocFuncs.count(&F) &&
          !Ctx->ContainerFuncs.count(&F) &&
          !shouldSkipFunction(&F)) {
        for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
          const Instruction *I = &*itr;
          if (containsPointerType(I->getType()))
            NF.createValueNode(I);
          if (const ReturnInst *RI = dyn_cast<ReturnInst>(I))
            Ctx->RetSites[&F] = RI;
          if (const CallBase *CB = dyn_cast<CallBase>(I)) {
            if (const Function *CF = CB->getCalledFunction()) {
              if (Ctx->AllocFuncs.count(CF))
                Ctx->AllocSites.insert(CB);
            }
          }
        }
      }
    }
  }

  // Collect global constructors/destructors
  processCtorsDtors(M);

  // Collect ifunc resolver targets
  for (const GlobalIFunc &IF : M->ifuncs())
    collectIFuncTargets(&IF);

  if (M == Ctx->Modules.back().first) {
    for (auto const &itr: Ctx->ExtGobjs) {
      // linker-array bounds with complete, enumerable contents get
      // their OWN identity (closed world) instead of the universal
      // fallback — registered BEFORE any edges are built so every
      // load of the symbol resolves to the dedicated node
      if (CFLLinkerArrays) {
        StringRef N = itr.second->getName();
        std::vector<std::string> exact, prefix;
        if (linkerBoundsSectionKeys(N, exact, prefix) &&
            !linkerExcludedFamily(N)) {
          bool unresolved = false;
          std::set<const GlobalValue *> ip, en;
          linkerArraySources(N, ip, en, &unresolved);
          if ((!ip.empty() || !en.empty()) && !unresolved)
            NF.addExtGobjOverride(itr.first);
        }
      }
      NF.createValueNode(itr.second);
    }
    for (auto const &itr: Ctx->ExtFuncs) {
      if (!itr.second->getReturnType()->isVoidTy())
        NF.createReturnNode(itr.second);
    }
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee mapping
  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;

    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      // map callsite to possible callees
      if (CallBase *CB = dyn_cast<CallBase>(&*i)) {
        if (CB->isInlineAsm())
          continue;
        // Ensure direct calls (including to alloc/container/skipped
        // functions) are recorded so they appear in the callgraph export.
        if (Function *CF = CB->getCalledFunction()) {
          const Function *RCF = getFuncDef(CF);
          if (!RCF->isIntrinsic())
            Ctx->Callees[CB].insert(RCF);
        }
        FuncSet &FS = Ctx->Callees[CB];
        // calculate the caller info here
        for (const Function *CF : FS) {
          CallInstSet &CIS = Ctx->Callers[CF];
          CIS.insert(CB);
        }
        // collect indirect call targets by type
        if (Ctx->IndirectCallInsts.find(CB) != Ctx->IndirectCallInsts.end()) {
          FuncSet &TS = calleeByType[CB];
          findCalleesByType(CB, TS);
        }
      }
    }
  }

  if (M == Ctx->Modules.back().first) {
    // compare callees found by CFL and type matching
    size_t total = 0, match = 0;
    for (auto &it : calleeByType) {
      const CallBase *CS = it.first;
      FuncSet &TS = it.second;
      FuncSet &FS = Ctx->Callees[CS];
      total += TS.size();
      extern cl::opt<bool> CFLDumpCalleeMismatch;
      for (const Function *F : TS) {
        if (FS.find(F) != FS.end()) {
          match++;
        } else if (CFLDumpCalleeMismatch) {
          // not found by CFL
          WARNING("Callee by type not found by CFL: " << F->getName() << " for " << *CS << "\n");
        }
      }
    }
    CG_LOG("Callee by type: total " << total << ", match by CFL " << match << "\n");
    CG_LOG("IntProvenance: modeled " << g_intProvStores << " int stores + "
           << g_intProvLoads << " int loads (witnessed); LEDGER unmodeled "
           << g_intStoreUnmodeled << " stores / " << g_intLoadUnmodeled
           << " loads with interprocedural int provenance\n");
    CG_LOG("StaticCall LEDGER: " << g_staticCallWired
           << " __SCT__ callsites wired through their keys, "
           << g_staticCallUpdates << " updates wired per-callsite; "
           << g_staticCallNoKey << " without a visible key + "
           << g_staticCallDynUpdate
           << " dynamic-key updates SUPPRESSED (tracepoints covered by "
           << g_tracepointProbes << " probe-registration wirings); "
           << g_staticCallTpIter
           << " tp_func sites -> iterator (probes transitive)\n");
    CG_LOG("InlineAsm LEDGER: modeled " << g_asmSlotLoads
           << " slot loads + " << g_asmSlotStores << " slot stores ("
           << g_asmWidthWitnessed << " width-witnessed), " << g_asmRegLoads
           << " reg-through loads + " << g_asmRegStores << " stores + "
           << g_asmRegCopies << " copies; declined " << g_asmLaunderDeclined
           << " unwitnessed launder candidates\n");
    if (!Ctx->SummarySpecs.empty())
      CG_LOG("FuncSummary LEDGER: " << Ctx->FuncSummaries.size()
             << " functions summarized; applied " << g_sumCpy << " CPY, "
             << g_sumAlias << " ALIAS, " << g_sumSt << " ST, " << g_sumLd
             << " LD, " << g_sumFreshSub << " FRESHSUB, " << g_sumInvoke
             << " INVOKE (" << g_sumInvokeDyn
             << " dynamic-fn pooled fallbacks, " << g_sumInvokeRet
             << " :ret bindings); " << g_sumSkipped
             << " atom refs skipped (missing arg/node)\n");
    {
      uint64_t uniExtGobj = 0, uniOther = 0;
      NF.getUniversalLedger(uniExtGobj, uniOther);
      CG_LOG("UniversalPtr LEDGER: " << uniExtGobj
             << " extern-global value resolutions + " << uniOther
             << " other fallbacks; " << g_uniEdgeTouches
             << " edges touch universal, " << g_uniDerefTouches
             << " deref-throughs, " << g_uniFptrIcalls
             << " icalls read unknown extern memory directly\n");
    }
    CG_LOG("PrintfSink: " << printfSinkCallsites << " benign vararg callsites ("
           << printfSinkArgsSkipped << " tail args unwired), "
           << printfNonConstFmt << " non-constant fmt kept, "
           << printfNonBenignFmt << " non-benign fmt kept\n");
    // Deterministic per-icall resolution dump (one line per pair; sort the
    // lines to diff runs — FuncSet iteration order is not stable).
    extern cl::opt<bool> CFLDumpICalls;
    if (CFLDumpICalls) {
      for (auto &it : Ctx->Callees) {
        const CallBase *CS = it.first;
        // direct-form sites stay out UNLESS they were reclassified as
        // icalls (static_call trampolines dispatch through their key)
        if (CS->isInlineAsm() ||
            (CS->getCalledFunction() &&
             !Ctx->IndirectCallInsts.count(const_cast<CallBase *>(CS))))
          continue;
        for (const Function *F : it.second)
          errs() << "ICALL " << CS->getFunction()->getName() << " :: " << *CS
                 << " -> " << F->getName() << "\n";
      }
    }
    // check if all address-taken functions are used in indirect calls
    FuncSet allCallees;
    for (auto &it : Ctx->Callees)
      allCallees.insert(it.second.begin(), it.second.end());
    size_t used = 0;
    for (const Function *F : Ctx->AddressTakenFuncs) {
      if (allCallees.find(F) != allCallees.end()) {
        used++;
      } else {
        WARNING("Address-taken function not used in indirect calls: " << F->getName() << "\n");
        // full-constant user dump serializes entire global initializers —
        // multi-GB on kernel inputs, so keep it at debug verbosity
        if (VerboseLevel >= 3) {
          for (auto *U : F->users()) {
            if (!isa<Function>(U)) // skip personality
              errs() << "  User: " << *U << "\n";
          }
        }
      }
    }
    CG_LOG("Address-taken functions: total " << Ctx->AddressTakenFuncs.size() << ", used " << used << "\n");
  }

  return false;
}

bool CallGraphPass::findCustomAllocators(const cfl_result_t &outputCFLGraph,
                                         bool rewriteEdges) {
  bool foundNewAlloc = false;
  FuncSet newAllocFuncs;
  std::vector<NodeIndex> memberNodes;
  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  for (auto *F : Ctx->CandidateAllocFuncs) {
    // get return value
    NodeIndex retNode;
    if (useDense) {
      retNode = getDenseID(NF.getReturnNodeFor(F));
    } else {
      retNode = getCanonicalNode(NF.getReturnNodeFor(F));
    }
    if (retNode == AndersNodeFactory::InvalidIndex ||
        (useDense && retNode == UINT32_MAX))
      continue;
    assert(retNode < outputCFLGraph.size() && "Return node out of CFL graph range");
    auto &cflSet = outputCFLGraph[retNode][EB.getLabelV()]; // find the alias set
    std::unordered_set<NodeIndex> seenRoots;
    for (auto idx : cflSet) {
      // Map back to original node if using dense mapping
      NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
      NodeIndex root = getCanonicalNode(origIdx);
      if (!seenRoots.insert(root).second)
        continue;
      bool reachesAllocSite = false;
      collectCanonicalMembers(root, memberNodes);
      for (NodeIndex member : memberNodes) {
        NodeIndex canonicalMember = getCanonicalNode(member);
        if (AllocSites.count(member) || AllocSites.count(canonicalMember)) {
          reachesAllocSite = true;
          break;
        }
      }
      if (reachesAllocSite) {
        // if return value is from a known allocation site
        CG_LOG("Custom allocator " << F->getName() << " return value from alloc site: " << idx << "\n");
        Ctx->AllocFuncs.insert(F);
        newAllocFuncs.insert(F);
        foundNewAlloc = true;
        if (rewriteEdges) {
          // update edge
          for (auto const& U : F->users()) {
            if (const CallBase *CI = dyn_cast<CallBase>(U)) {
              if (CI->getCalledFunction() == F) {
                NodeIndex callNode = getCanonicalNode(NF.getValueNodeFor(CI));
                assert(callNode != AndersNodeFactory::InvalidIndex && "CallBase node not found for candidate alloc func!");
                Ctx->AllocSites.insert(CI);
                AllocSites.insert(callNode);
                // create heap object node
                NodeIndex heapObj = NF.createOpaqueObjectNode(CI, true);
                EB.addDereferenceEdges(callNode, heapObj);
                // remove call edges
                removeCallEdges(CI, F);
                CG_LOG("Update custom allocator call: " << *CI << "\n");
              }
            }
          }
        }
        break;
      }
    }
  }

  if (foundNewAlloc) {
    // remove confirmed allocators from candidate set
    for (auto *F : newAllocFuncs) {
      Ctx->CandidateAllocFuncs.erase(F);
    }
  }

  return foundNewAlloc;
}

bool CallGraphPass::lookupRetDense(
    const Function *F,
    const std::unordered_map<std::string, uint32_t> &symMap,
    uint32_t graphSize, uint32_t &retDense) const {
  assert(F && "lookupRetDense: null Function");
  std::string retSym = "ret:" + std::to_string(F->getGUID());
  auto itDense = symMap.find(retSym);
  if (itDense != symMap.end() && itDense->second < graphSize) {
    retDense = itDense->second;
    return true;
  }

  std::string lretSym = "lret:" + getScopeName(F);
  auto itDenseLocal = symMap.find(lretSym);
  if (itDenseLocal == symMap.end() || itDenseLocal->second >= graphSize)
    return false;
  retDense = itDenseLocal->second;
  return true;
}

bool CallGraphPass::lookupArgDense(
    const Function *F, unsigned argNo,
    const std::unordered_map<std::string, uint32_t> &symMap,
    uint32_t graphSize, uint32_t &argDense) const {
  assert(F && "lookupArgDense: null Function");
  assert(argNo < F->arg_size() && "lookupArgDense: argNo out of range");


  std::string argSym =
      "arg:" + std::to_string(F->getGUID()) + ":" + std::to_string(argNo);
  auto itDense = symMap.find(argSym);
  if (itDense != symMap.end() && itDense->second < graphSize) {
    argDense = itDense->second;
    return true;
  }

  std::string largSym =
      "larg:" + getScopeName(F) + ":" + std::to_string(argNo);
  auto itDenseLocal = symMap.find(largSym);
  if (itDenseLocal == symMap.end() || itDenseLocal->second >= graphSize)
    return false;
  argDense = itDenseLocal->second;
  return true;
}

bool CallGraphPass::lookupVarargDense(
    const Function *F,
    const std::unordered_map<std::string, uint32_t> &symMap,
    uint32_t graphSize, uint32_t &varargDense) const {
  assert(F && "lookupVarargDense: null Function");
  assert(F->isVarArg() && "lookupVarargDense: Function is not vararg");


  std::string varargSym = "vararg:" + std::to_string(F->getGUID());
  auto itDense = symMap.find(varargSym);
  if (itDense != symMap.end() && itDense->second < graphSize) {
    varargDense = itDense->second;
    return true;
  }

  std::string lvarargSym = "lvararg:" + getScopeName(F);
  auto itDenseLocal = symMap.find(lvarargSym);
  if (itDenseLocal == symMap.end() || itDenseLocal->second >= graphSize)
    return false;
  varargDense = itDenseLocal->second;
  return true;
}

bool CallGraphPass::findCustomAllocatorsComposed(
    const cfl_result_t &composedGraph,
    const std::unordered_map<std::string, uint32_t> &symbolToDense) {
  if (composedGraph.empty())
    return false;
  const uint32_t labelV = EB.getLabelV();
  if (composedGraph[0].size() <= labelV) {
    WARNING("Compositional custom allocator detection skipped: V label index "
            << labelV << " is out of range\n");
    return false;
  }

  const uint32_t graphSize = composedGraph.size();

  std::unordered_set<uint32_t> knownAllocRetNodes;
  knownAllocRetNodes.reserve(Ctx->AllocFuncs.size() * 2 + 1);
  for (const Function *F : Ctx->AllocFuncs) {
    uint32_t retDense = UINT32_MAX;
    if (lookupRetDense(F, symbolToDense, graphSize, retDense)) {
      knownAllocRetNodes.insert(retDense);
      CG_DEBUG("Known allocator ret node: " << F->getName()
               << " -> " << retDense << "\n");
    } else {
      CG_DEBUG("Known allocator ret node missing in composed graph: "
               << F->getName() << "\n");
    }
  }

  bool foundNewAlloc = false;
  size_t promoted = 0;
  while (true) {
    FuncSet newlyConfirmed;
    for (const Function *F : Ctx->CandidateAllocFuncs) {
      uint32_t candRetDense = UINT32_MAX;
      if (!lookupRetDense(F, symbolToDense, graphSize, candRetDense)) {
        CG_DEBUG("Candidate allocator ret node missing in composed graph: "
                 << F->getName() << "\n");
        continue;
      }

      bool reachesKnownAlloc = knownAllocRetNodes.count(candRetDense) > 0;
      if (!reachesKnownAlloc) {
        const auto &vSet = composedGraph[candRetDense][labelV];
        for (uint32_t idx : vSet) {
          if (knownAllocRetNodes.count(idx)) {
            reachesKnownAlloc = true;
            break;
          }
        }
      }
      if (reachesKnownAlloc)
        newlyConfirmed.insert(F);
    }

    if (newlyConfirmed.empty())
      break;

    foundNewAlloc = true;
    promoted += newlyConfirmed.size();
    for (const Function *F : newlyConfirmed) {
      Ctx->AllocFuncs.insert(F);
      Ctx->CandidateAllocFuncs.erase(F);
      uint32_t retDense = UINT32_MAX;
      if (lookupRetDense(F, symbolToDense, graphSize, retDense))
        knownAllocRetNodes.insert(retDense);
      CG_LOG("Custom allocator (composed) " << F->getName()
             << " return value aliases known allocator return\n");
    }
  }

  if (foundNewAlloc) {
    CG_LOG("Compositional custom allocator detection promoted " << promoted
           << " allocator candidate(s)\n");
  }

  return foundNewAlloc;
}

bool CallGraphPass::addFieldAlias(const FieldStoreKey &A, const FieldStoreKey &B) {
  if (A == B)
    return false;
  bool changed = false;
  changed |= fieldAliasMap[A].insert(B).second;
  changed |= fieldAliasMap[B].insert(A).second;
  return changed;
}

bool CallGraphPass::fieldFilterAccepts(const Function *F,
                                       const std::string &callSiteStruct,
                                       unsigned callSiteFieldIdx) const {
  const Function *canonF = F;
  if (F) {
    auto itDef = Ctx->Funcs.find(F->getGUID());
    if (itDef != Ctx->Funcs.end())
      canonF = itDef->second;
  }

  // A function with any unclassified address escape must never be rejected.
  if (funcFieldStoresIncomplete.count(canonF))
    return true;

  auto it = funcFieldStores.find(canonF);
  if (it == funcFieldStores.end())
    return true;
  const auto &fieldSet = it->second;
  if (fieldSet.empty())
    return true;

  FieldStoreKey callSiteKey{callSiteStruct, callSiteFieldIdx};
  if (fieldSet.count(callSiteKey))
    return true;

  SmallVector<FieldStoreKey, 16> work;
  std::unordered_set<FieldStoreKey, FieldStoreKeyHash> seen;
  work.push_back(callSiteKey);
  seen.insert(callSiteKey);

  constexpr size_t kMaxAliasVisits = 256;
  size_t visits = 0;
  while (!work.empty() && visits++ < kMaxAliasVisits) {
    FieldStoreKey cur = work.pop_back_val();
    auto aliasIt = fieldAliasMap.find(cur);
    if (aliasIt == fieldAliasMap.end())
      continue;
    for (const auto &aliasKey : aliasIt->second) {
      if (fieldSet.count(aliasKey))
        return true;
      if (seen.insert(aliasKey).second)
        work.push_back(aliasKey);
    }
  }

  // If the BFS was exhausted (worklist non-empty but visit limit reached),
  // conservatively accept to avoid unsound rejections.
  if (!work.empty())
    return true;

  return false;
}

void CallGraphPass::buildFieldStoreMapFromIR(Module *M) {
  size_t directStores = 0, callbackStores = 0, copyAliases = 0;
  auto addAggregateCopyAliases = [&](const Value *DstPtr, const Value *SrcPtr) {
    std::string dstStruct, srcStruct;
    unsigned dstField = 0, srcField = 0;
    Type *dstFieldTy = nullptr;
    Type *srcFieldTy = nullptr;

    bool hasDst = getFieldKeyFromPointerOperand(DstPtr, dstStruct, dstField, dstFieldTy);
    bool hasSrc = getFieldKeyFromPointerOperand(SrcPtr, srcStruct, srcField, srcFieldTy);
    if (!hasDst && !hasSrc)
      return;

    auto addParentToNested = [&](const FieldStoreKey &parentKey, Type *fieldTy) {
      auto *ST = dyn_cast_or_null<StructType>(fieldTy);
      if (!ST || ST->isOpaque() || ST->isLiteral() || !ST->hasName())
        return;
      if (LLVM_STRING_STARTS_WITH(ST->getStructName(), "union"))
        return;
      std::string childStruct = stripStructNameSuffix(ST->getStructName()).str();
      for (unsigned i = 0; i < ST->getNumElements(); i++) {
        if (addFieldAlias(parentKey, {childStruct, i}))
          copyAliases++;
      }
    };

    if (hasDst && hasSrc && addFieldAlias({dstStruct, dstField}, {srcStruct, srcField}))
      copyAliases++;
    if (hasDst)
      addParentToNested({dstStruct, dstField}, dstFieldTy);
    if (hasSrc)
      addParentToNested({srcStruct, srcField}, srcFieldTy);

    auto *DstST = dyn_cast_or_null<StructType>(dstFieldTy);
    auto *SrcST = dyn_cast_or_null<StructType>(srcFieldTy);
    if (DstST && SrcST &&
        !DstST->isOpaque() && !SrcST->isOpaque() &&
        !DstST->isLiteral() && !SrcST->isLiteral() &&
        DstST->hasName() && SrcST->hasName() &&
        !LLVM_STRING_STARTS_WITH(DstST->getStructName(), "union") &&
        !LLVM_STRING_STARTS_WITH(SrcST->getStructName(), "union") &&
        isStructLayoutCompatible(DstST, SrcST)) {
      std::string dstChild = stripStructNameSuffix(DstST->getStructName()).str();
      std::string srcChild = stripStructNameSuffix(SrcST->getStructName()).str();
      for (unsigned i = 0; i < DstST->getNumElements(); i++) {
        if (addFieldAlias({dstChild, i}, {srcChild, i}))
          copyAliases++;
      }
    }
  };

  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;
    if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
      continue;
    if (shouldSkipFunction(&F))
      continue;

    for (inst_iterator II = inst_begin(F), IE = inst_end(F); II != IE; ++II) {
      // Case 1: Direct store of function pointer to struct field
      //   store @func, (getelementptr %struct, %ptr, 0, N)
      if (auto *SI = dyn_cast<StoreInst>(&*II)) {
        auto *StoredFunc = dyn_cast<Function>(
            SI->getValueOperand()->stripPointerCasts());
        if (!StoredFunc) continue;
        Function *canonStoredFunc = getFuncDef(StoredFunc);
        std::string sName;
        unsigned fIdx = 0;
        Type *fieldTy = nullptr;
        if (getFieldKeyFromPointerOperand(SI->getPointerOperand(), sName, fIdx, fieldTy)) {
          funcFieldStores[canonStoredFunc].insert({sName, fIdx});
          directStores++;
        }
        continue;
      }

      if (auto *MTI = dyn_cast<MemTransferInst>(&*II)) {
        addAggregateCopyAliases(MTI->getRawDest(), MTI->getRawSource());
        continue;
      }

      // Case 3: Function pointer passed as callback argument
      //   call @setter(%obj, @func) where setter stores param to struct field
      auto *CB = dyn_cast<CallBase>(&*II);
      if (!CB || CB->isInlineAsm()) continue;
      if (Function *Callee = CB->getCalledFunction()) {
        StringRef calleeName = Callee->getName();
        if ((LLVM_STRING_STARTS_WITH(calleeName, "llvm.memcpy.") ||
             LLVM_STRING_STARTS_WITH(calleeName, "llvm.memmove.") ||
             calleeName == "memcpy" ||
             calleeName == "memmove") &&
            CB->arg_size() >= 2) {
          addAggregateCopyAliases(CB->getArgOperand(0), CB->getArgOperand(1));
        }
      }

      for (unsigned i = 0; i < CB->arg_size(); i++) {
        auto *ArgFunc = dyn_cast<Function>(
            CB->getArgOperand(i)->stripPointerCasts());
        if (!ArgFunc) continue;
        Function *canonArgFunc = getFuncDef(ArgFunc);

        // Find the callee's definition (may be in another module)
        Function *callee = CB->getCalledFunction();
        if (!callee) continue;
        if (callee->isDeclaration()) {
          callee = getFuncDef(callee);
          if (callee->isDeclaration()) continue;
        }
        if (callee->empty()) continue;
        if (i >= callee->arg_size()) continue;

        // Trace parameter's uses in callee's body (one level only).
        // Handle the common -O0 pattern where params are stored to allocas:
        //   store %param, %alloca
        //   ...
        //   %val = load %alloca
        //   store %val, (GEP %struct, field N)
        Argument *param = callee->getArg(i);
        // Collect values that carry the parameter: the param itself,
        // casts of it, and loads from allocas it was stored to.
        SmallVector<Value*, 8> paramValues;
        paramValues.push_back(param);
        for (User *U : param->users()) {
          if (isa<CastInst>(U))
            paramValues.push_back(cast<Value>(U));
        }
        // Check for alloca spill pattern: param → store to alloca → load
        for (User *U : param->users()) {
          auto *SI = dyn_cast<StoreInst>(U);
          if (!SI || SI->getValueOperand() != param) continue;
          Value *allocaPtr = SI->getPointerOperand();
          if (!isa<AllocaInst>(allocaPtr)) continue;
          // Collect all loads from this alloca
          for (User *AU : allocaPtr->users()) {
            if (auto *LI = dyn_cast<LoadInst>(AU))
              paramValues.push_back(LI);
          }
        }
        bool traced = false;
        for (Value *PV : paramValues) {
          for (User *U : PV->users()) {
            auto *PSI = dyn_cast<StoreInst>(U);
            if (!PSI || PSI->getValueOperand() != PV) continue;
            std::string sName;
            unsigned fIdx = 0;
            Type *fieldTy = nullptr;
            if (getFieldKeyFromPointerOperand(PSI->getPointerOperand(), sName, fIdx, fieldTy)) {
              funcFieldStores[canonArgFunc].insert({sName, fIdx});
              callbackStores++;
              traced = true;
            }
          }
        }
        if (traced)
          fieldTraceOK.insert({CB, i});
      }
    }
  }

  // Completeness audit: the field filter may only reject a target if every
  // escape of its address was classified above. Walk each function's users;
  // any unclassified escape marks the function incomplete and the filter
  // falls back to always-accept for it.
  auto scannedFn = [&](const Function *PF) {
    return PF && !PF->isDeclaration() && !PF->isIntrinsic() && !PF->empty() &&
           (!Ctx->AllocFuncs.count(PF) || summaryInvokeKeepsBody(Ctx, PF)) &&
           !Ctx->ContainerFuncs.count(PF) && !shouldSkipFunction(PF);
  };
  size_t incompleteMarked = 0;
  for (Function &F : *M) {
    Function *canonF = getFuncDef(&F);
    if (funcFieldStoresIncomplete.count(canonF))
      continue;
    bool incomplete = false;
    SmallVector<const Value *, 16> vals;
    SmallPtrSet<const Value *, 32> seenV;
    vals.push_back(&F);
    while (!vals.empty() && !incomplete) {
      const Value *V = vals.pop_back_val();
      if (!seenV.insert(V).second)
        continue;
      for (const Use &U : V->uses()) {
        const User *Usr = U.getUser();
        if (const auto *C = dyn_cast<Constant>(Usr)) {
          if (isa<GlobalVariable>(C) || isa<GlobalAlias>(C))
            continue; // initializer: recorded by processInitializer or keyless
          if (const auto *CE = dyn_cast<ConstantExpr>(C)) {
            if (CE->getOpcode() == Instruction::PtrToInt) { incomplete = true; break; }
          }
          vals.push_back(C); // aggregates / cast / gep exprs: follow users
          continue;
        }
        const auto *I = dyn_cast<Instruction>(Usr);
        if (!I) { incomplete = true; break; }
        if (const auto *CB2 = dyn_cast<const CallBase>(I)) {
          if (CB2->isCallee(&U))
            continue; // direct call, no address flow
          if (CB2->isArgOperand(&U) && scannedFn(I->getFunction()) &&
              fieldTraceOK.count({CB2, CB2->getArgOperandNo(&U)}))
            continue; // one-level callback trace succeeded for this use
          incomplete = true; break;
        }
        if (const auto *SI2 = dyn_cast<StoreInst>(I)) {
          std::string sN; unsigned fI = 0; Type *fT = nullptr;
          if (SI2->getValueOperand() == V && scannedFn(I->getFunction()) &&
              getFieldKeyFromPointerOperand(SI2->getPointerOperand(), sN, fI, fT))
            continue; // classified as a direct field store above
          incomplete = true; break;
        }
        if (isa<CastInst>(I)) { vals.push_back(I); continue; }
        if (isa<CmpInst>(I)) continue; // comparison: no flow
        incomplete = true; break;      // phi/select/return/ptrtoint/...
      }
    }
    if (incomplete) {
      funcFieldStoresIncomplete.insert(canonF);
      incompleteMarked++;
    }
  }
  CG_LOG("FieldStore completeness [" << M->getModuleIdentifier() << "]: "
         << incompleteMarked << " functions marked incomplete (filter off)\n");

  CG_LOG("FieldStore IR [" << M->getModuleIdentifier() << "]: "
         << directStores << " direct, " << callbackStores << " callback, "
         << copyAliases << " copy-aliases, "
         << funcFieldStores.size() << " functions total, "
         << fieldAliasMap.size() << " alias roots\n");
}

bool CallGraphPass::handleIndirectCall(const cfl_result_t &outputCFLGraph,
                                       const CallInstSet &indirectCalls) {
  // resolve indirect calls
  bool Changed = false;
  std::vector<NodeIndex> memberNodes;
  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  for (auto *CS : indirectCalls) {
    CG_DEBUG("Handle indirect CallSite: " << *CS << " in function "
        << CS->getFunction()->getName() << "\n");
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    NodeIndex fptrNode;
    if (useDense) {
      fptrNode = getDenseID(NF.getValueNodeFor(fptr));
      if (fptrNode == UINT32_MAX) {
        WARNING("FuncPtr for " << *CS << " dense node not found!\n");
        continue;
      }
    } else {
      fptrNode = getCanonicalNode(NF.getValueNodeFor(fptr));
      if (fptrNode == AndersNodeFactory::InvalidIndex) {
        WARNING("FuncPtr for " << *CS << " node not found!\n");
        continue;
      }
    }
    assert(fptrNode < outputCFLGraph.size() && "Func-ptr node out of CFL graph range");

    // Extract call-site struct field info: trace through LoadInst → GEP
    std::string callSiteStruct;
    unsigned callSiteFieldIdx = 0;
    bool hasCallSiteField = getCallSiteFieldKey(fptr, callSiteStruct, callSiteFieldIdx);

    auto &cflSet = outputCFLGraph[fptrNode][EB.getLabelV()];
    CG_DEBUG("  fptr node " << fptrNode << " V-set size: " << cflSet.size() << "\n");
    std::unordered_set<const Function *> seenFuncs;
    std::unordered_set<NodeIndex> seenRoots;
    for (auto idx : cflSet) {
      NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
      NodeIndex root = getCanonicalNode(origIdx);
      if (!seenRoots.insert(root).second)
        continue;
      collectCanonicalMembers(root, memberNodes);
      for (NodeIndex member : memberNodes) {
        if (NF.isSpecialNode(member)) {
          WARNING("Indirect Call: " << *CS << " callee is a special node: " << member << "\n");
          continue;
        }
        // Return nodes and vararg nodes also store Function* as their value,
        // but they represent the return value / vararg slot, not the function
        // pointer itself. Skip them — only true value nodes are function ptrs.
        if (NF.isReturnNode(member))
          continue;
        if (NF.isVarargNode(member))
          continue;

        const Value *CV = NF.getValueForNode(member);
        if (CV == NULL)
          continue;

        const Function *CF = dyn_cast<Function>(CV);
        if (CF == NULL)
          continue;
        if (!seenFuncs.insert(CF).second)
          continue;

        // due to field insensitivity, we may have FPs, do a type match
        if (!isCompatible(CS, CF)) {
          continue;
        }
        // Struct-field-aware filtering:
        // If we know the call site loads from a specific struct field,
        // and we have positive evidence of which fields this function is
        // stored into, reject if none match.
        if (hasCallSiteField) {
          if (!fieldFilterAccepts(CF, callSiteStruct, callSiteFieldIdx)) {
            CG_LOG("FieldFilter: reject " << CF->getName()
                   << " for " << callSiteStruct << " field " << callSiteFieldIdx << "\n");
            continue;
          }
        }
        if (Ctx->Callees[CS].insert(CF).second) {
          // if new callee added, we need to rerun
          Changed = true;
          if (Ctx->AllocFuncs.count(CF)) {
            Ctx->AllocSites.insert(CS);
            NodeIndex callNode = getRepNodeForValue(CS);
            if (callNode == AndersNodeFactory::InvalidIndex) {
              // Result unused / non-pointer callsite: on-demand node,
              // mirroring handleCall (fired first on whole-kernel run).
              callNode = getCanonicalNode(NF.createValueNode(CS));
            }
            AllocSites.insert(callNode);
            NodeIndex heapObj = NF.createOpaqueObjectNode(CS, true);
            EB.addDereferenceEdges(callNode, heapObj);
            auto sit = Ctx->FuncSummaries.find(CF);
            if (sit != Ctx->FuncSummaries.end() &&
                applySummaryAtoms(CS, *sit->second))
              wireCallArgs(CS, CF); // dynamic-fn INVOKE: feed the body pool
            CG_LOG("Handle indirect allocator target: " << CF->getName() << "\n");
          } else if (Ctx->ContainerFuncs.count(CF)) {
            CG_LOG("Handle indirect target: " << CF->getName() << " (container)\n");
            handleContainerCall(CS, CF);
          } else {
            CG_LOG("Handle indirect target: " << CF->getName() << "\n");
            handleCall(CS, CF);
          }
        }
      }
    }
  }

  return Changed;
}

// ---- Global union-find dedup ----

NodeIndex CallGraphPass::globalFind(NodeIndex n) {
  // getValueNodeForConstant lazily creates nodes (e.g. for ConstantExpr GEPs
  // and vector-of-pointer constants) after globalUFParent was sized. Extend
  // both arrays on demand so new nodes start as their own roots with rank 0.
  if (n >= globalUFParent.size()) {
    size_t old = globalUFParent.size();
    globalUFParent.resize(n + 1);
    globalUFRank.resize(n + 1, 0);
    std::iota(globalUFParent.begin() + old, globalUFParent.end(), (NodeIndex)old);
  }
  NodeIndex root = n;
  while (globalUFParent[root] != root)
    root = globalUFParent[root];
  // Path compression
  while (globalUFParent[n] != root) {
    NodeIndex parent = globalUFParent[n];
    globalUFParent[n] = root;
    n = parent;
  }
  return root;
}

bool CallGraphPass::globalUnion(NodeIndex a, NodeIndex b) {
  if (a == AndersNodeFactory::InvalidIndex || b == AndersNodeFactory::InvalidIndex)
    return false;
  NodeIndex ra = globalFind(a);
  NodeIndex rb = globalFind(b);
  if (ra == rb)
    return false;

  if (globalUFRank[ra] < globalUFRank[rb])
    std::swap(ra, rb);
  globalUFParent[rb] = ra;
  if (globalUFRank[ra] == globalUFRank[rb])
    globalUFRank[ra]++;
  return true;
}

bool CallGraphPass::globalDedupScanFunction(const Function *F) {
  if (!F)
    return false;

  bool anyChanged = false;
  bool changed = false;
  do {
    changed = false;
    for (const Instruction &I : instructions(F)) {
      if (isa<BitCastInst>(&I) || isa<AddrSpaceCastInst>(&I)) {
        if (!I.getType()->isPointerTy())
          continue;
        Value *src = I.getOperand(0);
        if (!src->getType()->isPointerTy())
          continue;
        NodeIndex srcNode = NF.getValueNodeFor(src);
        NodeIndex dstNode = NF.getValueNodeFor(&I);
        if (srcNode != AndersNodeFactory::InvalidIndex &&
            dstNode != AndersNodeFactory::InvalidIndex)
          changed |= globalUnion(srcNode, dstNode);
        continue;
      }

      if (const auto *GEP = dyn_cast<GetElementPtrInst>(&I)) {
        if (!GEP->getType()->isPointerTy() || !isZeroOffsetGEP(GEP))
          continue;
        const Value *base = GEP->getPointerOperand();
        NodeIndex baseNode = NF.getValueNodeFor(base);
        NodeIndex gepNode = NF.getValueNodeFor(GEP);
        if (baseNode != AndersNodeFactory::InvalidIndex &&
            gepNode != AndersNodeFactory::InvalidIndex)
          changed |= globalUnion(baseNode, gepNode);
        continue;
      }

      if (const auto *PHI = dyn_cast<PHINode>(&I)) {
        if (!PHI->getType()->isPointerTy())
          continue;
        NodeIndex dstNode = NF.getValueNodeFor(PHI);
        if (dstNode == AndersNodeFactory::InvalidIndex)
          continue;

        NodeIndex classRep = AndersNodeFactory::InvalidIndex;
        bool allSame = true;
        for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; i++) {
          Value *src = PHI->getIncomingValue(i);
          if (shouldSkipValue(src)) {
            allSame = false;
            break;
          }
          NodeIndex srcNode = NF.getValueNodeFor(src);
          if (srcNode == AndersNodeFactory::InvalidIndex) {
            allSame = false;
            break;
          }
          NodeIndex srcRoot = globalFind(srcNode);
          if (classRep == AndersNodeFactory::InvalidIndex)
            classRep = srcRoot;
          else if (classRep != srcRoot) {
            allSame = false;
            break;
          }
        }
        if (allSame && classRep != AndersNodeFactory::InvalidIndex)
          changed |= globalUnion(dstNode, classRep);
        continue;
      }

      if (const auto *Sel = dyn_cast<SelectInst>(&I)) {
        if (!Sel->getType()->isPointerTy())
          continue;
        const Value *tVal = Sel->getTrueValue();
        const Value *fVal = Sel->getFalseValue();
        if (shouldSkipValue(tVal) || shouldSkipValue(fVal))
          continue;
        NodeIndex tNode = NF.getValueNodeFor(tVal);
        NodeIndex fNode = NF.getValueNodeFor(fVal);
        NodeIndex dstNode = NF.getValueNodeFor(Sel);
        if (tNode != AndersNodeFactory::InvalidIndex &&
            fNode != AndersNodeFactory::InvalidIndex &&
            dstNode != AndersNodeFactory::InvalidIndex &&
            globalFind(tNode) == globalFind(fNode))
          changed |= globalUnion(dstNode, tNode);
      }
    }
    anyChanged |= changed;
  } while (changed);
  return anyChanged;
}

// Merge value nodes that denote the same access path, across functions:
//   - GEPs with all-constant indices on the same base class and the same
//     accumulated byte offset compute the same address.
//   - Loads through the same pointer class read the same abstract cell
//     (flow-insensitively their only inflow is that cell's deref node).
// Both are pure-copy equivalences: merging them changes no points-to facts,
// it only removes duplicate registers from the constraint graph.
bool CallGraphPass::globalDedupScanAccessPaths() {
  struct GepKey {
    NodeIndex baseRoot;
    int64_t offset;
    bool operator==(const GepKey &o) const {
      return baseRoot == o.baseRoot && offset == o.offset;
    }
  };
  struct GepKeyHash {
    size_t operator()(const GepKey &k) const {
      return std::hash<uint64_t>()((uint64_t)k.baseRoot * 0x9E3779B97F4A7C15ULL ^
                                   (uint64_t)k.offset);
    }
  };

  std::unordered_map<GepKey, NodeIndex, GepKeyHash> gepReps;
  std::unordered_map<NodeIndex, NodeIndex> loadReps;
  bool changed = false;

  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;

      for (const Instruction &I : instructions(F)) {
        if (const auto *GEP = dyn_cast<GetElementPtrInst>(&I)) {
          if (!GEP->getType()->isPointerTy())
            continue;
          NodeIndex baseNode = NF.getValueNodeFor(GEP->getPointerOperand());
          NodeIndex gepNode = NF.getValueNodeFor(GEP);
          if (baseNode == AndersNodeFactory::InvalidIndex ||
              gepNode == AndersNodeFactory::InvalidIndex)
            continue;
          APInt Off(DL.getIndexTypeSizeInBits(GEP->getType()), 0);
          if (!GEP->accumulateConstantOffset(DL, Off))
            continue;
          GepKey key{globalFind(baseNode), Off.getSExtValue()};
          auto [it, inserted] = gepReps.emplace(key, gepNode);
          if (!inserted)
            changed |= globalUnion(it->second, gepNode);
          continue;
        }

        if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          if (!containsPointerType(LI->getType()))
            continue;
          NodeIndex ptrNode = NF.getValueNodeFor(LI->getPointerOperand());
          NodeIndex valNode = NF.getValueNodeFor(LI);
          if (ptrNode == AndersNodeFactory::InvalidIndex ||
              valNode == AndersNodeFactory::InvalidIndex)
            continue;
          auto [it, inserted] = loadReps.emplace(globalFind(ptrNode), valNode);
          if (!inserted)
            changed |= globalUnion(it->second, valNode);
          continue;
        }
      }
    }
  }

  return changed;
}

// Resolve a CallBase to its callee definition, or nullptr if unresolvable.
const Function *CallGraphPass::resolveDirectCallee(const CallBase *CS) {
  const Function *CF = CS->getCalledFunction();
  if (!CF) {
    Value *CO = CS->getCalledOperand()->stripPointerCastsAndAliases();
    if (auto *CE = dyn_cast<ConstantExpr>(CO)) {
      switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: {
          GEPOperator *GEP = dyn_cast<GEPOperator>(CE);
          CO = GEP->getPointerOperand()->stripPointerCastsAndAliases();
          break;
        }
        case Instruction::BitCast:
          CO = CE->getOperand(0);
          break;
        default:
          return nullptr;
      }
    }
    CF = dyn_cast<Function>(CO);
  }
  if (!CF)
    return nullptr;

  // Resolve to definition
  auto it = Ctx->Funcs.find(CF->getGUID());
  if (it != Ctx->Funcs.end())
    CF = it->second;

  if (CF->isIntrinsic() || CF->empty())
    return nullptr;
  if (Ctx->AllocFuncs.count(CF) || Ctx->ContainerFuncs.count(CF))
    return nullptr;
  if (shouldSkipFunction(CF))
    return nullptr;

  return CF;
}

void CallGraphPass::globalDedupScanCallEdges(
    const Function *F,
    const DenseSet<const Function *> &singleCallsiteCallees) {
  if (!F || F->isDeclaration() || F->isIntrinsic() || F->empty())
    return;

  for (const Instruction &I : instructions(F)) {
    const CallBase *CS = dyn_cast<CallBase>(&I);
    if (!CS || CS->isInlineAsm())
      continue;

    if (Ctx->AllocSites.count(CS))
      continue;

    const Function *CF = resolveDirectCallee(CS);
    if (!CF)
      continue;

    // Only merge for callees with exactly 1 callsite
    if (!singleCallsiteCallees.count(CF))
      continue;

    // Summarized callees: the summary REPLACES callsite arg wiring
    // (drain semantics). A single-callsite actual<->formal pre-merge
    // makes the actual and formal one union-find node, silently
    // defeating the drain (found via the t_chain2 wrapper lift: the
    // lifted registration stayed pooled through the merged node).
    if (Ctx->FuncSummaries.count(CF) ||
        Ctx->FuncSummaries.count(getFuncDef(const_cast<Function *>(CF))))
      continue;

    // Merge pointer args: fixed actual→formal, variadic tail→vararg node
    unsigned numArgs = CS->arg_size();
    unsigned numFormals = CF->arg_size();
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!containsPointerType(arg->getType()))
        continue;
      if (shouldSkipValue(arg))
        continue;
      NodeIndex argNode = NF.getValueNodeFor(arg);
      if (argNode == AndersNodeFactory::InvalidIndex)
        continue;
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = NF.getValueNodeFor(farg);
      if (formalNode != AndersNodeFactory::InvalidIndex)
        globalUnion(argNode, formalNode);
    }
    if (CF->isVarArg() &&
        !(CFLPrintfVarargSink && printfVarargSinkCallsite(CS, CF))) {
      NodeIndex varargNode = NF.getVarargNodeFor(CF);
      if (varargNode == AndersNodeFactory::InvalidIndex)
        continue;
      for (unsigned i = numFormals; i < numArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!containsPointerType(arg->getType()))
          continue;
        if (shouldSkipValue(arg))
          continue;
        NodeIndex argNode = NF.getValueNodeFor(arg);
        if (argNode != AndersNodeFactory::InvalidIndex)
          globalUnion(argNode, varargNode);
      }
    }

    // Merge return: returnNode → callsite
    if (containsPointerType(CF->getReturnType())) {
      NodeIndex retNode = NF.getReturnNodeFor(CF);
      NodeIndex callNode = NF.getValueNodeFor(CS);
      if (retNode != AndersNodeFactory::InvalidIndex &&
          callNode != AndersNodeFactory::InvalidIndex)
        globalUnion(retNode, callNode);
    }
  }
}

void CallGraphPass::globalDedupFinalize() {
  canonicalNodeMap.clear();
  canonicalClassMembers.clear();

  size_t mergedNodes = 0;
  for (NodeIndex i = 0; i < globalUFParent.size(); i++) {
    NodeIndex root = globalFind(i);
    if (root != i) {
      canonicalNodeMap[i] = root;
      mergedNodes++;
    }
    canonicalClassMembers[root].insert(i);
  }

  CG_LOG("Global dedup: " << globalUFParent.size() << " nodes, "
         << mergedNodes << " merged, "
         << canonicalClassMembers.size() << " equivalence classes\n");
}

void CallGraphPass::runGlobalDedup() {
  const size_t numNodes = NF.getNumNodes();
  globalUFParent.resize(numNodes);
  std::iota(globalUFParent.begin(), globalUFParent.end(), 0);
  globalUFRank.assign(numNodes, 0);

  // Intra-procedural copy merges + cross-function access-path merges.
  // Iterate to a fixpoint: access-path unions (same-offset GEPs, same-cell
  // loads) can enable further phi/select merges and vice versa. Unions are
  // monotone, so stopping at the cap only forgoes optimization, never
  // soundness.
  {
    constexpr unsigned kMaxDedupRounds = 8;
    unsigned round = 0;
    bool anyChanged = true;
    while (anyChanged && round++ < kMaxDedupRounds) {
      anyChanged = false;
      for (auto &[M, _] : Ctx->Modules) {
        for (Function &F : *M) {
          if (F.isDeclaration() || F.isIntrinsic() || F.empty())
            continue;
          if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
            continue;
          if (shouldSkipFunction(&F))
            continue;
          anyChanged |= globalDedupScanFunction(&F);
        }
      }
      anyChanged |= globalDedupScanAccessPaths();
    }
    CG_LOG("Global dedup: copy/access-path merges converged in "
           << round << " round(s)\n");
  }

  // Count direct callsites per callee to find single-callsite functions
  DenseMap<const Function *, unsigned> callsiteCount;
  for (auto &[M, _] : Ctx->Modules) {
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      for (const Instruction &I : instructions(F)) {
        const CallBase *CS = dyn_cast<CallBase>(&I);
        if (!CS || CS->isInlineAsm())
          continue;
        if (Ctx->AllocSites.count(CS))
          continue;
        const Function *CF = resolveDirectCallee(CS);
        if (CF)
          callsiteCount[CF]++;
      }
    }
  }

  DenseSet<const Function *> singleCallsiteCallees;
  size_t totalCallees = 0, multiCallees = 0;
  for (auto &[CF, Count] : callsiteCount) {
    totalCallees++;
    if (Count == 1)
      singleCallsiteCallees.insert(CF);
    else
      multiCallees++;
  }
  CG_LOG("Global dedup inter-proc: " << totalCallees << " callees, "
         << singleCallsiteCallees.size() << " single-callsite, "
         << multiCallees << " multi-callsite (skipped)\n");

  // Inter-procedural merges (only for single-callsite functions)
  for (auto &[M, _] : Ctx->Modules) {
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      globalDedupScanCallEdges(&F, singleCallsiteCallees);
    }
  }

  globalDedupFinalize();

  // Free UF vectors
  globalUFParent.clear();
  globalUFParent.shrink_to_fit();
  globalUFRank.clear();
  globalUFRank.shrink_to_fit();
}

void CallGraphPass::buildDenseMapping() {
  const auto &rawEdges = EB.getEdges();
  origToDense.assign(NF.getNumNodes(), UINT32_MAX);
  denseToOrig.clear();
  numDenseNodes = 0;

  // Assign dense IDs to nodes appearing in edges. Endpoints are canonicalized
  // so merges applied after edge emission (pre-solve merge) take effect.
  auto assignDense = [&](NodeIndex n) -> uint32_t {
    NodeIndex canon = getCanonicalNode(n);
    if (origToDense[canon] == UINT32_MAX) {
      origToDense[canon] = numDenseNodes;
      denseToOrig.push_back(canon);
      numDenseNodes++;
    }
    if (canon != n)
      origToDense[n] = origToDense[canon];
    return origToDense[canon];
  };
  for (const auto &E : rawEdges) {
    assignDense(E.from);
    assignDense(E.to);
  }

  // Remap + dedup. Self-loops are kept: they only arise from wildcard field
  // loops and pre-solve class merges, both of which the solver needs.
  std::unordered_set<EdgeKey, EdgeKeyHash> seen;
  seen.reserve(rawEdges.size());
  denseEdges.clear();
  denseEdges.reserve(rawEdges.size());
  for (const auto &E : rawEdges) {
    uint32_t from = origToDense[E.from];
    uint32_t to = origToDense[E.to];
    EdgeKey key{from, to, E.label};
    if (seen.insert(key).second)
      denseEdges.emplace_back(from, to, E.label);
  }

  CG_LOG("Dense mapping: " << NF.getNumNodes() << " orig nodes -> "
         << numDenseNodes << " dense nodes, "
         << rawEdges.size() << " raw edges -> "
         << denseEdges.size() << " dense edges\n");
}

uint32_t CallGraphPass::getDenseID(NodeIndex origNode) const {
  NodeIndex canonical = getCanonicalNode(origNode);
  if (canonical < origToDense.size())
    return origToDense[canonical];
  return UINT32_MAX;
}

void CallGraphPass::solveAndCompressPerTU(Module *M, size_t edgeStart, size_t edgeEnd) {
  auto tTotal = std::chrono::steady_clock::now();
  const auto &allEdges = EB.getEdges();
  assert(edgeStart <= edgeEnd &&
         "solveAndCompressPerTU: invalid edge range");
  assert(edgeEnd <= allEdges.size() &&
         "solveAndCompressPerTU: edge range exceeds current edge list");
  assert(EB.getGrammar() && "solveAndCompressPerTU: grammar not initialized");

  std::string moduleRawId = M ? M->getModuleIdentifier() : std::string("<null-module>");
  if (M) {
    auto it = Ctx->ModuleMaps.find(M);
    if (it != Ctx->ModuleMaps.end() && !it->second.empty())
      moduleRawId = it->second.str();
  }
  std::string moduleId = normalizeModuleIdentifier(moduleRawId);
  std::vector<std::string> coveredModules{moduleId};
  std::unordered_map<std::string, std::string> moduleHashes;
  std::string moduleHash;
  std::string hashErr;
  if (computeFileSHA256(moduleId, moduleHash, &hashErr))
    moduleHashes[moduleId] = moduleHash;
  else
    WARNING("Per-TU metadata: " << hashErr << "\n");

  CG_LOG("Per-TU solve [" << M->getModuleIdentifier()
         << "]: edges [" << edgeStart << ", " << edgeEnd << ")\n");

  const CallInstSet *moduleIcalls = nullptr;
  if (auto itIcalls = moduleIndirectCallInsts.find(M);
      itIcalls != moduleIndirectCallInsts.end()) {
    moduleIcalls = &itIcalls->second;
  }

  // Boundary nodes that must be exportable even if locally edge-isolated:
  // keep them in the per-TU dense graph as singleton SCCs.
  std::vector<NodeIndex> pinnedBoundaryNodes;
  pinnedBoundaryNodes.reserve(moduleIcalls ? moduleIcalls->size() * 2 : 0);
  std::unordered_set<NodeIndex> pinnedBoundarySet;
  pinnedBoundarySet.reserve(moduleIcalls ? moduleIcalls->size() * 2 : 0);
  auto pinBoundaryNode = [&](NodeIndex N) {
    if (N == AndersNodeFactory::InvalidIndex)
      return;
    NodeIndex C = getCanonicalNode(N);
    if (C == AndersNodeFactory::InvalidIndex)
      return;
    if (pinnedBoundarySet.insert(C).second)
      pinnedBoundaryNodes.push_back(C);
  };
  if (moduleIcalls) {
    for (auto *CS : *moduleIcalls) {
      Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
      pinBoundaryNode(NF.getValueNodeFor(fptr));
      if (containsPointerType(CS->getType()))
        pinBoundaryNode(NF.getValueNodeFor(CS));
      for (unsigned argNo = 0; argNo < CS->arg_size(); argNo++) {
        Value *arg = CS->getArgOperand(argNo);
        if (!containsPointerType(arg->getType()))
          continue;
        if (shouldSkipValue(arg))
          continue;
        pinBoundaryNode(NF.getValueNodeFor(arg));
      }
    }
  }

  if (edgeStart >= edgeEnd && pinnedBoundaryNodes.empty()) {
    CompressedGraphData data;
    data.numNodes = 0;
    data.metadataJson = encodeCflcgMetadata(getCurrentCflcgGrammarMeta(EB),
                                            "per-tu",
                                            coveredModules,
                                            moduleHashes);
    perTUGraphs.push_back(std::move(data));
    CG_LOG("Per-TU compressed: no CFL edges, emitted metadata-only graph\n");
    CG_LOG("TIMER per-tu-total [" << M->getModuleIdentifier() << "] "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tTotal).count()
           << " ms\n");
    return;
  }

  // Per-TU fixed point:
  // solve CFL -> resolve indirect calls in this TU -> append new call edges ->
  // repeat until this TU contributes no new edges.
  std::vector<size_t> tuEdgeIndices;
  tuEdgeIndices.reserve((edgeEnd - edgeStart) + 256);
  for (size_t i = edgeStart; i < edgeEnd; i++)
    tuEdgeIndices.push_back(i);

  if (CFLFptrSlice)
    sliceEdgesToFptrComponents(tuEdgeIndices);

  if (CFLPreSolveMerge)
    preSolveCopyFieldMerge(EB.getEdges(), &tuEdgeIndices);

  // Diagnostic: high-degree constraint nodes are the hubs whose deref cells
  // drive M-fusion; dump them with their IR values for attribution.
  if (VerboseLevel >= 2) {
    std::vector<std::pair<NodeIndex, size_t>> topNodes;
    EB.analyzeHighDegreeNodes(500, 15, &topNodes);
    for (const auto &[nodeId, degree] : topNodes)
      NF.dumpNode(nodeId);
  }

  constexpr size_t kMaxPerTUIterations = 32;
  size_t perTUIter = 0;
  std::unique_ptr<gracfl::SolverFWGramParallel> solver;

  while (true) {
    perTUIter++;
    const auto &iterEdges = EB.getEdges();

    // Step 1: Build local dense mapping from this TU's accumulated edge set.
    origToDense.assign(NF.getNumNodes(), UINT32_MAX);
    denseToOrig.clear();
    numDenseNodes = 0;

    // Route through getCanonicalNode so global-dedup union-find merges are
    // visible to the solver: edges from merged-away nodes get folded into
    // their canonical representative's dense slot.
    for (size_t edgeIdx : tuEdgeIndices) {
      assert(edgeIdx < iterEdges.size() &&
             "solveAndCompressPerTU: edge index out of range");
      const auto &E = iterEdges[edgeIdx];
      NodeIndex fromCanon = getCanonicalNode(E.from);
      NodeIndex toCanon = getCanonicalNode(E.to);
      if (origToDense[fromCanon] == UINT32_MAX) {
        origToDense[fromCanon] = numDenseNodes;
        denseToOrig.push_back(fromCanon);
        numDenseNodes++;
      }
      if (origToDense[toCanon] == UINT32_MAX) {
        origToDense[toCanon] = numDenseNodes;
        denseToOrig.push_back(toCanon);
        numDenseNodes++;
      }
    }

    for (NodeIndex pinned : pinnedBoundaryNodes) {
      if (pinned >= origToDense.size())
        continue;
      if (origToDense[pinned] == UINT32_MAX) {
        origToDense[pinned] = numDenseNodes;
        denseToOrig.push_back(pinned);
        numDenseNodes++;
      }
    }

    assert(numDenseNodes > 0 && "solveAndCompressPerTU: dense mapping produced 0 nodes");

    // Remap + dedup edges to dense IDs
    std::unordered_set<EdgeKey, EdgeKeyHash> seen;
    seen.reserve(tuEdgeIndices.size());
    denseEdges.clear();
    denseEdges.reserve(tuEdgeIndices.size());
    for (size_t edgeIdx : tuEdgeIndices) {
      const auto &E = iterEdges[edgeIdx];
      uint32_t from = origToDense[getCanonicalNode(E.from)];
      uint32_t to = origToDense[getCanonicalNode(E.to)];
      // Keep self-loops: wildcard field loops and collapsed-class edges are
      // needed by the solver (M/Fld derivations through merged nodes).
      EdgeKey key{from, to, E.label};
      if (seen.insert(key).second)
        denseEdges.emplace_back(from, to, E.label);
    }

    // Keep pinned boundary nodes alive in the solver graph even if isolated.
    // Use an epsilon/self-edge label so these nodes materialize as singleton SCCs
    // without introducing new cross-node connectivity.
    uint32_t boundarySeedLabel = EB.getLabelV();
    if (const auto *G = EB.getGrammar()) {
      const auto &Rule1 = G->getRule1();
      if (!Rule1.empty() && !Rule1[0].empty())
        boundarySeedLabel = Rule1[0][0];
    }
    size_t seededBoundarySelfEdges = 0;
    for (NodeIndex pinned : pinnedBoundaryNodes) {
      if (pinned >= origToDense.size())
        continue;
      uint32_t dense = origToDense[pinned];
      if (dense == UINT32_MAX)
        continue;
      EdgeKey key{dense, dense, boundarySeedLabel};
      if (seen.insert(key).second) {
        denseEdges.emplace_back(dense, dense, boundarySeedLabel);
        seededBoundarySelfEdges++;
      }
    }

    assert(!denseEdges.empty() && "solveAndCompressPerTU: no dense edges after remapping");

    CG_LOG("Per-TU dense mapping [iter " << perTUIter << "]: "
           << numDenseNodes << " nodes, "
           << tuEdgeIndices.size() << " raw edges -> "
           << denseEdges.size() << " dense edges"
           << " (pinned-boundary-nodes=" << pinnedBoundaryNodes.size()
           << ", seeded-self-edges=" << seededBoundarySelfEdges << ")\n");

    // Step 2: Solve CFL for this iteration.
    auto tSolve = std::chrono::steady_clock::now();
    solver = std::make_unique<gracfl::SolverFWGramParallel>(
        denseEdges, *EB.getGrammar(), cflThreads);
    solver->runCFL();
    CG_LOG("Per-TU CFL solve [iter " << perTUIter << "]: "
           << solver->getEdgeCount() << " final edges\n");
    CG_LOG("TIMER per-tu-cfl-solve [iter " << perTUIter << "] "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tSolve).count()
           << " ms\n");

    const auto &graph = solver->getReachability();
    assert(!graph.empty() && "solveAndCompressPerTU: solver produced empty graph");
    assert(graph[0].size() > EB.getLabelV() &&
           "solveAndCompressPerTU: V label out of range");

    // Keep allocator candidate/confirmed sets in sync in compositional mode.
    // Per-TU dense mappings make this alloc-site-based check comparable to the
    // monolithic detector, but we avoid mutating call edges here.
    const bool perTUAllocUpdated = findCustomAllocators(graph, false);
    if (perTUAllocUpdated) {
      CG_LOG("Per-TU custom allocator detection [iter " << perTUIter
             << "] updated allocator sets\n");
    }

    const size_t edgeCountBeforeResolve = iterEdges.size();
    bool indirectChanged = false;
    if (moduleIcalls && !moduleIcalls->empty())
      indirectChanged = handleIndirectCall(graph, *moduleIcalls);
    const auto &edgesAfterResolve = EB.getEdges();
    const size_t edgeCountAfterResolve = edgesAfterResolve.size();
    const size_t newEdges =
        (edgeCountAfterResolve > edgeCountBeforeResolve)
            ? (edgeCountAfterResolve - edgeCountBeforeResolve)
            : 0;

    if (newEdges > 0) {
      tuEdgeIndices.reserve(tuEdgeIndices.size() + newEdges);
      for (size_t i = edgeCountBeforeResolve; i < edgeCountAfterResolve; i++)
        tuEdgeIndices.push_back(i);
    }

    CG_LOG("Per-TU iterate [" << M->getModuleIdentifier() << "] #" << perTUIter
           << ": indirect-changed=" << (indirectChanged ? "yes" : "no")
           << ", new-edges=" << newEdges << "\n");

    if (newEdges == 0)
      break;

    if (perTUIter >= kMaxPerTUIterations) {
      errs() << "[UNSOUND-RISK] Per-TU fixed point hit iteration cap ("
             << kMaxPerTUIterations << ") for " << M->getModuleIdentifier()
             << "; result may under-approximate\n";
      soundnessCapped = true;
      break;
    }
  }

  assert(solver && "solveAndCompressPerTU: solver not initialized");
  const auto &graph = solver->getReachability();

  // Step 3: V-SCC compression for graph size reduction.
  // Field store map was already built from IR (buildFieldStoreMapFromIR)
  // before this function was called.
  const uint32_t LabelV = EB.getLabelV();
  std::vector<uint32_t> nodeToSCC;
  uint32_t numSCCs = 0;
  computeVSCC(graph, LabelV, nodeToSCC, numSCCs);

  CompressedGraphData data;
  compressConstraintGraph(graph, nodeToSCC, numSCCs, data);
  data.metadataJson = encodeCflcgMetadata(getCurrentCflcgGrammarMeta(EB),
                                          "per-tu",
                                          coveredModules,
                                          moduleHashes);

  assert(data.numNodes > 0 && "solveAndCompressPerTU: compression produced 0 SCC nodes");

  // Field store map is IR-derived (buildFieldStoreMapFromIR) and accumulated
  // in funcFieldStores across modules — no need to serialize per-TU.

  CG_LOG("Per-TU compressed: " << numSCCs << " SCC nodes, "
         << data.edges.size() << " edges, "
         << data.symbolTable.size() << " symbols\n");

  // Step 5: Store result
  perTUGraphs.push_back(std::move(data));

  // Clean up dense mapping state for next module
  origToDense.clear();
  denseToOrig.clear();
  numDenseNodes = 0;
  denseEdges.clear();

  CG_LOG("TIMER per-tu-total [" << M->getModuleIdentifier() << "] "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tTotal).count()
         << " ms\n");
}

// --cfl-census-invoke: MEASUREMENT-ONLY. Tier-1 discovery for the
// INVOKE summary vocabulary (task #28): scan every defined,
// not-yet-summarized function for the registration shapes, then rank
// candidates by constant-Function evidence at their direct callsites —
// the discriminator separating fn-registration APIs from generic
// container stores (opaque pointers make formal types useless).
// Shapes:
//   DIRECT   fptr formal invoked in the body with another formal at
//            call-arg position K  -> INVOKE(argF:fK<-argD) verbatim
//   FIELD    formal stored into a field of another formal (timer/rcu
//            shape: data IS the container; dispatcher supplies K)
//   COSTORE  two formals stored into one local/heap object (kthread
//            create-struct shape; dispatcher elsewhere)
// Adds no edges; emits proposal lines for the proposer/confirmer loop.
void CallGraphPass::runInvokeCensus() {
  struct Cand {
    const Function *F;
    int argF, argD;
    int fk;            // DIRECT only; -1 otherwise
    const char *shape;
    size_t callsites = 0, constFn = 0, nullFn = 0, dynFn = 0;
  };
  std::vector<Cand> cands;
  // (function, argF, argD, shape) dedup across multiple body sites
  std::set<std::tuple<const Function *, int, int, std::string>> seen;
  auto formalIdx = [](const Function &F, const Value *V) -> int {
    V = V->stripPointerCasts();
    for (const auto &A : F.args())
      if (&A == V) return (int)A.getArgNo();
    return -1;
  };
  auto storeBase = [](const Value *P) -> const Value * {
    P = P->stripPointerCasts();
    while (auto *G = dyn_cast<GEPOperator>(P))
      P = G->getPointerOperand()->stripPointerCasts();
    return P;
  };
  size_t nFuncs = 0;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
      if (shouldSkipFunction(&F)) continue;
      if (Ctx->FuncSummaries.count(&F)) continue; // already handled
      if (F.arg_size() < 2) continue;             // need (fn, data)
      nFuncs++;
      // per-object co-store map: base -> formal indices stored into it
      std::map<const Value *, std::set<int>> coStores;
      for (const Instruction &I : instructions(F)) {
        if (const auto *CB = dyn_cast<CallBase>(&I)) {
          if (CB->isInlineAsm()) continue;
          if (const Function *IC = CB->getCalledFunction()) {
            // PASSTHRU: formals forwarded into an already-summarized
            // INVOKE function -> the wrapper inherits the translated
            // atom (composition lift; closes kthread_create_on_cpu /
            // smpboot without hand-seeding)
            auto sit = Ctx->FuncSummaries.find(
                getFuncDef(const_cast<Function *>(IC)));
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(IC);
            if (sit != Ctx->FuncSummaries.end()) {
              for (const auto &A : sit->second->atoms) {
                if (A.kind != GlobalContext::SummaryAtom::Invoke) continue;
                if ((unsigned)A.dst >= CB->arg_size() ||
                    (unsigned)A.src >= CB->arg_size())
                  continue;
                int fIdx = formalIdx(F, CB->getArgOperand(A.dst));
                int dIdx = formalIdx(F, CB->getArgOperand(A.src));
                if (fIdx < 0 || dIdx < 0 || fIdx == dIdx) continue;
                if (seen.insert({&F, fIdx, dIdx, "PASSTHRU"}).second)
                  cands.push_back({&F, fIdx, dIdx, A.aux, "PASSTHRU"});
              }
            }
            continue;
          }
          int fIdx = formalIdx(F, CB->getCalledOperand());
          if (fIdx < 0) continue;
          for (unsigned k = 0; k < CB->arg_size(); k++) {
            int dIdx = formalIdx(F, CB->getArgOperand(k));
            if (dIdx < 0 || dIdx == fIdx) continue;
            if (!containsPointerType(CB->getArgOperand(k)->getType()))
              continue;
            if (seen.insert({&F, fIdx, dIdx, "DIRECT"}).second)
              cands.push_back({&F, fIdx, dIdx, (int)k, "DIRECT"});
          }
        } else if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          int vIdx = formalIdx(F, SI->getValueOperand());
          if (vIdx < 0) continue;
          const Value *base = storeBase(SI->getPointerOperand());
          int bIdx = formalIdx(F, base);
          if (bIdx >= 0 && bIdx != vIdx) {
            if (seen.insert({&F, vIdx, bIdx, "FIELD"}).second)
              cands.push_back({&F, vIdx, bIdx, -1, "FIELD"});
          } else if (isa<AllocaInst>(base) || isa<CallBase>(base) ||
                     isa<GlobalVariable>(base)) {
            coStores[base].insert(vIdx);
          }
        }
      }
      for (auto &[base, idxs] : coStores) {
        if (idxs.size() < 2) continue;
        // report each ordered pair once (fn identity unknown pre-callsite)
        for (int a : idxs)
          for (int b : idxs)
            if (a != b && seen.insert({&F, a, b, "COSTORE"}).second)
              cands.push_back({&F, a, b, -1, "COSTORE"});
      }
    }
  }
  // callsite evidence sweep: constant Function at argF position
  std::map<const Function *, std::vector<Cand *>> byFunc;
  for (auto &c : cands) byFunc[getFuncDef(const_cast<Function *>(c.F))]
                            .push_back(&c);
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.isDeclaration()) continue;
      for (const Instruction &I : instructions(F)) {
        const auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->isInlineAsm()) continue;
        const Function *CF = CB->getCalledFunction();
        if (!CF) continue;
        auto it = byFunc.find(getFuncDef(const_cast<Function *>(CF)));
        if (it == byFunc.end()) continue;
        for (Cand *c : it->second) {
          if ((unsigned)c->argF >= CB->arg_size()) continue;
          c->callsites++;
          const Value *fv = CB->getArgOperand(c->argF)->stripPointerCasts();
          if (isa<Function>(fv)) c->constFn++;
          else if (isa<ConstantPointerNull>(fv)) c->nullFn++;
          else c->dynFn++;
        }
      }
    }
  }
  std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
    return a.constFn != b.constFn ? a.constFn > b.constFn
                                  : a.callsites > b.callsites;
  });
  size_t withEvidence = 0, printed = 0;
  for (const auto &c : cands)
    if (c.constFn > 0) withEvidence++;
  errs() << "InvokeCensus: scanned " << nFuncs << " defined functions, "
         << cands.size() << " shape candidates, " << withEvidence
         << " with constant-Function callsite evidence\n";
  for (const auto &c : cands) {
    if (c.constFn == 0 || printed >= 200) break;
    printed++;
    errs() << "InvokeCensus: " << c.shape << " " << c.F->getName()
           << " fn=arg" << c.argF << " data=arg" << c.argD;
    if (c.fk >= 0) errs() << " f" << c.fk;
    errs() << " callsites=" << c.callsites << " constFn=" << c.constFn
           << " null=" << c.nullFn << " dyn=" << c.dynFn;
    if (c.fk >= 0)
      errs() << "  proposal: " << c.F->getName() << " INVOKE(arg" << c.argF
             << ":f" << c.fk << "<-arg" << c.argD << ")";
    errs() << "\n";
  }
  if (withEvidence > printed)
    errs() << "InvokeCensus: ... +" << (withEvidence - printed)
           << " more with evidence (raise the cap to see them)\n";
}

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  if (CFLConfirmFresh && iteration == 0 && M == Ctx->Modules.front().first)
    confirmFreshWrappers(); // all modules loaded; AllocFuncs seeded

  if (CFLConfirmInvoke && iteration == 0 && M == Ctx->Modules.front().first)
    confirmInvokeSummaries(); // before any callsite wiring

  if (CFLCensusInvoke && iteration == 0 && M == Ctx->Modules.front().first)
    runInvokeCensus(); // all modules + summaries loaded; adds no edges

  if (CFLCensusFields && iteration == 0 && M == Ctx->Modules.front().first)
    runFieldChannelCensus(); // measurement-only, adds no edges

  if (CFLOpsPairs && iteration == 0 && M == Ctx->Modules.front().first)
    certifyOpsPairs(); // pair certificates from IR use evidence

  if (CFLCensusStrata && iteration == 0 && M == Ctx->Modules.front().first)
    runStrataCensus(); // measurement-only, adds no edges

  if ((CFLConfirmSinks || CFLSinkInstr) && iteration == 0 &&
      M == Ctx->Modules.front().first)
    runSinkConfirmer(); // contract gate BEFORE any sealing can happen

  if (CFLCensusPtrToInt && iteration == 0 && M == Ctx->Modules.front().first)
    runPtrToIntCensus(); // measurement-only, adds no edges

  if (CFLCensusTracepoint && iteration == 0 &&
      M == Ctx->Modules.front().first)
    runTracepointCensus(); // measurement-only, adds no edges

  if (CFLTracepointKeys && iteration == 0 &&
      M == Ctx->Modules.front().first)
    bindTracepointMediatorPairs(); // before any callsite is visited

  if (CFLCensusNexus && iteration == 0 && M == Ctx->Modules.front().first)
    runNexusCensus(); // measurement-only, adds no edges

  // process global initializers and functions, only the first iteration
  if (iteration == 0) {
    // Pre-size edge vector on first module to avoid repeated reallocations.
    // Estimate ~4 edges per instruction (each add{Assignment,Dereference}Edges
    // emits 2 edges, and most instructions trigger at least one call).
    if (M == Ctx->Modules.front().first) {
      moduleEdgeRanges.clear();
      size_t totalInsts = 0;
      for (auto &[Mod, _] : Ctx->Modules)
        for (Function &F : *Mod)
          totalInsts += F.getInstructionCount();
      EB.reserve(totalInsts * 4);

      // Run global dedup on first module (all nodes exist from doInitialization).
      // The intra-procedural rules in globalDedupScanFunction are flow-insensitive-safe
      // by construction; cross-call merges in globalDedupScanCallEdges only fire for
      // single-callsite callees and are sound under per-TU solving as well.
      // Per-TU dense mapping below uses getCanonicalNode() so dedup classes are
      // visible to the solver.
      if (CFLGlobalDedup)
        runGlobalDedup();
    }

    // Track per-module edge ranges so repair mode can recompute selected modules.
    const bool perTUMode = CFLCompositional && CompressedGraphInputs.empty();
    const size_t edgeStart = EB.getEdges().size();
    moduleDerefEdgeRoots.clear();
    moduleFieldWildcardRoots.clear();
    moduleConstGEPFieldDone.clear();
    curDL = &M->getDataLayout();

    for (auto &GV : M->globals()) {
      // Skip compiler-introduced globals
      if (shouldSkipValue(&GV)) {
        CG_DEBUG("Skipping initializer for compiler global: " << GV.getName() << "\n");
        continue;
      }

      if (GV.hasInitializer()) {
        NodeIndex valNode = NF.getValueNodeFor(&GV);
        assert(valNode != AndersNodeFactory::InvalidIndex && "Global value node not found!");
        NodeIndex deref = NF.createDereferenceNode(valNode);
        EB.addDereferenceEdges(valNode, deref);
        CG_DEBUG("Processing initializer for GV " << GV.getName() << "\n");
        auto init = GV.getInitializer();
        processInitializer(deref, init, "", -1,
                           EB.hasFieldLabels() ? valNode
                                               : AndersNodeFactory::InvalidIndex);
      }
    }

    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty() ||
          (Ctx->AllocFuncs.count(&F) && !summaryInvokeKeepsBody(Ctx, &F)) ||
          Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      runOnFunction(&F);
    }

    // Build field-store map from IR uses (direct stores + one-level callbacks).
    // In per-TU mode, funcFieldStores was cleared above; in monolithic mode
    // it accumulates across modules.  processInitializer already added
    // global-initializer entries for this module.
    buildFieldStoreMapFromIR(M);

    const size_t edgeEnd = EB.getEdges().size();
    moduleEdgeRanges[M] = {edgeStart, edgeEnd};

    // Per-TU: solve and compress this module's edges (including edge-empty modules
    // so cache coverage metadata can represent the full input set).
    if (perTUMode)
      solveAndCompressPerTU(M, edgeStart, edgeEnd);

    // Linker-array wiring needs every module's section members and asm
    // targets: run once, after the last module's own edges. In per-TU
    // compositional mode these edges are cross-module by nature and
    // fall outside all module ranges — repair mode won't recompute
    // them; monolithic flows-to/saturation consume them normally.
    if (M == Ctx->Modules.back().first) {
      wireLinkerSectionArrays();
      finalizeChainPairs();
    }
  }

  bool Changed = false;
  if (M == Ctx->Modules.back().first) {
    // Analyze edge and cycle patterns before CFL solving
    CG_LOG("Analyzing constraint graph structure...\n");
    std::vector<std::pair<NodeIndex, size_t>> topNodes;
    EB.analyzeHighDegreeNodes(1000, 20, &topNodes);

    // Examine top nodes
    if (!topNodes.empty()) {
      CG_LOG("Examining top " << topNodes.size() << " high-degree nodes:\n");
      for (const auto& [nodeId, degree] : topNodes) {
        NF.dumpNode(nodeId);
      }
    }

    // Pre-solve copy/field merge before the monolithic dense mapping.
    if ((CFLPreSolveMerge || CFLFlowsTo) && !CFLCompositional)
      preSolveCopyFieldMerge(EB.getEdges(), nullptr);

    // ORCFL v0: answer-anchored resolution replaces the saturation solve.
    // Outer fixpoint: re-solve while resolution wires new callee flows
    // (the iterative driver re-enters doModulePass while we return true;
    // iteration >= 1 skips the edge build and goes straight to the solve).
    if (CFLFlowsTo && !CFLCompositional) {
      bool again = runFlowsToResolution();
      iteration++;
      return again;
    }

    // Build dense mapping if global dedup is active.
    // Skip in per-TU mode: per-TU graphs already have their own dense mappings.
    if (CFLGlobalDedup && perTUGraphs.empty())
      buildDenseMapping();

    // In compositional mode, skip the expensive monolithic CFL solve —
    // runCompositionalSolve() will compose per-TU or loaded graphs.
    if (CFLCompositional) {
      CG_LOG("Compositional mode: skipping full CFL solve\n");
      // In per-TU mode, export happens during runCompositionalSolve.
      // In loaded-cflcg mode (perTUGraphs empty), export the monolithic result.
      if (!CompressedGraphOutput.empty() && perTUGraphs.empty())
        exportCompressedGraph(CompressedGraphOutput);
      iteration++;
      return false;
    }

    // solve CFL constraints after processing the last module
    CG_LOG("Using " << cflThreads << " threads for FWGramParallel\n");
    const auto &inputEdges = EB.getEdges();
    const size_t inputEdgeCount = inputEdges.size();
    const auto *Grammar = EB.getGrammar();
    const std::vector<gracfl::Edge> *solverInputEdges = CFLGlobalDedup ? &denseEdges : &inputEdges;
    const size_t solverInputEdgeCount = solverInputEdges->size();

    if (VerboseLevel >= 2 && Grammar) {
      std::vector<size_t> rawLabelCounts(Grammar->getLabelSize(), 0);
      std::unordered_set<EdgeKey, EdgeKeyHash> uniqueInputEdges;
      uniqueInputEdges.reserve(inputEdgeCount + (inputEdgeCount >> 1) + 1);

      for (const auto &E : inputEdges) {
        if (E.label < rawLabelCounts.size())
          rawLabelCounts[E.label]++;
        uniqueInputEdges.insert(EdgeKey{E.from, E.to, E.label});
      }

      const size_t uniqueInputEdgeCount = uniqueInputEdges.size();
      CG_LOG("CFL Input Edges: raw=" << inputEdgeCount
             << ", unique=" << uniqueInputEdgeCount
             << ", duplicates=" << (inputEdgeCount - uniqueInputEdgeCount) << "\n");

      std::vector<std::pair<uint, size_t>> nonZeroLabels;
      nonZeroLabels.reserve(rawLabelCounts.size());
      for (uint L = 0; L < rawLabelCounts.size(); L++) {
        if (rawLabelCounts[L] > 0)
          nonZeroLabels.emplace_back(L, rawLabelCounts[L]);
      }
      std::sort(nonZeroLabels.begin(), nonZeroLabels.end(),
                [](const auto &A, const auto &B) { return A.second > B.second; });

      const auto &idToSymbol = Grammar->getIDToSymbolMap();
      const size_t toReport = std::min<size_t>(8, nonZeroLabels.size());
      CG_LOG("CFL Input Label Distribution (top " << toReport << "/"
             << nonZeroLabels.size() << "):\n");
      for (size_t i = 0; i < toReport; i++) {
        const auto [Label, Count] = nonZeroLabels[i];
        auto It = idToSymbol.find(Label);
        StringRef LabelName = (It != idToSymbol.end()) ? StringRef(It->second) : StringRef("unknown");
        CG_LOG("  " << LabelName << " (" << Label << "): " << Count << "\n");
      }
    }

    bool rebuildSolver = false;
    if (!cflSolver || cflForceRebuild || cflSolvedInputEdgeCount > solverInputEdgeCount) {
      rebuildSolver = true;
    } else {
      // If new edges reference nodes beyond the existing solver graph,
      // rebuild with a resized graph.
      const size_t nodeCount = cflSolver->getNodeCount();
      const size_t beginCheck = cflSolvedInputEdgeCount;
      for (size_t i = beginCheck; i < solverInputEdgeCount; i++) {
        const auto &E = (*solverInputEdges)[i];
        if (E.from >= nodeCount || E.to >= nodeCount) {
          rebuildSolver = true;
          break;
        }
      }
    }

    size_t incrementalAdded = 0;
    if (rebuildSolver) {
      cflSolver = std::make_unique<gracfl::SolverFWGramParallel>(*solverInputEdges, *EB.getGrammar(), cflThreads);
      cflSolvedInputEdgeCount = solverInputEdgeCount;
      cflForceRebuild = false;
      CG_LOG("CFL Mode: full rebuild\n");
    } else if (solverInputEdgeCount > cflSolvedInputEdgeCount) {
      const size_t rawNewEdges = solverInputEdgeCount - cflSolvedInputEdgeCount;
      incrementalAdded = cflSolver->addInputEdges(*solverInputEdges, cflSolvedInputEdgeCount);
      cflSolvedInputEdgeCount = solverInputEdgeCount;
      CG_LOG("CFL Mode: incremental resume with " << incrementalAdded
             << " new frontier edges (" << rawNewEdges
             << " raw additions)\n");
    } else {
      CG_LOG("CFL Mode: reusing cached fixed-point (no new input edges)\n");
    }

    if (rebuildSolver || incrementalAdded > 0) {
      auto initEdges = cflSolver->getEdgeCount();
      CG_LOG("CFL Init Edges: " << initEdges << "\n");
      auto cflStart = std::chrono::steady_clock::now();
      cflSolver->runCFL();
      auto cflEnd = std::chrono::steady_clock::now();
      auto finalEdges = cflSolver->getEdgeCount();
      CG_LOG("CFL Final Edges: " << finalEdges << "\n");
      CG_LOG("TIMER cfl-solve "
             << std::chrono::duration_cast<std::chrono::milliseconds>(cflEnd - cflStart).count()
             << " ms\n");
    }

    const auto &outputCFLGraph = cflSolver->getReachability();

    if (VerboseLevel >= 2 && Grammar && !outputCFLGraph.empty()) {
      std::vector<unsigned long long> finalLabelCounts(outputCFLGraph[0].size(), 0);
      for (const auto &PerNode : outputCFLGraph) {
        for (size_t L = 0; L < PerNode.size(); L++)
          finalLabelCounts[L] += static_cast<unsigned long long>(PerNode[L].size());
      }

      std::vector<std::pair<uint, unsigned long long>> nonZeroLabels;
      nonZeroLabels.reserve(finalLabelCounts.size());
      for (uint L = 0; L < finalLabelCounts.size(); L++) {
        if (finalLabelCounts[L] > 0)
          nonZeroLabels.emplace_back(L, finalLabelCounts[L]);
      }
      std::sort(nonZeroLabels.begin(), nonZeroLabels.end(),
                [](const auto &A, const auto &B) { return A.second > B.second; });

      const auto &idToSymbol = Grammar->getIDToSymbolMap();
      const size_t toReport = std::min<size_t>(10, nonZeroLabels.size());
      CG_LOG("CFL Final Label Distribution (top " << toReport << "/"
             << nonZeroLabels.size() << "):\n");
      for (size_t i = 0; i < toReport; i++) {
        const auto [Label, Count] = nonZeroLabels[i];
        auto It = idToSymbol.find(Label);
        StringRef LabelName = (It != idToSymbol.end()) ? StringRef(It->second) : StringRef("unknown");
        CG_LOG("  " << LabelName << " (" << Label << "): " << Count << "\n");
      }

      if (EB.getLabelV() < finalLabelCounts.size()) {
        CG_LOG("CFL Final V edges: " << finalLabelCounts[EB.getLabelV()] << "\n");
      }
      if (EB.getLabelM() < finalLabelCounts.size()) {
        CG_LOG("CFL Final M edges: " << finalLabelCounts[EB.getLabelM()] << "\n");
      }
    }

    // R1/ORCFL hypothesis metric: alias-shaped scaffolding (V facts) vs
    // answer-shaped facts (function flows-to pairs actually consumable by
    // the callgraph client).
    if (VerboseLevel >= 2 && !outputCFLGraph.empty() &&
        EB.getLabelV() < outputCFLGraph[0].size()) {
      std::vector<bool> funcDense(outputCFLGraph.size(), false);
      for (uint32_t n = 0; n < outputCFLGraph.size(); n++) {
        NodeIndex orig = (CFLGlobalDedup && n < denseToOrig.size()) ? denseToOrig[n] : n;
        const Value *FV = NF.getValueForNode(orig);
        if (FV && isa<Function>(FV))
          funcDense[n] = true;
      }
      uint64_t vFacts = 0, ftFacts = 0;
      for (uint32_t n = 0; n < outputCFLGraph.size(); n++) {
        const auto &VS = outputCFLGraph[n][EB.getLabelV()];
        vFacts += VS.size();
        for (uint32_t mm : VS)
          if (mm < funcDense.size() && funcDense[mm])
            ftFacts++;
      }
      CG_LOG("ORCFL metric: V facts " << vFacts
             << ", function-flows-to facts " << ftFacts
             << ", scaffolding ratio "
             << (ftFacts ? (double)vFacts / (double)ftFacts : 0.0) << "\n");
    }

    // handle custom allocators
    const bool allocatorRewritten = findCustomAllocators(outputCFLGraph);
    if (allocatorRewritten) {
      // custom allocator discovery may rewrite/remove call edges;
      // trigger a full rebuild on the next iteration.
      cflForceRebuild = true;
      cflSolvedInputEdgeCount = 0;
    }
    Changed |= allocatorRewritten;

    // parse results and update call edges
    Changed |= handleIndirectCall(outputCFLGraph, Ctx->IndirectCallInsts);

    // Export compressed graph if requested
    if (!CompressedGraphOutput.empty())
      exportCompressedGraph(CompressedGraphOutput);

    iteration++;
  }

  return Changed;
}

// debug
void CallGraphPass::dumpFuncPtrs(raw_ostream &OS) {
  for (FuncPtrMap::iterator i = Ctx->FuncPtrs.begin(),
       e = Ctx->FuncPtrs.end(); i != e; ++i) {
    if (i->second.empty())
      continue;
    OS << i->first << "\n";
    FuncSet &v = i->second;
    for (FuncSet::iterator j = v.begin(), ej = v.end();
         j != ej; ++j) {
      OS << "  " << ((*j)->hasInternalLinkage() ? "f" : "F")
         << " " << (*j)->getName().str() << "\n";
    }
  }
}

// ---- JSON call graph export helpers ----

// Extract source file path from debug info for a function.
// Iterates instructions to find DILocation, falls back to module source filename.
static std::string getFuncSourceFile(const Function *F) {
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (DILocation *Loc = I.getDebugLoc()) {
        StringRef Dir = Loc->getDirectory();
        StringRef File = Loc->getFilename();
        if (File.empty()) {
          if (DILocation *IL = Loc->getInlinedAt()) {
            Dir = IL->getDirectory();
            File = IL->getFilename();
          }
        }
        if (!File.empty()) {
          if (sys::path::is_absolute(File))
            return File.str();
          SmallString<256> FullPath;
          if (!Dir.empty())
            FullPath = Dir;
          sys::path::append(FullPath, File);
          sys::path::remove_dots(FullPath, true);
          return std::string(FullPath);
        }
      }
    }
  }
  // Fallback to module source filename
  return F->getParent()->getSourceFileName();
}

// Return a function ID: bare name for external linkage, "file:name" for internal.
static std::string getFuncId(const Function *F) {
  // For intrinsics, use the base name without type suffixes
  // e.g., "llvm.memcpy.p0.p0.i64" -> "llvm.memcpy"
  if (F->isIntrinsic())
    return Intrinsic::getBaseName(F->getIntrinsicID()).str();
  if (F->hasExternalLinkage())
    return F->getName().str();
  return getFuncSourceFile(F) + ":" + F->getName().str();
}

// Extract source line from a CallBase's debug location.
// Returns 0 if no debug info available.
static unsigned getCallLine(const CallBase *CI) {
  if (DILocation *Loc = CI->getDebugLoc()) {
    unsigned L = Loc->getLine();
    if (L == 0) {
      if (DILocation *IL = Loc->getInlinedAt())
        L = IL->getLine();
    }
    return L;
  }
  return 0;
}

// Get the min/max line range of a function from debug info.
static std::pair<unsigned, unsigned> getFuncLineRange(const Function *F) {
  unsigned minLine = UINT_MAX, maxLine = 0;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (DILocation *Loc = I.getDebugLoc()) {
        unsigned L = Loc->getLine();
        if (L > 0) {
          if (L < minLine) minLine = L;
          if (L > maxLine) maxLine = L;
        }
      }
    }
  }
  if (minLine == UINT_MAX)
    minLine = 0;
  return {minLine, maxLine};
}

void CallGraphPass::dumpCallGraphJSON(StringRef Path) {
  std::error_code EC;
  raw_fd_ostream OS(Path, EC);
  if (EC) {
    WARNING("Failed to open call graph JSON file for writing: " << Path
            << ": " << EC.message() << "\n");
    return;
  }

  // Collect all functions that appear in Callees or Callers.
  // Group by getFuncId to merge multiple Function* for the same symbol
  // (e.g., external declarations appear in each module).
  DenseSet<const Function *> AllFuncs;
  for (auto &[CS, FS] : Ctx->Callees) {
    const Function *Caller = CS->getFunction();
    if (Caller && !Caller->isDeclaration() && !Caller->isIntrinsic())
      AllFuncs.insert(Caller);
    for (const Function *F : FS) {
      if (F && !(F->isIntrinsic() && !isImportantIntrinsic(F)))
        AllFuncs.insert(F);
    }
  }
  for (auto &[F, CIS] : Ctx->Callers) {
    if (F && !(F->isIntrinsic() && !isImportantIntrinsic(F)))
      AllFuncs.insert(F);
  }

  // Build merged Callers map keyed by getFuncId string, since external
  // declarations have separate Function* per module.
  StringMap<CallInstSet> MergedCallers;
  for (auto &[F, CIS] : Ctx->Callers) {
    if (!F || (F->isIntrinsic() && !isImportantIntrinsic(F)))
      continue;
    auto &merged = MergedCallers[getFuncId(F)];
    merged.insert(CIS.begin(), CIS.end());
  }

  json::Object Functions;
  size_t totalEdges = 0, directEdges = 0, indirectEdges = 0;

  for (const Function *F : AllFuncs) {
    if (F->isIntrinsic() && !isImportantIntrinsic(F))
      continue;

    std::string FuncID = getFuncId(F);
    // Skip if already emitted (multiple Function* for the same symbol).
    if (Functions.find(FuncID) != Functions.end())
      continue;

    std::string SrcFile = getFuncSourceFile(F);
    auto [LineStart, LineEnd] = getFuncLineRange(F);

    json::Object FuncObj;
    FuncObj["file"] = SrcFile;
    if (LineStart > 0)
      FuncObj["line_start"] = static_cast<int64_t>(LineStart);
    if (LineEnd > 0)
      FuncObj["line_end"] = static_cast<int64_t>(LineEnd);
    FuncObj["linkage"] = F->hasExternalLinkage() ? "external" : "internal";

    // Build callees array by iterating call instructions in this function
    json::Array CalleesArr;
    if (!F->isDeclaration()) {
      for (auto &BB : *F) {
        for (auto &I : BB) {
          const CallBase *CI = dyn_cast<CallBase>(&I);
          if (!CI || CI->isInlineAsm())
            continue;

          auto it = Ctx->Callees.find(CI);
          if (it == Ctx->Callees.end())
            continue;

          bool isDirect = (CI->getCalledFunction() != nullptr);
          unsigned line = getCallLine(CI);

          for (const Function *Callee : it->second) {
            if (Callee->isIntrinsic() && !isImportantIntrinsic(Callee))
              continue;
            json::Object Edge;
            Edge["callee"] = getFuncId(Callee);
            Edge["call_type"] = isDirect ? "direct" : "indirect";
            if (line > 0)
              Edge["line"] = static_cast<int64_t>(line);
            CalleesArr.push_back(std::move(Edge));
            totalEdges++;
            if (isDirect) directEdges++;
            else indirectEdges++;
          }
        }
      }
    }
    FuncObj["callees"] = std::move(CalleesArr);

    // Build callers array from merged callers map
    json::Array CallersArr;
    auto callerIt = MergedCallers.find(FuncID);
    if (callerIt != MergedCallers.end()) {
      for (const CallBase *CI : callerIt->second) {
        const Function *CallerF = CI->getFunction();
        if (!CallerF || (CallerF->isIntrinsic() && !isImportantIntrinsic(CallerF)))
          continue;
        bool isDirect = (CI->getCalledFunction() != nullptr);
        unsigned line = getCallLine(CI);

        json::Object Edge;
        Edge["caller"] = getFuncId(CallerF);
        Edge["call_type"] = isDirect ? "direct" : "indirect";
        if (line > 0)
          Edge["line"] = static_cast<int64_t>(line);
        CallersArr.push_back(std::move(Edge));
      }
    }
    FuncObj["callers"] = std::move(CallersArr);

    Functions[FuncID] = std::move(FuncObj);
  }

  json::Object Metadata;
  Metadata["version"] = 1;
  Metadata["total_functions"] = static_cast<int64_t>(Functions.size());
  Metadata["total_call_edges"] = static_cast<int64_t>(totalEdges);
  Metadata["total_direct_calls"] = static_cast<int64_t>(directEdges);
  Metadata["total_indirect_calls"] = static_cast<int64_t>(indirectEdges);
  Metadata["soundness_capped"] = soundnessCapped;

  json::Object Root;
  Root["metadata"] = std::move(Metadata);
  Root["functions"] = std::move(Functions);

  OS << json::Value(std::move(Root)) << "\n";
  CG_LOG("Exported call graph JSON to " << Path << ": "
         << AllFuncs.size() << " functions, "
         << totalEdges << " edges ("
         << directEdges << " direct, "
         << indirectEdges << " indirect)\n");
}

void CallGraphPass::dumpVSnapshot(StringRef Path) {
  if (CFLCompositional) {
    dumpComposedVSnapshot(Path);
    return;
  }

  assert(cflSolver && "dumpVSnapshot called without a solved CFL graph");
  const cfl_result_t *GraphPtr = &cflSolver->getReachability();
  if (!GraphPtr || GraphPtr->empty()) {
    WARNING("VSnapshot: empty CFL graph, skip export to " << Path << "\n");
    return;
  }

  const auto &Graph = *GraphPtr;
  const uint32_t LabelV = EB.getLabelV();
  if (Graph[0].size() <= LabelV) {
    WARNING("VSnapshot: V label index " << LabelV << " is out of range\n");
    return;
  }

  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  const uint32_t NodeCount = NF.getNumNodes();

  if (!useDense && Graph.size() < NodeCount) {
    WARNING("VSnapshot: CFL graph node count " << Graph.size()
            << " is smaller than NodeFactory node count " << NodeCount << "\n");
    return;
  }

  std::unordered_map<NodeIndex, uint32_t> RootToDense;
  RootToDense.reserve(NodeCount);
  std::vector<uint32_t> NodeToRepDense(NodeCount, 0);
  std::vector<uint32_t> RepToNode;
  RepToNode.reserve(NodeCount);
  std::vector<std::vector<uint32_t>> MembersByRep;
  MembersByRep.reserve(NodeCount);
  for (uint32_t N = 0; N < NodeCount; N++) {
    NodeIndex Root = getCanonicalNode(N);
    auto It = RootToDense.find(Root);
    uint32_t Dense = 0;
    if (It == RootToDense.end()) {
      Dense = static_cast<uint32_t>(RepToNode.size());
      RootToDense.emplace(Root, Dense);
      RepToNode.push_back(Root);
      MembersByRep.emplace_back();
    } else {
      Dense = It->second;
    }
    NodeToRepDense[N] = Dense;
    MembersByRep[Dense].push_back(N);
  }
  const uint32_t RepCount = static_cast<uint32_t>(RepToNode.size());

  std::vector<VSnapshotNamedEntry> NamedEntries;
  NamedEntries.reserve(NodeCount / 8 + 32);
  for (uint32_t N = 0; N < NodeCount; N++) {
    const Value *V = NF.getValueForNode(N);
    if (!V)
      continue;

    VSnapshotNamedEntry E;
    E.node = N;

    if (NF.isReturnNode(N)) {
      const Function *F = dyn_cast<Function>(V);
      if (!F)
        continue;
      E.kind = 6; // return node
      E.name = ("ret:" + F->getName()).str();
      NamedEntries.push_back(std::move(E));
      continue;
    }
    if (NF.isVarargNode(N)) {
      const Function *F = dyn_cast<Function>(V);
      if (!F)
        continue;
      E.kind = 7; // vararg node
      E.name = ("vararg:" + F->getName()).str();
      NamedEntries.push_back(std::move(E));
      continue;
    }

    if (const Function *F = dyn_cast<Function>(V)) {
      E.kind = 1;
      E.name = F->getName().str();
    } else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(V)) {
      E.kind = 2;
      E.name = GV->getName().str();
    } else if (const Argument *A = dyn_cast<Argument>(V)) {
      E.kind = 3;
      const Function *F = A->getParent();
      std::string FName = F ? F->getName().str() : std::string("<unknown>");
      if (A->hasName())
        E.name = FName + "::arg:" + A->getName().str();
      else
        E.name = FName + "::arg#" + std::to_string(A->getArgNo());
    } else if (const Instruction *I = dyn_cast<Instruction>(V)) {
      if (!I->hasName())
        continue;
      E.kind = 4;
      const Function *F = I->getFunction();
      std::string FName = F ? F->getName().str() : std::string("<unknown>");
      E.name = FName + "::%" + I->getName().str();
    } else if (V->hasName()) {
      E.kind = 5;
      E.name = V->getName().str();
    } else {
      continue;
    }

    if (!E.name.empty())
      NamedEntries.push_back(std::move(E));
  }

  std::sort(NamedEntries.begin(), NamedEntries.end(),
            [](const VSnapshotNamedEntry &A, const VSnapshotNamedEntry &B) {
              if (A.name != B.name)
                return A.name < B.name;
              if (A.kind != B.kind)
                return A.kind < B.kind;
              return A.node < B.node;
            });

  json::Object MetaObj;
  MetaObj["tool"] = "kanalyzer";
  MetaObj["snapshot_type"] = "V-relation";
  MetaObj["version"] = static_cast<int64_t>(VSnapshotData::kVersion);
  MetaObj["label_v"] = static_cast<int64_t>(LabelV);
  MetaObj["global_dedup"] = static_cast<bool>(CFLGlobalDedup);
  MetaObj["local_alloca_summary"] = static_cast<bool>(CFLLocalAllocaSummary);
  MetaObj["node_count"] = static_cast<int64_t>(NodeCount);
  MetaObj["rep_count"] = static_cast<int64_t>(RepCount);

  VSnapshotData Data;
  Data.labelV = LabelV;
  Data.flags = 0;
  Data.metadataJson = formatv("{0}", json::Value(std::move(MetaObj))).str();
  Data.nodeToRep = std::move(NodeToRepDense);
  Data.repToNode = std::move(RepToNode);
  Data.namedEntries = std::move(NamedEntries);

  std::string ErrMsg;
  uint64_t EdgeCount = 0;
  auto RowProvider = [&](uint32_t Rep, std::vector<uint32_t> &RowOut) {
    std::unordered_set<uint32_t> Dsts;
    for (uint32_t Member : MembersByRep[Rep]) {
      if (useDense) {
        uint32_t denseIdx = (Member < origToDense.size()) ? origToDense[Member] : UINT32_MAX;
        if (denseIdx == UINT32_MAX || denseIdx >= Graph.size())
          continue;
        const auto &VSet = Graph[denseIdx][LabelV];
        Dsts.reserve(Dsts.size() + VSet.size());
        for (NodeIndex D : VSet) {
          if (D >= denseToOrig.size()) continue;
          NodeIndex origD = denseToOrig[D];
          if (origD >= NodeCount) continue;
          Dsts.insert(Data.nodeToRep[origD]);
        }
      } else {
        assert(Member < Graph.size() && "member node out of CFL graph range");
        const auto &VSet = Graph[Member][LabelV];
        Dsts.reserve(Dsts.size() + VSet.size());
        for (NodeIndex D : VSet) {
          if (D >= NodeCount)
            continue;
          Dsts.insert(Data.nodeToRep[D]);
        }
      }
    }
    RowOut.assign(Dsts.begin(), Dsts.end());
    EdgeCount += RowOut.size();
  };

  if (!saveVSnapshotWithRowProvider(Path, Data, RowProvider, &ErrMsg)) {
    WARNING("VSnapshot: failed to export " << Path << ": " << ErrMsg << "\n");
    return;
  }
  CG_LOG("Exported V snapshot to " << Path
         << ": nodes=" << Data.nodeToRep.size()
         << ", reps=" << Data.repToNode.size()
         << ", V-edges=" << EdgeCount
         << ", names=" << Data.namedEntries.size() << "\n");
}

void CallGraphPass::dumpComposedVSnapshot(StringRef Path) {
  if (!composedSolver || composedSymbolToDense.empty()) {
    WARNING("VSnapshot: no composed solver result, skip export to " << Path << "\n");
    return;
  }

  const auto &Graph = composedSolver->getReachability();
  const uint32_t LabelV = EB.getLabelV();
  if (Graph.empty() || Graph[0].size() <= LabelV) {
    WARNING("VSnapshot: empty or invalid composed graph\n");
    return;
  }

  // In the composed graph, each dense ID is already a V-SCC representative.
  // nodeToRep and repToNode are both identity mappings.
  const uint32_t NumDense = composedNumDense;
  std::vector<uint32_t> NodeToRep(NumDense);
  std::vector<uint32_t> RepToNode(NumDense);
  std::iota(NodeToRep.begin(), NodeToRep.end(), 0);
  std::iota(RepToNode.begin(), RepToNode.end(), 0);

  // Build GUID → Function*/GlobalVariable* reverse maps for name lookup
  std::unordered_map<uint64_t, const Function *> guidToFunc;
  for (const auto &[guid, F] : Ctx->Funcs)
    if (F) guidToFunc[guid] = F;
  for (const auto &[guid, F] : Ctx->ExtFuncs)
    if (F) guidToFunc.emplace(guid, F);  // don't overwrite definitions

  std::unordered_map<uint64_t, const GlobalVariable *> guidToGV;
  for (const auto &[guid, GV] : Ctx->Gobjs)
    if (GV) guidToGV[guid] = GV;
  for (const auto &[guid, GV] : Ctx->ExtGobjs)
    if (GV) guidToGV.emplace(guid, GV);

  // Build named entries from boundary symbols
  std::vector<VSnapshotNamedEntry> NamedEntries;
  NamedEntries.reserve(composedSymbolToDense.size());

  for (const auto &[symbol, denseId] : composedSymbolToDense) {
    if (denseId >= NumDense)
      continue;

    VSnapshotNamedEntry E;
    E.node = denseId;

    if (symbol.compare(0, 5, "func:") == 0) {
      uint64_t guid = std::stoull(symbol.substr(5));
      auto it = guidToFunc.find(guid);
      if (it == guidToFunc.end()) continue;
      E.kind = 1;
      E.name = it->second->getName().str();
    } else if (symbol.compare(0, 4, "arg:") == 0) {
      // Format: "arg:GUID:N"
      size_t colon1 = 4;
      size_t colon2 = symbol.find(':', colon1);
      if (colon2 == std::string::npos) continue;
      uint64_t guid = std::stoull(symbol.substr(colon1, colon2 - colon1));
      unsigned argNo = std::stoul(symbol.substr(colon2 + 1));
      auto it = guidToFunc.find(guid);
      if (it == guidToFunc.end()) continue;
      E.kind = 3;
      E.name = it->second->getName().str() + "::arg#" + std::to_string(argNo);
    } else if (symbol.compare(0, 4, "ret:") == 0) {
      uint64_t guid = std::stoull(symbol.substr(4));
      auto it = guidToFunc.find(guid);
      if (it == guidToFunc.end()) continue;
      E.kind = 6;
      E.name = "ret:" + it->second->getName().str();
    } else if (symbol.compare(0, 7, "vararg:") == 0) {
      uint64_t guid = std::stoull(symbol.substr(7));
      auto it = guidToFunc.find(guid);
      if (it == guidToFunc.end()) continue;
      E.kind = 7;
      E.name = "vararg:" + it->second->getName().str();
    } else if (symbol.compare(0, 5, "glob:") == 0) {
      uint64_t guid = std::stoull(symbol.substr(5));
      auto it = guidToGV.find(guid);
      if (it == guidToGV.end()) continue;
      E.kind = 2;
      E.name = it->second->getName().str();
    } else {
      // Skip icall: and unknown symbols
      continue;
    }

    if (!E.name.empty())
      NamedEntries.push_back(std::move(E));
  }

  std::sort(NamedEntries.begin(), NamedEntries.end(),
            [](const VSnapshotNamedEntry &A, const VSnapshotNamedEntry &B) {
              if (A.name != B.name) return A.name < B.name;
              if (A.kind != B.kind) return A.kind < B.kind;
              return A.node < B.node;
            });

  json::Object MetaObj;
  MetaObj["tool"] = "kanalyzer";
  MetaObj["snapshot_type"] = "V-relation";
  MetaObj["version"] = static_cast<int64_t>(VSnapshotData::kVersion);
  MetaObj["label_v"] = static_cast<int64_t>(LabelV);
  MetaObj["compositional"] = true;
  MetaObj["node_count"] = static_cast<int64_t>(NumDense);
  MetaObj["rep_count"] = static_cast<int64_t>(NumDense);

  VSnapshotData Data;
  Data.labelV = LabelV;
  Data.flags = 0;
  Data.metadataJson = formatv("{0}", json::Value(std::move(MetaObj))).str();
  Data.nodeToRep = std::move(NodeToRep);
  Data.repToNode = std::move(RepToNode);
  Data.namedEntries = std::move(NamedEntries);

  std::string ErrMsg;
  uint64_t EdgeCount = 0;
  auto RowProvider = [&](uint32_t Rep, std::vector<uint32_t> &RowOut) {
    if (Rep >= Graph.size()) return;
    const auto &VSet = Graph[Rep][LabelV];
    RowOut.assign(VSet.begin(), VSet.end());
    std::sort(RowOut.begin(), RowOut.end());
    EdgeCount += RowOut.size();
  };

  if (!saveVSnapshotWithRowProvider(Path, Data, RowProvider, &ErrMsg)) {
    WARNING("VSnapshot: failed to export composed snapshot " << Path
            << ": " << ErrMsg << "\n");
    return;
  }
  CG_LOG("Exported composed V snapshot to " << Path
         << ": dense_nodes=" << NumDense
         << ", V-edges=" << EdgeCount
         << ", names=" << Data.namedEntries.size() << "\n");
}

void CallGraphPass::computeVSCC(const cfl_result_t &outputCFLGraph,
                                unsigned labelV,
                                std::vector<uint32_t> &nodeToSCC,
                                uint32_t &numSCCs) {
  const uint32_t N = static_cast<uint32_t>(outputCFLGraph.size());
  nodeToSCC.assign(N, UINT32_MAX);
  numSCCs = 0;

  if (N == 0 || outputCFLGraph[0].size() <= labelV)
    return;

  // Iterative Tarjan's SCC on V-reachability adjacency
  std::vector<uint32_t> sccIndex(N, UINT32_MAX);
  std::vector<uint32_t> sccLowlink(N, UINT32_MAX);
  std::vector<bool> onStack(N, false);
  std::vector<uint32_t> sccStack;
  uint32_t index = 0;

  // Frame for iterative DFS
  struct Frame {
    uint32_t node;
    // Iterator state: we iterate over V-reachable neighbors
    std::vector<uint32_t> neighbors;
    size_t neighborIdx;
  };

  std::vector<Frame> dfsStack;

  for (uint32_t startNode = 0; startNode < N; startNode++) {
    if (sccIndex[startNode] != UINT32_MAX)
      continue;

    // Push start node
    dfsStack.push_back(Frame{startNode, {}, 0});
    {
      auto &f = dfsStack.back();
      sccIndex[startNode] = sccLowlink[startNode] = index++;
      onStack[startNode] = true;
      sccStack.push_back(startNode);
      // Collect V-reachable neighbors
      const auto &VSet = outputCFLGraph[startNode][labelV];
      f.neighbors.reserve(VSet.size());
      for (uint32_t w : VSet) {
        if (w < N)
          f.neighbors.push_back(w);
      }
    }

    while (!dfsStack.empty()) {
      auto &frame = dfsStack.back();
      bool pushed = false;

      while (frame.neighborIdx < frame.neighbors.size()) {
        uint32_t w = frame.neighbors[frame.neighborIdx];
        frame.neighborIdx++;

        if (sccIndex[w] == UINT32_MAX) {
          // Not yet visited: push onto DFS stack
          sccIndex[w] = sccLowlink[w] = index++;
          onStack[w] = true;
          sccStack.push_back(w);

          Frame newFrame;
          newFrame.node = w;
          newFrame.neighborIdx = 0;
          const auto &WSet = outputCFLGraph[w][labelV];
          newFrame.neighbors.reserve(WSet.size());
          for (uint32_t x : WSet) {
            if (x < N)
              newFrame.neighbors.push_back(x);
          }
          dfsStack.push_back(std::move(newFrame));
          pushed = true;
          break;
        } else if (onStack[w]) {
          sccLowlink[frame.node] = std::min(sccLowlink[frame.node], sccIndex[w]);
        }
      }

      if (pushed)
        continue;

      // All neighbors processed
      uint32_t v = frame.node;
      if (sccLowlink[v] == sccIndex[v]) {
        // Root of SCC
        uint32_t sccId = numSCCs++;
        uint32_t w;
        do {
          w = sccStack.back();
          sccStack.pop_back();
          onStack[w] = false;
          nodeToSCC[w] = sccId;
        } while (w != v);
      }

      dfsStack.pop_back();

      // Update parent lowlink
      if (!dfsStack.empty()) {
        auto &parent = dfsStack.back();
        sccLowlink[parent.node] = std::min(sccLowlink[parent.node], sccLowlink[v]);
      }
    }
  }

  CG_LOG("V-SCC computation: " << N << " nodes -> " << numSCCs << " SCCs\n");
}

void CallGraphPass::compressConstraintGraph(
    const cfl_result_t &outputCFLGraph,
    const std::vector<uint32_t> &nodeToSCC,
    uint32_t numSCCs,
    CompressedGraphData &out) {
  out = CompressedGraphData();
  out.numNodes = numSCCs;

  const bool useDense = CFLGlobalDedup && !origToDense.empty();

  // Helper: map an original NF node to its SCC ID
  auto origNodeToSCC = [&](NodeIndex origNode) -> uint32_t {
    NodeIndex canon = getCanonicalNode(origNode);
    uint32_t graphNode;
    if (useDense) {
      if (canon >= origToDense.size()) return UINT32_MAX;
      graphNode = origToDense[canon];
    } else {
      graphNode = canon;
    }
    if (graphNode == UINT32_MAX || graphNode >= nodeToSCC.size())
      return UINT32_MAX;
    return nodeToSCC[graphNode];
  };

  // Step 1: Remap edges through SCC and deduplicate
  const auto &rawEdges = useDense ? denseEdges : EB.getEdges();
  std::unordered_set<EdgeKey, EdgeKeyHash> edgeSeen;
  edgeSeen.reserve(rawEdges.size());
  out.edges.reserve(rawEdges.size() / 2);

  // Field-label self-loops must be preserved through SCC collapse: like the
  // a/-a/d/-d self-loops re-added in step 1.5, intra-SCC f-edges are needed
  // for Fld derivations that cross the SCC after composition.
  std::vector<bool> fieldLblMask;
  if (EB.hasFieldLabels()) {
    uint32_t maxL = std::max(EB.getLabelFieldAny(), EB.getLabelFieldAnyInv());
    for (unsigned b = 0; b < EB.getNumFieldBuckets(); b++)
      maxL = std::max({maxL, EB.getLabelField(b), EB.getLabelFieldInv(b)});
    fieldLblMask.assign(maxL + 1, false);
    fieldLblMask[EB.getLabelFieldAny()] = true;
    fieldLblMask[EB.getLabelFieldAnyInv()] = true;
    for (unsigned b = 0; b < EB.getNumFieldBuckets(); b++) {
      fieldLblMask[EB.getLabelField(b)] = true;
      fieldLblMask[EB.getLabelFieldInv(b)] = true;
    }
  }
  auto isFieldLbl = [&](uint32_t lbl) {
    return lbl < fieldLblMask.size() && fieldLblMask[lbl];
  };

  for (const auto &E : rawEdges) {
    uint32_t sccFrom = (E.from < nodeToSCC.size()) ? nodeToSCC[E.from] : UINT32_MAX;
    uint32_t sccTo = (E.to < nodeToSCC.size()) ? nodeToSCC[E.to] : UINT32_MAX;
    if (sccFrom == UINT32_MAX || sccTo == UINT32_MAX)
      continue;
    if (sccFrom == sccTo && !isFieldLbl(E.label) &&
        E.from != E.to)
      continue; // drop SCC-collapsed self-loops (step 1.5 re-adds terminals),
                // but keep pre-existing self-loops (fx loops, merged classes)
    EdgeKey key{sccFrom, sccTo, E.label};
    if (edgeSeen.insert(key).second)
      out.edges.emplace_back(sccFrom, sccTo, E.label);
  }

  // Step 1.5: Add self-loop edges for multi-node V-SCCs.
  // V-SCC compression collapses all intra-SCC edges (a/-a AND d/-d) into
  // self-loops that are dropped.  The composed CFL solver needs:
  //   - self-loop a/-a for MA/AM derivation: MA(x, scc) = M(x, scc) -a(scc, scc)
  //   - self-loop d/-d for M derivation:     M(x, scc) = -d(x, scc) V(scc, scc) d(scc, scc)
  // Without these, V-reachability through memory-alias chains is blocked.
  {
    const uint32_t labels[] = {
      EB.getLabelAssign(), EB.getLabelAssignInv(),
      EB.getLabelDeref(), EB.getLabelDerefInv()
    };
    // Count nodes per SCC to find multi-node SCCs
    std::vector<uint32_t> sccSize(numSCCs, 0);
    for (uint32_t n = 0; n < nodeToSCC.size(); n++)
      if (nodeToSCC[n] < numSCCs) sccSize[nodeToSCC[n]]++;
    uint32_t selfLoopsAdded = 0;
    for (uint32_t scc = 0; scc < numSCCs; scc++) {
      if (sccSize[scc] < 2) continue;
      for (uint32_t lbl : labels)
        out.edges.emplace_back(scc, scc, lbl);
      selfLoopsAdded++;
    }
    CG_LOG("Step 1.5: added self-loops (a/-a/d/-d) for "
           << selfLoopsAdded << " multi-node SCCs\n");
  }

  // Step 2: Build symbol table from boundary nodes
  // Functions (including local-linkage definitions)
  for (const auto &[guid, F] : Ctx->Funcs) {
    if (!F)
      continue;
    std::string guidStr = std::to_string(guid);

    // Function value node
    NodeIndex valNode = NF.getValueNodeFor(F);
    if (valNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(valNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{"func:" + guidStr}] = scc;
    }

    // Arg nodes
    for (const auto &Arg : F->args()) {
      NodeIndex argNode = NF.getValueNodeFor(&Arg);
      if (argNode != AndersNodeFactory::InvalidIndex) {
        uint32_t scc = origNodeToSCC(argNode);
        if (scc != UINT32_MAX)
          out.symbolTable[BoundarySymbol{
            "arg:" + guidStr + ":" + std::to_string(Arg.getArgNo())}] = scc;
      }
    }

    // Return node
    NodeIndex retNode = NF.getReturnNodeFor(F);
    if (retNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(retNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{"ret:" + guidStr}] = scc;
    }

    // Vararg node
    NodeIndex vaNode = NF.getVarargNodeFor(F);
    if (vaNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(vaNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{"vararg:" + guidStr}] = scc;
    }
  }

  // External function references (declared but not defined in this TU set).
  // These are needed for compositional analysis to connect cross-TU calls.
  for (const auto &[guid, F] : Ctx->ExtFuncs) {
    if (!F)
      continue;
    std::string guidStr = std::to_string(guid);

    NodeIndex valNode = NF.getValueNodeFor(F);
    if (valNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(valNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{"func:" + guidStr}] = scc;
    }

    for (const auto &Arg : F->args()) {
      NodeIndex argNode = NF.getValueNodeFor(&Arg);
      if (argNode != AndersNodeFactory::InvalidIndex) {
        uint32_t scc = origNodeToSCC(argNode);
        if (scc != UINT32_MAX)
          out.symbolTable[BoundarySymbol{
            "arg:" + guidStr + ":" + std::to_string(Arg.getArgNo())}] = scc;
      }
    }

    NodeIndex retNode = NF.getReturnNodeFor(F);
    if (retNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(retNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{"ret:" + guidStr}] = scc;
    }

    NodeIndex vaNode = NF.getVarargNodeFor(F);
    if (vaNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(vaNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{"vararg:" + guidStr}] = scc;
    }
  }

  // Local-linkage function return symbols (for compositional icall-ret summary).
  size_t localRetAdded = 0;
  size_t localArgAdded = 0;
  size_t localVarargAdded = 0;
  for (const Function *F : Ctx->AddressTakenFuncs) {
    if (!F || !F->hasLocalLinkage())
      continue;
    std::string scope = getScopeName(F);

    NodeIndex retNode = NF.getReturnNodeFor(F);
    if (retNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(retNode);
      if (scc != UINT32_MAX) {
        out.symbolTable[BoundarySymbol{"lret:" + scope}] = scc;
        localRetAdded++;
      }
    }

    for (const auto &Arg : F->args()) {
      NodeIndex argNode = NF.getValueNodeFor(&Arg);
      if (argNode == AndersNodeFactory::InvalidIndex)
        continue;
      uint32_t argScc = origNodeToSCC(argNode);
      if (argScc == UINT32_MAX)
        continue;
      out.symbolTable[BoundarySymbol{
          "larg:" + scope + ":" + std::to_string(Arg.getArgNo())}] = argScc;
      localArgAdded++;
    }

    NodeIndex vaNode = NF.getVarargNodeFor(F);
    if (vaNode != AndersNodeFactory::InvalidIndex) {
      uint32_t vaScc = origNodeToSCC(vaNode);
      if (vaScc != UINT32_MAX) {
        out.symbolTable[BoundarySymbol{"lvararg:" + scope}] = vaScc;
        localVarargAdded++;
      }
    }
  }
  CG_LOG("Local-linkage boundary: lret=" << localRetAdded
         << ", larg=" << localArgAdded
         << ", lvararg=" << localVarargAdded << "\n");

  // Global objects
  for (const auto &[guid, GV] : Ctx->Gobjs) {
    if (!GV)
      continue;
    NodeIndex valNode = NF.getValueNodeFor(GV);
    if (valNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(valNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{
          "glob:" + std::to_string(guid)}] = scc;
    }
  }

  // External global object references
  for (const auto &[guid, GV] : Ctx->ExtGobjs) {
    if (!GV)
      continue;
    NodeIndex valNode = NF.getValueNodeFor(GV);
    if (valNode != AndersNodeFactory::InvalidIndex) {
      uint32_t scc = origNodeToSCC(valNode);
      if (scc != UINT32_MAX)
        out.symbolTable[BoundarySymbol{
          "glob:" + std::to_string(guid)}] = scc;
    }
  }

  // Canonical global-field pointer/deref nodes.
  // These nodes are shared globally in monolithic mode (via canonicalized
  // ConstantExpr GEP keys), but become disconnected across per-TU compressed
  // graphs unless we expose them as boundary symbols.
  size_t globFieldPtrAdded = 0;
  size_t globFieldDerefAdded = 0;
  const uint32_t nodeCount = useDense ? numDenseNodes : NF.getNumNodes();
  for (uint32_t n = 0; n < nodeCount; n++) {
    NodeIndex origIdx = useDense ? denseToOrig[n] : n;
    const Value *V = NF.getValueForNode(origIdx);
    if (!V)
      continue;

    std::string fieldKey;
    if (!getGlobalFieldBoundaryKey(V, fieldKey))
      continue;

    uint32_t ptrSCC = (n < nodeToSCC.size()) ? nodeToSCC[n] : UINT32_MAX;
    if (ptrSCC == UINT32_MAX)
      continue;
    out.symbolTable[BoundarySymbol{"gptr:" + fieldKey}] = ptrSCC;
    globFieldPtrAdded++;

    NodeIndex derefNode = NF.getDereferenceNodeFor(origIdx);
    if (derefNode == AndersNodeFactory::InvalidIndex)
      continue;
    uint32_t derefSCC = origNodeToSCC(derefNode);
    if (derefSCC == UINT32_MAX)
      continue;
    out.symbolTable[BoundarySymbol{"gderef:" + fieldKey}] = derefSCC;
    globFieldDerefAdded++;
  }
  CG_LOG("Global-field boundary: gptr=" << globFieldPtrAdded
         << ", gderef=" << globFieldDerefAdded << "\n");

  // Indirect call nodes as boundary symbols
  //   icall:<id>    -> function-pointer operand node
  //   icallarg:<id>:N -> callsite pointer-typed argument node
  //   icallret:<id> -> call result value node (if pointer-typed and present)
  size_t icallTotal = 0, icallNoMD = 0, icallNoNode = 0, icallNoSCC = 0, icallAdded = 0;
  size_t icallArgAdded = 0;
  size_t icallRetAdded = 0;
  for (auto *CS : Ctx->IndirectCallInsts) {
    icallTotal++;
    auto *MD = CS->getMetadata("ka.icall.id");
    if (!MD) { icallNoMD++; continue; }
    auto *S = dyn_cast<MDString>(MD->getOperand(0));
    if (!S) { icallNoMD++; continue; }
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    NodeIndex fptrNode = NF.getValueNodeFor(fptr);
    if (fptrNode == AndersNodeFactory::InvalidIndex) { icallNoNode++; continue; }
    uint32_t scc = origNodeToSCC(fptrNode);
    if (scc == UINT32_MAX) { icallNoSCC++; continue; }
    out.symbolTable[BoundarySymbol{"icall:" + S->getString().str()}] = scc;
    icallAdded++;

    for (unsigned argNo = 0; argNo < CS->arg_size(); argNo++) {
      Value *arg = CS->getArgOperand(argNo);
      if (!containsPointerType(arg->getType()))
        continue;
      if (shouldSkipValue(arg))
        continue;
      NodeIndex argNode = NF.getValueNodeFor(arg);
      if (argNode == AndersNodeFactory::InvalidIndex)
        continue;
      uint32_t argScc = origNodeToSCC(argNode);
      if (argScc == UINT32_MAX)
        continue;
      out.symbolTable[BoundarySymbol{
          "icallarg:" + S->getString().str() + ":" + std::to_string(argNo)}] = argScc;
      icallArgAdded++;
    }

    if (containsPointerType(CS->getType())) {
      NodeIndex retNode = NF.getValueNodeFor(CS);
      if (retNode != AndersNodeFactory::InvalidIndex) {
        uint32_t retSCC = origNodeToSCC(retNode);
        if (retSCC != UINT32_MAX) {
          out.symbolTable[BoundarySymbol{"icallret:" + S->getString().str()}] = retSCC;
          icallRetAdded++;
        }
      }
    }
  }
  CG_LOG("Icall boundary: total=" << icallTotal << " noMD=" << icallNoMD
         << " noNode=" << icallNoNode << " noSCC=" << icallNoSCC
         << " added=" << icallAdded
         << " arg-added=" << icallArgAdded
         << " ret-added=" << icallRetAdded << "\n");


  // Step 3: Build funcNodes - scan all nodes for Function* values.
  // Use GUID-based address-taken filtering instead of Function* identity.
  // NodeFactory canonicalizes declaration values to defining Function* when
  // available, so pointer-identity checks against AddressTakenFuncs can drop
  // legitimate indirect targets in compositional mode.
  std::unordered_set<uint64_t> addressTakenGuids;
  addressTakenGuids.reserve(Ctx->AddressTakenFuncs.size());
  for (const Function *AT : Ctx->AddressTakenFuncs) {
    if (AT)
      addressTakenGuids.insert(AT->getGUID());
  }
  for (uint32_t n = 0; n < nodeCount; n++) {
    NodeIndex origIdx = useDense ? denseToOrig[n] : n;
    const Value *V = NF.getValueForNode(origIdx);
    if (!V) continue;
    const Function *F = dyn_cast<Function>(V);
    if (!F) continue;
    // Only include address-taken functions (those that can be indirect targets)
    if (!addressTakenGuids.count(F->getGUID()))
      continue;
    // Don't count return/vararg nodes
    if (NF.isReturnNode(origIdx) || NF.isVarargNode(origIdx))
      continue;
    uint32_t sccId = (n < nodeToSCC.size()) ? nodeToSCC[n] : UINT32_MAX;
    if (sccId != UINT32_MAX)
      out.funcNodes[sccId].push_back(getScopeName(F));
  }

  // Deduplicate function names within each SCC
  for (auto &[sccId, names] : out.funcNodes) {
    std::sort(names.begin(), names.end());
    names.erase(std::unique(names.begin(), names.end()), names.end());
  }

  CG_LOG("Compressed graph: " << numSCCs << " SCC nodes, "
         << out.edges.size() << " edges, "
         << out.symbolTable.size() << " boundary symbols, "
         << out.funcNodes.size() << " func-bearing nodes\n");
}

void CallGraphPass::exportCompressedGraph(StringRef Path) {
  auto tTotal = std::chrono::steady_clock::now();

  const cfl_result_t *GraphPtr = nullptr;
  std::unique_ptr<gracfl::SolverFWGramParallel> TmpSolver;
  if (cflSolver) {
    GraphPtr = &cflSolver->getReachability();
  } else {
    CG_LOG("TIMER export-cfl-solve: solving CFL for compressed graph export...\n");
    auto tSolve = std::chrono::steady_clock::now();
    const auto &solverEdges = (CFLGlobalDedup && !denseEdges.empty())
                                  ? denseEdges : EB.getEdges();
    TmpSolver = std::make_unique<gracfl::SolverFWGramParallel>(
        solverEdges, *EB.getGrammar(), cflThreads);
    TmpSolver->runCFL();
    GraphPtr = &TmpSolver->getReachability();
    CG_LOG("TIMER export-cfl-solve "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tSolve).count()
           << " ms\n");
  }
  if (!GraphPtr || GraphPtr->empty()) {
    WARNING("CompressedGraph: empty CFL graph, skip export to " << Path << "\n");
    return;
  }

  const auto &Graph = *GraphPtr;
  const uint32_t LabelV = EB.getLabelV();
  if (Graph[0].size() <= LabelV) {
    WARNING("CompressedGraph: V label index " << LabelV << " is out of range\n");
    return;
  }

  auto tVSCC = std::chrono::steady_clock::now();
  std::vector<uint32_t> nodeToSCC;
  uint32_t numSCCs = 0;
  computeVSCC(Graph, LabelV, nodeToSCC, numSCCs);
  CG_LOG("TIMER export-vscc "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tVSCC).count()
         << " ms\n");

  auto tCompress = std::chrono::steady_clock::now();
  CompressedGraphData data;
  compressConstraintGraph(Graph, nodeToSCC, numSCCs, data);
  std::vector<std::string> coveredModules;
  std::unordered_map<std::string, std::string> moduleHashes;
  coveredModules.reserve(Ctx->Modules.size());
  for (const auto &[M, _] : Ctx->Modules) {
    std::string rawId = M ? M->getModuleIdentifier() : std::string("<null-module>");
    auto it = Ctx->ModuleMaps.find(M);
    if (it != Ctx->ModuleMaps.end() && !it->second.empty())
      rawId = it->second.str();
    std::string moduleId = normalizeModuleIdentifier(rawId);
    coveredModules.push_back(moduleId);

    std::string moduleHash;
    std::string hashErr;
    if (computeFileSHA256(moduleId, moduleHash, &hashErr))
      moduleHashes[moduleId] = moduleHash;
    else
      WARNING("CompressedGraph metadata: " << hashErr << "\n");
  }
  data.metadataJson = encodeCflcgMetadata(getCurrentCflcgGrammarMeta(EB),
                                          "monolithic-export",
                                          coveredModules,
                                          moduleHashes);
  CG_LOG("TIMER export-compress "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tCompress).count()
         << " ms\n");

  auto tSave = std::chrono::steady_clock::now();
  std::string ErrMsg;
  if (!saveCompressedGraph(Path, data, &ErrMsg)) {
    WARNING("CompressedGraph: failed to export " << Path << ": " << ErrMsg << "\n");
    return;
  }
  CG_LOG("TIMER export-save "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tSave).count()
         << " ms\n");

  CG_LOG("Exported compressed graph to " << Path
         << ": nodes=" << data.numNodes
         << ", edges=" << data.edges.size()
         << ", symbols=" << data.symbolTable.size() << "\n");
  CG_LOG("TIMER export-total "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tTotal).count()
         << " ms\n");
}

bool CallGraphPass::runCompositionalSolve() {
  struct GraphSource {
    CompressedGraphData graph;
    std::string source;
    bool fromFile = false;
    CflcgMetadata metadata;
    bool metadataParsed = false;
  };

  struct CurrentModuleInfo {
    Module *module = nullptr;
    std::string moduleId;
    std::string moduleHash;
    size_t edgeStart = 0;
    size_t edgeEnd = 0;
  };

  const bool strictMode = static_cast<bool>(CFLCGCacheStrict);
  const bool repairMode = static_cast<bool>(CFLCGCacheRepair);
  const bool allowDuplicateCoverage =
      static_cast<bool>(CFLCGAllowDuplicateCoverage);
  const bool enforceCacheChecks = strictMode || repairMode;
  const CflcgGrammarMeta expectedMeta = getCurrentCflcgGrammarMeta(EB);

  std::vector<GraphSource> graphInputs;
  graphInputs.reserve(perTUGraphs.size() + CompressedGraphInputs.size());
  for (size_t i = 0; i < perTUGraphs.size(); i++) {
    GraphSource inMem;
    inMem.graph = std::move(perTUGraphs[i]);
    inMem.source = "in-memory graph #" + std::to_string(i);
    graphInputs.push_back(std::move(inMem));
  }
  perTUGraphs.clear();

  CG_LOG("Compositional CFL solve: " << graphInputs.size()
         << " in-memory per-TU graphs, "
         << CompressedGraphInputs.size() << " file inputs"
         << " (strict=" << strictMode
         << ", repair=" << repairMode
         << ", allow-duplicate-coverage=" << allowDuplicateCoverage << ")\n");

  auto tLoad = std::chrono::steady_clock::now();
  for (size_t i = 0; i < CompressedGraphInputs.size(); i++) {
    GraphSource loaded;
    loaded.source = CompressedGraphInputs[i];
    loaded.fromFile = true;
    std::string errMsg;
    if (!loadCompressedGraph(CompressedGraphInputs[i], loaded.graph, &errMsg)) {
      errs() << "Failed to load compressed graph '"
             << CompressedGraphInputs[i] << "': " << errMsg << "\n";
      return false;
    }
    CG_LOG("  Loaded " << CompressedGraphInputs[i]
           << ": nodes=" << loaded.graph.numNodes
           << ", edges=" << loaded.graph.edges.size()
           << ", symbols=" << loaded.graph.symbolTable.size() << "\n");
    graphInputs.push_back(std::move(loaded));
  }
  CG_LOG("TIMER comp-load "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tLoad).count()
         << " ms\n");

  if (graphInputs.empty()) {
    WARNING("Compositional solve: no graphs (need per-TU or --cfl-compressed-input)\n");
    return false;
  }

  for (auto &GI : graphInputs)
    GI.metadataParsed = parseCflcgMetadata(GI.graph.metadataJson, GI.metadata);

  std::map<std::string, CurrentModuleInfo> currentModules;
  std::set<std::string> missingModules;
  std::set<std::string> staleModules;
  std::set<std::string> duplicateModules;
  std::set<std::string> incompatibleItems;

  for (const auto &[M, _] : Ctx->Modules) {
    std::string rawId = M ? M->getModuleIdentifier() : std::string("<null-module>");
    auto itPath = Ctx->ModuleMaps.find(M);
    if (itPath != Ctx->ModuleMaps.end() && !itPath->second.empty())
      rawId = itPath->second.str();
    std::string moduleId = normalizeModuleIdentifier(rawId);

    CurrentModuleInfo info;
    info.module = M;
    info.moduleId = moduleId;
    std::string hashErr;
    if (!computeFileSHA256(moduleId, info.moduleHash, &hashErr)) {
      if (enforceCacheChecks)
        incompatibleItems.insert("current-module-hash:" + moduleId + " (" + hashErr + ")");
      else
        WARNING("Compositional cache check (lenient): " << hashErr << "\n");
    }

    auto itRange = moduleEdgeRanges.find(M);
    if (itRange != moduleEdgeRanges.end()) {
      info.edgeStart = itRange->second.first;
      info.edgeEnd = itRange->second.second;
    }

    auto inserted = currentModules.emplace(moduleId, std::move(info));
    if (!inserted.second) {
      incompatibleItems.insert("duplicate-current-module-id:" + moduleId);
    }
  }

  auto emitSet = [&](StringRef name, const std::set<std::string> &items) {
    errs() << "  " << name << " (" << items.size() << ")";
    if (items.empty()) {
      errs() << ": <none>\n";
      return;
    }
    errs() << ":\n";
    size_t shown = 0;
    for (const auto &item : items) {
      errs() << "    - " << item << "\n";
      shown++;
      if (shown >= 32 && items.size() > shown) {
        errs() << "    ... +" << (items.size() - shown) << " more\n";
        break;
      }
    }
  };

  auto recomputeAllModules = [&](std::vector<GraphSource> &outGraphs) -> bool {
    outGraphs.clear();
    perTUGraphs.clear();
    for (const auto &[moduleId, info] : currentModules) {
      solveAndCompressPerTU(info.module, info.edgeStart, info.edgeEnd);
      if (perTUGraphs.empty()) {
        errs() << "Repair mode failed: recomputation did not emit graph for "
               << moduleId << "\n";
        return false;
      }
      GraphSource rebuilt;
      rebuilt.graph = std::move(perTUGraphs.back());
      perTUGraphs.pop_back();
      rebuilt.source = "repair:" + moduleId;
      rebuilt.metadataParsed = parseCflcgMetadata(rebuilt.graph.metadataJson, rebuilt.metadata);
      if (!rebuilt.metadataParsed) {
        errs() << "Repair mode failed: invalid metadata in recomputed graph for "
               << moduleId << "\n";
        return false;
      }
      if (enforceCacheChecks &&
          (!rebuilt.metadata.hasAnalysisKey ||
           !rebuilt.metadata.hasCoverage ||
           !rebuilt.metadata.hasModuleHashes)) {
        errs() << "Repair mode failed: recomputed graph for " << moduleId
               << " is missing strict metadata fields\n";
        return false;
      }
      outGraphs.push_back(std::move(rebuilt));
    }
    perTUGraphs.clear();
    return true;
  };

  if (enforceCacheChecks) {
    std::unordered_map<std::string, size_t> coverageCounts;
    std::set<std::string> coveredCurrentModules;

    for (const auto &GI : graphInputs) {
      if (!GI.metadataParsed) {
        incompatibleItems.insert("invalid-metadata:" + GI.source);
        continue;
      }

      const auto &MD = GI.metadata;
      if (!MD.hasAnalysisKey) {
        incompatibleItems.insert("missing-analysis_key:" + GI.source);
      } else if (!cflcgMetadataCompatible(MD.analysisKey, expectedMeta)) {
        incompatibleItems.insert("analysis-key-mismatch:" + GI.source);
      }
      if (!MD.hasCoverage)
        incompatibleItems.insert("missing-covered_modules:" + GI.source);
      if (!MD.hasModuleHashes)
        incompatibleItems.insert("missing-module_hashes:" + GI.source);

      if (!MD.hasCoverage)
        continue;

      for (const auto &moduleId : MD.coveredModules) {
        auto itCur = currentModules.find(moduleId);
        if (itCur == currentModules.end()) {
          incompatibleItems.insert("unknown-covered-module:" + GI.source + ":" + moduleId);
          continue;
        }
        coveredCurrentModules.insert(moduleId);
        coverageCounts[moduleId]++;

        if (!MD.hasModuleHashes) {
          staleModules.insert(moduleId);
          continue;
        }
        auto itHash = MD.moduleHashes.find(moduleId);
        if (itHash == MD.moduleHashes.end() || itHash->second.empty()) {
          staleModules.insert(moduleId);
          continue;
        }
        if (itCur->second.moduleHash.empty() ||
            itCur->second.moduleHash != itHash->second) {
          staleModules.insert(moduleId);
        }
      }
    }

    for (const auto &[moduleId, _] : currentModules) {
      if (!coveredCurrentModules.count(moduleId))
        missingModules.insert(moduleId);
    }

    if (!allowDuplicateCoverage) {
      for (const auto &[moduleId, count] : coverageCounts) {
        if (count > 1) {
          if (staleModules.count(moduleId)) {
            // Hash conflict: different versions of the same module in different
            // .cflcg files — this is a real error.
            duplicateModules.insert(moduleId);
          } else {
            // Benign duplicate: all covering .cflcg files agree on the hash
            // (same content). The composition step deduplicates edges, so this
            // is safe to ignore.
            CG_LOG("Duplicate coverage for " << moduleId
                   << " (benign, all inputs agree on hash)\n");
          }
        }
      }
    }
  } else {
    for (const auto &GI : graphInputs) {
      if (!GI.metadataParsed) {
        WARNING("CompressedGraph: missing/invalid metadata in " << GI.source
                << " (strict mode disabled)\n");
        continue;
      }
      if (GI.metadata.hasAnalysisKey &&
          !cflcgMetadataCompatible(GI.metadata.analysisKey, expectedMeta)) {
        WARNING("CompressedGraph: analysis key mismatch in "
                << GI.source << " (strict mode disabled)\n");
      }
    }
  }

  bool needRepair = enforceCacheChecks &&
                    (!missingModules.empty() || !staleModules.empty() ||
                     !duplicateModules.empty() || !incompatibleItems.empty());

  if (needRepair) {
    errs() << "Compositional cache validation failed:\n";
    emitSet("missing", missingModules);
    emitSet("stale", staleModules);
    emitSet("duplicate", duplicateModules);
    emitSet("incompatible", incompatibleItems);
    if (!repairMode) {
      errs() << "Hint: use --cfl-cache-repair to rebuild stale/missing cache inputs.\n";
      return false;
    }
  }

  std::vector<GraphSource> composeSources;
  bool recomputedFromIR = false;
  if (needRepair) {
    CG_LOG("Repair mode: rebuilding compositional inputs from current IR\n");
    if (!recomputeAllModules(composeSources))
      return false;
    recomputedFromIR = true;
  } else {
    composeSources = std::move(graphInputs);
  }

  if (composeSources.empty()) {
    WARNING("Compositional solve: no usable graphs after cache validation/repair\n");
    return false;
  }

  std::vector<std::string> currentModuleIds;
  std::unordered_map<std::string, std::string> currentModuleHashes;
  currentModuleIds.reserve(currentModules.size());
  currentModuleHashes.reserve(currentModules.size());
  for (const auto &[moduleId, info] : currentModules) {
    currentModuleIds.push_back(moduleId);
    if (!info.moduleHash.empty())
      currentModuleHashes[moduleId] = info.moduleHash;
  }

  auto classifyBoundary = [](StringRef symbol) -> std::string {
    if (LLVM_STRING_STARTS_WITH(symbol, "func:")) return "func";
    if (LLVM_STRING_STARTS_WITH(symbol, "arg:")) return "arg";
    if (LLVM_STRING_STARTS_WITH(symbol, "larg:")) return "larg";
    if (LLVM_STRING_STARTS_WITH(symbol, "ret:")) return "ret";
    if (LLVM_STRING_STARTS_WITH(symbol, "lret:")) return "lret";
    if (LLVM_STRING_STARTS_WITH(symbol, "vararg:")) return "vararg";
    if (LLVM_STRING_STARTS_WITH(symbol, "lvararg:")) return "lvararg";
    if (LLVM_STRING_STARTS_WITH(symbol, "glob:")) return "glob";
    if (LLVM_STRING_STARTS_WITH(symbol, "icall:")) return "icall";
    if (LLVM_STRING_STARTS_WITH(symbol, "icallarg:")) return "icallarg";
    if (LLVM_STRING_STARTS_WITH(symbol, "icallret:")) return "icallret";
    return "other";
  };

  std::unordered_set<NodeIndex> activeCFLNodes;
  activeCFLNodes.reserve(EB.getEdges().size() * 2 + 1);
  for (const auto &E : EB.getEdges()) {
    activeCFLNodes.insert(getCanonicalNode(E.from));
    activeCFLNodes.insert(getCanonicalNode(E.to));
  }
  auto isActiveBoundaryNode = [&](NodeIndex N) -> bool {
    if (N == AndersNodeFactory::InvalidIndex)
      return false;
    NodeIndex C = getCanonicalNode(N);
    // Under fptr slicing, boundary symbols only exist for kept components.
    if (CFLFptrSlice && !fptrSliceKept.count(C))
      return false;
    return activeCFLNodes.count(C) > 0;
  };

  auto collectExpectedBoundarySymbols =
      [&](std::unordered_set<std::string> &expected,
          std::unordered_map<std::string, size_t> &classCounts) {
    expected.clear();
    classCounts.clear();

    auto addExpected = [&](const std::string &symbol) {
      if (expected.insert(symbol).second)
        classCounts[classifyBoundary(symbol)]++;
    };

    for (const auto &[guid, F] : Ctx->Funcs) {
      if (!F || F->hasLocalLinkage())
        continue;
      std::string guidStr = std::to_string(guid);
      if (isActiveBoundaryNode(NF.getValueNodeFor(F)))
        addExpected("func:" + guidStr);
      for (const auto &Arg : F->args()) {
        if (isActiveBoundaryNode(NF.getValueNodeFor(&Arg))) {
          addExpected("arg:" + guidStr + ":" + std::to_string(Arg.getArgNo()));
        }
      }
      if (isActiveBoundaryNode(NF.getReturnNodeFor(F)))
        addExpected("ret:" + guidStr);
      if (isActiveBoundaryNode(NF.getVarargNodeFor(F)))
        addExpected("vararg:" + guidStr);
    }

    for (const auto &[guid, F] : Ctx->ExtFuncs) {
      if (!F)
        continue;
      std::string guidStr = std::to_string(guid);
      if (isActiveBoundaryNode(NF.getValueNodeFor(F)))
        addExpected("func:" + guidStr);
      for (const auto &Arg : F->args()) {
        if (isActiveBoundaryNode(NF.getValueNodeFor(&Arg))) {
          addExpected("arg:" + guidStr + ":" + std::to_string(Arg.getArgNo()));
        }
      }
      if (isActiveBoundaryNode(NF.getReturnNodeFor(F)))
        addExpected("ret:" + guidStr);
      if (isActiveBoundaryNode(NF.getVarargNodeFor(F)))
        addExpected("vararg:" + guidStr);
    }

    for (const auto &[guid, GV] : Ctx->Gobjs) {
      if (!GV)
        continue;
      if (isActiveBoundaryNode(NF.getValueNodeFor(GV)))
        addExpected("glob:" + std::to_string(guid));
    }
    for (const auto &[guid, GV] : Ctx->ExtGobjs) {
      if (!GV)
        continue;
      if (isActiveBoundaryNode(NF.getValueNodeFor(GV)))
        addExpected("glob:" + std::to_string(guid));
    }

    for (const Function *F : Ctx->AddressTakenFuncs) {
      if (!F || !F->hasLocalLinkage())
        continue;
      std::string scope = getScopeName(F);
      for (const auto &Arg : F->args()) {
        if (isActiveBoundaryNode(NF.getValueNodeFor(&Arg))) {
          addExpected("larg:" + scope + ":" + std::to_string(Arg.getArgNo()));
        }
      }
      if (isActiveBoundaryNode(NF.getReturnNodeFor(F)))
        addExpected("lret:" + scope);
      if (isActiveBoundaryNode(NF.getVarargNodeFor(F)))
        addExpected("lvararg:" + scope);
    }

    for (auto *CS : Ctx->IndirectCallInsts) {
      auto *MD = CS->getMetadata("ka.icall.id");
      if (!MD)
        continue;
      auto *S = dyn_cast<MDString>(MD->getOperand(0));
      if (!S)
        continue;
      Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
      if (!isActiveBoundaryNode(NF.getValueNodeFor(fptr)))
        continue;
      std::string idStr = S->getString().str();
      addExpected("icall:" + idStr);
      for (unsigned argNo = 0; argNo < CS->arg_size(); argNo++) {
        Value *arg = CS->getArgOperand(argNo);
        if (!containsPointerType(arg->getType()))
          continue;
        if (shouldSkipValue(arg))
          continue;
        if (isActiveBoundaryNode(NF.getValueNodeFor(arg))) {
          addExpected("icallarg:" + idStr + ":" + std::to_string(argNo));
        }
      }
      if (containsPointerType(CS->getType()) &&
          isActiveBoundaryNode(NF.getValueNodeFor(CS))) {
        addExpected("icallret:" + idStr);
      }
    }
  };

  if (enforceCacheChecks) {
    std::unordered_set<std::string> expectedSymbols;
    std::unordered_map<std::string, size_t> expectedClassCounts;
    collectExpectedBoundarySymbols(expectedSymbols, expectedClassCounts);

    for (unsigned attempt = 0; attempt < 2; attempt++) {
      std::unordered_set<std::string> availableSymbols;
      std::unordered_map<std::string, size_t> availableClassCounts;
      for (const auto &GS : composeSources) {
        for (const auto &[sym, _] : GS.graph.symbolTable) {
          if (availableSymbols.insert(sym.symbol).second)
            availableClassCounts[classifyBoundary(sym.symbol)]++;
        }
      }

      std::set<std::string> missingBoundarySymbols;
      for (const auto &sym : expectedSymbols) {
        if (!availableSymbols.count(sym))
          missingBoundarySymbols.insert(sym);
      }

      // A missing ret:GUID is benign when the function is in ExtFuncs (defined
      // in another TU, not locally).  Two valid reasons it can be absent:
      //   1. The library analyzed the function and its return value carries no
      //      pointer aliasing (e.g., always-null), so ret:GUID was never active
      //      and was not exported to the boundary cache.
      //   2. The function is truly external (libc etc.) and not analyzed anywhere.
      // In both cases the composition is sound: the return is treated as
      // unconstrained, which over-approximates.  Keep the strict check for
      // functions defined in the current TU (Ctx->Funcs) where an active return
      // node MUST appear in the per-module cache.
      if (!missingBoundarySymbols.empty()) {
        std::unordered_set<std::string> extFuncGUIDs;
        extFuncGUIDs.reserve(Ctx->ExtFuncs.size());
        for (const auto &[guid, F] : Ctx->ExtFuncs)
          extFuncGUIDs.insert(std::to_string(guid));
        for (auto it = missingBoundarySymbols.begin();
             it != missingBoundarySymbols.end(); ) {
          StringRef S(*it);
          if (LLVM_STRING_STARTS_WITH(S, "ret:") && extFuncGUIDs.count(S.drop_front(4).str()))
            it = missingBoundarySymbols.erase(it);
          else
            ++it;
        }
      }

      std::set<std::string> missingBoundaryClasses;
      const std::array<const char *, 11> requiredClasses = {
          "func", "arg", "ret", "vararg", "glob", "icall",
          "larg", "lret", "lvararg", "icallarg", "icallret"};
      for (const char *C : requiredClasses) {
        const size_t expectedCount = expectedClassCounts[C];
        const size_t gotCount = availableClassCounts[C];
        if (expectedCount > 0 && gotCount == 0)
          missingBoundaryClasses.insert(C);
      }

      if (missingBoundarySymbols.empty() && missingBoundaryClasses.empty())
        break;

      errs() << "Compositional boundary cache sanity failed:\n";
      errs() << "  missing-boundary-symbols: " << missingBoundarySymbols.size() << "\n";
      size_t shown = 0;
      for (const auto &sym : missingBoundarySymbols) {
        errs() << "    - " << sym << "\n";
        shown++;
        if (shown >= 32 && missingBoundarySymbols.size() > shown) {
          errs() << "    ... +" << (missingBoundarySymbols.size() - shown)
                 << " more\n";
          break;
        }
      }
      errs() << "  missing-boundary-classes: " << missingBoundaryClasses.size() << "\n";
      for (const auto &cls : missingBoundaryClasses)
        errs() << "    - " << cls << "\n";

      if (repairMode && !recomputedFromIR && attempt == 0) {
        CG_LOG("Repair mode: boundary mismatch detected, rebuilding from current IR\n");
        if (!recomputeAllModules(composeSources))
          return false;
        recomputedFromIR = true;
        continue;
      }
      if (strictMode)
        return false;
      break;
    }
  }

  std::vector<CompressedGraphData> graphs;
  graphs.reserve(composeSources.size());
  for (auto &GS : composeSources)
    graphs.push_back(std::move(GS.graph));

  // Step 2: Assign node offsets and build unified ID space
  auto tBuild = std::chrono::steady_clock::now();
  std::vector<uint32_t> nodeOffsets(graphs.size());
  uint32_t totalNodes = 0;
  for (size_t i = 0; i < graphs.size(); i++) {
    nodeOffsets[i] = totalNodes;
    totalNodes += graphs[i].numNodes;
  }

  CG_LOG("Unified node space: " << totalNodes << " nodes\n");

  // Step 3: Build boundary symbol -> list<(graph_idx, unified_node_id)> map
  std::unordered_map<std::string,
                     std::vector<std::pair<size_t, uint32_t>>> symbolOccurrences;
  for (size_t i = 0; i < graphs.size(); i++) {
    for (const auto &[sym, localId] : graphs[i].symbolTable) {
      if (localId >= graphs[i].numNodes && graphs[i].numNodes != 0)
        continue;
      uint32_t unifiedId = nodeOffsets[i] + localId;
      symbolOccurrences[sym.symbol].emplace_back(i, unifiedId);
    }
  }

  // Step 4: Merge matching boundary nodes with union-find
  std::vector<uint32_t> ufParent(totalNodes);
  std::vector<uint8_t> ufRank(totalNodes, 0);
  std::iota(ufParent.begin(), ufParent.end(), 0);

  auto ufFind = [&](uint32_t n) -> uint32_t {
    uint32_t root = n;
    while (ufParent[root] != root)
      root = ufParent[root];
    while (ufParent[n] != root) {
      uint32_t parent = ufParent[n];
      ufParent[n] = root;
      n = parent;
    }
    return root;
  };

  auto ufUnion = [&](uint32_t a, uint32_t b) {
    uint32_t ra = ufFind(a);
    uint32_t rb = ufFind(b);
    if (ra == rb) return;
    if (ufRank[ra] < ufRank[rb]) std::swap(ra, rb);
    ufParent[rb] = ra;
    if (ufRank[ra] == ufRank[rb]) ufRank[ra]++;
  };

  size_t mergeCount = 0;
  for (const auto &[symbol, occurrences] : symbolOccurrences) {
    if (occurrences.size() < 2)
      continue;
    uint32_t first = occurrences[0].second;
    for (size_t j = 1; j < occurrences.size(); j++) {
      ufUnion(first, occurrences[j].second);
      mergeCount++;
    }
  }

  CG_LOG("Boundary merges: " << mergeCount << " unions across "
         << symbolOccurrences.size() << " symbols\n");

  // Step 5: Build dense remapping through union-find
  std::unordered_map<uint32_t, uint32_t> rootToDense;
  rootToDense.reserve(totalNodes);
  uint32_t numDense = 0;
  std::vector<uint32_t> unifiedToDense(totalNodes);
  for (uint32_t n = 0; n < totalNodes; n++) {
    uint32_t root = ufFind(n);
    auto it = rootToDense.find(root);
    if (it == rootToDense.end()) {
      rootToDense[root] = numDense;
      unifiedToDense[n] = numDense;
      numDense++;
    } else {
      unifiedToDense[n] = it->second;
    }
  }

  CG_LOG("After union-find: " << totalNodes << " unified -> "
         << numDense << " dense nodes\n");

  // Debug: dump boundary symbol -> dense mapping
  for (const auto &[symbol, occurrences] : symbolOccurrences) {
    if (occurrences.size() < 2) continue;
    uint32_t denseId = unifiedToDense[ufFind(occurrences[0].second)];
    CG_DEBUG("BoundaryMerge: " << symbol << " -> dense=" << denseId
             << " (from graphs:");
    for (const auto &[gi, uid] : occurrences)
      CG_DEBUG(" g" << gi << ":local" << (uid - nodeOffsets[gi])
               << "->unified" << uid);
    CG_DEBUG(")\n");
  }

  // Step 6: Remap all edges through union-find and deduplicate
  std::unordered_set<EdgeKey, EdgeKeyHash> edgeSeen;
  std::vector<gracfl::Edge> combinedEdges;
  size_t totalInputEdges = 0;
  for (const auto &G : graphs)
    totalInputEdges += G.edges.size();
  edgeSeen.reserve(totalInputEdges);
  combinedEdges.reserve(totalInputEdges);

  for (size_t i = 0; i < graphs.size(); i++) {
    uint32_t offset = nodeOffsets[i];
    for (const auto &E : graphs[i].edges) {
      if ((E.from >= graphs[i].numNodes || E.to >= graphs[i].numNodes) &&
          graphs[i].numNodes != 0) {
        continue;
      }
      uint32_t from = unifiedToDense[offset + E.from];
      uint32_t to = unifiedToDense[offset + E.to];
      EdgeKey key{from, to, E.label};
      if (edgeSeen.insert(key).second)
        combinedEdges.emplace_back(from, to, E.label);
    }
  }

  CG_LOG("Combined edges: " << totalInputEdges << " input -> "
         << combinedEdges.size() << " deduplicated\n");
  CG_LOG("TIMER comp-build "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tBuild).count()
         << " ms\n");

  extern cl::opt<std::string> CompressedGraphOutput;
  const uint32_t LabelV = EB.getLabelV();

  if (numDense == 0) {
    composedSolver.reset();
    composedNumDense = 0;
    composedSymbolToDense.clear();
    CG_LOG("Compositional solve: no dense nodes after composition\n");

    if (!CompressedGraphOutput.empty()) {
      CompressedGraphData exportData;
      exportData.numNodes = 0;
      exportData.metadataJson = encodeCflcgMetadata(expectedMeta,
                                                    "composed-export",
                                                    currentModuleIds,
                                                    currentModuleHashes);
      std::string errMsg;
      if (!saveCompressedGraph(CompressedGraphOutput, exportData, &errMsg)) {
        WARNING("Failed to export empty composed graph: " << errMsg << "\n");
      }
    }
    return true;
  }

  // Step 7: Solve CFL on combined graph
  if (!EB.getGrammar()) {
    errs() << "Compositional solve: grammar not initialized\n";
    return false;
  }

  CG_LOG("Running CFL solver on combined graph (" << numDense
         << " nodes, " << combinedEdges.size() << " edges)...\n");
  auto tSolve = std::chrono::steady_clock::now();
  auto solver = std::make_unique<gracfl::SolverFWGramParallel>(
      combinedEdges, *EB.getGrammar(), cflThreads);
  solver->runCFL();
  CG_LOG("CFL solve complete. Final edges: " << solver->getEdgeCount() << "\n");
  CG_LOG("TIMER comp-solve "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tSolve).count()
         << " ms\n");

  // Store composed solver and symbol->dense mapping for V-snapshot export.
  composedSolver = std::move(solver);
  composedNumDense = numDense;
  composedSymbolToDense.clear();
  composedSymbolToDense.reserve(symbolOccurrences.size());
  for (const auto &[symbol, occurrences] : symbolOccurrences)
    composedSymbolToDense[symbol] = unifiedToDense[ufFind(occurrences[0].second)];

  // Step 8: Build reverse map from dense node -> function names
  std::unordered_map<uint32_t, std::vector<std::string>> denseToFuncNames;
  for (size_t i = 0; i < graphs.size(); i++) {
    uint32_t offset = nodeOffsets[i];
    for (const auto &[localId, names] : graphs[i].funcNodes) {
      if (localId >= graphs[i].numNodes && graphs[i].numNodes != 0)
        continue;
      uint32_t denseId = unifiedToDense[offset + localId];
      auto &merged = denseToFuncNames[denseId];
      merged.insert(merged.end(), names.begin(), names.end());
    }
  }
  for (auto &[id, names] : denseToFuncNames) {
    std::sort(names.begin(), names.end());
    names.erase(std::unique(names.begin(), names.end()), names.end());
  }

  // Build function name -> Function* map for resolving.
  std::unordered_map<std::string, Function *> nameToFunc;
  for (auto &[M, _] : Ctx->Modules) {
    for (Function &F : *M) {
      if (F.isIntrinsic())
        continue;
      std::string scope = getScopeName(&F);
      auto [it, inserted] = nameToFunc.emplace(scope, &F);
      if (!inserted && it->second->isDeclaration() && !F.isDeclaration())
        it->second = &F;
    }
  }

  CG_LOG("Field store map (IR-based): " << funcFieldStores.size()
         << " functions\n");

  const auto &composedGraph = composedSolver->getReachability();

  if (!CompressedGraphOutput.empty()) {
    auto tExport = std::chrono::steady_clock::now();

    std::vector<uint32_t> nodeToSCC;
    uint32_t numSCCs = 0;
    computeVSCC(composedGraph, LabelV, nodeToSCC, numSCCs);

    CompressedGraphData exportData;
    exportData.numNodes = numSCCs;

    std::unordered_set<EdgeKey, EdgeKeyHash> exportEdgeSeen;
    exportEdgeSeen.reserve(combinedEdges.size());
    exportData.edges.reserve(combinedEdges.size() / 2);
    // Note: self-loops (including field-label ones) are kept here — this loop
    // has no self-loop skip, matching the compositional bug-fix #3 rationale.
    for (const auto &E : combinedEdges) {
      uint32_t sccFrom = (E.from < nodeToSCC.size()) ? nodeToSCC[E.from] : UINT32_MAX;
      uint32_t sccTo = (E.to < nodeToSCC.size()) ? nodeToSCC[E.to] : UINT32_MAX;
      if (sccFrom == UINT32_MAX || sccTo == UINT32_MAX)
        continue;
      EdgeKey key{sccFrom, sccTo, E.label};
      if (exportEdgeSeen.insert(key).second)
        exportData.edges.emplace_back(sccFrom, sccTo, E.label);
    }

    {
      const uint32_t labels[] = {
        EB.getLabelAssign(), EB.getLabelAssignInv(),
        EB.getLabelDeref(), EB.getLabelDerefInv()
      };
      std::vector<uint32_t> sccSize(numSCCs, 0);
      for (uint32_t n = 0; n < nodeToSCC.size(); n++)
        if (nodeToSCC[n] < numSCCs) sccSize[nodeToSCC[n]]++;
      uint32_t loopsAdded = 0;
      for (uint32_t scc = 0; scc < numSCCs; scc++) {
        if (sccSize[scc] < 2) continue;
        for (uint32_t lbl : labels) {
          EdgeKey key{scc, scc, lbl};
          if (exportEdgeSeen.insert(key).second) {
            exportData.edges.emplace_back(scc, scc, lbl);
            loopsAdded++;
          }
        }
      }
      CG_LOG("Composed export: added " << loopsAdded
             << " terminal self-loops for multi-node V-SCCs\n");
    }

    for (const auto &[symbol, occurrences] : symbolOccurrences) {
      uint32_t denseNode = unifiedToDense[ufFind(occurrences[0].second)];
      if (denseNode >= nodeToSCC.size()) continue;
      uint32_t sccId = nodeToSCC[denseNode];
      exportData.symbolTable[{symbol}] = sccId;
    }

    for (const auto &[denseId, names] : denseToFuncNames) {
      if (denseId >= nodeToSCC.size()) continue;
      uint32_t sccId = nodeToSCC[denseId];
      auto &existing = exportData.funcNodes[sccId];
      existing.insert(existing.end(), names.begin(), names.end());
    }
    for (auto &[id, names] : exportData.funcNodes) {
      std::sort(names.begin(), names.end());
      names.erase(std::unique(names.begin(), names.end()), names.end());
    }

    exportData.metadataJson = encodeCflcgMetadata(expectedMeta,
                                                  "composed-export",
                                                  currentModuleIds,
                                                  currentModuleHashes);

    std::string errMsg;
    if (!saveCompressedGraph(CompressedGraphOutput, exportData, &errMsg)) {
      WARNING("Failed to export composed graph: " << errMsg << "\n");
    } else {
      CG_LOG("Exported composed compressed graph to " << CompressedGraphOutput
             << ": nodes=" << exportData.numNodes
             << ", edges=" << exportData.edges.size()
             << ", symbols=" << exportData.symbolTable.size() << "\n");
    }
    CG_LOG("TIMER comp-export "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tExport).count()
           << " ms\n");
  }

  std::unordered_map<std::string, uint32_t> icallSymbolToDense;
  std::unordered_map<std::string, uint32_t> icallArgSymbolToDense;
  std::unordered_map<std::string, uint32_t> icallRetSymbolToDense;
  for (const auto &[symbol, occurrences] : symbolOccurrences) {
    uint32_t dense = unifiedToDense[ufFind(occurrences[0].second)];
    if (symbol.compare(0, 6, "icall:") == 0)
      icallSymbolToDense[symbol] = dense;
    else if (symbol.compare(0, 9, "icallarg:") == 0)
      icallArgSymbolToDense[symbol] = dense;
    else if (symbol.compare(0, 9, "icallret:") == 0)
      icallRetSymbolToDense[symbol] = dense;
  }
  CG_LOG("Composed icall symbols: " << icallSymbolToDense.size()
         << ", icallarg symbols: " << icallArgSymbolToDense.size()
         << ", icallret symbols: " << icallRetSymbolToDense.size() << "\n");

  const uint32_t labelAssign = EB.getLabelAssign();
  const uint32_t labelAssignInv = EB.getLabelAssignInv();

  size_t resolvedCalls = 0;
  size_t totalTargets = 0;
  size_t skippedNoSymbol = 0;
  size_t newCalleePairs = 0;
  size_t newSummaryEdges = 0;

  constexpr size_t kMaxCompIterations = 8;
  bool composedConverged = false;
  for (size_t iterNo = 1; iterNo <= kMaxCompIterations; iterNo++) {
    const auto &iterGraph = composedSolver->getReachability();
    size_t iterResolvedCalls = 0;
    size_t iterTotalTargets = 0;
    size_t iterSkippedNoSymbol = 0;
    size_t iterNewCalleePairs = 0;
    size_t iterNewSummaryEdges = 0;

    for (auto *CS : Ctx->IndirectCallInsts) {
      auto *MD = CS->getMetadata("ka.icall.id");
      if (!MD) continue;
      auto *S = dyn_cast<MDString>(MD->getOperand(0));
      if (!S) continue;
      std::string idStr = S->getString().str();
      std::string icallKey = "icall:" + idStr;
      std::string icallRetKey = "icallret:" + idStr;
      auto makeIcallArgKey = [&](unsigned argNo) {
        return "icallarg:" + idStr + ":" + std::to_string(argNo);
      };

      auto symIt = icallSymbolToDense.find(icallKey);
      if (symIt == icallSymbolToDense.end()) {
        iterSkippedNoSymbol++;
        continue;
      }
      uint32_t denseNode = symIt->second;
      if (denseNode >= iterGraph.size())
        continue;

      Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
      std::string callSiteStruct;
      unsigned callSiteFieldIdx = 0;
      bool hasCallSiteField = getCallSiteFieldKey(fptr, callSiteStruct, callSiteFieldIdx);

      const auto &VSet = iterGraph[denseNode][LabelV];
      size_t vWithFunc = 0;
      for (uint32_t t : VSet)
        if (denseToFuncNames.count(t)) vWithFunc++;
      bool selfHasFunc = denseToFuncNames.count(denseNode) > 0;
      CG_DEBUG("Icall " << icallKey << " dense=" << denseNode
               << " VSet=" << VSet.size()
               << " withFunc=" << vWithFunc
               << " selfFunc=" << selfHasFunc << "\n");
      if (VSet.size() <= 10) {
        for (uint32_t t : VSet) {
          auto fn = denseToFuncNames.find(t);
          if (fn != denseToFuncNames.end()) {
            for (const auto &n : fn->second)
              CG_DEBUG("  VSet[" << t << "] -> " << n << "\n");
          } else {
            CG_DEBUG("  VSet[" << t << "] (no func)\n");
          }
        }
      }
      if (selfHasFunc) {
        for (const auto &n : denseToFuncNames.at(denseNode))
          CG_DEBUG("  Self[" << denseNode << "] -> " << n << "\n");
      }

      FuncSet targets;
      auto resolveCandidate = [&](uint32_t target) {
        auto fnIt = denseToFuncNames.find(target);
        if (fnIt == denseToFuncNames.end())
          return;
        for (const auto &funcName : fnIt->second) {
          auto fIt = nameToFunc.find(funcName);
          if (fIt == nameToFunc.end())
            continue;
          Function *F = getFuncDef(fIt->second);
          if (!isCompatible(CS, F))
            continue;
          if (hasCallSiteField) {
            if (!fieldFilterAccepts(F, callSiteStruct, callSiteFieldIdx)) {
              CG_LOG("FieldFilter: reject " << F->getName()
                     << " for " << callSiteStruct << " field "
                     << callSiteFieldIdx << "\n");
              continue;
            }
          }
          targets.insert(F);
        }
      };

      resolveCandidate(denseNode);
      for (uint32_t target : VSet)
        resolveCandidate(target);

      if (!targets.empty()) {
        iterResolvedCalls++;
        iterTotalTargets += targets.size();
      }

      for (const Function *F : targets) {
        if (Ctx->Callees[CS].insert(F).second)
          iterNewCalleePairs++;
      }

      // Wire assign edges between an actual-arg dense node and a target dense node.
      auto addAssignEdgePair = [&](uint32_t actualDense, uint32_t targetDense) {
        EdgeKey keyFwd{actualDense, targetDense, labelAssign};
        if (edgeSeen.insert(keyFwd).second) {
          combinedEdges.emplace_back(actualDense, targetDense, labelAssign);
          iterNewSummaryEdges++;
        }
        EdgeKey keyRev{targetDense, actualDense, labelAssignInv};
        if (edgeSeen.insert(keyRev).second) {
          combinedEdges.emplace_back(targetDense, actualDense, labelAssignInv);
          iterNewSummaryEdges++;
        }
      };

      const unsigned numActualArgs = CS->arg_size();
      for (const Function *F : targets) {
        const unsigned numFormals = F->arg_size();
        const unsigned minArgs = std::min(numActualArgs, numFormals);
        for (unsigned argNo = 0; argNo < minArgs; argNo++) {
          Value *actual = CS->getArgOperand(argNo);
          if (!containsPointerType(actual->getType()))
            continue;
          if (shouldSkipValue(actual))
            continue;

          auto argIt = icallArgSymbolToDense.find(makeIcallArgKey(argNo));
          if (argIt == icallArgSymbolToDense.end())
            continue;
          uint32_t actualDense = argIt->second;
          if (actualDense >= numDense)
            continue;

          uint32_t formalDense = UINT32_MAX;
          if (!lookupArgDense(F, argNo, composedSymbolToDense, numDense, formalDense))
            continue;

          addAssignEdgePair(actualDense, formalDense);
        }

        if (!F->isVarArg() || numActualArgs <= numFormals)
          continue;
        uint32_t varargDense = UINT32_MAX;
        if (!lookupVarargDense(F, composedSymbolToDense, numDense, varargDense))
          continue;

        for (unsigned argNo = numFormals; argNo < numActualArgs; argNo++) {
          Value *actual = CS->getArgOperand(argNo);
          if (!containsPointerType(actual->getType()))
            continue;
          if (shouldSkipValue(actual))
            continue;

          auto argIt = icallArgSymbolToDense.find(makeIcallArgKey(argNo));
          if (argIt == icallArgSymbolToDense.end())
            continue;
          uint32_t actualDense = argIt->second;
          if (actualDense >= numDense)
            continue;

          addAssignEdgePair(actualDense, varargDense);
        }
      }

      auto retIt = icallRetSymbolToDense.find(icallRetKey);
      if (retIt == icallRetSymbolToDense.end())
        continue;
      uint32_t icallRetDense = retIt->second;
      if (icallRetDense >= numDense)
        continue;

      for (const Function *F : targets) {
        if (!F->getReturnType()->isPointerTy())
          continue;
        uint32_t calleeRetDense = UINT32_MAX;
        if (!lookupRetDense(F, composedSymbolToDense, numDense, calleeRetDense)) {
          CG_DEBUG("No composed ret symbol for target " << F->getName()
                   << " at " << icallKey << "\n");
          continue;
        }
        EdgeKey keyFwd{calleeRetDense, icallRetDense, labelAssign};
        if (edgeSeen.insert(keyFwd).second) {
          combinedEdges.emplace_back(calleeRetDense, icallRetDense, labelAssign);
          iterNewSummaryEdges++;
        }
        EdgeKey keyRev{icallRetDense, calleeRetDense, labelAssignInv};
        if (edgeSeen.insert(keyRev).second) {
          combinedEdges.emplace_back(icallRetDense, calleeRetDense, labelAssignInv);
          iterNewSummaryEdges++;
        }
      }
    }

    resolvedCalls += iterResolvedCalls;
    totalTargets += iterTotalTargets;
    skippedNoSymbol += iterSkippedNoSymbol;
    newCalleePairs += iterNewCalleePairs;
    newSummaryEdges += iterNewSummaryEdges;

    CG_LOG("Compositional iterate #" << iterNo
           << ": resolved-calls=" << iterResolvedCalls
           << ", total-targets=" << iterTotalTargets
           << ", new-callee-pairs=" << iterNewCalleePairs
           << ", new-summary-edges=" << iterNewSummaryEdges
           << ", skipped-no-symbol=" << iterSkippedNoSymbol << "\n");

    if (iterNewSummaryEdges == 0) {
      composedConverged = true;
      break;
    }

    auto tIterSolve = std::chrono::steady_clock::now();
    auto nextSolver = std::make_unique<gracfl::SolverFWGramParallel>(
        combinedEdges, *EB.getGrammar(), cflThreads);
    nextSolver->runCFL();
    composedSolver = std::move(nextSolver);
    CG_LOG("TIMER comp-iter-solve #" << iterNo << " "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tIterSolve).count()
           << " ms, final edges=" << composedSolver->getEdgeCount() << "\n");
  }

  if (!composedConverged) {
    errs() << "[UNSOUND-RISK] Composed summary loop hit iteration cap ("
           << kMaxCompIterations << ") before fixed point; "
           << "result may under-approximate\n";
    soundnessCapped = true;
  }

  CG_LOG("Compositional solve: resolved " << resolvedCalls
         << " indirect-call observations with " << totalTargets
         << " total targets, " << newCalleePairs << " new callee pairs, "
         << newSummaryEdges << " new summary edges"
         << " (skipped " << skippedNoSymbol << " without symbol)\n");

  const auto &finalComposedGraph = composedSolver->getReachability();
  const bool allocatorUpdated =
      findCustomAllocatorsComposed(finalComposedGraph, composedSymbolToDense);
  if (allocatorUpdated) {
    CG_LOG("Compositional solve: custom allocator candidates updated\n");
  }

  return true;
}

void CallGraphPass::dumpGlobals(raw_ostream &OS) {
  CG_LOG("\n[dumpGlobals]\n");
  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  const auto &solverEdges = useDense ? denseEdges : EB.getEdges();
  auto solver = std::make_unique<gracfl::SolverFWGramParallel>(solverEdges, *EB.getGrammar(), cflThreads);
  solver->runCFL();
  const auto &outputCFLGraph = solver->getReachability();
  for (auto &it : Ctx->Gobjs) {
    Value *GV = it.second;
    NodeIndex valNode;
    if (useDense) {
      valNode = getDenseID(NF.getValueNodeFor(GV));
      if (valNode == UINT32_MAX) continue;
    } else {
      valNode = getCanonicalNode(NF.getValueNodeFor(GV));
    }
    if (valNode != AndersNodeFactory::InvalidIndex) {
      assert(valNode < outputCFLGraph.size() && "Global node out of CFL graph range");
      auto &cflSect = outputCFLGraph[valNode][EB.getLabelV()];
      if (cflSect.empty())
        continue;
      CG_DEBUG("GlobalVar: " << GV->getName() << " : " << valNode << " ->\n");
      for (auto idx : cflSect) {
        NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
        if (origIdx == valNode)
          continue;
        if (NF.isSpecialNode(origIdx)) {
          CG_DEBUG("\tSpecialNode: " << origIdx << "\n");
          continue;
        }
        const Value *CV = NF.getValueForNode(origIdx);
        if (CV == NULL) {
          CG_DEBUG("\tNoValue: " << origIdx << "\n");
          continue;
        }
        CG_DEBUG("\t" << *CV << " : " << origIdx << "\n");
      }
    }
  }
  CG_LOG("\n[End of dumpGlobals]\n");
}
