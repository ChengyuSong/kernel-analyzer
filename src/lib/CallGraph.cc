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
#include <fstream>
#include <map>
#include <numeric>
#include <set>
#include <thread>
#include <unordered_map>
#include <unordered_set>

#include "CallGraph.h"
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
    if (dstTy && dstTy == srcTy && isa<StructType>(dstTy) && curDL) {
      emitFieldwiseCopyEdges(srcNode, dstNode, dstTy, 0);
    } else {
      addAssignmentEdge(srcNode, dstNode);
      addAssignmentEdge(dstNode, srcNode);
      addFieldWildcardLoop(srcNode);
      addFieldWildcardLoop(dstNode);
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
    addFieldWildcardLoop(srcAddr);
    addFieldWildcardLoop(dstAddr);
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

bool CallGraphPass::handleCall(const CallBase *CS, const Function *CF) {
  if (CF->isIntrinsic()) {
    // handle intrinsic functions
    return false;
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

  // handle args:
  // - fixed arguments map to formal params
  // - variadic tail (if any) maps to the callee's vararg summary node
  unsigned numArgs = CS->arg_size();
  unsigned numFormals = CF->arg_size();
  unsigned minArgs = std::min(numArgs, numFormals);
  for (unsigned i = 0; i < minArgs; i++) {
    Value *arg = CS->getArgOperand(i);
    if (!arg->getType()->isPointerTy())
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
    NodeIndex varargNode = NF.getVarargNodeFor(CF);
    if (varargNode == AndersNodeFactory::InvalidIndex)
      varargNode = NF.createVarargNode(CF);
    varargNode = getCanonicalNode(varargNode);
    for (unsigned i = numFormals; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
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

  // handle return
  if (CF->getReturnType()->isPointerTy()) {
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
    addFieldWildcardLoop(containerNode);
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
    if (!arg->getType()->isPointerTy())
      continue; // skip non-pointer args
    NodeIndex argNode = getRepNodeForValue(arg);
    assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
    Value *farg = CF->getArg(i);
    NodeIndex formalNode = getRepNodeForValue(farg);
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    EB.removeAssignmentEdges(getCanonicalNode(argNode), getCanonicalNode(formalNode));
  }
  // Remove variadic-tail edges
  if (CF->isVarArg()) {
    NodeIndex varargNode = getCanonicalNode(NF.getVarargNodeFor(CF));
    assert(varargNode != AndersNodeFactory::InvalidIndex && "Vararg node not found!");
    for (unsigned i = numFormals; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue;
      NodeIndex argNode = getRepNodeForValue(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      EB.removeAssignmentEdges(getCanonicalNode(argNode), varargNode);
    }
  }

  // handle return
  if (CF->getReturnType()->isPointerTy()) {
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
  // In field mode, canonical ConstantExpr-GEP nodes need their field edges
  // from the base emitted (once per module) wherever they appear as operands.
  if (EB.hasFieldLabels()) {
    if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
      if (CE->getOpcode() == Instruction::GetElementPtr)
        ensureConstGEPFieldEdges(CE);
    }
  }
  return getCanonicalNode(n);
}

NodeIndex CallGraphPass::getRepDerefNode(NodeIndex ptrNode) {
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

void CallGraphPass::addFieldWildcardLoop(NodeIndex n) {
  if (n == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex canon = getCanonicalNode(n);
  if (moduleFieldWildcardRoots.insert(canon).second)
    EB.addFieldWildcardSelfLoop(canon);
}

void CallGraphPass::applyFieldFallback(NodeIndex baseNode, NodeIndex resultNode) {
  addAssignmentEdge(baseNode, resultNode);
  addFieldWildcardLoop(baseNode);
}

void CallGraphPass::mergeCanonicalClasses(NodeIndex a, NodeIndex b) {
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
  gracfl::SolverFWGramParallel sub(subEdges, *EB.getGrammar(), cflThreads);
  sub.runCFL();
  const auto &graph = sub.getReachability();

  std::vector<uint32_t> nodeToSCC;
  uint32_t numSCCs = 0;
  computeVSCC(graph, EB.getLabelV(), nodeToSCC, numSCCs);

  std::vector<NodeIndex> sccRep(numSCCs, AndersNodeFactory::InvalidIndex);
  size_t merged = 0;
  for (uint32_t ln = 0; ln < toCanon.size() && ln < nodeToSCC.size(); ln++) {
    uint32_t scc = nodeToSCC[ln];
    if (scc == UINT32_MAX)
      continue;
    if (sccRep[scc] == AndersNodeFactory::InvalidIndex) {
      sccRep[scc] = toCanon[ln];
    } else {
      mergeCanonicalClasses(sccRep[scc], toCanon[ln]);
      merged++;
    }
  }
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
  const uint32_t N = toOrig.size();
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
  std::unordered_map<uint32_t, const Function *> funcRootOf;
  std::vector<std::pair<uint32_t, uint32_t>> seeds; // (class, root id)
  uint32_t nextRoot = 0;
  for (uint32_t n = 0; n < N; n++) {
    if (!inSlice.empty() && !inSlice[n]) continue;
    auto fit = funcOfCanon.find(toOrig[n]);
    const bool isFunc = fit != funcOfCanon.end();
    if (!hasIn[n] || isFunc) {
      uint32_t rid = nextRoot++;
      seeds.emplace_back(n, rid);
      if (isFunc) funcRootOf[rid] = fit->second;
    }
  }

  // Solver core: union-find clusters + bit-plane difference propagation.
  // Exact-fact joins are transitive (same (o, s) => same abstract cell),
  // so cluster members MERGE into one class — no hub nodes, no duplicated
  // fact sets, no k-fold re-propagation. The (o, X) cluster is unioned
  // with every exact-shift cluster of the same origin when both exist
  // (VX; identical fixpoint to the former bidirectional hub links, which
  // equalized member fact sets anyway). Propagation is word-parallel:
  // OR whole planes across a-edges, plane-rotated OR across f-edges.
  CG_LOG("FlowsTo: minted " << nextRoot << " roots ("
         << funcRootOf.size() << " function), " << wildcardNodes.size()
         << " wildcard nodes, " << NSHIFT << " shift planes\n");
  std::vector<uint32_t> ufp(N), ufrank(N, 0);
  for (uint32_t i = 0; i < N; i++) ufp[i] = i;
  auto find = [&](uint32_t x) {
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
  std::vector<std::vector<llvm::BitVector>> R(N), RB(N), dirty(N),
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
  std::vector<uint32_t> worklist;
  std::vector<bool> inWL(N, false);
  auto push = [&](uint32_t n) {
    if (!inWL[n]) { inWL[n] = true; worklist.push_back(n); }
  };
  uint64_t factCount = 0;
  auto ensure = [&](llvm::BitVector &bv) {
    if (bv.size() < nextRoot) bv.resize(nextRoot);
  };
  // OR src natively into rep n's plane s. Bits new to the class enter all
  // three deltas; bits previously only bridged are promoted (their joins
  // and a/f propagation already ran — only bridge-crossing is new).
  auto addBits = [&](uint32_t n, uint32_t s, const llvm::BitVector &src) {
    if (src.none()) return;
    ensure(R[n][s]);
    llvm::BitVector nb(src);
    ensure(nb);
    nb.reset(R[n][s]);
    if (nb.none()) return;
    llvm::BitVector promoted;
    if (RB[n][s].size()) {
      promoted = nb;
      promoted &= RB[n][s];
      RB[n][s].reset(nb);
      nb.reset(promoted); // truly-new bits only
    }
    R[n][s] |= nb;
    if (promoted.size() && promoted.any()) {
      R[n][s] |= promoted;
      ensure(dirtyBr[n][s]);
      dirtyBr[n][s] |= promoted;
    }
    if (nb.any()) {
      ensure(dirty[n][s]);
      dirty[n][s] |= nb;
      ensure(jdirty[n][s]);
      jdirty[n][s] |= nb;
      ensure(dirtyBr[n][s]);
      dirtyBr[n][s] |= nb;
      factCount += nb.count();
    }
    push(n);
  };
  auto addFact = [&](uint32_t n, uint32_t s, uint32_t o) {
    ensure(R[n][s]);
    if (R[n][s].test(o)) return;
    if (RB[n][s].size() && RB[n][s].test(o)) {
      RB[n][s].reset(o);
      R[n][s].set(o);
      ensure(dirtyBr[n][s]);
      dirtyBr[n][s].set(o);
      push(n);
      return;
    }
    R[n][s].set(o);
    ensure(dirty[n][s]);
    dirty[n][s].set(o);
    ensure(jdirty[n][s]);
    jdirty[n][s].set(o);
    ensure(dirtyBr[n][s]);
    dirtyBr[n][s].set(o);
    factCount++;
    push(n);
  };
  // OR src as bridged: skipped where already known either way; bridged
  // bits run joins and a/f propagation but never dirtyBr.
  auto addBitsBridged = [&](uint32_t n, uint32_t s,
                            const llvm::BitVector &src) {
    if (src.none()) return;
    ensure(RB[n][s]);
    llvm::BitVector nb(src);
    ensure(nb);
    nb.reset(RB[n][s]);
    if (R[n][s].size()) nb.reset(R[n][s]);
    if (nb.none()) return;
    RB[n][s] |= nb;
    ensure(dirty[n][s]);
    dirty[n][s] |= nb;
    ensure(jdirty[n][s]);
    jdirty[n][s] |= nb;
    factCount += nb.count();
    push(n);
  };
  size_t mergeCount = 0;
  auto merge = [&](uint32_t a, uint32_t b) -> uint32_t {
    a = find(a); b = find(b);
    if (a == b) return a;
    if (ufrank[a] < ufrank[b]) std::swap(a, b);
    if (ufrank[a] == ufrank[b]) ufrank[a]++;
    ufp[b] = a;
    mergeCount++;
    for (uint32_t s = 0; s < NSHIFT; s++) {
      // Propagation delta: only facts genuinely new to the keeper. The
      // keeper's old facts reach the loser's former neighbors via the
      // one-time direct push below, NOT via a full re-dirty (that made
      // every merge re-offer the whole fact set on the whole edge list).
      if (R[b][s].any()) {
        llvm::BitVector nb(R[b][s]);
        ensure(nb);
        nb.reset(R[a][s]);
        if (nb.any()) {
          // Split: bits only bridged at the keeper are promotions
          // (bridge-crossing newly allowed); the rest are fully new.
          llvm::BitVector promoted(nb);
          promoted &= RB[a][s];
          RB[a][s].reset(nb);
          nb.reset(promoted);
          ensure(R[a][s]);
          R[a][s] |= nb;
          R[a][s] |= promoted;
          ensure(dirty[a][s]);
          dirty[a][s] |= nb;
          ensure(dirtyBr[a][s]);
          dirtyBr[a][s] |= nb;
          dirtyBr[a][s] |= promoted;
        }
      }
      if (RB[b][s].any()) {
        llvm::BitVector nb(RB[b][s]);
        ensure(nb);
        nb.reset(R[a][s]);
        nb.reset(RB[a][s]);
        if (nb.any()) {
          ensure(RB[a][s]);
          RB[a][s] |= nb;
          ensure(dirty[a][s]);
          dirty[a][s] |= nb;
        }
      }
      if (dirty[b][s].any()) { ensure(dirty[a][s]); dirty[a][s] |= dirty[b][s]; }
      if (dirtyBr[b][s].any()) {
        ensure(dirtyBr[a][s]);
        dirtyBr[a][s] |= dirtyBr[b][s];
      }
      R[b][s].clear();
      RB[b][s].clear();
      dirty[b][s].clear();
      dirtyBr[b][s].clear();
      // Join backlog: the merged cell list must be swept with the full
      // merged fact set (filtered by `joined`, which keeps only facts
      // that reached BOTH sides' cells).
      if (R[a][s].size()) { ensure(jdirty[a][s]); jdirty[a][s] |= R[a][s]; }
      if (RB[a][s].size()) { ensure(jdirty[a][s]); jdirty[a][s] |= RB[a][s]; }
      jdirty[b][s].clear();
      if (joined[a][s].size() && joined[b][s].size()) {
        ensure(joined[a][s]); ensure(joined[b][s]);
        joined[a][s] &= joined[b][s];
      } else {
        joined[a][s].clear();
      }
      joined[b][s].clear();
    }
    // One-time pushes along the loser's moved lists (keeper's old lists
    // only ever need deltas): merged facts along a/f edges (emission is
    // native — value flow launders provenance), natives across bridges.
    for (uint32_t t : outA[b]) {
      uint32_t tt = find(t);
      if (tt == a) continue;
      for (uint32_t s = 0; s < NSHIFT; s++) {
        if (R[a][s].any()) addBits(tt, s, R[a][s]);
        if (RB[a][s].any()) addBits(tt, s, RB[a][s]);
      }
    }
    for (auto [t, r] : outF[b]) {
      uint32_t tt = find(t);
      for (uint32_t s = 0; s < NSHIFT; s++) {
        uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + r) % NB;
        if (tt == a && s2 == s) continue;
        if (R[a][s].any()) addBits(tt, s2, R[a][s]);
        if (RB[a][s].any()) addBits(tt, s2, RB[a][s]);
      }
    }
    for (uint32_t br : bridgesOf[b]) {
      uint32_t bb = find(br);
      if (bb == a) continue;
      for (uint32_t s = 0; s < NSHIFT; s++)
        if (R[a][s].any()) addBitsBridged(bb, s, R[a][s]);
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
        if (R[a][s].any()) addBits(a, SHIFT_X, R[a][s]);
        if (RB[a][s].any()) addBitsBridged(a, SHIFT_X, RB[a][s]);
      }
    wflag[a] |= wflag[b];
    push(a);
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
  // find() on read.
  boost::unordered_flat_map<uint64_t, uint32_t> clusterRep;
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
    for (uint32_t s = 0; s < NSHIFT; s++) {
      if (R[x][s].any()) addBitsBridged(y, s, R[x][s]);
      if (R[y][s].any()) addBitsBridged(x, s, R[y][s]);
    }
  };
  auto joinCluster = [&](uint32_t cell, uint32_t o, uint32_t s) {
    const uint64_t key = (uint64_t)o * NSHIFT + s;
    auto [it, ins] = clusterRep.emplace(key, find(cell));
    if (!ins) {
      it->second = merge(it->second, cell);
      return;
    }
    if (NB == 0) return;
    // VX linking: bridge the (o, X) cluster with each exact cluster of o.
    if (s == SHIFT_X) {
      for (uint64_t ek : shiftKeysOf[o]) {
        auto eIt = clusterRep.find(ek);
        addBridge(clusterRep.find(key)->second, eIt->second);
      }
    } else {
      shiftKeysOf[o].push_back(key);
      auto xIt = clusterRep.find((uint64_t)o * NSHIFT + SHIFT_X);
      if (xIt != clusterRep.end())
        addBridge(it->second, xIt->second);
    }
  };
  for (auto [n, rid] : seeds) addFact(find(n), 0, rid);

  size_t iterations = 0;
  llvm::BitVector d;
  while (!worklist.empty()) {
    uint32_t n = worklist.back();
    worklist.pop_back();
    inWL[n] = false;
    if (find(n) != n) continue; // merged away; keeper carries the state
    iterations++;
    if ((iterations & ((1u << 20) - 1)) == 0)
      CG_LOG("FlowsTo progress: " << iterations << " pops, " << factCount
             << " facts, " << clusterRep.size() << " clusters, "
             << mergeCount << " merges, "
             << std::chrono::duration_cast<std::chrono::milliseconds>(
                    std::chrono::steady_clock::now() - tStart).count()
             << " ms\n");
    if (outA[n].size() + outF[n].size() + cellsOf[n].size() +
            bridgesOf[n].size() >
        compactMark[n])
      compactLists(n);
    for (uint32_t s = 0; s < NSHIFT && find(n) == n; s++) {
      // Cell join (M ::= -d V d | -d VX d): sweep the join backlog —
      // facts never yet pushed to this class's full cell list — against
      // the per-fact clusters. A merge can absorb n itself: stop; the
      // keeper inherits the backlog and is re-queued.
      if (jdirty[n][s].any()) {
        llvm::BitVector todo(jdirty[n][s]);
        jdirty[n][s].reset();
        if (!cellsOf[n].empty()) {
          if (joined[n][s].size()) { ensure(todo); todo.reset(joined[n][s]); }
          ensure(joined[n][s]);
          for (int o = todo.find_first(); o != -1; o = todo.find_next(o)) {
            bool aborted = false;
            for (size_t ci = 0; ci < cellsOf[n].size(); ci++) {
              joinCluster(cellsOf[n][ci], (uint32_t)o, s);
              if (find(n) != n) { aborted = true; break; }
            }
            if (aborted) break;
            // A merge that kept n may have intersected/cleared the
            // plane; re-ensure. Cells appended mid-loop were covered
            // (the inner bound re-reads cellsOf[n].size()).
            ensure(joined[n][s]);
            joined[n][s].set((unsigned)o);
          }
          if (find(n) != n) break;
        }
      }
      // Bridge crossings: native backlog only, arriving bridged.
      if (dirtyBr[n][s].any() && !bridgesOf[n].empty()) {
        llvm::BitVector db(dirtyBr[n][s]);
        dirtyBr[n][s].reset();
        for (uint32_t br : bridgesOf[n]) {
          uint32_t bb = find(br);
          if (bb != n) addBitsBridged(bb, s, db);
        }
      } else {
        dirtyBr[n][s].reset();
      }
      if (dirty[n][s].none()) continue;
      d = dirty[n][s];
      dirty[n][s].reset();
      // Wildcard (fx self-loop): new facts also hold at unknown shift,
      // kind preserved (retroactive projection on wflag gain is in merge).
      if (NB > 0 && wflag[n] && s != SHIFT_X) {
        llvm::BitVector dNat(d), dBr(d);
        ensure(dNat); ensure(dBr);
        dNat &= R[n][s];
        dBr &= RB[n][s];
        if (dNat.any()) addBits(n, SHIFT_X, dNat);
        if (dBr.any()) addBitsBridged(n, SHIFT_X, dBr);
      }
      // Propagate the delta: whole-plane OR along a-edges, plane-rotated
      // OR along f-edges (X absorbs). Emission is native — value flow
      // launders bridge provenance, exactly like the grammar (M-hops
      // are separated by a-steps in every V derivation).
      for (uint32_t t : outA[n]) {
        uint32_t tt = find(t);
        if (tt != n) addBits(tt, s, d);
      }
      for (auto [t, r] : outF[n]) {
        uint32_t tt = find(t);
        uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + r) % NB;
        if (tt != n || s2 != s) addBits(tt, s2, d);
      }
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
         << "(vs pairwise V), " << clusterRep.size() << " cell clusters, "
         << bridgeCount << " VX bridges, "
         << iterations << " worklist pops, "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tStart).count() << " ms\n");

  // Resolution: origins at the fptr class whose shift is zero or unknown
  // (an exact nonzero shift is a provably misaligned pointer, not a call
  // target), intersected with function roots, then the standard filters.
  size_t resolved = 0, totalTargets = 0;
  for (auto *CS : Ctx->IndirectCallInsts) {
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    NodeIndex fn = NF.getValueNodeFor(fptr);
    if (fn == AndersNodeFactory::InvalidIndex) continue;
    auto dIt = toDense.find(getCanonicalNode(fn));
    if (dIt == toDense.end()) continue;
    std::string csStruct; unsigned csField = 0;
    bool hasKey = getCallSiteFieldKey(fptr, csStruct, csField);
    FuncSet targets;
    const uint32_t rep = find(dIt->second);
    auto collect = [&](const llvm::BitVector &plane) {
      for (int o = plane.find_first(); o != -1; o = plane.find_next(o)) {
        auto rIt = funcRootOf.find((uint32_t)o);
        if (rIt == funcRootOf.end()) continue;
        Function *F = getFuncDef(const_cast<Function *>(rIt->second));
        if (!isCompatible(CS, F)) continue;
        if (hasKey && !fieldFilterAccepts(F, csStruct, csField)) continue;
        targets.insert(F);
      }
    };
    collect(R[rep][0]);
    if (RB[rep][0].size()) collect(RB[rep][0]);
    if (NB > 0) {
      collect(R[rep][SHIFT_X]);
      if (RB[rep][SHIFT_X].size()) collect(RB[rep][SHIFT_X]);
    }
    if (!targets.empty()) { resolved++; totalTargets += targets.size(); }
    for (const Function *F : targets)
      Ctx->Callees[CS].insert(F);
  }
  CG_LOG("FlowsTo: resolved " << resolved << " icalls, "
         << totalTargets << " targets\n");
  return true;
}

void CallGraphPass::ensureConstGEPFieldEdges(const ConstantExpr *CE) {
  if (!EB.hasFieldLabels() || !curDL)
    return;
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

  SmallVector<int64_t, 4> levels;
  if (!decomposeGEPLevels(GEP, *curDL, levels)) {
    applyFieldFallback(baseNode, node);
    return;
  }
  if (levels.empty())
    addAssignmentEdge(baseNode, node);
  else
    addFieldChainEdges(baseNode, node, levels);
}

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
    if (!ET || !containsPointerType(ET))
      continue;

    NodeIndex ptrNode = getRepNodeForValue(CS.getArgOperand(aIdx));
    if (ptrNode == AndersNodeFactory::InvalidIndex)
      continue;
    NodeIndex derefNode = getRepDerefNode(ptrNode);

    if (CI.Type == InlineAsm::isOutput) {
      // =*m: store to *ptr — conservatively, any ptr-typed direct input could be stored
      for (unsigned j = 0; j < Constraints.size(); j++) {
        if (Constraints[j].Type != InlineAsm::isInput)
          continue;
        int sIdx = cToArg[j];
        if (sIdx < 0 || (unsigned)sIdx >= CS.arg_size())
          continue;
        Value *srcVal = CS.getArgOperand(sIdx);
        if (!srcVal->getType()->isPointerTy() || Constraints[j].isIndirect)
          continue;
        NodeIndex srcNode = getRepNodeForValue(srcVal);
        if (srcNode == AndersNodeFactory::InvalidIndex)
          continue;
        CG_DEBUG("InlineAsm: indirect store edge from input arg " << sIdx
                 << " to deref of output arg " << aIdx << "\n");
        addAssignmentEdge(srcNode, derefNode);
      }
    } else if (CI.Type == InlineAsm::isInput) {
      // *m: load from *ptr — loaded value could flow to ptr-typed outputs
      if (CS.getType()->isPointerTy() || containsPointerType(CS.getType())) {
        NodeIndex dstNode = getRepNodeForValue(&CS);
        if (dstNode != AndersNodeFactory::InvalidIndex) {
          CG_DEBUG("InlineAsm: indirect load edge from deref of input arg " << aIdx
                   << " to result\n");
          addAssignmentEdge(derefNode, dstNode);
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
        CG_DEBUG("InlineAsm: call target \"" << funcName << "\" not found in Funcs\n");
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
      if (CF->getReturnType()->isPointerTy()) {
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

  // Check for function pointer cycles
  if (!CS.getCalledFunction()) {
    Value *CO = CS.getCalledOperand()->stripPointerCastsAndAliases();
    if (auto *Load = dyn_cast<LoadInst>(CO)) {
      CG_DEBUG("Indirect call through loaded function pointer: " << *Load->getPointerOperand() << "\n");
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

void CallGraphPass::InstHandler::visitLoadInst(LoadInst &I) {
  if (!containsPointerType(I.getType())) {
    // XXX only consider pointer type
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

  // Aggregate loads read every field through the whole-object cell; the
  // wildcard loop keeps per-field stores reachable from it.
  if (CGP.EB.hasFieldLabels() && I.getType()->isAggregateType())
    CGP.addFieldWildcardLoop(ptrNode);

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  CGP.addAssignmentEdge(derefNode, valNode);
}

void CallGraphPass::InstHandler::visitStoreInst(StoreInst &I) {
  Value *val = I.getOperand(0);
  if (!containsPointerType(val->getType())) {
    // XXX only consider pointer type
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

  // Aggregate stores write every field through the whole-object cell.
  if (CGP.EB.hasFieldLabels() && val->getType()->isAggregateType())
    CGP.addFieldWildcardLoop(ptrNode);

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
      CGP.applyFieldFallback(ptrNode, valNode);
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

void CallGraphPass::InstHandler::visitPHINode(PHINode &PHI) {
  if (!containsPointerType(PHI.getType())) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&PHI);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find phi dst node");
  for (unsigned i = 0, e = PHI.getNumIncomingValues(); i != e; ++i) {
    Value *src = PHI.getIncomingValue(i);

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in PHI: " << *src << "\n");
      continue;
    }

    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
    // if (srcNode == AndersNodeFactory::InvalidIndex) {
    //   srcNode = CGP.NF.createValueNode(src);
    //   CG_DEBUG("Create value node " << srcNode << " for PHI src " << *src << "\n");
    // }
    CGP.addAssignmentEdge(srcNode, dstNode);
  }
}

void CallGraphPass::InstHandler::visitSelectInst(SelectInst &I) {
  if (!containsPointerType(I.getType())) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find select dst node");
  // NodeIndex dstNode = CGP.NF.createValueNode(&I);
  for (unsigned i = 1; i < I.getNumOperands(); i++) {
    Value *src = I.getOperand(i);

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in Select: " << *src << "\n");
      continue;
    }

    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node");
    // if (srcNode == AndersNodeFactory::InvalidIndex) {
    //   srcNode = CGP.NF.createValueNode(src);
    //   CG_DEBUG("Create value node " << srcNode << " for select src " << *src << "\n");
    // }
    CGP.addAssignmentEdge(srcNode, dstNode);
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
  // any field (disguised GEP); absorb with the wildcard loop at the source.
  if (CGP.EB.hasFieldLabels())
    CGP.addFieldWildcardLoop(srcNode);
  CGP.addAssignmentEdge(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitBinaryOperator(BinaryOperator &I) {
  if (!I.getType()->isIntegerTy())
    return;

  // Check if exactly one operand is pointer-derived and the other is constant.
  NodeIndex srcNode = AndersNodeFactory::InvalidIndex;
  bool otherIsConst = false;
  for (unsigned i = 0; i < 2; i++) {
    NodeIndex n = CGP.getRepNodeForValue(I.getOperand(i));
    if (n != AndersNodeFactory::InvalidIndex && !CGP.NF.isSpecialNode(n)) {
      srcNode = n;
      otherIsConst = isa<Constant>(I.getOperand(1 - i));
    }
  }
  if (srcNode == AndersNodeFactory::InvalidIndex)
    return;

  if (!otherIsConst) {
    WARNING("BinOp on pointer-derived integer with non-constant operand: " << I << "\n");
    return;
  }

  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
    CG_DEBUG("BinOp: created value node " << dstNode << " for " << I << "\n");
  }
  CG_DEBUG("BinOp: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.addAssignmentEdge(srcNode, dstNode);
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
    // Record direct function store into struct field
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      funcFieldStores[canonStoredFunc].insert(
          {enclosingStruct, static_cast<unsigned>(enclosingFieldIdx)});
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
      addFieldWildcardLoop(addrNode);
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

bool CallGraphPass::doInitialization(Module *M) {
  if (iteration == 0 && M == Ctx->Modules.front().first) {
    canonicalNodeMap.clear();
    canonicalClassMembers.clear();
    moduleIndirectCallInsts.clear();
    fieldAliasMap.clear();
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

    // collect address-taken functions
    if (F.hasAddressTaken()) {
      Ctx->AddressTakenFuncs.insert(&F);

      // only add fval -> fobj edge in call graph analysis?
      // create a value node for function pointer
      NodeIndex valNode = NF.createValueNode(&F);
      (void)valNode;
    }

    // Populate AllocFuncs for all functions matching known allocator names,
    // regardless of whether they are declarations or definitions
    {
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
    // Deterministic per-icall resolution dump (one line per pair; sort the
    // lines to diff runs — FuncSet iteration order is not stable).
    if (VerboseLevel >= 2) {
      for (auto &it : Ctx->Callees) {
        const CallBase *CS = it.first;
        if (CS->isInlineAsm() || CS->getCalledFunction())
          continue;
        for (const Function *F : it.second)
          errs() << "ICALL " << CS->getFunction()->getName() << " :: " << *CS
                 << " -> " << F->getName() << "\n";
      }
    }
    // check if all address-taken functions are used in indirect calls
    size_t used = 0;
    for (const Function *F : Ctx->AddressTakenFuncs) {
      bool found = false;
      for (auto &it : Ctx->Callees) {
        FuncSet &FS = it.second;
        if (FS.find(F) != FS.end()) {
          found = true;
          break;
        }
      }
      if (found) {
        used++;
      } else {
        WARNING("Address-taken function not used in indirect calls: " << F->getName() << "\n");
        // print all users
        for (auto *U : F->users()) {
          if (!isa<Function>(U)) // skip personality
            errs() << "  User: " << *U << "\n";
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
           !Ctx->AllocFuncs.count(PF) && !Ctx->ContainerFuncs.count(PF) &&
           !shouldSkipFunction(PF);
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
            assert(callNode != AndersNodeFactory::InvalidIndex &&
                   "CallBase node not found for indirect allocator target");
            AllocSites.insert(callNode);
            NodeIndex heapObj = NF.createOpaqueObjectNode(CS, true);
            EB.addDereferenceEdges(callNode, heapObj);
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

    // Merge pointer args: fixed actual→formal, variadic tail→vararg node
    unsigned numArgs = CS->arg_size();
    unsigned numFormals = CF->arg_size();
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
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
    if (CF->isVarArg()) {
      NodeIndex varargNode = NF.getVarargNodeFor(CF);
      if (varargNode == AndersNodeFactory::InvalidIndex)
        continue;
      for (unsigned i = numFormals; i < numArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!arg->getType()->isPointerTy())
          continue;
        if (shouldSkipValue(arg))
          continue;
        NodeIndex argNode = NF.getValueNodeFor(arg);
        if (argNode != AndersNodeFactory::InvalidIndex)
          globalUnion(argNode, varargNode);
      }
    }

    // Merge return: returnNode → callsite
    if (CF->getReturnType()->isPointerTy()) {
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

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

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
          Ctx->AllocFuncs.count(&F) ||
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
    if (CFLFlowsTo && !CFLCompositional) {
      if (runFlowsToResolution()) {
        iteration++;
        return false;
      }
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
