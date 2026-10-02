/*
 * CFL-reachability call-graph baseline (see CFLCGPass.h).
 *
 * Copyright (C) 2015 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/SHA256.h>

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <map>
#include <numeric>
#include <set>
#include <thread>
#include <unordered_map>
#include <unordered_set>

#include "Annotation.h"
#include "BaselineFlags.h"
#include "CFLCGPass.h"
#include "SCC.h"
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


} // namespace

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


CFLCGPass::CFLCGPass(GlobalContext *Ctx_,
                     const std::vector<std::string> &grammarLines,
                     const std::string &grammarFile)
    : CallGraphPass(Ctx_), cflThreads(detectPhysicalCoreCount()) {
  if (grammarFile.empty())
    EB.initialize(Graph, grammarLines);
  else
    EB.initialize(Graph, grammarFile);
}

bool CFLCGPass::compositional() const { return CFLCompositional; }

bool CFLCGPass::perTUSolve() const {
  return CFLCompositional && CompressedGraphInputs.empty();
}

bool CFLCGPass::exportsCallBoundaries() const {
  // In compositional mode, fall through to create on-demand arg/ret nodes
  // so cross-TU data flow is captured in the compressed graph.
  return !CompressedGraphOutput.empty() || CFLCompositional;
}

void CFLCGPass::moduleBuilt(Module *M, size_t edgeStart, size_t edgeEnd) {
  // EB's labelled edges 2i, 2i+1 are the graph's typed edge i.
  if (M == Ctx->Modules.front().first)
    moduleEdgeRanges.clear();
  // Track per-module edge ranges so repair mode can recompute selected modules.
  moduleEdgeRanges[M] = {2 * edgeStart, 2 * edgeEnd};
  // Per-TU: solve and compress this module's edges (including edge-empty modules
  // so cache coverage metadata can represent the full input set).
  if (perTUSolve())
    solveAndCompressPerTU(M, 2 * edgeStart, 2 * edgeEnd);
}

std::vector<size_t>
CFLCGPass::typedEdgeIndices(const std::vector<size_t> &idx) const {
  std::vector<size_t> typed;
  typed.reserve(idx.size() / 2);
  for (size_t k = 0; k < idx.size(); k++) {
    if (idx[k] % 2 == 0) {
      assert(k + 1 < idx.size() && idx[k + 1] == idx[k] + 1 &&
             "a typed edge's labelled pair was split");
      typed.push_back(idx[k] / 2);
    } else {
      assert(k > 0 && idx[k - 1] == idx[k] - 1 &&
             "a typed edge's labelled pair was split");
    }
  }
  return typed;
}

bool CFLCGPass::solve() {
  bool Changed = false;
  {
    logHighDegreeNodes(1000, 20);

    // Pre-solve copy/field merge before the monolithic dense mapping.
    if (CFLPreSolveMerge && !CFLCompositional &&
        (!CFLPreSolveOnce || iteration == 0))
      preSolveCopyFieldMerge(nullptr);

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

bool CFLCGPass::findCustomAllocators(const cfl_result_t &outputCFLGraph,
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
                Graph.addDeref(callNode, heapObj);
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


bool CFLCGPass::lookupRetDense(
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


bool CFLCGPass::lookupArgDense(
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


bool CFLCGPass::lookupVarargDense(
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


bool CFLCGPass::findCustomAllocatorsComposed(
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


bool CFLCGPass::handleIndirectCall(const cfl_result_t &outputCFLGraph,
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
        // Field filter retired from the answer path (see the flows-to
        // extraction site for the full rationale): counting only.
        if (hasCallSiteField &&
            !fieldFilterAccepts(CF, callSiteStruct, callSiteFieldIdx))
          CG_LOG("FieldFilter(retired): would reject " << CF->getName()
                 << " for " << callSiteStruct << " field "
                 << callSiteFieldIdx << "\n");
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
            Graph.addDeref(callNode, heapObj);
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


void CFLCGPass::buildDenseMapping() {
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


uint32_t CFLCGPass::getDenseID(NodeIndex origNode) const {
  NodeIndex canonical = getCanonicalNode(origNode);
  if (canonical < origToDense.size())
    return origToDense[canonical];
  return UINT32_MAX;
}


void CFLCGPass::solveAndCompressPerTU(Module *M, size_t edgeStart, size_t edgeEnd) {
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
    {
      const std::vector<size_t> typedIdx = typedEdgeIndices(tuEdgeIndices);
      preSolveCopyFieldMerge(&typedIdx);
    }

  // Diagnostic: high-degree constraint nodes are the hubs whose deref cells
  // drive M-fusion; dump them with their IR values for attribution.
  if (VerboseLevel >= 2) {
    std::vector<std::pair<NodeIndex, size_t>> topNodes;
    Graph.analyzeHighDegreeNodes(500, 15, &topNodes);
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


void CFLCGPass::dumpVSnapshot(StringRef Path) {
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


void CFLCGPass::dumpComposedVSnapshot(StringRef Path) {
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


void CFLCGPass::computeVSCC(const cfl_result_t &outputCFLGraph,
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


void CFLCGPass::compressConstraintGraph(
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


void CFLCGPass::exportCompressedGraph(StringRef Path) {
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


bool CFLCGPass::runCompositionalSolve() {
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


// Fptr-flow slicing (--cfl-fptr-slice): drop constraint-graph components
// that cannot participate in any function-pointer derivation. Function
// pointers originate only at address-taken Function value nodes (type-free
// ground truth, robust to opaque pointers), and every CFL derivation follows
// constraint edges; therefore a node in a weakly-connected component that
// contains no Function node can never contribute a callee fact. Keep exactly
// the seeded components.
void CFLCGPass::sliceEdgesToFptrComponents(std::vector<size_t> &idx) {
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

