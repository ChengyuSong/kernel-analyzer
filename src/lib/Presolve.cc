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

// Presolve.cc: pre-solve quotient of the memory-free sublanguage (V-components or mutual-flow SCCs).
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

void CallGraphPass::preSolveCopyFieldMerge(const std::vector<size_t> *idx) {
  // Edges of the memory-free sublanguage: copy and field steps (every
  // kind but Deref), each standing for itself and its implied inverse.
  // Source values must not glue unrelated classes: two slots holding the
  // same function/global would chain-merge through it (common-sink smear),
  // manufacturing false targets. Drop their edges from the sublanguage.
  auto isBarrierNode = [&](NodeIndex canon) {
    if (NF.isSpecialNode(canon))
      return true;
    // Named-cell shadows hold one name's content: merging one into any
    // class would pour it into every name.
    if (isShadowCell(canon))
      return true;
    const Value *v = NF.getValueForNode(canon);
    if (!v)
      return false;
    return isa<Function>(v) || isa<GlobalVariable>(v);
  };
  std::unordered_map<NodeIndex, uint32_t> toLocal;
  std::vector<NodeIndex> toCanon;
  struct SubEdge {
    uint32_t from, to;
    EdgeKind kind;
    uint32_t bucket;
  };
  std::vector<SubEdge> subEdges;
  auto localId = [&](NodeIndex canon) -> uint32_t {
    auto [it, inserted] = toLocal.emplace(canon, (uint32_t)toCanon.size());
    if (inserted)
      toCanon.push_back(canon);
    return it->second;
  };

  const auto &edges = Graph.edges();
  const size_t n = idx ? idx->size() : edges.size();
  for (size_t i = 0; i < n; i++) {
    const GraphEdge &E = edges[idx ? (*idx)[i] : i];
    if (E.kind == EdgeKind::Deref)
      continue;
    NodeIndex from = getCanonicalNode(E.from);
    NodeIndex to = getCanonicalNode(E.to);
    if (from == to)
      continue;
    if (isBarrierNode(from) || isBarrierNode(to))
      continue;
    const uint32_t lf = localId(from), lt = localId(to);
    subEdges.push_back({lf, lt, E.kind, E.bucket});
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
  // Channel cells require the exact quotient: the V-component merge is
  // itself a symmetric (Steensgaard-style) unification, the class of
  // merge the pairwise cell model exists to remove.
  if (CFLPreSolveExact || CFLChannelCells) {
    const uint32_t M2 = (uint32_t)toCanon.size();
    std::vector<std::vector<uint32_t>> adjX(M2);
    for (auto &E : subEdges)
      adjX[E.from].push_back(E.to);
    std::vector<uint32_t> comp(M2, UINT32_MAX);
    uint32_t nComp = 0;
    ka::tarjanSCC(
        M2, [](uint32_t) { return false; },
        [&](uint32_t u) { return adjX[u].size(); },
        [&](uint32_t u, size_t i) { return adjX[u][i]; },
        [&](const std::vector<uint32_t> &members) {
          for (uint32_t w : members)
            comp[w] = nComp;
          nComp++;
        });
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
  // V-components of the sublanguage (ka::valleyComponents states the
  // relation and why walking from root SCCs computes it exactly).
  std::vector<uint32_t> nodeToSCC;
  uint32_t numSCCs = 0;
  {
    const unsigned NB = Graph.numFieldBuckets();
    std::vector<std::vector<std::pair<uint32_t, uint32_t>>> outV(
        toCanon.size());
    for (auto &E : subEdges)
      if (E.kind != EdgeKind::FieldAny) // no V rule consumes fx
        outV[E.from].emplace_back(E.to, E.bucket);
    numSCCs = ka::valleyComponents((uint32_t)toCanon.size(),
                                   NB > 0 ? NB : 1, outV, nodeToSCC);
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
  if (CFLPreSolveCone && !CFLChannelCells) {
    // Named cells: a load through name n reads what every store under n
    // wrote, wherever the solve puts the cells — shadows are barriers, so
    // the cone crosses names explicitly: a named load's value in the cone
    // brings every value stored under its name. Such values (and icall
    // operands read only through shadows) need not touch the sublanguage:
    // give them local ids so the cone can hold them.
    std::unordered_map<uint32_t, std::vector<uint32_t>> loadNames; // local -> names
    std::unordered_map<uint32_t, std::vector<uint32_t>> storedUnder; // name -> locals
    if (namedPlanes())
      for (const GraphEdge &E : edges) {
        if (E.kind != EdgeKind::Copy)
          continue;
        const NodeIndex f = getCanonicalNode(E.from), t = getCanonicalNode(E.to);
        const uint32_t fn = shadowInfoOf(f).second, tn = shadowInfoOf(t).second;
        if (fn >= ka::AccessNames::FirstName && !isBarrierNode(t))
          loadNames[localId(t)].push_back(fn);
        if (tn >= ka::AccessNames::FirstName && !isBarrierNode(f))
          storedUnder[tn].push_back(localId(f));
      }
    std::vector<uint32_t> seeds;
    for (const CallBase *CS2 : Ctx->IndirectCallInsts) {
      NodeIndex n2 = NF.getValueNodeFor(
          CS2->getCalledOperand()->stripPointerCastsAndAliases());
      if (n2 == AndersNodeFactory::InvalidIndex)
        continue;
      const NodeIndex c2 = getCanonicalNode(n2);
      if (namedPlanes() && !isBarrierNode(c2))
        seeds.push_back(localId(c2));
      else if (auto lit = toLocal.find(c2); lit != toLocal.end())
        seeds.push_back(lit->second);
    }
    const uint32_t Mc = (uint32_t)toCanon.size();
    inCone.assign(Mc, 0);
    std::vector<std::vector<uint32_t>> radjC(Mc);
    for (auto &E : subEdges)
      radjC[E.to].push_back(E.from);
    std::vector<uint32_t> bfs;
    for (uint32_t l : seeds)
      if (!inCone[l]) {
        inCone[l] = 1;
        bfs.push_back(l);
      }
    std::unordered_set<uint32_t> namesInCone;
    for (size_t qi = 0; qi < bfs.size(); qi++) {
      for (uint32_t w : radjC[bfs[qi]])
        if (!inCone[w]) {
          inCone[w] = 1;
          bfs.push_back(w);
        }
      auto ln = loadNames.find(bfs[qi]);
      if (ln == loadNames.end())
        continue;
      for (uint32_t nm : ln->second) {
        if (!namesInCone.insert(nm).second)
          continue;
        for (uint32_t w : storedUnder[nm])
          if (!inCone[w]) {
            inCone[w] = 1;
            bfs.push_back(w);
          }
      }
    }
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
