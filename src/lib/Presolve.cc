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
  auto isBarrierNodeV = [&](NodeIndex canon) {
    if (NF.isSpecialNode(canon))
      return true;
    const Value *v = NF.getValueForNode(canon);
    if (!v)
      return false;
    // MEASUREMENT probe: cut context-insensitive call junctions
    // (formals) and module-unique constant-expression nodes (one CE
    // used in N functions = one node wired into all their webs —
    // the same common-source smear rationale as the fn/global
    // barriers below) — what glues the born component?
    if (CFLProbeNoFormalPresolve &&
        (isa<Argument>(v) || isa<ConstantExpr>(v)))
      return true;
    return isa<Function>(v) || isa<GlobalVariable>(v);
  };
  auto isBarrierNode = [&](NodeIndex canon) {
    // Probe extension: DEREF nodes as barriers — memory cells acting
    // as through-nodes in the memory-FREE sublanguage (asm reg-load
    // and summary-CPY a-edges land on them; deref(@global) is
    // module-shared, e.g. deref(pcpu_hot) fans into every `current`
    // user).
    if (CFLProbeNoFormalPresolve && NF.isDereferenceNode(canon))
      return true;
    return isBarrierNodeV(canon);
  };

  // Probe census: name the junction formals — fan-in per Argument
  // node in the sublanguage (who glues the born component?).
  boost::unordered_flat_map<NodeIndex, uint32_t> formalFan;
  auto tallyFormal = [&](NodeIndex canon) {
    if (!CFLProbeNoFormalPresolve)
      return;
    const Value *v = NF.getValueForNode(canon);
    if (v && isa<Argument>(v))
      formalFan[canon]++;
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
    if (isBarrierNode(from) || isBarrierNode(to)) {
      // once per direction: the census counts edges as the grammar does
      for (int dir = 0; dir < 2; dir++) {
        tallyFormal(from);
        tallyFormal(to);
      }
      continue;
    }
    const uint32_t lf = localId(from), lt = localId(to);
    subEdges.push_back({lf, lt, E.kind, E.bucket});
  }
  if (CFLProbeNoFormalPresolve && !formalFan.empty()) {
    std::vector<std::pair<uint32_t, NodeIndex>> top;
    uint64_t mass = 0;
    for (auto &kv : formalFan) {
      top.emplace_back(kv.second, kv.first);
      mass += kv.second;
    }
    std::sort(top.begin(), top.end(), std::greater<>());
    CG_LOG("JunctionFormals: " << top.size() << " junction formals, total "
           << "fan-in mass " << mass << "\n");
    // Full-depth dump (fan-in >= 4, cap 5000 lines): the reduction
    // question is fan-in-WEIGHTED coverage of the prover over the
    // functions that stitch the giant, not top-25 name-dropping.
    for (size_t i = 0; i < std::min<size_t>(5000, top.size()); i++) {
      if (top[i].first < 4) break;
      const auto *A = cast<Argument>(NF.getValueForNode(top[i].second));
      CG_LOG("JunctionFormals: x" << top[i].first << " "
             << A->getParent()->getName() << "::arg" << A->getArgNo()
             << "\n");
    }
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
      std::vector<std::vector<uint32_t>> adj(M), radj(M);
      std::vector<uint32_t> deg(M, 0);
      for (auto &E : subEdges) {
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
  if (CFLPreSolveCone && !CFLChannelCells) {
    const uint32_t Mc = (uint32_t)toCanon.size();
    inCone.assign(Mc, 0);
    std::vector<std::vector<uint32_t>> radjC(Mc);
    for (auto &E : subEdges)
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
