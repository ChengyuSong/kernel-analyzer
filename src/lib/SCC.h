#ifndef KA_SCC_H
#define KA_SCC_H

// One strongly-connected-component routine for every graph the solver
// and the presolve condense (iterative Tarjan; no recursion, so million-
// node graphs do not overflow the stack).

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

namespace ka {

constexpr uint32_t kNoNode = UINT32_MAX;

// Tarjan over nodes [0, N).
//   skipStart(v)  v never starts a DFS (it may still be reached as a
//                 successor unless succ() filters it out)
//   degree(u)     number of out-edge slots of u
//   succ(u, i)    target of u's i-th slot, or kNoNode to ignore the slot
//   emit(members) called once per SCC, in Tarjan's order (every SCC is
//                 emitted after all SCCs it reaches: sinks first);
//                 members are in stack pop order, the DFS root last
// Visiting order is node order for roots and slot order for edges, so
// the emitted sequence is a deterministic function of the inputs.
template <typename SkipStart, typename Degree, typename Succ, typename Emit>
void tarjanSCC(uint32_t N, SkipStart skipStart, Degree degree, Succ succ,
               Emit emit) {
  std::vector<uint32_t> low(N), dfn(N, 0), tarjanStack, members;
  std::vector<std::pair<uint32_t, size_t>> callStack;
  std::vector<bool> onStack(N, false);
  uint32_t timer = 1;
  for (uint32_t start = 0; start < N; start++) {
    if (dfn[start] || skipStart(start))
      continue;
    callStack.emplace_back(start, 0);
    dfn[start] = low[start] = timer++;
    tarjanStack.push_back(start);
    onStack[start] = true;
    while (!callStack.empty()) {
      auto &[u, ei] = callStack.back();
      if (ei < degree(u)) {
        const uint32_t v = succ(u, ei++);
        if (v == kNoNode || v == u)
          continue;
        if (!dfn[v]) {
          dfn[v] = low[v] = timer++;
          tarjanStack.push_back(v);
          onStack[v] = true;
          callStack.emplace_back(v, 0);
        } else if (onStack[v]) {
          low[u] = std::min(low[u], dfn[v]);
        }
        continue;
      }
      if (low[u] == dfn[u]) {
        members.clear();
        while (true) {
          const uint32_t w = tarjanStack.back();
          tarjanStack.pop_back();
          onStack[w] = false;
          members.push_back(w);
          if (w == u)
            break;
        }
        emit(static_cast<const std::vector<uint32_t> &>(members));
      }
      const uint32_t uu = u;
      callStack.pop_back();
      if (!callStack.empty())
        low[callStack.back().first] =
            std::min(low[callStack.back().first], low[uu]);
    }
  }
}

// Valley components of a shift-labelled copy graph, without saturating
// it. out[u] lists u's exact edges (v, shift) with shift in [0, P);
// edges of unknown shift are not in `out`. Two nodes x, y are related
// (V) when some source z reaches both with the same net shift mod P:
//   x V y  iff  exists z, s:  z ~>_s x  and  z ~>_s y
// This is the V of the field-shift valley grammar (src/baseline/Grammar.h,
// buildP2GrammarWithFields) restricted to the memory-free sublanguage
// (no d edges, hence no M), where V ::= Up<s> Dn<s>; with P = 1 it is
// the field-insensitive V = -a* a*. comp[] receives the connected
// components of V (V is symmetric, so these are its SCCs), numbered
// by first member in node order; the return value is their count.
//
// Exactness: call a pair (z, s) a token of x when z ~>_s x; x V y iff
// x and y share a token. Every z is reached from a member w of a ROOT
// SCC of the edge graph (an SCC with no edge entering it from another
// SCC), say w ~>_d z, so every token (z, s) of x yields the token
// (w, s + d) of x: tokens from root-SCC members already relate every
// pair a token from z relates. Conversely each such token is a real
// token. So it suffices to walk (node, shift) states forward from one
// member of each root SCC and union the nodes reached at equal shift.
// Cost: sum over root SCCs of |reachable states|, at most what a
// saturating solver spends deriving Dn<s> from every node; with P = 1,
// O(N + E) (see shareAcrossWalks).
inline uint32_t valleyComponents(
    uint32_t N, unsigned P,
    const std::vector<std::vector<std::pair<uint32_t, uint32_t>>> &out,
    std::vector<uint32_t> &comp) {
  // Root SCCs of the edge graph (shifts ignored).
  std::vector<uint32_t> sccOf(N, kNoNode), sccSource;
  tarjanSCC(
      N, [](uint32_t) { return false; },
      [&](uint32_t u) { return out[u].size(); },
      [&](uint32_t u, size_t i) { return out[u][i].first; },
      [&](const std::vector<uint32_t> &members) {
        const uint32_t id = (uint32_t)sccSource.size();
        uint32_t lowest = kNoNode;
        for (uint32_t m : members) {
          sccOf[m] = id;
          lowest = std::min(lowest, m);
        }
        sccSource.push_back(lowest);
      });
  std::vector<char> entered(sccSource.size(), 0);
  for (uint32_t u = 0; u < N; u++)
    for (auto &[v, s] : out[u])
      if (sccOf[v] != sccOf[u])
        entered[sccOf[v]] = 1;

  std::vector<uint32_t> parent(N);
  for (uint32_t i = 0; i < N; i++)
    parent[i] = i;
  auto find = [&](uint32_t x) {
    while (parent[x] != x) {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  };
  auto unite = [&](uint32_t a, uint32_t b) {
    a = find(a);
    b = find(b);
    if (a != b)
      parent[std::max(a, b)] = std::min(a, b);
  };

  // Per-walk visited (node, shift) states: a stamp per node plus one bit
  // per shift, reset lazily when a walk first touches the node.
  const unsigned W = (P + 63) / 64;
  std::vector<uint64_t> seen((size_t)N * W, 0);
  std::vector<uint32_t> stamp(N, 0);
  std::vector<uint32_t> firstAt(P, kNoNode), touchedShifts;
  std::vector<std::pair<uint32_t, uint32_t>> queue;
  uint32_t walk = 0;
  // With one shift (P = 1) every node a walk reaches joins that walk's
  // single group, so a node expanded by an earlier walk already has its
  // whole reach in its class: later walks only join it and stop there.
  const bool shareAcrossWalks = P == 1;
  auto visit = [&](uint32_t x, uint32_t s) {
    if (shareAcrossWalks && stamp[x] != 0 && stamp[x] != walk) {
      unite(firstAt[0] == kNoNode ? x : firstAt[0], x);
      if (firstAt[0] == kNoNode) {
        firstAt[0] = x;
        touchedShifts.push_back(0);
      }
      return;
    }
    if (stamp[x] != walk) {
      stamp[x] = walk;
      std::fill(seen.begin() + (size_t)x * W, seen.begin() + (size_t)x * W + W,
                0);
    }
    uint64_t &word = seen[(size_t)x * W + s / 64];
    const uint64_t bit = (uint64_t)1 << (s % 64);
    if (word & bit)
      return;
    word |= bit;
    queue.emplace_back(x, s);
    if (firstAt[s] == kNoNode) {
      firstAt[s] = x;
      touchedShifts.push_back(s);
    } else {
      unite(firstAt[s], x);
    }
  };
  for (uint32_t c = 0; c < sccSource.size(); c++) {
    if (entered[c])
      continue;
    walk++;
    queue.clear();
    visit(sccSource[c], 0);
    for (size_t qi = 0; qi < queue.size(); qi++) {
      const auto [x, s] = queue[qi];
      for (auto &[y, d] : out[x])
        visit(y, (s + d) % P);
    }
    for (uint32_t s : touchedShifts)
      firstAt[s] = kNoNode;
    touchedShifts.clear();
  }

  comp.assign(N, kNoNode);
  std::vector<uint32_t> idOfRoot(N, kNoNode);
  uint32_t nComp = 0;
  for (uint32_t x = 0; x < N; x++) {
    const uint32_t r = find(x);
    if (idOfRoot[r] == kNoNode)
      idOfRoot[r] = nComp++;
    comp[x] = idOfRoot[r];
  }
  return nComp;
}

} // namespace ka

#endif
