/*
 * Copyright (C) 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// CellSolver.cc: the cell solver (--cfl-cells, plan 3.26).
//
// Facts are cells (origin, name). An origin is a function, a global, a
// stack slot or an allocation site. A name is a byte offset in the
// origin's object, read through the object's label: the layout of its IR
// type (globals, stack slots) or of the struct its typed writes declare
// (heap). The layout folds every array element onto element 0, and a
// labeled heap object is an array of its label. An unlabeled object's
// name is its raw byte offset. Two more names per object: `*`, any offset
// (unknown arithmetic), and `out`, an address outside the object, which no
// legal access dereferences.
//
// Values flow by inclusion. A dereference node of the constraint graph is
// a per-pointer hub, never a cell: a load through pointer p reads every
// cell p holds, a store through p writes every cell p holds. No two cells
// are ever unified, so a cell's content is exactly what the program
// writes into that (origin, name).
//
// A member step of struct S on a labeled object checks that S starts at
// the address's offset in the object's layout; a mismatch is counted (rule
// (b): a pun or a bug in the program) and the step still uses the cell the
// address carries.

#include "CallGraphInternal.h"
#include "SCC.h"
#include <llvm/ADT/BitVector.h>

using namespace llvm;

namespace {

// A set of fact ids: sorted while small, a bit vector once large.
class Facts {
  SmallVector<uint32_t, 4> S;
  BitVector D;
  size_t N = 0;
  bool dense = false;

public:
  bool set(uint32_t f) {
    if (dense) {
      if (f >= D.size()) D.resize(std::max<size_t>(f + 1, D.size() * 2));
      if (D.test(f)) return false;
      D.set(f);
      N++;
      return true;
    }
    auto it = std::lower_bound(S.begin(), S.end(), f);
    if (it != S.end() && *it == f) return false;
    S.insert(it, f);
    N++;
    if (S.size() > 64) {
      D.resize(std::max<uint32_t>(S.back() + 1, 1024));
      for (uint32_t x : S) D.set(x);
      S.clear();
      S = SmallVector<uint32_t, 4>();
      dense = true;
    }
    return true;
  }
  size_t count() const { return N; }
  template <class Fn> void forEach(Fn fn) const {
    if (dense)
      for (unsigned f : D.set_bits()) fn(f);
    else
      for (uint32_t f : S) fn(f);
  }
};

// Offsets one folded offset or one strided step may stand for before the
// step yields the object's any-offset cell (counted).
constexpr size_t kExpandCap = 1 << 16;

enum class CellKind : uint8_t { Func, Off, Any, Out };

struct Cell {
  uint32_t obj;
  CellKind kind;
  int64_t off;     // Off: the folded offset
  uint32_t store;  // solver node a store writes (Off, Any)
  uint32_t load;   // solver node a load reads (Off, Any)
  NodeIndex node;  // the factory's cell node
};

struct Obj {
  NodeIndex origin;
  const Function *fn = nullptr;
  Type *layout = nullptr; // null: unlabeled
  bool repeats = false;   // an array of `layout` of unknown length
  int64_t size = 0;       // layout's allocation size
  std::string label;
  boost::unordered_flat_map<int64_t, uint32_t> offCells;
  boost::unordered_flat_map<int64_t, uint32_t> atRaw; // raw offset -> cell
  std::vector<uint32_t> loadNodes; // of the Off cells
  uint32_t any = UINT32_MAX, out = UINT32_MAX, func = UINT32_MAX;
};

// The folded offset of byte `off` inside one instance of T: every array
// element is element 0. Offsets in padding or past T stay as they are.
int64_t foldIn(Type *T, int64_t off, const DataLayout &DL) {
  if (off < 0) return off;
  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->isOpaque()) return off;
    const StructLayout *SL = DL.getStructLayout(ST);
    if ((uint64_t)off >= SL->getSizeInBytes()) return off;
    unsigned i = SL->getElementContainingOffset(off);
    int64_t eo = (int64_t)SL->getElementOffset(i);
    Type *E = ST->getElementType(i);
    if (off - eo >= (int64_t)DL.getTypeAllocSize(E)) return off; // padding
    return eo + foldIn(E, off - eo, DL);
  }
  Type *E = nullptr;
  uint64_t n = 0;
  if (auto *AT = dyn_cast<ArrayType>(T)) {
    E = AT->getElementType(); n = AT->getNumElements();
  } else if (auto *VT = dyn_cast<FixedVectorType>(T)) {
    E = VT->getElementType(); n = VT->getNumElements();
  }
  if (E) {
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0 || off >= e * (int64_t)n) return off;
    return foldIn(E, off % e, DL);
  }
  return off;
}

// Every offset the folded offset `c` stands for inside one instance of T
// (one per element of each array it lies in). False when there are more
// than `cap`.
bool expandIn(Type *T, int64_t c, int64_t base, const DataLayout &DL,
              size_t cap, std::vector<int64_t> &out) {
  if (c >= 0) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (!ST->isOpaque()) {
        const StructLayout *SL = DL.getStructLayout(ST);
        if ((uint64_t)c < SL->getSizeInBytes()) {
          unsigned i = SL->getElementContainingOffset(c);
          int64_t eo = (int64_t)SL->getElementOffset(i);
          Type *E = ST->getElementType(i);
          if (c - eo < (int64_t)DL.getTypeAllocSize(E))
            return expandIn(E, c - eo, base + eo, DL, cap, out);
        }
      }
    } else {
      Type *E = nullptr;
      uint64_t n = 0;
      if (auto *AT = dyn_cast<ArrayType>(T)) {
        E = AT->getElementType(); n = AT->getNumElements();
      } else if (auto *VT = dyn_cast<FixedVectorType>(T)) {
        E = VT->getElementType(); n = VT->getNumElements();
      }
      const int64_t e = E ? (int64_t)DL.getTypeAllocSize(E) : 0;
      if (E && e > 0 && c < e) {
        for (uint64_t j = 0; j < n; j++)
          if (!expandIn(E, c, base + (int64_t)j * e, DL, cap, out))
            return false;
        return true;
      }
    }
  }
  if (out.size() >= cap) return false;
  out.push_back(base + c);
  return true;
}

// Does a struct named like S start at offset `off` of T (through nested
// members and array elements)?
bool structStartsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL) {
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->hasName() && stripStructNameSuffix(ST->getName()) == S)
        return true;
      if (ST->isOpaque()) return false;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return false;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return false;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return false;
    off %= e;
    T = E;
  }
  return false;
}

std::string typeLabel(Type *T) {
  while (auto *AT = dyn_cast<ArrayType>(T)) T = AT->getElementType();
  if (auto *ST = dyn_cast<StructType>(T))
    if (ST->hasName()) return stripStructNameSuffix(ST->getName()).str();
  std::string s;
  raw_string_ostream os(s);
  T->print(os);
  return os.str();
}

} // namespace

bool CallGraphPass::runCellResolution() {
  using Clock = std::chrono::steady_clock;
  const auto t0 = Clock::now();
  const DataLayout &DL = Ctx->Modules.front().first->getDataLayout();

  // The kernel's answer-level channels (static_call tables, tracepoint
  // keys) live in the cluster solver's resolution; refuse their inputs.
  for (const CallBase *CS : Ctx->IndirectCallInsts)
    if (const Function *CF = CS->getCalledFunction())
      assert(!CF->getName().starts_with("__SCT__") &&
             !CF->getName().starts_with("__traceiter_") &&
             "--cfl-cells does not model static_call or tracepoint dispatch");

  // ---- Solver nodes: graph nodes keep their factory index; cells and
  // store collectors are numbered after them. ----
  const uint32_t G = NF.getNumNodes();
  uint32_t numNodes = G;
  std::vector<Facts> pts;
  std::vector<std::vector<uint32_t>> pend; // added, not yet propagated
  std::vector<std::vector<uint32_t>> succ;
  std::vector<char> inWL;
  // Copy cycles collapse into one solver node (mutual flow: equal sets,
  // so the merge loses nothing; cells stay distinct facts). The
  // representative inherits every constraint of its members.
  std::vector<uint32_t> repOf;
  std::vector<std::vector<uint32_t>> hubsOf; // pointer -> its hubs
  std::vector<std::vector<std::pair<uint32_t, uint32_t>>> fieldOut;
  std::vector<char> anyLoop;
  auto grow = [&](uint32_t n) {
    if (n <= pts.size()) return;
    size_t cap = std::max<size_t>(n, pts.size() * 3 / 2);
    const size_t old = repOf.size();
    pts.resize(cap); pend.resize(cap); succ.resize(cap); inWL.resize(cap, 0);
    hubsOf.resize(cap); fieldOut.resize(cap); anyLoop.resize(cap, 0);
    repOf.resize(cap);
    for (size_t i = old; i < cap; i++) repOf[i] = i;
  };
  grow(G);
  auto find = [&](uint32_t n) {
    while (repOf[n] != n) n = repOf[n] = repOf[repOf[n]];
    return n;
  };
  auto newNode = [&]() { grow(numNodes + 1); return numNodes++; };
  std::vector<uint32_t> worklist;
  auto push = [&](uint32_t n) {
    if (!inWL[n]) { inWL[n] = 1; worklist.push_back(n); }
  };
  auto add = [&](uint32_t n, uint32_t f) {
    n = find(n);
    if (pts[n].set(f)) {
      pend[n].push_back(f);
      push(n);
    }
  };
  boost::unordered_flat_set<uint64_t> edgeSet;
  size_t dynEdges = 0;
  auto addEdge = [&](uint32_t a, uint32_t b) {
    a = find(a);
    b = find(b);
    if (a == b || !edgeSet.insert((uint64_t)a << 32 | b).second) return;
    succ[a].push_back(b);
    pts[a].forEach([&](uint32_t f) { add(b, f); });
  };

  // ---- Static constraints ----
  auto canon = [&](NodeIndex n) -> uint32_t {
    uint32_t c = getCanonicalNode(n);
    assert(c < G && "edge endpoint created after the solve began");
    return c;
  };
  std::vector<char> isHub(G, 0), inGraph(G, 0);
  size_t graphFieldEdges = 0;
  for (const GraphEdge &E : Graph.edges())
    if (E.kind == EdgeKind::Deref) {
      const uint32_t p = canon(E.from), h = canon(E.to);
      inGraph[p] = inGraph[h] = 1;
      if (std::find(hubsOf[p].begin(), hubsOf[p].end(), h) == hubsOf[p].end())
        hubsOf[p].push_back(h);
      isHub[h] = 1;
    }
  std::vector<uint32_t> storeHub(G, UINT32_MAX);
  size_t staticCopies = 0, stores = 0;
  for (const GraphEdge &E : Graph.edges()) {
    switch (E.kind) {
    case EdgeKind::Copy: {
      const uint32_t a = canon(E.from), b = canon(E.to);
      inGraph[a] = inGraph[b] = 1;
      if (isHub[b]) { // a store: into the cells the hub's pointers hold
        if (storeHub[b] == UINT32_MAX) storeHub[b] = newNode();
        addEdge(a, storeHub[b]);
        stores++;
      } else {
        addEdge(a, b);
        staticCopies++;
      }
      break;
    }
    case EdgeKind::FieldAny:
      assert(canon(E.from) == canon(E.to) && "field-any edges are loops");
      anyLoop[canon(E.from)] = 1;
      inGraph[canon(E.from)] = 1;
      break;
    case EdgeKind::Field:
      graphFieldEdges++;
      break;
    case EdgeKind::Deref:
      break;
    }
  }
  assert(graphFieldEdges == lazyFEdges.size() &&
         "every field edge carries an exact label");
  for (auto &[f, t, li] : lazyFEdges) {
    const uint32_t a = canon(f), b = canon(t);
    inGraph[a] = inGraph[b] = 1;
    assert(!isHub[b] && "a field address is never a dereference");
    if (a != b || lazyLabels[li].off != 0 || lazyLabels[li].stride != 0)
      fieldOut[a].push_back({b, li});
  }

  // Collapse the copy cycles of the current graph (static edges and the
  // hub edges added so far).
  size_t collapses = 0, collapsedNodes = 0;
  double collapseSecs = 0;
  std::vector<uint32_t> fs2;
  auto collapseCycles = [&]() {
    const auto tc = Clock::now();
    collapses++;
    std::vector<std::vector<uint32_t>> sccs;
    ka::tarjanSCC(
        numNodes, [&](uint32_t u) { return find(u) != u; },
        [&](uint32_t u) { return succ[u].size(); },
        [&](uint32_t u, size_t i) -> uint32_t {
          const uint32_t v = find(succ[u][i]);
          return v == u ? ka::kNoNode : v;
        },
        [&](const std::vector<uint32_t> &members) {
          if (members.size() > 1) sccs.push_back(members);
        });
    for (auto &M : sccs) {
      const uint32_t r = *std::min_element(M.begin(), M.end());
      for (uint32_t m : M) {
        if (m == r) continue;
        repOf[m] = r;
        collapsedNodes++;
        pts[m].forEach([&](uint32_t f) { pts[r].set(f); });
        pts[m] = Facts();
        pend[m].clear();
        succ[r].insert(succ[r].end(), succ[m].begin(), succ[m].end());
        succ[m].clear();
        hubsOf[r].insert(hubsOf[r].end(), hubsOf[m].begin(), hubsOf[m].end());
        hubsOf[m].clear();
        fieldOut[r].insert(fieldOut[r].end(), fieldOut[m].begin(),
                           fieldOut[m].end());
        fieldOut[m].clear();
        anyLoop[r] |= anyLoop[m];
      }
    }
    // Representatives: successor lists through the union-find, and every
    // fact re-propagated (members brought facts the others' successors
    // and constraints have not seen).
    for (auto &M : sccs) {
      const uint32_t r = find(M[0]);
      std::vector<uint32_t> &S = succ[r];
      for (uint32_t &v : S) v = find(v);
      std::sort(S.begin(), S.end());
      S.erase(std::unique(S.begin(), S.end()), S.end());
      S.erase(std::remove(S.begin(), S.end(), r), S.end());
      for (uint32_t v : S) edgeSet.insert((uint64_t)r << 32 | v);
      pend[r].clear();
      pts[r].forEach([&](uint32_t f) { pend[r].push_back(f); });
      if (!pend[r].empty()) push(r);
    }
    collapseSecs += std::chrono::duration<double>(Clock::now() - tc).count();
  };
  collapseCycles(); // static cycles, before any fact moves

  // ---- Objects and cells ----
  std::vector<Obj> objs;
  std::vector<Cell> cells;
  size_t cappedMints = 0, outMints = 0;
  auto internName = [&](const std::string &s) { return NF.internCellName(s); };
  std::function<uint32_t(uint32_t)> anyOf; // mints link to it, it to them
  auto mintOff = [&](uint32_t o, int64_t off) -> uint32_t {
    Obj &O = objs[o];
    auto it = O.offCells.find(off);
    if (it != O.offCells.end()) return it->second;
    if (!O.layout && O.offCells.size() >= CFLCellCap) {
      cappedMints++;
      return anyOf(o);
    }
    const uint32_t f = cells.size();
    const uint32_t n = newNode();
    Obj &O2 = O;
    const std::string nm = (O2.layout ? O2.label : std::string()) + "+" +
                           std::to_string(off);
    cells.push_back({o, CellKind::Off, off, n, n,
                     NF.getCellNode(O2.origin, internName(nm))});
    O2.offCells.emplace(off, f);
    O2.loadNodes.push_back(n);
    if (O2.any != UINT32_MAX) {
      const Cell &A = cells[O2.any];
      addEdge(A.store, n);
      addEdge(n, A.load);
    }
    return f;
  };
  anyOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].any != UINT32_MAX) return objs[o].any;
    const uint32_t f = cells.size();
    const uint32_t w = newNode(), r = newNode();
    cells.push_back({o, CellKind::Any, 0, w, r,
                     NF.getCellNode(objs[o].origin, internName("*"))});
    objs[o].any = f;
    addEdge(w, r);
    for (uint32_t c : objs[o].loadNodes) {
      addEdge(w, c);
      addEdge(c, r);
    }
    return f;
  };
  auto outOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].out != UINT32_MAX) return objs[o].out;
    const uint32_t f = cells.size();
    cells.push_back({o, CellKind::Out, 0, UINT32_MAX, UINT32_MAX,
                     NF.getCellNode(objs[o].origin, internName("out"))});
    objs[o].out = f;
    outMints++;
    return f;
  };
  // The cell of byte `off` of object o.
  auto cellAt = [&](uint32_t o, int64_t off) -> uint32_t {
    Obj &O = objs[o];
    if (!O.layout)
      return off < 0 ? outOf(o) : mintOff(o, off);
    if (O.repeats)
      off = ((off % O.size) + O.size) % O.size;
    else if (off < 0 || off >= O.size)
      return outOf(o);
    auto it = O.atRaw.find(off);
    if (it != O.atRaw.end()) return it->second;
    const uint32_t f = mintOff(o, foldIn(O.layout, off, DL));
    objs[o].atRaw.emplace(off, f);
    return f;
  };

  // Labels: globals and stack slots by their IR types, heap objects by the
  // struct their typed writes declare (one struct, else unlabeled).
  std::unordered_map<const Value *, std::set<std::string>> labels;
  staticLabels(labels);
  const double labelSecs =
      std::chrono::duration<double>(Clock::now() - t0).count();
  size_t heapLabeled = 0, heapUnlabeled = 0, heapConflict = 0;
  auto newObj = [&](NodeIndex origin, const Value *V) -> uint32_t {
    Obj O;
    O.origin = origin;
    if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) {
      O.layout = GV->getValueType();
    } else if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) {
      O.layout = AI->getAllocatedType();
      O.repeats = AI->isArrayAllocation();
    } else if (const auto *C = dyn_cast_or_null<CallBase>(V)) {
      auto lit = labels.find(C);
      if (lit != labels.end() && lit->second.size() == 1) {
        O.layout = StructType::getTypeByName(C->getContext(),
                                             *lit->second.begin());
        O.repeats = true;
        if (O.layout) heapLabeled++;
        else heapUnlabeled++;
      } else if (lit != labels.end() && lit->second.size() > 1) {
        heapConflict++;
      } else {
        heapUnlabeled++;
      }
    }
    if (O.layout && O.layout->isSized())
      O.size = (int64_t)DL.getTypeAllocSize(O.layout);
    if (O.size <= 0) O.layout = nullptr; // opaque or empty: unlabeled
    else O.label = typeLabel(O.layout);
    objs.push_back(std::move(O));
    return objs.size() - 1;
  };

  // ---- Seeds: functions and objects ----
  size_t funcSeeds = 0, objSeeds = 0;
  std::unordered_map<const Function *, uint32_t> funcFact;
  for (const Function *F : Ctx->AddressTakenFuncs) {
    const NodeIndex vn = NF.getValueNodeFor(F);
    if (vn == AndersNodeFactory::InvalidIndex) continue;
    const uint32_t n = canon(vn);
    if (!inGraph[n]) continue;
    const Function *FD = getFuncDef(const_cast<Function *>(F));
    auto [it, ins] = funcFact.try_emplace(FD, 0);
    if (ins) {
      Obj O;
      O.origin = vn;
      O.fn = FD;
      objs.push_back(std::move(O));
      const uint32_t f = cells.size();
      cells.push_back({(uint32_t)objs.size() - 1, CellKind::Func, 0,
                       UINT32_MAX, UINT32_MAX,
                       NF.getCellNode(vn, internName("fn"))});
      objs.back().func = f;
      it->second = f;
    }
    add(n, it->second);
    funcSeeds++;
  }
  auto isOrigin = [&](NodeIndex m) {
    if (!NF.isValueNode(m)) return false;
    if (AllocSites.count(m)) return true;
    const Value *v = NF.getValueForNode(m);
    return v && (isa<AllocaInst>(v) || isa<GlobalVariable>(v));
  };
  std::vector<NodeIndex> members;
  for (uint32_t n = 0; n < G; n++) {
    if (!inGraph[n] || getCanonicalNode(n) != n) continue;
    members.clear();
    collectCanonicalMembers(n, members);
    if (members.empty()) members.push_back(n);
    for (NodeIndex m : members) {
      const bool special = m == NF.getUniversalPtrNode() ||
                           m == NF.getUniversalObjNode();
      if (!special && !isOrigin(m)) continue;
      const uint32_t o = newObj(m, NF.getValueForNode(m));
      add(n, cellAt(o, 0));
      objSeeds++;
    }
  }

  // ---- Steps: a field edge maps each cell to the cell(s) at the new
  // offset, through every element its folded offset stands for. ----
  boost::unordered_flat_map<uint64_t, std::vector<uint32_t>> stepMemo;
  size_t stridedUnlabeled = 0, expandCapped = 0, ruleB = 0, stepCalls = 0,
         stepOffsets = 0;
  std::map<std::pair<std::string, std::string>, size_t> ruleBPairs;
  std::vector<int64_t> actual;
  auto step = [&](uint32_t f, uint32_t li) -> const std::vector<uint32_t> & {
    auto [it, ins] = stepMemo.try_emplace((uint64_t)f << 32 | li);
    if (!ins) return it->second;
    std::vector<uint32_t> res;
    stepCalls++;
    const Cell C = cells[f];
    const LazyLabel &L = lazyLabels[li];
    switch (C.kind) {
    case CellKind::Func:
    case CellKind::Any:
      res.push_back(f);
      break;
    case CellKind::Out:
      res.push_back(anyOf(C.obj));
      break;
    case CellKind::Off: {
      const Obj &O = objs[C.obj];
      if (!O.layout) {
        if (L.stride) {
          stridedUnlabeled++;
          res.push_back(anyOf(C.obj));
        } else {
          res.push_back(cellAt(C.obj, C.off + L.off));
        }
        break;
      }
      if (L.ty && L.stride == 0 &&
          !structStartsAt(O.layout, C.off, stripStructNameSuffix(L.ty->getName()), DL)) {
        ruleB++;
        ruleBPairs[{O.label, stripStructNameSuffix(L.ty->getName()).str()}]++;
      }
      actual.clear();
      if (!expandIn(O.layout, C.off, 0, DL, kExpandCap, actual)) {
        expandCapped++;
        res.push_back(anyOf(C.obj));
        break;
      }
      stepOffsets += actual.size();
      if (!L.stride) {
        for (int64_t a : actual) res.push_back(cellAt(C.obj, a + L.off));
        break;
      }
      // Strided: from each start a + off, every a + off + m*stride the
      // extent (or the object) allows. Starts are merged per residue
      // class first, so an array's elements are walked once, not once
      // per element.
      struct Run { int64_t step, res, lo, hi; }; // lo, lo+step, ... < hi
      std::vector<Run> runs;
      for (int64_t a : actual) {
        const int64_t st = (int64_t)L.stride, start = a + L.off;
        if (O.repeats && !L.extent) {
          const int64_t g = std::gcd(st, O.size);
          const int64_t r = ((start % g) + g) % g;
          runs.push_back({g, r, r, O.size});
        } else {
          int64_t hi = L.extent ? start + (int64_t)L.extent
                                : (O.repeats ? start + O.size : O.size);
          if (hi <= start) hi = start + 1; // the base element itself
          runs.push_back({st, ((start % st) + st) % st, start, hi});
        }
      }
      std::sort(runs.begin(), runs.end(), [](const Run &x, const Run &y) {
        return std::tie(x.step, x.res, x.lo) < std::tie(y.step, y.res, y.lo);
      });
      size_t walked = 0;
      bool capped = false;
      for (size_t i = 0; i < runs.size() && !capped;) {
        Run R = runs[i++];
        while (i < runs.size() && runs[i].step == R.step &&
               runs[i].res == R.res && runs[i].lo <= R.hi) {
          R.hi = std::max(R.hi, runs[i].hi); // overlapping or adjacent
          i++;
        }
        walked += (size_t)((R.hi - R.lo + R.step - 1) / R.step);
        if (walked > kExpandCap) { capped = true; break; }
        for (int64_t x = R.lo; x < R.hi; x += R.step)
          res.push_back(cellAt(C.obj, x));
      }
      if (capped) {
        expandCapped++;
        res.assign(1, anyOf(C.obj));
      }
      break;
    }
    }
    std::sort(res.begin(), res.end());
    res.erase(std::unique(res.begin(), res.end()), res.end());
    auto &slot = stepMemo[(uint64_t)f << 32 | li]; // cellAt may rehash
    slot = std::move(res);
    return slot;
  };

  // The objects with the most offset cells (verbose reports).
  auto topObjects = [&](size_t k) {
    std::vector<std::pair<size_t, uint32_t>> big;
    for (uint32_t o = 0; o < objs.size(); o++)
      if (!objs[o].fn) big.push_back({objs[o].offCells.size(), o});
    std::sort(big.rbegin(), big.rend());
    for (size_t i = 0; i < big.size() && i < k; i++) {
      const Obj &O = objs[big[i].second];
      const Value *V = NF.getValueForNode(O.origin);
      std::string where = "<special>";
      if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
        where = (I->getFunction()->getName() + "::" + I->getOpcodeName()).str();
        if (const auto *CB = dyn_cast<CallBase>(I))
          if (const Function *CF = CB->getCalledFunction())
            where += " " + CF->getName().str();
      } else if (V) {
        where = V->getName().str();
      }
      CG_LOG("Cells:   object " << where << " ["
             << (O.layout ? O.label : std::string("unlabeled"))
             << (O.repeats ? " array" : "") << ", " << O.size << " B]: "
             << big[i].first << " offset cells"
             << (O.any != UINT32_MAX ? " + any" : "") << "\n");
    }
  };
  // Where the fact mass is: (node, fact) pairs by the fact's object and
  // cell kind, and how many solver nodes hold some fact of the object.
  auto describe = [&](const Obj &O) {
    const Value *V = NF.getValueForNode(O.origin);
    std::string where = "<special>";
    if (O.fn) return "fn " + O.fn->getName().str();
    if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
      where = (I->getFunction()->getName() + "::" + I->getOpcodeName()).str();
      if (const auto *CB = dyn_cast<CallBase>(I))
        if (const Function *CF = CB->getCalledFunction())
          where += " " + CF->getName().str();
    } else if (V) {
      where = V->getName().str();
    }
    return where + " [" + (O.layout ? O.label : std::string("unlabeled")) +
           (O.repeats ? " array" : "") + "]";
  };
  auto massByObject = [&](size_t k) {
    std::vector<uint64_t> mass(objs.size(), 0), holders(objs.size(), 0);
    uint64_t byKind[4] = {0, 0, 0, 0};
    std::vector<uint32_t> seen(objs.size(), UINT32_MAX);
    for (uint32_t m = 0; m < numNodes; m++)
      pts[m].forEach([&](uint32_t f) {
        const Cell &C = cells[f];
        mass[C.obj]++;
        byKind[(int)C.kind]++;
        if (seen[C.obj] != m) { seen[C.obj] = m; holders[C.obj]++; }
      });
    CG_LOG("Cells: mass by kind: function " << byKind[0] << ", offset "
           << byKind[1] << ", any " << byKind[2] << ", outside "
           << byKind[3] << "\n");
    std::vector<std::pair<uint64_t, uint32_t>> top;
    for (uint32_t o = 0; o < objs.size(); o++) top.push_back({mass[o], o});
    std::sort(top.rbegin(), top.rend());
    for (size_t i = 0; i < top.size() && i < k; i++) {
      const Obj &O = objs[top[i].second];
      CG_LOG("Cells:   mass " << top[i].first << " in "
             << holders[top[i].second] << " nodes: " << describe(O) << ", "
             << O.offCells.size() << " cells\n");
    }
    if (top.empty()) return;
    // The holders of the heaviest object, by function and node kind.
    const uint32_t o0 = top[0].second;
    std::map<std::string, size_t> byFn, byKindH;
    for (uint32_t m = 0; m < numNodes; m++) {
      bool has = false;
      pts[m].forEach([&](uint32_t f) { has |= cells[f].obj == o0; });
      if (!has) continue;
      std::string fn = "<none>", kind = m < G ? "graph" : "cell/collector";
      if (m < G) {
        const Value *V = NF.getValueForNode(m);
        if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
          fn = I->getFunction()->getName().str();
          kind = I->getOpcodeName();
        } else if (const auto *A = dyn_cast_or_null<Argument>(V)) {
          fn = A->getParent()->getName().str();
          kind = "formal";
        } else if (NF.isDereferenceNode(m) || NF.isObjectNode(m)) {
          kind = "hub";
          const NodeIndex par = NF.getDerefParent(m);
          if (par != AndersNodeFactory::InvalidIndex)
            if (const auto *I = dyn_cast_or_null<Instruction>(
                    NF.getValueForNode(par)))
              fn = I->getFunction()->getName().str();
        } else if (NF.isReturnNode(m) || NF.isVarargNode(m)) {
          kind = NF.isReturnNode(m) ? "return" : "vararg";
          fn = cast<Function>(V)->getName().str();
        } else if (V) {
          kind = "value";
        }
      }
      byFn[fn]++;
      byKindH[kind]++;
    }
    std::string kl;
    for (auto &[kk, c] : byKindH) kl += " " + kk + "=" + std::to_string(c);
    CG_LOG("Cells:   holders of the heaviest object by kind:" << kl << "\n");
    std::vector<std::pair<size_t, std::string>> fns;
    for (auto &[fn, c] : byFn) fns.push_back({c, fn});
    std::sort(fns.rbegin(), fns.rend());
    std::string fl;
    for (size_t i = 0; i < fns.size() && i < 25; i++)
      fl += " " + fns[i].second + "(" + std::to_string(fns[i].first) + ")";
    CG_LOG("Cells:   ... by function (" << fns.size() << "):" << fl << "\n");
  };
  // ---- Propagation (difference propagation over a worklist) ----
  const auto tSolve = Clock::now();
  uint64_t pops = 0;
  size_t hubLinks = 0, funcDerefs = 0, outDerefs = 0;
  auto linkHub = [&](uint32_t h, uint32_t f) {
    const Cell &C = cells[f];
    if (C.kind == CellKind::Func) { funcDerefs++; return; }
    if (C.kind == CellKind::Out) { outDerefs++; return; }
    hubLinks++;
    const uint32_t ld = C.load, st = C.store;
    addEdge(ld, h);
    if (storeHub[h] != UINT32_MAX) addEdge(storeHub[h], st);
  };
  std::vector<uint32_t> delta;
  uint64_t lastCollapsePops = 0;
  size_t edgesAtCollapse = edgeSet.size();
  while (!worklist.empty()) {
    const uint32_t n = worklist.back();
    worklist.pop_back();
    inWL[n] = 0;
    if (find(n) != n) continue; // merged: its facts moved to the rep
    delta.clear();
    delta.swap(pend[n]);
    if (delta.empty()) continue;
    if (++pops % (1u << 20) == 0) {
      size_t mass = 0;
      for (uint32_t m = 0; m < numNodes; m++) mass += pts[m].count();
      CG_LOG("Cells: progress " << pops << " pops, " << worklist.size()
             << " queued, " << numNodes << " nodes, " << cells.size()
             << " cells, " << mass << " facts, " << edgeSet.size()
             << " edges, " << stepCalls << " steps, "
             << std::chrono::duration<double>(Clock::now() - tSolve).count()
             << " s\n");
      topObjects(4);
      if (pops % (1u << 22) == 0) massByObject(12);
    }
    {
      for (uint32_t h : hubsOf[n])
        for (uint32_t f : delta) linkHub(h, f);
      for (auto [dst, li] : fieldOut[n])
        for (uint32_t f : delta)
          for (uint32_t f2 : step(f, li)) add(dst, f2);
      if (anyLoop[n])
        for (uint32_t f : delta) {
          const CellKind k = cells[f].kind;
          if (k == CellKind::Off || k == CellKind::Out)
            add(n, anyOf(cells[f].obj));
        }
    }
    for (uint32_t m : succ[n])
      for (uint32_t f : delta) add(m, f);
    if (pops - lastCollapsePops >= (1u << 18) &&
        edgeSet.size() > edgesAtCollapse + edgesAtCollapse / 8) {
      collapseCycles();
      lastCollapsePops = pops;
      edgesAtCollapse = edgeSet.size();
    }
  }
  dynEdges = edgeSet.size() - staticCopies - stores;
  const double solveSecs =
      std::chrono::duration<double>(Clock::now() - tSolve).count();

  // ---- Answers ----
  size_t resolved = 0, totalTargets = 0, newPairs = 0, typeRej = 0;
  const std::vector<const CallBase *> icallSnapshot(
      Ctx->IndirectCallInsts.begin(), Ctx->IndirectCallInsts.end());
  for (const CallBase *CS : icallSnapshot) {
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    const NodeIndex fn = NF.getValueNodeFor(fptr);
    if (fn == AndersNodeFactory::InvalidIndex) continue;
    if (getCanonicalNode(fn) >= G) continue;
    const uint32_t n = find(getCanonicalNode(fn));
    FuncSet targets;
    pts[n].forEach([&](uint32_t f) {
      const Cell &C = cells[f];
      if (C.kind != CellKind::Func) return;
      const Function *F = objs[C.obj].fn;
      if (const Function *called = CS->getCalledFunction())
        if (F == called || F->getGUID() == called->getGUID()) return;
      if (!isCompatible(CS, F)) { typeRej++; return; }
      targets.insert(F);
    });
    if (!targets.empty()) { resolved++; totalTargets += targets.size(); }
    for (const Function *F : targets)
      if (wireResolvedCallee(CS, F)) newPairs++;
  }

  // ---- Report ----
  size_t factMass = 0, offCells = 0, anyCells = 0;
  for (uint32_t n = 0; n < numNodes; n++) factMass += pts[n].count();
  CG_LOG("Cells: " << collapses << " cycle collapses merged "
         << collapsedNodes << " solver nodes (" << collapseSecs << " s)\n");
  for (const Cell &C : cells) {
    offCells += C.kind == CellKind::Off;
    anyCells += C.kind == CellKind::Any;
  }
  const double secs =
      std::chrono::duration<double>(Clock::now() - t0).count();
  CG_LOG("Cells: iteration " << iteration << ": " << objs.size()
         << " origins (" << funcSeeds << " function seeds, " << objSeeds
         << " objects; heap " << heapLabeled << " labeled, " << heapUnlabeled
         << " unlabeled, " << heapConflict << " with conflicting labels), "
         << cells.size() << " cells (" << offCells << " named offsets, "
         << anyCells << " any-offset, " << outMints << " outside)\n");
  CG_LOG("Cells: " << numNodes << " solver nodes, " << staticCopies
         << " copies, " << stores << " stores, " << lazyFEdges.size()
         << " field edges, " << dynEdges << " hub edges (" << hubLinks
         << " links), " << pops << " pops, " << factMass << " facts, "
         << secs << " s (labels " << labelSecs << " s, propagation "
         << solveSecs << " s)\n");
  CG_LOG("Cells: any-offset from: " << cappedMints << " capped mints, "
         << stridedUnlabeled << " strided steps on unlabeled objects, "
         << expandCapped << " capped expansions (" << stepCalls
         << " steps over " << stepOffsets << " offsets); dereferences of a "
         << "function " << funcDerefs << ", of an outside address "
         << outDerefs << "\n");
  CG_LOG("Cells: rule (b) member steps whose struct is not at the "
         << "address's offset: " << ruleB << " (" << ruleBPairs.size()
         << " object label / struct pairs)\n");
  if (VerboseLevel >= 2) {
    topObjects(12);
    std::vector<std::pair<size_t, std::pair<std::string, std::string>>> top;
    for (auto &[k, c] : ruleBPairs) top.push_back({c, k});
    std::sort(top.rbegin(), top.rend());
    for (size_t i = 0; i < top.size() && i < 20; i++)
      CG_LOG("Cells:   rule (b) x" << top[i].first << " object "
             << top[i].second.first << ", step of struct "
             << top[i].second.second << "\n");
  }
  CG_LOG("FlowsTo: resolved " << resolved << " icalls, " << totalTargets
         << " targets (" << newPairs << " new pairs wired, " << typeRej
         << " type-rejected), iteration " << iteration << "\n");

  if (newPairs == 0) return false;
  if (iteration + 1 >= (int)CFLFlowsToMaxIters) {
    if (!CFLIterCapOk) {
      errs() << "ERROR: cell solver hit the iteration cap ("
             << CFLFlowsToMaxIters.getValue() << ") with " << newPairs
             << " newly wired pairs unprocessed; raise "
             << "--cfl-flows-to-max-iters\n";
      exit(1);
    }
    WARNING("[UNSOUND-RISK] cell solver hit the iteration cap with "
            << newPairs << " newly wired pairs unprocessed\n");
    soundnessCapped = true;
    return false;
  }
  return true;
}
