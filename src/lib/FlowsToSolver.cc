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

// FlowsToSolver.cc: the rooted flows-to solver (runFlowsToResolution) and its fact-set machinery.
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

static const llvm::CallBase *
uniqueAllocSource(const llvm::Value *v,
                  const std::function<bool(const llvm::CallBase *)> &isAlloc);
namespace {

// Q1 estimator (paper, 2026-08-30): full class-size distribution +
// the closure-mass law Sigma|C|^2 — the fact count a saturating
// solver would materialize over this partition (per shift plane).
// Emitted at BlobForm INITIAL (input topology after presolve
// compression) and FINAL (the realized bidirected quotient).
static void cflDumpClassHist(const char *label,
                             std::vector<uint64_t> &szs) {
  std::sort(szs.begin(), szs.end(), std::greater<>());
  unsigned long long sum = 0, sumSq = 0;
  for (uint64_t s : szs) {
    sum += s;
    sumSq += (unsigned long long)s * s;
  }
  errs() << "ClassHist[" << label << "]: classes=" << szs.size()
         << " mass=" << sum << " sumSq=" << sumSq << "\n";
  for (size_t i = 0; i < std::min<size_t>(10, szs.size()); i++)
    errs() << "ClassHist[" << label << "]: top" << i << " |C|=" << szs[i]
           << " |C|^2=" << (unsigned long long)szs[i] * szs[i] << "\n";
  // log2-bucketed tail: bucket b holds sizes in [2^b, 2^(b+1))
  uint64_t bucketN[64] = {0}, bucketMass[64] = {0};
  unsigned long long bucketSq[64] = {0};
  for (uint64_t s : szs) {
    unsigned b = 63 - __builtin_clzll(s);
    bucketN[b]++;
    bucketMass[b] += s;
    bucketSq[b] += (unsigned long long)s * s;
  }
  for (unsigned b = 0; b < 64; b++)
    if (bucketN[b])
      errs() << "ClassHist[" << label << "]: bucket 2^" << b
             << " n=" << bucketN[b] << " mass=" << bucketMass[b]
             << " sumSq=" << bucketSq[b] << "\n";
}

} // namespace

// task #38 rung 2: canonical nodes of the presolve fptr backward cone,
// persisted for the in-solve join-cone experiment (--cfl-join-cone).

// --cfl-census-couplers (task #38, user thesis: kernel modularity at the
// DATA-OBJECT level). Subsystem = first two path components of the
// origin's defining module. A cross-subsystem WELD = a merge whose two
// sides each own data origins from subsystems the other lacks — after
// it, readers of either cell see both subsystems' objects. Fn origins
// are excluded (the identity channels already bind ops per object).
static boost::unordered_flat_map<std::string, uint8_t> g_subsysIds;
static boost::unordered_flat_map<std::string, uint32_t> g_weldRepOf;
static std::vector<std::string> g_subsysNames;
// Absolute-path bc-lists share a machine-specific prefix (/home/...) that
// would collapse every module into one subsystem key; strip the corpus
// root = longest common directory prefix over all module identifiers.
static std::string g_subsysRoot;
static void subsysComputeRoot(const ModuleList &mods) {
  g_subsysRoot.clear();
  bool first = true;
  for (auto &mp : mods) {
    llvm::StringRef p(mp.first->getModuleIdentifier());
    if (first) {
      g_subsysRoot = p.str();
      first = false;
      continue;
    }
    size_t n = 0, lim = std::min(g_subsysRoot.size(), (size_t)p.size());
    while (n < lim && g_subsysRoot[n] == p[n])
      n++;
    g_subsysRoot.resize(n);
  }
  size_t sl = g_subsysRoot.rfind('/');
  g_subsysRoot.resize(sl == std::string::npos ? 0 : sl + 1);
}
uint8_t subsysBitOf(const llvm::Module *M2) {
  if (!M2) return 63;
  llvm::StringRef p2 = M2->getModuleIdentifier();
  p2.consume_front(g_subsysRoot);
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
// Batch-local fact universe: during a batch's drain every live rid is
// in [batchLo, batchHi), so plane bits store rid - batchLo and DENSE
// planes are batch-width, not nextRoot-width — at kernel scale that is
// 42.5KB -> 2.5KB per promoted plane, the difference between fitting
// and the OOM cliff. Bits translate back to global rids at the join
// sweep (the only drain-time consumer of rid identity) and at harvest.
static uint32_t g_ridBase = 0;
// ---- Task #42: plane spill/restore (offload over recompute) ----
// With --cfl-batch-spill=<dir>, each batch's planes are serialized
// after its drain; later rounds RESTORE and drain only the delta
// instead of re-deriving from seeds. Restored class ids fold through
// find(); only classes touched by merges or new bridges since the
// save (the touch-log window) are re-dirtied — the delta is the
// cross-batch coupling, not the batch. The touch log records both
// endpoints of every merge and bridge, in order; per-round cursors
// bound the window.
static std::vector<uint32_t> g_touchLog;
static bool g_touchTrack = false;
static boost::unordered_flat_set<uint32_t> g_dirtyRestore;

class FactSet {
  llvm::SmallVector<uint32_t, 2> S; // sorted, unique (sparse mode)
  // Dense buffers are COW-shared (task #46 interning): the intern sweep
  // and the adopt-on-copy fast paths point multiple planes at one
  // buffer, so EVERY mutation of *D must go through mutD(), which
  // detaches a shared buffer first. Sharing is only CREATED when
  // EnableShare is on (sequential solver: concurrent in-place OR-ins
  // at T>1 would race with COW pointer swaps); detach stays
  // unconditional so correctness never depends on the gate.
  std::shared_ptr<ka::BitPlane> D; // non-null => dense mode
  static constexpr size_t kPromote = 128;
  ka::BitPlane &mutD() {
    if (D.use_count() > 1) D = std::make_shared<ka::BitPlane>(*D);
    return *D;
  }
  void promote() {
    // Size to the content, not just the universe: grid-space mark
    // planes (batch join fast path) hold GLOBAL rids past the
    // batch-local Universe — BitVector(Universe) then set(o) was the
    // #48-era batch OOB. S is sorted, so back() is the max.
    D = std::make_shared<ka::BitPlane>(
        std::max<uint32_t>(Universe, S.empty() ? 0 : S.back() + 1));
    for (uint32_t o : S) D->set(o);
    S.clear();
  }

public:
  static uint32_t Universe;
  static bool EnableShare;
  bool none() const { return D ? D->none() : S.empty(); }
  bool any() const { return !none(); }
  size_t count() const { return D ? D->count() : S.size(); }
  bool isDense() const { return (bool)D; }
  // Pointer-equality witnesses for the interned fast paths: two planes
  // sharing one buffer are content-identical by construction.
  bool sharesDense(const FactSet &o) const { return D && D == o.D; }
  bool denseUnique() const { return D && D.use_count() == 1; }
  const ka::BitPlane *denseData() const { return D.get(); }
  size_t denseCapBytes() const { return D ? D->capBytes() : 0; }
  void adoptDense(const FactSet &o) { // intern: content-equality proven
    assert(o.D && "adoptDense needs a dense source");
    D = o.D;
    S.clear();
  }
  bool test(uint32_t o) const {
    if (D) return o < D->size() && D->test(o);
    return std::binary_search(S.begin(), S.end(), o);
  }
  // Fused-kernel support (single-pass delta-OR in addBits/addBitsBridged):
  // expose a UNIQUE dense buffer for direct word access. mutDense
  // preserves content (detach shared, promote sparse, widen narrow);
  // scratchDense returns an exact-width buffer with UNSPECIFIED content
  // (the caller overwrites every word).
  ka::BitPlane &mutDense(uint32_t bits) {
    if (!D) promote();
    else if (D.use_count() > 1) D = std::make_shared<ka::BitPlane>(*D);
    if (D->size() < bits) D->resize(std::max<uint32_t>(Universe, bits));
    return *D;
  }
  ka::BitPlane &scratchDense(uint32_t bits) {
    if (!D || D.use_count() > 1)
      D = std::make_shared<ka::BitPlane>(bits);
    else
      D->resize(bits); // shrink truncates, grow zero-fills: exact width
    S.clear();
    return *D;
  }
  void set(uint32_t o) {
    if (D) {
      if (o < D->size() && D->test(o)) return; // no detach for a no-op
      auto &B = mutD();
      // Universe can grow between drains (incrementally minted roots);
      // dense buffers widen lazily on first touch past their old width.
      if (o >= B.size()) B.resize(std::max<uint32_t>(Universe, o + 1));
      B.set(o);
      return;
    }
    auto it = std::lower_bound(S.begin(), S.end(), o);
    if (it != S.end() && *it == o) return;
    S.insert(it, o);
    if (S.size() > kPromote) promote();
  }
  void reset(uint32_t o) {
    if (D) {
      if (o < D->size() && D->test(o)) mutD().reset(o);
      return;
    }
    auto it = std::lower_bound(S.begin(), S.end(), o);
    if (it != S.end() && *it == o) S.erase(it);
  }
  void clear() {
    if (D) {
      // Shared buffer: drop the handle (zeroing would clear the other
      // owners' bits). Unique buffer: keep it warm (hot delta planes).
      if (D.use_count() > 1) D.reset();
      else D->reset();
    }
    S.clear();
  }
  void release() {
    D.reset();
    llvm::SmallVector<uint32_t, 2>().swap(S); // drop heap capacity too
  }
  void copyFrom(const FactSet &o) {
    if (this == &o) return;
    if (o.D) {
      if (D == o.D) return; // already identical (shared)
      // Adopt only buffers that are ALREADY shared (interned): adopting
      // a unique buffer (e.g. scratch) would force ITS owner to detach
      // on next reuse — the hot-path churn the in-flight-dedup negative
      // taught us to avoid. The intern sweep is the sole origin of
      // sharing; adoption just propagates it.
      if (!D && EnableShare && o.D.use_count() > 1) {
        D = o.D; // adopt share: O(1); first mutation detaches
      } else if (D && D.use_count() == 1) {
        *D = *o.D; // reuse our unique buffer (hot scratch path)
      } else {
        D = std::make_shared<ka::BitPlane>(*o.D);
      }
      S.clear();
    } else if (D) {
      if (D.use_count() > 1) {
        D.reset(); // sparse content fits sparse mode; drop the share
        S = o.S;
        return;
      }
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
      if (D == o.D) return; // interned fast path
      if (!D && S.empty() && EnableShare && o.D.use_count() > 1) {
        D = o.D; // empty target adopts an interned share: O(1)
        return;
      }
      if (!D) promote();
      mutD() |= *o.D;
    } else if (D) {
      auto &B = mutD();
      for (uint32_t x : o.S) {
        if (x >= B.size()) B.resize(std::max<uint32_t>(Universe, x + 1));
        B.set(x);
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
  void copyShifted(const FactSet &o, uint32_t base) { // this := {x+base}
    assert(this != &o && "shifted copy cannot alias");
    if (base == 0) { copyFrom(o); return; }
    if (!o.D) { // sparse source: a constant shift preserves sort order
      if (D && D.use_count() > 1) D.reset(); // never mutate a shared buffer
      if (D) {
        auto &B = *D; // unique scratch: reuse the buffer
        B.reset();
        for (uint32_t x : o.S) {
          const uint32_t g = x + base;
          if (g >= B.size()) B.resize(g + 1);
          B.set(g);
        }
      } else {
        S.clear();
        for (uint32_t x : o.S) S.push_back(x + base);
      }
      return;
    }
    // Dense source: word copy, widen, then shift up. llvm's <<= keeps
    // the size fixed (high bits would fall off), so widen FIRST; bit i
    // then lands at i + base with zeroes below.
    if (!D || D.use_count() > 1)
      D = std::make_shared<ka::BitPlane>();
    ka::BitPlane &B = *D;
    B = *o.D;
    B.resize(o.D->size() + base);
    B <<= base;
    S.clear();
  }
  bool subsetOf(const FactSet &o) const { // this ⊆ o? read-only, no alloc
    if (none()) return true;
    if (o.none()) return false;
    if (D && D == o.D) return true; // interned fast path: X ⊆ X
    if (D && o.D) {
      const uint64_t *A = D->words();
      const uint64_t *B = o.D->words();
      // Widths may differ (lazy widening): our bits past o's width fail.
      const size_t na = D->numWords();
      const size_t nb = std::min(na, o.D->numWords());
      for (size_t i = 0; i < nb; i++)
        if (A[i] & ~B[i]) return false;
      for (size_t i = nb; i < na; i++)
        if (A[i]) return false;
      return true;
    }
    if (D) { // dense this vs tiny sparse o: first unmatched bit exits
      for (int i = D->find_first(); i != -1; i = D->find_next(i))
        if (!std::binary_search(o.S.begin(), o.S.end(), (uint32_t)i))
          return false;
      return true;
    }
    for (uint32_t x : S)
      if (!o.test(x)) return false;
    return true;
  }
  void subtract(const FactSet &o) { // this \= o
    if (none() || o.none()) return;
    if (D && D == o.D) { // interned fast path: X \ X = empty
      clear();
      return;
    }
    if (D) {
      auto &B = mutD();
      if (o.D) B.reset(*o.D);
      else for (uint32_t x : o.S) if (x < B.size()) B.reset(x);
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
    if (D && D == o.D) return; // interned fast path: X ∩ X = X
    if (D && o.D) {
      mutD() &= *o.D;
    } else if (D) { // dense this, sparse other
      llvm::SmallVector<uint32_t, kPromote> surv;
      for (uint32_t x : o.S)
        if (test(x)) surv.push_back(x);
      auto &B = mutD();
      B.reset();
      for (uint32_t x : surv) B.set(x);
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
bool FactSet::EnableShare = false;

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

boost::unordered_flat_set<NodeIndex> g_tpKeyHasDynProbe;
size_t g_tpKeyModelAnswered = 0, g_tpKeyDynProbe = 0,
              g_tpKeyFallbackSites = 0, g_tpKeyTypeRej = 0;

static bool g_sctTableBuilt = false;
// --cfl-sink-instr / --cfl-confirm-sinks (task #31/#32 design)
size_t g_sinkSitesConfirmed = 0, g_sinkSitesEscaped = 0,
              g_sinkSitesViolated = 0;
bool CallGraphPass::runFlowsToResolution() {
  if (CFLDumpFnptrOffsets) {
    dumpFnPtrOffsets();
    exit(0);
  }
  if (!CFLGTTypeCensus.empty()) {
    runGTTypeCensus(CFLGTTypeCensus);
    errs() << "GT-TYPE census complete — exiting (census-only mode)\n";
    exit(0);
  }
  if (CFLDumpGTAux) {
    // GT-matcher fidelity aux (2026-08-25): the matcher consults only
    // ICALL pairs, so (1) compiler-DEVIRTUALIZED dispatches (drbg
    // crypto_init folded to a direct call under a single-table config)
    // and (2) static_call trampoline targets (we resolve THROUGH
    // __SCT__*, GT names the trampoline) can only be credited via pool
    // smear — which precision levers then remove, surfacing phantom
    // FNs. Dump DCALL (direct defined-callee edges) + SCTCALL (direct
    // __SCT__* calls) for gt-match.py --aux; config-independent.
    boost::unordered_flat_set<std::string> seen;
    size_t nD = 0, nS = 0;
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration()) continue;
        for (inst_iterator ii = inst_begin(F), ie = inst_end(F); ii != ie;
             ++ii) {
          const auto *CB = dyn_cast<CallBase>(&*ii);
          if (!CB) continue;
          const Function *CF = CB->getCalledFunction();
          if (!CF || CF->isIntrinsic()) continue;
          const bool sct = CF->getName().starts_with("__SCT__");
          if (!sct && CF->isDeclaration() &&
              !getFuncDef(const_cast<Function *>(CF))->isDeclaration())
            CF = getFuncDef(const_cast<Function *>(CF));
          if (!sct && CF->isDeclaration()) continue;
          std::string line = (sct ? "SCTCALL " : "DCALL ") +
                             F.getName().str() + " " + CF->getName().str();
          if (seen.insert(line).second) {
            errs() << line << "\n";
            (sct ? nS : nD)++;
          }
        }
      }
    }
    errs() << "GT-AUX dump complete: " << nD << " DCALL + " << nS
           << " SCTCALL edges — exiting (dump-only mode)\n";
    exit(0);
  }
  auto tStart = std::chrono::steady_clock::now();
  // Lazy addresses (docs/lazy-address-design.md): the grammar labels still
  // exist (f-edges are collected from them) but the solver runs ONE fact
  // plane; exact offsets live in per-edge labels and per-root descriptors.
  const bool lazyAddr = CFLLazyAddress;
  const unsigned NBg = Graph.numFieldBuckets(); // graph field buckets
  const unsigned NB = lazyAddr ? 0 : NBg;        // solver planes; 0 = one plane

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
  for (const GraphEdge &E : Graph.edges()) {
    NodeIndex cf = getCanonicalNode(E.from), ct = getCanonicalNode(E.to);
    switch (E.kind) {
    case EdgeKind::Copy:
      if (cf != ct) aEdges.emplace_back(dense(cf), dense(ct));
      break;
    case EdgeKind::Deref:
      dEdges.emplace_back(dense(cf), dense(ct));
      break;
    case EdgeKind::FieldAny:
      wildcardNodes.insert(dense(cf));
      break;
    case EdgeKind::Field:
      if (!lazyAddr) // lazy mode takes its f-edges from lazyFEdges below
        fEdges.emplace_back(dense(cf), dense(ct), E.bucket);
      break;
    }
  }
  if (lazyAddr) {
    // Exact-labelled f-edges, one per recorded edge (self-loops kept:
    // a field edge folded onto its own class is a walk).
    std::set<std::tuple<uint32_t, uint32_t, uint32_t>> seenF;
    for (auto &[f, t, li] : lazyFEdges) {
      const uint32_t cf = dense(getCanonicalNode(f)), ct = dense(getCanonicalNode(t));
      if (seenF.insert(std::make_tuple(cf, ct, li)).second)
        fEdges.emplace_back(cf, ct, li);
    }
  }
  const uint32_t N = toOrig.size();
  // Named cells: the name id of each shadow cell (0 for every other
  // node). Shadows are presolve barriers, so each is its own class.
  std::vector<uint32_t> cellNameOf;
  if (namedPlanes()) {
    cellNameOf.assign(N, ka::AccessNames::Original);
    for (uint32_t n = 0; n < N; n++)
      cellNameOf[n] = shadowInfoOf(toOrig[n]).second;
  }
  const uint64_t namedOpenEpoch0 = namedOpenEpoch;
  auto nameOfCell = [&](uint32_t c) -> uint32_t {
    return c < cellNameOf.size() ? cellNameOf[c] : ka::AccessNames::Original;
  };
  std::vector<std::vector<uint32_t>> outA(N);
  for (auto [s, t] : aEdges) outA[s].push_back(t);
  // f-edges as shift transformers: (target, residue).
  std::vector<std::vector<std::pair<uint32_t, uint32_t>>> outF(N);
  for (auto &[b, r, bk] : fEdges)
    outF[b].emplace_back(r, bk);

  // --cfl-dump-agraph: the dense graph of this iteration, nodes =
  // presolve classes, edges classified by what they model so an
  // offline pass can attribute a value-flow component to the edge
  // kind that closes its cycles (call web, memory round trips, ...).
  if (!CFLDumpAGraph.empty()) {
    std::set<std::tuple<const Value *, std::string, unsigned>> directActuals;
    for (auto &Mp : Ctx->Modules)
      for (Function &F2 : *Mp.first)
        for (Instruction &I2 : instructions(F2))
          if (auto *CB2 = dyn_cast<CallBase>(&I2))
            if (const Function *CF2 = CB2->getCalledFunction())
              for (unsigned i = 0; i < CB2->arg_size(); i++)
                directActuals.insert(
                    {CB2->getArgOperand(i), CF2->getName().str(), i});
    boost::unordered_flat_map<NodeIndex, NodeIndex> cellPtr; // deref -> ptr
    for (auto &[p3, d3] : NF.getDerefMap()) cellPtr[d3] = p3;
    auto nodeName = [&](NodeIndex m3) -> std::string {
      const Value *V3 = NF.getValueForNode(m3);
      if (!V3) {
        auto pit = g_opaqueProvenance.find(m3);
        if (pit != g_opaqueProvenance.end()) return pit->second;
        return NF.isObjectNode(m3) ? "<obj>" : "<syn>";
      }
      if (const auto *A2 = dyn_cast<Argument>(V3))
        return (A2->getParent()->getName() + "::arg" + Twine(A2->getArgNo()))
            .str();
      if (const auto *I2 = dyn_cast<Instruction>(V3)) {
        std::string s =
            (I2->getFunction()->getName() + "::" + I2->getOpcodeName()).str();
        if (const auto *CB2 = dyn_cast<CallBase>(I2)) {
          const Function *CF2 = CB2->getCalledFunction();
          s += ":" + (CF2 ? CF2->getName().str() : std::string("<icall>"));
        }
        return s;
      }
      if (V3->hasName()) return V3->getName().str();
      if (const auto *CE2 = dyn_cast<ConstantExpr>(V3)) {
        const Value *base = CE2;
        while (const auto *U2 = dyn_cast<ConstantExpr>(base))
          base = U2->getOperand(0);
        return std::string("cexpr:") + CE2->getOpcodeName() + "(" +
               (base->hasName() ? base->getName().str() : "?") + ")";
      }
      return "<const>";
    };
    auto nodeKind = [&](NodeIndex m3) -> std::string {
      if (NF.isDereferenceNode(m3)) return "deref";
      const Value *V3 = NF.getValueForNode(m3);
      if (!V3) return NF.isObjectNode(m3) ? "obj" : "syn";
      if (isa<Argument>(V3)) return "arg";
      if (const auto *I2 = dyn_cast<Instruction>(V3))
        return std::string("inst:") + I2->getOpcodeName();
      if (isa<Function>(V3)) return "fn";
      if (isa<GlobalVariable>(V3)) return "global";
      if (isa<ConstantExpr>(V3)) return "cexpr";
      return "const";
    };
    const std::string pfx =
        CFLDumpAGraph + ".it" + std::to_string(iteration);
    std::error_code ec1, ec2, ec3;
    raw_fd_ostream nodesOut(pfx + ".nodes", ec1);
    raw_fd_ostream edgesOut(pfx + ".edges", ec2);
    raw_fd_ostream membersOut(pfx + ".members", ec3);
    if (ec1 || ec2 || ec3) {
      WARNING("FlowsTo: cannot write a-graph dump " << pfx << "\n");
    } else {
      // Presolve classes are named by their rep; list every member of
      // a multi-member class so a value can be located by name.
      for (uint32_t n = 0; n < N; n++) {
        auto mit = canonicalClassMembers.find(toOrig[n]);
        if (mit == canonicalClassMembers.end() || mit->second.size() <= 1)
          continue;
        for (NodeIndex m3 : mit->second)
          membersOut << n << " " << nodeKind(m3) << " " << nodeName(m3) << "\n";
      }
      // Node line: id kind members name [ptr-id for cells].
      for (uint32_t n = 0; n < N; n++) {
        NodeIndex canon = toOrig[n];
        size_t mem = 1;
        auto mit = canonicalClassMembers.find(canon);
        if (mit != canonicalClassMembers.end()) mem = mit->second.size();
        nodesOut << n << " " << nodeKind(canon) << " " << mem << " ";
        if (NF.isDereferenceNode(canon)) {
          auto cp = cellPtr.find(canon);
          NodeIndex p3 = cp == cellPtr.end() ? AndersNodeFactory::InvalidIndex
                                             : cp->second;
          nodesOut << "*" << (p3 == AndersNodeFactory::InvalidIndex
                                  ? std::string("?")
                                  : nodeName(p3));
          auto dp = p3 == AndersNodeFactory::InvalidIndex
                        ? toDense.end()
                        : toDense.find(getCanonicalNode(p3));
          if (dp != toDense.end()) nodesOut << " " << dp->second;
        } else {
          nodesOut << nodeName(canon);
        }
        nodesOut << "\n";
      }
      // Edge kind from the endpoint classes. A formal's in-edge is a
      // DIRECT call edge when any member of the source class is an
      // actual of a direct call to that function at that position;
      // every other actual->formal edge is indirect-call wiring (or
      // summary wiring, which is also site-pooled).
      auto isDirectActual = [&](NodeIndex sc, const Argument *A2) {
        auto chk = [&](NodeIndex m3) {
          const Value *V3 = NF.getValueForNode(m3);
          return V3 && directActuals.count({V3, A2->getParent()->getName().str(),
                                            A2->getArgNo()});
        };
        if (chk(sc)) return true;
        auto mit = canonicalClassMembers.find(sc);
        if (mit != canonicalClassMembers.end())
          for (NodeIndex m3 : mit->second)
            if (chk(m3)) return true;
        return false;
      };
      auto edgeKind = [&](uint32_t s, uint32_t t) -> std::string {
        NodeIndex sc = toOrig[s], tc = toOrig[t];
        const bool sd = NF.isDereferenceNode(sc), td = NF.isDereferenceNode(tc);
        if (sd && td) return "memcpy";
        if (td) return "store";
        if (sd) return "load";
        const Value *Vt = NF.getValueForNode(tc);
        if (const auto *A2 = dyn_cast_or_null<Argument>(Vt))
          return isDirectActual(sc, A2) ? "call" : "icall";
        if (Vt && isa<CallBase>(Vt)) return "ret";
        if (const auto *I2 = dyn_cast_or_null<Instruction>(Vt))
          return std::string("copy:") + I2->getOpcodeName();
        return "copy";
      };
      for (auto [s, t] : aEdges)
        edgesOut << s << " " << t << " " << edgeKind(s, t) << "\n";
      for (auto &[b, r, bk] : fEdges)
        edgesOut << b << " " << r << " f" << bk << "\n";
      CG_LOG("FlowsTo: a-graph dumped to " << pfx << ".{nodes,edges} (" << N
             << " nodes, " << aEdges.size() << " a + " << fEdges.size()
             << " f edges)\n");
    }
  }

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
    if (n == AndersNodeFactory::InvalidIndex) {
      WARNING("FlowsTo: AT function has NO value node (never mintable): "
              << F->getName() << "\n");
      continue;
    }
    NodeIndex canon = getCanonicalNode(n);
    auto [it, ins] = funcOfCanon.emplace(canon, F);
    if (!ins && it->second != F && it->second->getName() != F->getName())
      // Same-name entries are per-TU Function* copies of one symbol
      // (the #45 display footgun) — only DIFFERENT functions sharing a
      // class lose an identity.
      WARNING("FlowsTo: AT function canonical collision: "
              << F->getName() << " shares class with " << it->second->getName()
              << " — only one identity minted\n");
    if (!toDense.count(canon))
      CG_LOG("FlowsTo: AT function class edge-less (not in dense graph, "
             "never mintable this round): " << F->getName() << "\n");
  }

  // Derivation slice (1-bit taint): keep only classes that can appear in
  // some function->fptr derivation, or that supply alias evidence (shared
  // value origins) for a memory join usable by one. Alias is
  // over-approximated by Steensgaard classes (unification), which the
  // precise shared-root join then refines on the slice.
  std::vector<char> inSlice; // empty => no slicing
  // Channel-cell wiring cone: classes that can influence an indirect
  // call's callee expression at all — backward over a/f edges from the
  // callee expressions, jumping at a cell to every cell of its
  // Steensgaard class (may-alias over-approximation) AND to those
  // cells' owner pointers (a pointer produced by a load needs its own
  // cell wired before it can acquire keys). Cells outside this cone
  // never need a channel: their content cannot reach any answer.
  std::vector<char> wireCone; // empty => wire every cell
  if (CFLFlowsToSlice || (CFLChannelCells && CFLChannelCone)) {
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
    if (CFLChannelCells && CFLChannelCone) {
      wireCone.assign(N, 0);
      boost::unordered_flat_set<uint32_t> jumpedW;
      std::vector<uint32_t> qW;
      auto addW = [&](uint32_t v) {
        if (!wireCone[v]) { wireCone[v] = 1; qW.push_back(v); }
      };
      for (uint32_t v : bSeeds) addW(v);
      while (!qW.empty()) {
        uint32_t v = qW.back();
        qW.pop_back();
        if (isCell[v]) {
          uint32_t cls = find(v);
          if (jumpedW.insert(cls).second)
            for (uint32_t c : classCells[cls]) {
              addW(c);
              for (uint32_t p : cellParents[c]) addW(p);
            }
          for (uint32_t p : cellParents[v]) addW(p);
        }
        for (uint32_t u : inA[v]) addW(u);
      }
      size_t nCone = 0;
      for (uint32_t v = 0; v < N; v++) nCone += wireCone[v];
      CG_LOG("ChannelCone: " << nCone << "/" << N
             << " classes can influence a callee expression; channels are "
                "wired for their cells only\n");
    }
    if (CFLFlowsToSlice) { // slice pruning proper (cone-only runs keep the graph)

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
    } // slice pruning
  }

  // Every load/store has its own assistant cell node, so a pointer class
  // carries one cell per access site — keep them all; the join rule must
  // see the store-side and load-side cells of the same class.
  std::vector<std::vector<uint32_t>> cellsOf(N);
  for (auto [p, c] : dEdges) {
    auto &cs = cellsOf[p];
    if (std::find(cs.begin(), cs.end(), c) == cs.end()) cs.push_back(c);
  }
  // Channel cells (docs/channel-cells-design.md): no access role is
  // inferred here any more — the flush splits every cell into its
  // write half (in-edges) and read half (out-edges) unconditionally.
  if (CFLChannelCells) {
    std::vector<char> isCellN(N, 0);
    for (auto [p, c] : dEdges) isCellN[c] = 1;
    if (VerboseLevel >= 3 && N < 200) {
      // Tiny-graph full dump: every class with its edges — the whole
      // truth for micro repros.
      auto gnm = [&](uint32_t c2) -> std::string {
        const Value *V2 = NF.getValueForNode(toOrig[c2]);
        if (V2 && V2->hasName()) return V2->getName().str();
        if (V2)
          if (const auto *I2 = dyn_cast<Instruction>(V2))
            return (I2->getFunction()->getName() + "::" +
                    I2->getOpcodeName()).str();
        return NF.isObjectNode(toOrig[c2]) ? "<obj>" : "<syn>";
      };
      for (uint32_t c = 0; c < N; c++) {
        errs() << "G c" << c << " [" << gnm(c) << "]"
               << (isCellN[c] ? " CELL" : "");
        for (auto [ea, eb] : aEdges)
          if (ea == c) errs() << " a->c" << eb;
        for (auto [pa, pb] : dEdges)
          if (pa == c) errs() << " d->c" << pb;
        for (auto &[fa, fb, fk] : fEdges)
          if (fa == c) errs() << " f" << fk << "->c" << fb;
        errs() << "\n";
      }
    }
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
  std::vector<uint32_t> bidiPrunedCls; // origins the cone gate skipped
  std::vector<uint32_t> starvedCls;    // adoption-starved formals not minted
  // Re-callable (#43): incremental wiring appends its edge deltas to
  // aEdges/dEdges/fEdges/wildcardNodes and recomputes — the prune's
  // soundness argument ("the oracle recomputes per outer iteration")
  // otherwise breaks if the graph were reused across rebuilds.
  auto computeBidiCone = [&]() {
    auto tBidi = std::chrono::steady_clock::now();
    bidiUF.assign(N, 0);
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
    // Named cells: a shadow is a plane of its cell's class (satellite),
    // so it belongs to its cell's partition.
    for (uint32_t u = 0; u < (uint32_t)cellNameOf.size(); u++)
      if (cellNameOf[u] != ka::AccessNames::Original) {
        auto d = toDense.find(getCanonicalNode(shadowInfoOf(toOrig[u]).first));
        assert(d != toDense.end() && "a shadow's cell is in the graph");
        bunite(u, d->second);
      }
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
  };
  if (CFLBidiPrune) computeBidiCone();
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
  // The graph node a root was minted on. Key-identity roots
  // (--cfl-key-identity) are minted on channel nodes, which lie past the
  // dense graph and have no graph node: InvalidIndex.
  auto rootOrig = [&](uint32_t rid) -> NodeIndex {
    if (rid >= rootClassOf.size() || rootClassOf[rid] >= toOrig.size())
      return AndersNodeFactory::InvalidIndex;
    return toOrig[rootClassOf[rid]];
  };
  auto rootValue = [&](uint32_t rid) -> const Value * {
    const NodeIndex n = rootOrig(rid);
    return n == AndersNodeFactory::InvalidIndex ? nullptr
                                                : NF.getValueForNode(n);
  };
  std::vector<char> rootParkable;    // rid -> pure no-in identity
  std::vector<std::pair<uint32_t, uint32_t>> seeds; // (class, root id)
  uint32_t nextRoot = 0;
  size_t bidiPrunable = 0;
  size_t cellIdentityAblated = 0; // --cfl-key-identity: cells left rootless
  // usercopy-certificate classes must be minted unconditionally: letting
  // the bidi/lazy oracles skip them would pre-decide the very question
  // the certificate asks (does this origin reach an fptr operand?).
  boost::unordered_flat_set<uint32_t> certCls;
  if (CFLCertUserCopy)
    for (auto &p : g_userCertObjs) {
      auto dIt = toDense.find(getCanonicalNode(p.first));
      if (dIt != toDense.end()) certCls.insert(dIt->second);
    }
  // Identity roots by what they stand for: content of a cell nothing in
  // the program wrote, a formal no call reaches, the result of a call
  // without a body, a loaded or computed value with no incoming edge.
  // Plan 3.11: only formals, bodiless call results and the varargs of an
  // uncalled function are environment objects; the rest are no objects.
  enum IdKind { IdSpecial, IdFormal, IdCallResult, IdCell, IdLoad,
                IdIntValue, IdVararg, IdOther };
  static const char *idKindName[] = {"special", "formal", "call-result",
                                     "cell", "load", "int-value", "vararg",
                                     "other"};
  auto identityKindOf = [&](uint32_t n) -> IdKind {
    std::vector<NodeIndex> members;
    collectCanonicalMembers(toOrig[n], members);
    if (members.empty()) members.push_back(toOrig[n]);
    int best = IdOther;
    for (NodeIndex m : members) {
      int k = IdOther;
      const Value *V = NF.getValueForNode(m);
      if (NF.isSpecialNode(m)) k = IdSpecial;
      else if (NF.isVarargNode(m)) k = IdVararg;
      else if (NF.isDereferenceNode(m)) k = IdCell;
      else if (V && isa<Argument>(V)) k = IdFormal;
      else if (V && isa<CallBase>(V)) k = IdCallResult;
      else if (V && isa<LoadInst>(V))
        k = V->getType()->isPointerTy() ? IdLoad : IdIntValue;
      else if (V && !V->getType()->isPointerTy()) k = IdIntValue;
      best = std::min(best, k);
    }
    return (IdKind)best;
  };
  auto isEnvKind = [](IdKind k) {
    return k == IdSpecial || k == IdFormal || k == IdCallResult ||
           k == IdVararg;
  };
  auto isExternGlobalClass = [&](uint32_t n) {
    auto ext = [&](NodeIndex m) {
      const auto *G = dyn_cast_or_null<GlobalVariable>(NF.getValueForNode(m));
      return G && G->isDeclaration();
    };
    if (ext(toOrig[n])) return true;
    auto mit = canonicalClassMembers.find(toOrig[n]);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m : mit->second)
        if (ext(m)) return true;
    return false;
  };
  std::map<std::string, size_t> identityKinds, identityNotMinted;
  // --cfl-alloc-origins: environment roots (rid-indexed), their depth
  // (0 = an environment site; d = content d levels below one), and the
  // content root of each cluster key an environment root anchors.
  std::vector<char> envRoot;
  std::vector<uint8_t> envDepth;
  boost::unordered_flat_map<uint64_t, uint32_t> envContentOfKey;
  for (uint32_t n = 0; n < N; n++) {
    if (!inSlice.empty() && !inSlice[n]) continue;
    // A shadow holds only content filed under its name; content nobody
    // wrote is the identity of the cell it shadows (seeded below).
    if (nameOfCell(n) != ka::AccessNames::Original) continue;
    auto fit = funcOfCanon.find(toOrig[n]);
    const bool isFunc = fit != funcOfCanon.end();
    const bool isCert = !certCls.empty() && certCls.count(n);
    // Adoption-starved formals/varargs: in-degree 0 because the
    // summary OWNS the callsite wiring, not because the value is a
    // source. Minting them creates tracer-dye origins that traverse
    // the walked body's whole value web and weld every deref cell
    // they touch into one cluster (5.18 3-TU repro: an unnamed
    // formal origin fused the ethtool reader cells with the
    // phy_fixup_list chains — reader sites went 3 -> 73 targets).
    if (!hasIn[n] && !isFunc && !isCert && !hasOrigin[n]) {
      auto starvedBy = [&](const Value *cv) -> const Function * {
        if (const auto *A2 = dyn_cast_or_null<Argument>(cv))
          return A2->getParent();
        return nullptr;
      };
      const Function *PF = starvedBy(NF.getValueForNode(toOrig[n]));
      if (!PF) {
        auto mIt = canonicalClassMembers.find(toOrig[n]);
        if (mIt != canonicalClassMembers.end())
          for (NodeIndex m : mIt->second) {
            PF = starvedBy(NF.getValueForNode(m));
            if (!PF && NF.isVarargNode(m))
              PF = dyn_cast_or_null<Function>(NF.getValueForNode(m));
            if (PF) break;
          }
      }
      if (PF &&
          Ctx->FuncSummaries.count(getFuncDef(const_cast<Function *>(PF)))) {
        starvedCls.push_back(n); // C7 mirrors this refusal
        continue;
      }
    }
    if (!hasIn[n] || isFunc || hasOrigin[n] || isCert) {
      if (!bidiMarked.empty() && !isFunc && !isCert && !bidiMarked[n]) {
        // Outside the fptr cone: this origin's facts can key joins only
        // at cells inside its partition's d/f closure, which never
        // meets an fptr partition — it cannot influence any answer.
        // The oracle recomputes per outer iteration, so cone growth
        // from newly wired callee edges re-admits origins as needed.
        bidiPrunable++;
        bidiPrunedCls.push_back(n);
        continue;
      }
      if (!lazyA.empty() && !isFunc && !isCert && !lazyA[n]) {
        // Not backward-reachable from any answer on the initial
        // quotient: defer — the post-drain expansion re-checks on the
        // live quotient and mints the moment the class enters A.
        lazyDeferred.push_back(n);
        continue;
      }
      // --cfl-key-identity: NO dereference cell gets a root — the
      // content identity lives on the channel key (minted at channel
      // creation for external origins).
      if (CFLKeyIdentity && !isFunc && !isCert && !hasOrigin[n] &&
          NF.isDereferenceNode(toOrig[n])) {
        cellIdentityAblated++;
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
      bool env = false;
      if (!isFunc && !hasOrigin[n] && !isCert) {
        const IdKind ik = identityKindOf(n);
        if (VerboseLevel >= 2) identityKinds[idKindName[ik]]++;
        if (CFLAllocOrigins && !isEnvKind(ik)) {
          identityNotMinted[idKindName[ik]]++;
          continue; // not an object: a read of it is empty (rule a)
        }
        env = true;
      } else if (CFLAllocOrigins && !isFunc && isExternGlobalClass(n)) {
        env = true;
      }
      uint32_t rid = nextRoot++;
      if (CFLAllocOrigins) {
        envRoot.resize(nextRoot, 0);
        envRoot[rid] = env;
      }
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

  if (CFLAllocOrigins) {
    envRoot.resize(nextRoot, 0);
    envDepth.assign(nextRoot, 0);
  }

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
    uint64_t at;        // worklist pops at merge time (event order)
  };
  // Small graphs afford the FULL merge log (a few 10k events), which
  // lets the report show the giant's growth from its first merge; the
  // size gate below is what keeps kernel-scale logs bounded.
  const bool blobLogAll = CFLProbeBlobFormation && N < 200000;
  std::vector<BlobEv> blobEvents;
  const char *blobCtx = "?";
  uint32_t blobCtxOrigin = UINT32_MAX;
  uint32_t blobCtxShift = 0; // residue of the join key (fs runs)
  clsSize.assign(N, 1);
  for (uint32_t n2 = 0; n2 < N; n2++) {
    auto cit2 = canonicalClassMembers.find(toOrig[n2]);
    if (cit2 != canonicalClassMembers.end() && cit2->second.size() > 1)
      clsSize[n2] = (uint32_t)cit2->second.size();
  }
  if (CFLProbeBlobFormation) {
    // Q1 estimator: one entry per canonical class (dedupe by the
    // canonical key), singletons included at size 1.
    {
      boost::unordered_flat_set<NodeIndex> seenCls;
      std::vector<uint64_t> szs;
      for (uint32_t n2 = 0; n2 < N; n2++) {
        auto cit2 = canonicalClassMembers.find(toOrig[n2]);
        if (cit2 == canonicalClassMembers.end() || cit2->second.size() <= 1) {
          szs.push_back(1);
          continue;
        }
        if (seenCls.insert(toOrig[n2]).second)
          szs.push_back((uint64_t)cit2->second.size());
      }
      cflDumpClassHist("INITIAL", szs);
    }
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

  boost::unordered_flat_map<NodeIndex, NodeIndex> derefToPtr; // cell -> ptr
  // Solver-made nodes (channel hubs, read halves) have no factory node;
  // the flush records a name so traces can show them.
  std::unordered_map<uint32_t, std::string> chanNodeName;
  // Name of one factory node (value, cell "*p", object); "" when nameless.
  auto nodeNameOf = [&](NodeIndex m3) -> std::string {
      std::string pre;
      // derefMap is keyed by the POINTER; invert it so a cell is named
      // after the pointer it dereferences ("*p", "**p").
      for (int lvl = 0; lvl < 3 && NF.isDereferenceNode(m3); lvl++) {
        if (derefToPtr.size() != NF.getDerefMap().size()) {
          derefToPtr.clear();
          for (auto &[p3, d3] : NF.getDerefMap()) derefToPtr[d3] = p3;
        }
        auto dit = derefToPtr.find(m3);
        if (dit == derefToPtr.end()) return std::string();
        pre += "*";
        m3 = dit->second;
      }
      const Value *V3 = NF.getValueForNode(m3);
      if (!V3) {
        auto pit = g_opaqueProvenance.find(m3);
        if (pit != g_opaqueProvenance.end()) return pre + pit->second;
        if (NF.isObjectNode(m3))
          return std::string("<obj") + (NF.isHeapObject(m3) ? " heap" : "") +
                 (NF.isOpaqueObject(m3) ? " opaque" : "") + ">";
        return std::string();
      }
      if (V3->hasName())
        return pre + V3->getName().str();
      if (const auto *I2 = dyn_cast<Instruction>(V3)) {
        std::string s =
            (I2->getFunction()->getName() + "::" + I2->getOpcodeName()).str();
        if (const auto *CB2 = dyn_cast<CallBase>(I2)) {
          const Function *CF2 = CB2->getCalledFunction();
          s += ":" + (CF2 ? CF2->getName().str() : std::string("<icall>"));
        } else if (const auto *AI2 = dyn_cast<AllocaInst>(I2)) {
          // Locals are unnamed at O0: the allocated struct type is the
          // only handle a user has to name one ("...::alloca:struct.x").
          if (const auto *ST2 = dyn_cast<StructType>(AI2->getAllocatedType()))
            if (ST2->hasName()) s += ":" + ST2->getName().str();
        }
        // Source line when debug info is present ("fn::load@736"): the
        // opcode alone does not identify an access in a big function.
        if (const DebugLoc &DL2 = I2->getDebugLoc())
          if (DL2.getLine()) s += "@" + std::to_string(DL2.getLine());
        return pre + s;
      }
      if (const auto *A2 = dyn_cast<Argument>(V3))
        return pre + (A2->getParent()->getName() + "::arg" +
                      Twine(A2->getArgNo())).str();
      if (const auto *CE2 = dyn_cast<ConstantExpr>(V3)) {
        // Name by the first global the expression is built on.
        const Value *base = CE2;
        while (const auto *U2 = dyn_cast<ConstantExpr>(base))
          base = U2->getOperand(0);
        return pre + "cexpr:" + CE2->getOpcodeName() + "(" +
               (base->hasName() ? base->getName().str() : "?") + ")";
      }
      if (isa<Constant>(V3))
        return pre + "const:" + std::string(V3->getType()->isPointerTy()
                                                ? "ptr" : "data");
      return pre + "<valnode#" + std::to_string(m3) + ">";
  };
  // Name match for instruments that address a node by name: a dense id
  // names its presolve-canonical node, so a node folded into a presolve
  // class is only reachable through that class's member list.
  auto denseNameMatches = [&](uint32_t d, StringRef sub) -> bool {
    if (d >= toOrig.size()) {
      auto cn = chanNodeName.find(d);
      return cn != chanNodeName.end() && StringRef(cn->second).contains(sub);
    }
    const NodeIndex canon = toOrig[d];
    if (StringRef(nodeNameOf(canon)).contains(sub)) return true;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m2 : mit->second)
        if (StringRef(nodeNameOf(m2)).contains(sub)) return true;
    return false;
  };
  // Edge-kind label for a class (by its canonical node): tells a chain
  // reader whether an a-edge arrival is a call (into a formal), a return
  // (into a call result), a load from a cell, a store into a cell, or a
  // copy. Formals are further marked when their function has no direct
  // caller (reached only through icall wiring) or is fixed-arity yet
  // admitted at a variadic-typed call (the lenient varargs rule).
  std::unordered_map<const Function *, std::string> formalMarkMemo;
  auto nodeKind = [&](uint32_t cls) -> std::string {
    if (cls >= toOrig.size()) return "chan";
    const NodeIndex canon = toOrig[cls];
    if (NF.isDereferenceNode(canon)) return "cell";
    const Value *V = NF.getValueForNode(canon);
    if (!V) return NF.isObjectNode(canon) ? "obj" : "value";
    if (const auto *A = dyn_cast<Argument>(V)) {
      const Function *F = A->getParent();
      auto it = formalMarkMemo.find(F);
      if (it == formalMarkMemo.end()) {
        bool direct = false, varargAdmitted = false;
        auto cit = Ctx->Callers.find(F);
        if (cit != Ctx->Callers.end())
          for (const CallBase *CB : cit->second) {
            if (CB->getCalledFunction() == F) direct = true;
            else if (!F->isVarArg() && CB->getFunctionType()->isVarArg())
              varargAdmitted = true;
          }
        std::string m = "formal";
        if (!direct) m += "/icall-only";
        if (varargAdmitted) m += "/vararg-admitted";
        it = formalMarkMemo.emplace(F, m).first;
      }
      return it->second;
    }
    if (isa<CallBase>(V)) return "callret";
    if (isa<LoadInst>(V)) return "load";
    if (isa<GetElementPtrInst>(V)) return "gep";
    if (isa<PHINode>(V) || isa<SelectInst>(V) || isa<CastInst>(V)) return "copy";
    if (isa<AllocaInst>(V)) return "alloca";
    if (isa<GlobalValue>(V)) return "global";
    if (isa<Constant>(V)) return "const";
    return "value";
  };
  auto protBlameName = [&](uint32_t cls) -> std::string {
    if (cls >= toOrig.size()) {
      auto cn = chanNodeName.find(cls);
      return cn != chanNodeName.end() ? cn->second : "<synthetic>";
    }
    NodeIndex canon = toOrig[cls];
    auto &nameOf = nodeNameOf;
    std::string n = nameOf(canon);
    if (!n.empty())
      return n;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m2 : mit->second) {
        n = nameOf(m2);
        if (!n.empty())
          return n;
      }
    return std::string(NF.isDereferenceNode(canon) ? "<deref#"
                       : NF.isValueNode(canon)      ? "<valnode#"
                                                    : "<node#") +
           std::to_string(canon) + ">";
  };
  // Coupler census state: per-class subsystem masks over OWNED data
  // origins; weld events recorded in merge().
  std::vector<uint64_t> ownedMask;
  boost::unordered_flat_map<std::string, std::pair<uint64_t, uint64_t>>
      weldBlame; // name -> (count, united-bits)
  size_t weldEvents = 0, mergeEvents = 0;
  if (CFLCensusCouplers) {
    subsysComputeRoot(Ctx->Modules);
    ownedMask.assign(N, 0);
    for (uint32_t rid = 0; rid < nextRoot; rid++) {
      if (funcRootOf.count(rid))
        continue; // fn identities excluded: data-object plane only
      const Value *ov = rootValue(rid);
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
  // Constant globals without pointer-typed content (string literals,
  // lookup tables): nothing can store into them, so their cells never
  // carry a pointer and a channel for them is pure fan-out. Per root.
  auto isConstDataRoot = [&](uint32_t cls) -> char {
    if (cls >= toOrig.size()) return 0;
    const auto *GV =
        dyn_cast_or_null<GlobalVariable>(NF.getValueForNode(toOrig[cls]));
    return GV && GV->isConstant() && !containsPointerType(GV->getValueType());
  };
  std::vector<char> rootConstData(nextRoot, 0);
  for (uint32_t rid = 0; rid < nextRoot; rid++)
    rootConstData[rid] = isConstDataRoot(rootClassOf[rid]);
  // Lazy addresses: per-root descriptor (object root, byte offset, stride:
  // 0 exact, UINT32_MAX = the object's range wildcard). Non-address roots
  // (functions, identities, channel-minted ids) never remap.
  std::vector<uint32_t> addrObj;
  std::vector<int64_t> addrOff;
  std::vector<uint32_t> addrStride;
  std::vector<uint32_t> addrExtent; // strided: byte length covered from addrOff (0 = to the object's end)
  std::vector<char> addrIsObj;
  std::map<std::tuple<uint32_t, int64_t, uint32_t, uint32_t>, uint32_t> addrIndex;
  std::unordered_map<uint32_t, std::vector<uint32_t>> addrKeysOfObj;
  size_t lazyMinted = 0, lazyStrided = 0, lazyX = 0, lazyOverlapBridges = 0;
  auto addrGrow = [&]() {
    if (addrIsObj.size() < nextRoot) {
      addrObj.resize(nextRoot, UINT32_MAX);
      addrOff.resize(nextRoot, 0);
      addrStride.resize(nextRoot, 0);
      addrExtent.resize(nextRoot, 0);
      addrIsObj.resize(nextRoot, 0);
    }
  };
  // Object extent in bytes (0 = unknown): exact offsets outside it, and
  // negative offsets, are the range wildcard, so pointer walks over an
  // object of known size terminate at its end.
  std::unordered_map<uint32_t, int64_t> objBytesMemo;
  auto objBytes = [&](uint32_t obj) -> int64_t {
    auto it = objBytesMemo.find(obj);
    if (it != objBytesMemo.end()) return it->second;
    int64_t sz = 0;
    const uint32_t rc = obj < rootClassOf.size() ? rootClassOf[obj] : UINT32_MAX;
    const Value *V = rc < toOrig.size() ? NF.getValueForNode(toOrig[rc]) : nullptr;
    if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) {
      sz = (int64_t)GV->getParent()->getDataLayout().getTypeAllocSize(GV->getValueType());
    } else if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) {
      const DataLayout &DLa = AI->getModule()->getDataLayout();
      sz = (int64_t)DLa.getTypeAllocSize(AI->getAllocatedType());
      if (const auto *CI = dyn_cast<ConstantInt>(AI->getArraySize())) sz *= CI->getSExtValue();
      else sz = 0;
    } else if (const auto *CB = dyn_cast_or_null<CallBase>(V)) {
      if (CB->arg_size() >= 1)
        if (const auto *CI = dyn_cast<ConstantInt>(CB->getArgOperand(0)))
          if (CI->getType()->isIntegerTy(64) || CI->getType()->isIntegerTy(32)) sz = CI->getSExtValue();
    }
    if (sz < 0) sz = 0;
    objBytesMemo[obj] = sz;
    return sz;
  };
  // Per-object cap: a walk whose cycle passes through memory (store,
  // reload, increment) is invisible to the a/f SCC pass; after kLazyCap
  // distinct exact addresses an object's further exact mints become its
  // range root (sound: X over-approximates every offset).
  // The cap exists for objects of UNKNOWN size: an object whose byte size
  // is known has finitely many in-bounds offsets (an offset at or past the
  // size is already the range), so counting them buys nothing and cost
  // every struct with more than 32 fields its field sensitivity (bfd ~45,
  // elf_backend_data 103, asection ~40: 9.1 M capped mints on nm-new,
  // which made the exact model field-insensitive on exactly the objects
  // the dispatch reads go through). Identity roots have no size; they
  // get a cap wide enough for any struct they stand for.
  const uint32_t kLazyCap = CFLLazyCap;      // per writable object without a struct type
  const uint32_t kLazyCapId = CFLLazyCap;    // identity roots
  std::unordered_map<uint32_t, uint32_t> addrCountOf;
  std::unordered_set<uint32_t> lazyCappedObjs;
  std::unordered_map<uint32_t, uint64_t> lazyCappedHits; // obj -> refused mints
  // Struct-typed objects get one address per 8-byte slot plus slack (the
  // type is known only after the typed-access census below is declared).
  std::function<uint32_t(uint32_t)> capForTypedObj;
  auto isConstGlobalRoot = [&](uint32_t obj) -> bool { // never walked: uncapped
    const uint32_t rc = obj < rootClassOf.size() ? rootClassOf[obj] : UINT32_MAX;
    if (rc >= toOrig.size()) return false;
    const auto *GV = dyn_cast_or_null<GlobalVariable>(NF.getValueForNode(toOrig[rc]));
    return GV && GV->isConstant();
  };
  auto isIdentityRoot = [&](uint32_t obj) -> bool {
    const uint32_t rc = obj < rootClassOf.size() ? rootClassOf[obj] : UINT32_MAX;
    if (rc >= toOrig.size()) return true;
    const Value *V = NF.getValueForNode(toOrig[rc]);
    return !V || NF.isDereferenceNode(toOrig[rc]);
  };
  size_t lazyCapped = 0;
  // Progression widening (walks through memory are invisible to the SCC
  // pass): an arithmetic exact mint e whose object already holds e-s and
  // e-2s is a walk; the run becomes one strided root (base, s), which
  // absorbs the rest. Member offsets never take part.
  std::unordered_map<uint32_t, std::set<int64_t>> arithOffs;
  std::unordered_map<uint32_t, std::vector<std::tuple<int64_t, uint32_t, uint32_t>>> objStrided; // off, stride, extent
  size_t lazyWidened = 0, lazyAbsorbed = 0;
  std::function<void(size_t)> typeConflictReport; // defined with the census below
  std::function<uint32_t(uint32_t, int64_t, uint32_t, bool, uint32_t)> mintAddrE;
  auto mintAddr = [&](uint32_t obj, int64_t off, uint32_t stride, bool arith) -> uint32_t {
    return mintAddrE(obj, off, stride, arith, 0);
  };
  mintAddrE = [&](uint32_t obj, int64_t off, uint32_t stride, bool arith, uint32_t extent) -> uint32_t {
    if (stride == 0 || stride == UINT32_MAX) extent = 0;
    if (stride != UINT32_MAX) {
      const int64_t sz = objBytes(obj);
      if (off < 0 || (sz > 0 && off >= sz) || off > ((int64_t)1 << 20))
        return mintAddr(obj, 0, UINT32_MAX, false);
    } else off = 0;
    if (stride == 0 && arith) {
      for (auto &[b, st, ex] : objStrided[obj]) // covered by a strided root already
        if (off >= b && (off - b) % (int64_t)st == 0 && (ex == 0 || off < b + (int64_t)ex)) {
          lazyAbsorbed++;
          return mintAddrE(obj, b, st, false, ex);
        }
      auto &offs = arithOffs[obj];
      offs.insert(off);
      auto it0 = offs.find(off);
      int scanned = 0;
      for (auto it1 = it0; it1 != offs.begin() && scanned < 8; scanned++) {
        --it1;
        const int64_t st = off - *it1;
        if (st <= 0 || st > ((int64_t)1 << 20)) continue;
        if (!offs.count(*it1 - st)) continue;
        int64_t base = *it1 - st;
        while (offs.count(base - st)) base -= st;
        lazyWidened++;
        return mintAddr(obj, base, (uint32_t)st, false);
      }
    }
    auto [it, ins] = addrIndex.try_emplace(std::make_tuple(obj, off, stride, extent), 0u);
    if (!ins) return it->second;
    if (stride != UINT32_MAX) {
      uint32_t &cnt = addrCountOf[obj];
      // Constant globals are never walked by the program but byte
      // arithmetic over them still mints offset by offset: a higher cap
      // (above any vtable's slot count) keeps their slots exact.
      uint32_t capHere = isConstGlobalRoot(obj) ? std::max<uint32_t>(128, 4 * kLazyCap)
                         : isIdentityRoot(obj) ? kLazyCapId : kLazyCap;
      if (capForTypedObj) capHere = std::max(capHere, capForTypedObj(obj));
      if (cnt >= capHere) {
        addrIndex.erase(it);
        // Measured 2026-09-27: falling back to the strided root (off mod
        // sizeof T, stride sizeof T) instead of the range keeps fields
        // apart across an array's elements but mints a family per field
        // per object and bridges each with every exact address it
        // overlaps: the 46-function exact reproducer went from 1:36 to
        // 67 min (14,725 families, 243,863 bridges, 296 M facts) with no
        // change in its answer. The range stays the fallback.
        if (lazyCappedObjs.insert(obj).second && lazyCappedObjs.size() <= 5)
          WARNING("LazyAddr: object r" << obj << " ("
                  << protBlameName(rootClassOf[obj]).substr(0, 50)
                  << ", size " << objBytes(obj) << ") passed " << capHere
                  << " exact addresses; further offsets are its range\n");
        lazyCapped++;
        lazyCappedHits[obj]++;
        return mintAddr(obj, 0, UINT32_MAX, false);
      }
      cnt++;
    }
    if (lazyMinted && lazyMinted % 50000 == 0) {
      CG_LOG("LazyAddr: " << lazyMinted << " addresses so far; last r" << obj
             << " " << protBlameName(rootClassOf[obj]).substr(0, 40) << " +" << off
             << " stride " << stride << "\n");
      if (lazyMinted == 50000 && typeConflictReport) typeConflictReport(60);
    }
    const uint32_t rid = nextRoot++;
    FactSet::Universe = nextRoot; // widen BEFORE the first set
    rootClassOf.push_back(rootClassOf[obj]); // named after its object
    rootConstData.push_back(rootConstData[obj]);
    rootParkable.push_back(rootParkable[obj]);
    if (nexusGate) rootNexus.push_back(rootNexus[obj]);
    addrGrow();
    addrObj[rid] = obj; addrOff[rid] = off; addrStride[rid] = stride; addrExtent[rid] = extent;
    addrIsObj[rid] = 1;
    it->second = rid;
    lazyMinted++;
    if (stride == UINT32_MAX) lazyX++;
    else if (stride) { lazyStrided++; objStrided[obj].emplace_back(off, stride, extent); }
    return rid;
  };
  // Pointer-walk cycles: an f-edge inside an a/f SCC with nonzero net
  // shift is a strided walk (stride = gcd of the SCC's exact shifts); a
  // cycle with a negative or strided step is the range wildcard. Computed
  // once over the presolved graph; the fixpoint terminates because a
  // strided root absorbs further steps that are multiples of its stride.
  std::vector<uint32_t> sccIdOf;
  std::vector<int64_t> sccG;
  std::vector<char> sccX;
  // Per-root memo of remaps: (label, cycle?) -> result. A remap is an
  // indexed lookup on the hot path; the tuple map is touched only when a
  // new address is minted.
  std::vector<std::vector<std::pair<uint32_t, uint32_t>>> remapMemo;
  std::function<uint32_t(uint32_t, uint32_t, uint32_t, uint32_t)> remapRidSlow;
  auto remapRid = [&](uint32_t rid, uint32_t label, uint32_t from, uint32_t to) -> uint32_t {
    addrGrow();
    if (!addrIsObj[rid] || addrStride[rid] == UINT32_MAX) return rid;
    const bool cyc = from < sccIdOf.size() && to < sccIdOf.size() &&
                     sccIdOf[from] == sccIdOf[to] &&
                     (sccG[sccIdOf[from]] != 0 || sccX[sccIdOf[from]]);
    const uint32_t key = (label << 1) | (cyc ? 1u : 0u);
    if (remapMemo.size() <= rid) remapMemo.resize(nextRoot + 1024);
    for (auto &pr : remapMemo[rid]) if (pr.first == key) return pr.second;
    const uint32_t res = remapRidSlow(rid, label, from, to);
    if (remapMemo.size() <= rid) remapMemo.resize(nextRoot + 1024);
    remapMemo[rid].emplace_back(key, res);
    return res;
  };
  // Typed-heap conflict census (docs/lazy-address-design.md, user 09-17):
  // an object has one type; every member access whose struct is not
  // compatible with it (same type at an element boundary, embedded at that
  // offset, or embedding it: container_of) is a conflict = a real type
  // confusion or the first imprecise arrival of a pointer at the object.
  // Recorded in solve order with the delivering edge; never prunes.
  struct TypeWitness { const StructType *ty; int64_t base; };
  struct TypeConflict { uint32_t obj, from, to; const StructType *ty; int64_t base; };
  std::unordered_map<uint32_t, TypeWitness> objPrimary;
  std::unordered_map<uint32_t, std::set<const StructType *>> objConflictTys;
  std::vector<TypeConflict> typeConflicts;
  std::unordered_map<std::string, uint32_t> conflictEdgeCount;
  size_t typedObjects = 0, witnessChecks = 0;
  const DataLayout *lazyDL = Ctx->Modules.empty() ? nullptr : &Ctx->Modules.front().first->getDataLayout();
  auto sameStruct = [&](const StructType *a, const StructType *b) -> bool {
    if (a == b) return true;
    if (!a || !b || !a->hasName() || !b->hasName()) return false;
    return stripStructNameSuffix(a->getName()) == stripStructNameSuffix(b->getName());
  };
  // A C union is lowered to a struct holding its largest member; any
  // member type that fits at offset 0 of a union is a legitimate view.
  auto isUnionTy = [&](const StructType *T) -> bool {
    return T && T->hasName() && T->getName().starts_with("union.");
  };
  std::function<bool(const StructType *, int64_t, const StructType *)> embeds;
  embeds = [&](const StructType *Sy, int64_t off, const StructType *S2) -> bool {
    if (off == 0 && sameStruct(Sy, S2)) return true;
    if (off < 0 || !lazyDL || Sy->isOpaque() || Sy->getNumElements() == 0) return false;
    const StructLayout *SL = lazyDL->getStructLayout(const_cast<StructType *>(Sy));
    if ((uint64_t)off >= SL->getSizeInBytes()) return false;
    if (off == 0 && isUnionTy(Sy) && !S2->isOpaque() &&
        lazyDL->getStructLayout(const_cast<StructType *>(S2))->getSizeInBytes() <= SL->getSizeInBytes())
      return true;
    const unsigned idx = SL->getElementContainingOffset((uint64_t)off);
    int64_t fo = (int64_t)SL->getElementOffset(idx);
    Type *FT = Sy->getElementType(idx);
    while (auto *AT = dyn_cast<ArrayType>(FT)) {
      const int64_t es = (int64_t)lazyDL->getTypeAllocSize(AT->getElementType());
      if (es <= 0) return false;
      fo += ((off - fo) / es) * es;
      FT = AT->getElementType();
    }
    if (auto *FS = dyn_cast<StructType>(FT)) return embeds(FS, off - fo, S2);
    return false;
  };
  auto typeCompatible = [&](const TypeWitness &P, const StructType *S2, int64_t b2) -> bool {
    if (!lazyDL || !P.ty) return true;
    int64_t rel = b2 - P.base;
    const int64_t psz = P.ty->isOpaque() ? 0 : (int64_t)lazyDL->getStructLayout(const_cast<StructType *>(P.ty))->getSizeInBytes();
    if (psz > 0 && rel >= 0) rel %= psz; // arrays of the primary type
    if (rel >= 0 && embeds(P.ty, rel, S2)) return true;   // S2 inside P
    if (rel <= 0 && embeds(S2, -rel, P.ty)) return true;  // P inside S2 (container_of)
    return false;
  };
  auto declaredType = [&](uint32_t obj) -> const StructType * {
    const uint32_t rc = obj < rootClassOf.size() ? rootClassOf[obj] : UINT32_MAX;
    const Value *V = rc < toOrig.size() ? NF.getValueForNode(toOrig[rc]) : nullptr;
    Type *T = nullptr;
    if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) T = GV->getValueType();
    else if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) T = AI->getAllocatedType();
    while (T && isa<ArrayType>(T)) T = cast<ArrayType>(T)->getElementType();
    return dyn_cast_or_null<StructType>(T);
  };
  size_t untypedSkipped = 0;
  auto isAllocatedObject = [&](uint32_t obj) -> bool { // heap: an allocation call
    const uint32_t rc = obj < rootClassOf.size() ? rootClassOf[obj] : UINT32_MAX;
    const Value *V = rc < toOrig.size() ? NF.getValueForNode(toOrig[rc]) : nullptr;
    return V && isa<CallBase>(V) && !NF.isDereferenceNode(toOrig[rc]);
  };
  size_t lazyTypedDrops = 0;
  // Cap hook for mintAddrE: a struct-typed object (declared type of a
  // global or alloca; the first typed access of a heap object) has one
  // address per 8-byte slot at most, so its field offsets are never
  // capped away (bfd ~45 fields, elf_backend_data 103 hooks). Untyped
  // objects (byte buffers, arrays walked through memory) keep the count
  // cap, which is what it was for.
  capForTypedObj = [&](uint32_t obj) -> uint32_t {
    if (!lazyDL) return 0;
    // Declared objects: the whole value type (an array of structs is as
    // many slots as the array has).
    const uint32_t rc = obj < rootClassOf.size() ? rootClassOf[obj] : UINT32_MAX;
    const Value *V = rc < toOrig.size() ? NF.getValueForNode(toOrig[rc]) : nullptr;
    Type *Full = nullptr;
    if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) Full = GV->getValueType();
    else if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) Full = AI->getAllocatedType();
    if (Full && declaredType(obj)) {
      const uint64_t sz = lazyDL->getTypeAllocSize(Full);
      return sz > (1u << 20) ? 0 : (uint32_t)(sz / 8 + 8);
    }
    auto it = objPrimary.find(obj);
    const StructType *T = it != objPrimary.end() ? it->second.ty : nullptr;
    if (!T || T->isOpaque()) return 0;
    const uint64_t sz = lazyDL->getStructLayout(const_cast<StructType *>(T))->getSizeInBytes();
    if (sz > (1u << 20)) return 0;
    // A heap object of known size holding k copies of its type: k slots' worth.
    const int64_t ob = objBytes(obj);
    const uint64_t span = (ob > 0 && (uint64_t)ob > sz) ? (uint64_t)ob : sz;
    return span > (1u << 20) ? 0 : (uint32_t)(span / 8 + 8);
  };
  auto noteTypeWitness = [&](uint32_t obj, const StructType *S2, int64_t base,
                             uint32_t from, uint32_t to) -> bool { // true = compatible
    witnessChecks++;
    auto pit = objPrimary.find(obj);
    if (pit == objPrimary.end()) {
      const StructType *D = declaredType(obj);
      if (!D && !isAllocatedObject(obj) &&
          !(CFLLazyTypeIdentity && isIdentityRoot(obj) && obj < rootClassOf.size() &&
            rootClassOf[obj] < toOrig.size())) {
        untypedSkipped++; return true; // synthetic: no type of its own
      }
      if (!D) {
        // Heap: the first typed access defines the object, unless the
        // allocation size is constant and this type does not fit it (an
        // early confused access must not mistype the object).
        const int64_t sz = objBytes(obj);
        const int64_t s2sz = S2->isOpaque() ? 0 : (int64_t)lazyDL->getStructLayout(const_cast<StructType *>(S2))->getSizeInBytes();
        if (sz > 0 && s2sz > 0 && s2sz != sz && sz % s2sz != 0) return true;
      }
      pit = objPrimary.emplace(obj, TypeWitness{D ? D : S2, D ? 0 : base}).first;
      typedObjects++;
      if (!D) return true;
    }
    if (typeCompatible(pit->second, S2, base)) return true;
    if (objConflictTys[obj].insert(S2).second) {
      if (typeConflicts.size() < 500000) typeConflicts.push_back({obj, from, to, S2, base});
      conflictEdgeCount[protBlameName(from).substr(0, 70)]++;
    }
    return false;
  };
  typeConflictReport = [&](size_t firstN) {
    errs() << "TypeConfusion: " << objConflictTys.size() << " objects with conflicting access types of "
           << typedObjects << " typed (" << witnessChecks << " checks, " << typeConflicts.size()
           << " (object,type) conflicts; " << untypedSkipped
           << " checks on identity/synthetic content skipped)\n";
    size_t shown = 0;
    for (const TypeConflict &c : typeConflicts) {
      if (shown++ >= firstN) break;
      const TypeWitness &P = objPrimary[c.obj];
      errs() << "TypeConfusion:  #" << shown << " obj r" << c.obj << " "
             << protBlameName(rootClassOf[c.obj]).substr(0, 44) << " primary "
             << (P.ty && P.ty->hasName() ? stripStructNameSuffix(P.ty->getName()).str() : "?")
             << " <- " << (c.ty->hasName() ? stripStructNameSuffix(c.ty->getName()).str() : "?")
             << "@" << c.base << " via " << protBlameName(c.from).substr(0, 50) << " ["
             << nodeKind(c.from) << "] -> " << protBlameName(c.to).substr(0, 40) << "\n";
    }
    std::vector<std::pair<uint32_t, std::string>> top;
    for (auto &[nm, cnt] : conflictEdgeCount) top.push_back({cnt, nm});
    std::sort(top.begin(), top.end(), std::greater<>());
    errs() << "TypeConfusion: top pointers by (object,type) conflicts they deliver:\n";
    for (size_t i2 = 0; i2 < top.size() && i2 < 20; i2++)
      errs() << "TypeConfusion:   " << top[i2].first << "  " << top[i2].second << "\n";
  };
  auto lazyTraced = [&](uint32_t obj) -> bool {
    if (CFLLazyTraceObject.empty()) return false;
    return StringRef(protBlameName(rootClassOf[obj])).contains(CFLLazyTraceObject);
  };
  remapRidSlow = [&](uint32_t rid, uint32_t label, uint32_t from, uint32_t to) -> uint32_t {
    addrGrow();
    if (!addrIsObj[rid]) return rid;
    {
      const LazyLabel &L0 = lazyLabels[label];
      if (L0.ty && L0.stride == 0 && addrStride[rid] == 0 &&
          !noteTypeWitness(addrObj[rid], L0.ty, addrOff[rid], from, to) &&
          CFLLazyTypedAccess) {
        lazyTypedDrops++;
        return UINT32_MAX; // typed access: no address for a mistyped object
      }
    }
    if (lazyTraced(addrObj[rid])) {
      const LazyLabel &L = lazyLabels[label];
      errs() << "LazyTrace: obj r" << addrObj[rid] << " from address r" << rid
             << " (+" << addrOff[rid] << " s" << addrStride[rid] << ") label +" << L.off
             << " stride " << L.stride << (L.arith ? " arith" : " member")
             << " edge " << protBlameName(from).substr(0, 60) << " -> "
             << protBlameName(to).substr(0, 60) << " [" << nodeKind(from) << ">"
             << nodeKind(to) << "]\n";
    }
    const uint32_t st = addrStride[rid];
    if (st == UINT32_MAX) return rid; // X stays X
    const LazyLabel &L = lazyLabels[label];
    const uint32_t obj = addrObj[rid];
    const bool cyc = from < sccIdOf.size() && to < sccIdOf.size() &&
                     sccIdOf[from] == sccIdOf[to] &&
                     (sccG[sccIdOf[from]] != 0 || sccX[sccIdOf[from]]);
    if (cyc) {
      if (sccX[sccIdOf[from]] || L.stride != 0) return mintAddr(obj, 0, UINT32_MAX, false);
      const int64_t g = sccG[sccIdOf[from]];
      if (g == 1) return mintAddr(obj, 0, UINT32_MAX, false); // byte walk: every offset
      if (st == 0) return mintAddr(obj, addrOff[rid], (uint32_t)g, false);
      return mintAddr(obj, addrOff[rid], (uint32_t)std::gcd((int64_t)st, g), false);
    }
    if (L.stride == 0) {
      if (st != 0 && L.off >= 0 && L.off % (int64_t)st == 0 &&
          (addrExtent[rid] == 0 || L.off < (int64_t)addrExtent[rid]))
        return rid; // absorbed: a member step inside the strided range
      // A member step off a strided address shifts the whole family; the
      // covered length is unchanged.
      return mintAddrE(obj, addrOff[rid] + L.off, st, L.arith && st == 0, addrExtent[rid]);
    }
    if (st == 0) return mintAddrE(obj, addrOff[rid] + L.off, L.stride, false, L.extent);
    return mintAddr(obj, 0, UINT32_MAX, false); // two variable indices
  };
  auto mintX = [&](uint32_t rid) -> uint32_t {
    addrGrow();
    if (!addrIsObj[rid]) return rid;
    return mintAddr(addrObj[rid], 0, UINT32_MAX, false);
  };
  auto remapPlane = [&](const FactSet &src, uint32_t label, uint32_t from,
                        uint32_t to, FactSet &out) {
    out.clear();
    src.forEach([&](uint32_t bit) {
      const uint32_t r2 = remapRid(bit, label, from, to);
      if (r2 != UINT32_MAX) out.set(r2);
    });
  };
  // Scratch for the remapped plane: one per thread, capacity retained.
  auto remapScratch = [&]() -> FactSet & {
    static thread_local FactSet rm;
    return rm;
  };
  // A strided address covers {off + k*stride : k >= 0, off + k*stride <
  // off + extent} (extent 0: to the object's end). The bound is what
  // keeps a variable index into `[4 x ptr]` from reading every later slot.
  auto strEnd = [&](uint32_t s) -> int64_t {
    return addrExtent[s] ? addrOff[s] + (int64_t)addrExtent[s] : INT64_MAX;
  };
  auto addrOverlap = [&](uint32_t a, uint32_t b) -> bool {
    if (addrObj[a] != addrObj[b]) return false;
    const uint32_t sa = addrStride[a], sb = addrStride[b];
    if (sa == UINT32_MAX || sb == UINT32_MAX) return true;
    if (sa == 0 && sb == 0) return addrOff[a] == addrOff[b];
    if (sa == 0)
      return addrOff[a] >= addrOff[b] && addrOff[a] < strEnd(b) &&
             (addrOff[a] - addrOff[b]) % (int64_t)sb == 0;
    if (sb == 0)
      return addrOff[b] >= addrOff[a] && addrOff[b] < strEnd(a) &&
             (addrOff[b] - addrOff[a]) % (int64_t)sa == 0;
    if (addrOff[a] >= strEnd(b) || addrOff[b] >= strEnd(a)) return false; // disjoint ranges
    const int64_t g = std::gcd((int64_t)sa, (int64_t)sb);
    return ((addrOff[a] - addrOff[b]) % g) == 0; // residues compatible; conservative within the overlap
  };
  if (lazyAddr) {
    addrGrow();
    for (uint32_t rid = 0; rid < nextRoot; rid++) {
      const uint32_t rc = rootClassOf[rid];
      addrObj[rid] = rid; addrOff[rid] = 0; addrStride[rid] = 0; addrExtent[rid] = 0;
      addrIsObj[rid] = !funcRootOf.count(rid) && rc < toOrig.size();
      addrIndex[std::make_tuple(rid, (int64_t)0, (uint32_t)0, (uint32_t)0)] = rid;
    }
    if (lazyLabels.empty()) lazyLabelFor(0, 0);
  }
  if (!bidiMarked.empty())
    CG_LOG("BidiPrune: pruned " << bidiPrunable << " origins outside the "
           << "fptr cone; minted " << nextRoot << " roots ("
           << (100.0 * bidiPrunable / std::max<size_t>(1, bidiPrunable + nextRoot))
           << "% pruned)\n");
  CG_LOG("FlowsTo: minted " << nextRoot << " roots ("
         << funcRootOf.size() << " function), " << wildcardNodes.size()
         << " wildcard nodes, " << NSHIFT << " shift planes\n");
  if (!identityKinds.empty()) {
    std::string line;
    for (auto &[k, c] : identityKinds)
      line += " " + k + " " + std::to_string(c);
    CG_LOG("FlowsTo: identity candidates by kind:" << line << "\n");
  }
  if (CFLAllocOrigins) {
    std::string line;
    for (auto &[k, c] : identityNotMinted)
      line += " " + k + " " + std::to_string(c);
    size_t nEnvRoots = 0;
    for (char e : envRoot) nEnvRoots += e;
    CG_LOG("AllocOrigins: " << nEnvRoots << " environment roots; not "
           << "minted:" << line << "\n");
  }
  if (!lazyA.empty())
    CG_LOG("LazyMint: deferred " << lazyDeferred.size()
           << " candidate roots outside initial A ("
           << (100.0 * lazyDeferred.size() /
               std::max<size_t>(1, lazyDeferred.size() + nextRoot))
           << "% of candidates)\n");
  for (auto &[why, cnt] : wildcardReasons)
    CG_LOG("FlowsTo wildcard[" << why << "]: " << cnt << "\n");
  if (CFLKeyIdentity)
    CG_LOG("KeyIdentity: " << cellIdentityAblated
           << " dereference cells left without a per-access root\n");
  // --cfl-trace-func: follow one function root's fact through the solve.
  int64_t traceRoot = -1;
  // "r<N>" names a root by id (ids are printed by the meet tracer and
  // the channel names, so a smear can be followed by the exact origin).
  // Ids past the presolve roots name roots minted DURING the solve (key
  // identities, lazy mints): accepted, resolved when they appear.
  auto ridOf = [&](StringRef s) -> int64_t {
    uint32_t v;
    return s.size() > 1 && s[0] == 'r' && !s.substr(1).getAsInteger(10, v)
               ? (int64_t)v
               : -1;
  };
  // A comma-separated list traces several roots in one solve (the
  // coupler census needs the key origins of many joins); arrivals are
  // tagged root=r<N>. traceRoot stays the first root for the single-root
  // consumers (final-reach dump, per-value trace).
  std::vector<uint32_t> traceRoots;
  std::vector<uint8_t> traceMark; // rid -> traced (grown on demand)
  auto resolveRoot = [&](StringRef want) -> int64_t {
    if (ridOf(want) >= 0) {
      const int64_t r = ridOf(want);
      errs() << "TRACE root " << r << " = "
             << ((uint64_t)r < rootClassOf.size()
                     ? protBlameName(rootClassOf[r])
                     : std::string("<minted during the solve>"))
             << " (by id)\n";
      return r;
    }
    for (auto &[rid, F] : funcRootOf)
      if (F->getName() == want) {
        errs() << "TRACE root " << rid << " = " << F->getName() << "\n";
        return rid;
      }
    for (auto &[rid, F] : funcRootOf)
      if (F->getName().contains(want)) {
        errs() << "TRACE root " << rid << " = " << F->getName() << "\n";
        return rid;
      }
    // Not a function: trace an OBJECT origin by its value name (a
    // global/alloca/alloc-site) — needed to follow how an object
    // reaches a load's owner pointer (the breadth side of the
    // derivation witness), not only how a function reaches the fptr.
    // Same naming as the blob probe / meet tracer, so unnamed O0
    // values (allocation calls "fn::call:callee", locals
    // "fn::alloca:struct.T") are addressable; cell roots ("*p") only
    // when asked for explicitly. Exact name wins over substring.
    int64_t sub = -1;
    for (uint32_t rid = 0; rid < rootClassOf.size(); rid++) {
      const uint32_t rc = rootClassOf[rid];
      if (rc >= toOrig.size()) continue;
      std::string nm = protBlameName(rc);
      if (nm.empty()) continue;
      if (nm[0] == '*' && !want.starts_with("*")) continue;
      if (StringRef(nm) == want) {
        errs() << "TRACE root " << rid << " = origin " << nm << "\n";
        return rid;
      }
      if (sub < 0 && StringRef(nm).contains(want)) sub = rid;
    }
    if (sub >= 0)
      errs() << "TRACE root " << sub << " = origin "
             << protBlameName(rootClassOf[sub]) << " (substring)\n";
    else
      errs() << "TRACE: no function/origin root matches '" << want << "'\n";
    return sub;
  };
  if (!CFLTraceFunc.empty()) {
    StringRef spec(CFLTraceFunc);
    while (!spec.empty()) {
      auto [head, rest] = spec.split(',');
      spec = rest;
      if (head.empty()) continue;
      const int64_t r = resolveRoot(head);
      if (r < 0) continue;
      traceRoots.push_back((uint32_t)r);
      if (traceMark.size() <= (size_t)r) traceMark.resize(r + 1, 0);
      traceMark[r] = 1;
    }
    if (!traceRoots.empty()) traceRoot = traceRoots.front();
  }
  size_t traceEvents = 0;
  const char *tHow = "seed";
  uint32_t tFrom = UINT32_MAX;
  uint32_t tKeyO = UINT32_MAX, tKeyS = 0; // join/bridge key behind a merge-or-bridge arrival
  uint32_t tCell = UINT32_MAX;            // the dereference cell whose join caused it
  uint32_t tPtr = UINT32_MAX;             // the pointer class whose sweep issued the join
  const size_t traceCap = 200000 * std::max<size_t>(1, traceRoots.size());
  // --cfl-trace-first: log only the first arrival of a root at a class
  // (what a chain walk uses), so the log is bounded by the class count
  // and the event cap never truncates the chain to a far site.
  boost::unordered_flat_set<uint64_t> traceFirstSeen;
  auto traceHit = [&](uint32_t n, uint32_t s, bool bridged,
                      int64_t rid = -1) {
    if (CFLTraceFirst) {
      const uint64_t k = ((uint64_t)(rid < 0 ? traceRoot : rid) << 40) | ((uint64_t)n << 8) | (s & 0xff);
      if (!traceFirstSeen.insert(k).second) return;
    } else if (traceEvents++ > traceCap) return;
    errs() << "TRACE + c" << n << " s" << s << (bridged ? " [br]" : "")
           << " via " << tHow;
    // Edge kind of an a-edge arrival: what the target class is (formal,
    // call result, load, cell, copy) — the reader needs "call into a
    // formal" vs "load from a cell" to tell a root cause from propagation.
    if (StringRef(tHow) == "a-prop" || StringRef(tHow).starts_with("merge-move"))
      errs() << "[" << (tFrom == UINT32_MAX ? std::string("?") : nodeKind(tFrom))
             << ">" << nodeKind(n) << "]";
    errs() << " from c";
    if (tFrom == UINT32_MAX) errs() << "?"; else errs() << tFrom;
    if (rid >= 0 && traceRoots.size() > 1) errs() << " root=r" << rid;
    // Name at arrival time: later merges retire these ids, so the
    // fixpoint census cannot name a chain read off this log.
    errs() << "  " << protBlameName(n).substr(0, 70);
    // Use-type tag: the struct types this value is dereferenced as (GEP
    // source element types over its users), so a scan can find the
    // first arrival of an object at a value used as a foreign type.
    {
      static std::unordered_map<uint32_t, std::string> useMemo;
      auto um = useMemo.find(n);
      if (um == useMemo.end()) {
        std::string tag;
        if (n < toOrig.size())
          if (const Value *V = NF.getValueForNode(toOrig[n]))
            if (V->getType()->isPointerTy()) {
              SmallVector<StringRef, 4> tys;
              for (const User *U : V->users()) {
                const auto *G = dyn_cast<GetElementPtrInst>(U);
                if (!G || G->getPointerOperand() != V) continue;
                const auto *ST = dyn_cast<StructType>(G->getSourceElementType());
                if (!ST || !ST->hasName()) continue;
                StringRef nm = ST->getName();
                nm.consume_front("struct."); nm.consume_front("union.");
                nm = nm.rsplit('.').first.empty() ? nm : nm.rsplit('.').first; // strip .NNN
                if (std::find(tys.begin(), tys.end(), nm) == tys.end()) tys.push_back(nm);
                if (tys.size() == 3) break;
              }
              for (StringRef t : tys) tag += (tag.empty() ? " use=" : ",") + t.str();
            }
        um = useMemo.emplace(n, tag).first;
      }
      errs() << um->second;
    }
    // A join-triggered merge is explained by its key and by the pointer
    // whose facts carried that key into the sweep: "why did these two
    // cells become one" is answered by naming that pointer, then asking
    // why IT holds both keys.
    if (StringRef(tHow).starts_with("merge") && tKeyO != UINT32_MAX &&
        tKeyO < rootClassOf.size()) {
      errs() << "  key=(r" << tKeyO << " "
             << protBlameName(rootClassOf[tKeyO]).substr(0, 40) << ",s"
             << tKeyS << ")";
      if (tPtr != UINT32_MAX)
        errs() << " by-ptr=c" << tPtr << ":" << protBlameName(tPtr).substr(0, 60);
    }
    errs() << "\n";
  };
  // --cfl-trace-meet=A,B: two origins that must never alias. Record how
  // each arrives at every class (propagation kind, source class,
  // residue) and report the first classes that come to hold both, with
  // both chains walked back to their seeds: the meeting class is where
  // the analysis unions them, the chains say through which edges or
  // merges.
  int64_t meetRid[2] = {-1, -1};
  if (!CFLTraceMeet.empty()) {
    auto [nA, nB] = StringRef(CFLTraceMeet).split(',');
    StringRef want[2] = {nA, nB};
    for (int w = 0; w < 2; w++) {
      if (ridOf(want[w]) >= 0) {
        meetRid[w] = ridOf(want[w]);
        errs() << "TRACE-MEET root " << (w ? "B" : "A") << " = r" << meetRid[w]
               << " "
               << ((uint64_t)meetRid[w] < rootClassOf.size()
                       ? protBlameName(rootClassOf[meetRid[w]])
                       : std::string("<minted during the solve>"))
               << " (by id)\n";
      }
      for (uint32_t rid = 0; rid < rootClassOf.size() && meetRid[w] < 0; rid++) {
        auto fit = funcRootOf.find(rid);
        std::string nm = fit != funcRootOf.end()
                             ? fit->second->getName().str()
                             : protBlameName(rootClassOf[rid]);
        // A cell root ("*p") matches only when asked for explicitly.
        if (!nm.empty() && nm[0] == '*' && !want[w].starts_with("*")) continue;
        bool hit = StringRef(nm).contains(want[w]);
        if (!hit) {
          // The rep may be another member of a merged class: scan them.
          auto mit = canonicalClassMembers.find(rootOrig(rid));
          if (mit != canonicalClassMembers.end())
            for (NodeIndex m3 : mit->second) {
              std::string mn = nodeNameOf(m3);
              if (!mn.empty() && mn[0] != '*' && StringRef(mn).contains(want[w])) {
                hit = true; nm = mn; break;
              }
            }
        }
        if (hit) {
          meetRid[w] = rid;
          errs() << "TRACE-MEET root " << (w ? "B" : "A") << " = r" << rid
                 << " " << nm << "\n";
        }
      }
      if (meetRid[w] < 0)
        errs() << "TRACE-MEET: no root matches '" << want[w] << "'\n";
    }
    if (meetRid[0] < 0 || meetRid[1] < 0) meetRid[0] = meetRid[1] = -1;
  }
  // Every arrival of a traced origin at a class (capped), oldest first;
  // the chain walk follows the OLDEST arrival's source. Merge and bridge
  // arrivals carry the (origin, residue) key that caused them.
  struct MeetArr { const char *how; uint32_t from, s, keyO, keyS, cell; };
  std::unordered_map<uint32_t, SmallVector<MeetArr, 4>> meetArr[2];
  size_t meetsShown = 0;
  auto keyStr = [&](const MeetArr &m) -> std::string {
    if (m.keyO == UINT32_MAX || m.keyO >= rootClassOf.size()) return "";
    std::string r = " key=(r" + std::to_string(m.keyO) + " " +
                    protBlameName(rootClassOf[m.keyO]).substr(0, 40) + ",s" +
                    std::to_string(m.keyS) + ")";
    if (m.cell != UINT32_MAX && m.cell < toOrig.size())
      r += " by-cell=" + protBlameName(m.cell).substr(0, 50); // "*p": p joined the key
    return r;
  };
  auto meetHit = [&](uint32_t n, uint32_t s, int w) {
    auto &v = meetArr[w][n];
    const bool first = v.empty();
    const bool isMerge = StringRef(tHow).starts_with("merge");
    const bool chanHop = StringRef(tHow).starts_with("chan"); // flush wiring
    const bool keyed = isMerge || chanHop || StringRef(tHow) == "bridge-init";
    if (v.size() < 4)
      v.push_back({tHow, tFrom, s, keyed ? tKeyO : UINT32_MAX, tKeyS,
                   (isMerge || chanHop) ? tCell : UINT32_MAX});
    if (!first || !meetArr[1 - w].count(n) || meetsShown >= 5) return;
    meetsShown++;
    errs() << "TRACE-MEET #" << meetsShown << " at c" << n << " size="
           << clsSize[n] << " " << protBlameName(n).substr(0, 70) << "\n";
    for (int k = 0; k < 2; k++) {
      errs() << "TRACE-MEET   " << (k ? "B" : "A") << " chain (newest first):";
      uint32_t cur = n;
      boost::unordered_flat_set<uint32_t> seen;
      for (int d = 0; d < 40; d++) {
        auto it = meetArr[k].find(cur);
        if (it == meetArr[k].end()) {
          // Unhooked arrival (the root was already in this class when
          // it became the merge keeper): name the class at least.
          errs() << " [no record c" << cur << " size=" << clsSize[cur] << " "
                 << protBlameName(cur).substr(0, 50) << "]";
          break;
        }
        const MeetArr &m = it->second.front();
        errs() << "\n" << "TRACE-MEET     c" << cur << " s" << m.s << " via "
               << m.how << keyStr(m) << "  " << protBlameName(cur).substr(0, 64);
        if (it->second.size() > 1) {
          errs() << "  [also:";
          for (size_t i = 1; i < it->second.size(); i++)
            errs() << " " << it->second[i].how << "<c" << it->second[i].from
                   << keyStr(it->second[i]);
          errs() << "]";
        }
        if (m.from == UINT32_MAX || !seen.insert(cur).second) break;
        cur = m.from;
      }
      errs() << "\n";
    }
  };
  const bool traceAny = traceRoot >= 0 || meetRid[0] >= 0;
  auto traceCheck = [&](uint32_t n, uint32_t s, bool br, const FactSet &bits) {
    for (uint32_t r : traceRoots)
      if (bits.test(r)) traceHit(n, s, br, r);
    if (meetRid[0] >= 0) {
      if (bits.test((uint32_t)meetRid[0])) meetHit(n, s, 0);
      if (bits.test((uint32_t)meetRid[1])) meetHit(n, s, 1);
    }
  };
  auto traceCheckOne = [&](uint32_t n, uint32_t s, uint32_t o) {
    if (o < traceMark.size() && traceMark[o]) traceHit(n, s, false, o);
    if (meetRid[0] >= 0) {
      if (o == (uint32_t)meetRid[0]) meetHit(n, s, 0);
      if (o == (uint32_t)meetRid[1]) meetHit(n, s, 1);
    }
  };
  // Threading: parallel phases freeze the union-find (no merges, no path
  // compression — find is a pure read walk) and guard every write to
  // another class's planes with that class's spinlock. Merges, cluster
  // registry inserts and SCC collapses run only between phases, on the
  // main thread; WavePool::run barriers give the happens-before edges.
  unsigned solverThreads = CFLSolverThreads == 0
                               ? std::max(1u, std::thread::hardware_concurrency())
                               : (unsigned)CFLSolverThreads;
  if (traceAny && solverThreads > 1) {
    CG_LOG("FlowsTo: --cfl-trace-func/--cfl-trace-meet are single-threaded; "
           "forcing --cfl-solver-threads=1\n");
    solverThreads = 1;
  }
  if (CFLBatchWorkers > 1 && solverThreads > 1) {
    // fork() does not carry the wave pool's threads into workers, and
    // the parent only replays events — all parallelism is processes.
    CG_LOG("FlowsTo: --cfl-batch-workers active; drains run "
           "single-threaded per worker\n");
    solverThreads = 1;
  }
  // Task #46: dense-plane interning (hash-consed COW buffers). Sharing
  // is created only for strictly sequential drains: at T>1 the in-place
  // OR-ins race with COW pointer swaps, and forked batch workers may
  // re-raise their own thread count after the fork — so workers-mode
  // disables it wholesale. (T>1-safe sharing = a future lever, paired
  // with target-partitioned exchange.)
  // Batching (even sequential, no workers) is ALSO excluded: batch-
  // local fact universes resize the dense-plane width per batch, and a
  // COW-shared buffer adopted under one batch's universe can receive a
  // bit past its width after the universe reshapes (BitVector::set OOB
  // at km, found 2026-08-11 — a #46 regression dormant since a997bc1
  // because no sequential-batch run had been taken since).
  const bool internOK = CFLInternPlanes && solverThreads == 1 &&
                        CFLBatchWorkers <= 1 && CFLBatchRoots == 0;
  FactSet::EnableShare = internOK;
  if (CFLInternPlanes && !internOK)
    CG_LOG("FlowsTo: plane interning inactive (requires a sequential "
           "unbatched solve: T=1, no batch roots/workers)\n");
  bool parallelPhase = false; // true only inside a parallel wave phase
  // Channel-cells headroom: channel nodes are appended at barrier
  // flushes; the fixed atomic arrays (classLk/inWL/keyCount) cannot
  // grow, so they get capacity up front. Vectors grow at the barrier
  // (no live references across the flush).
  // Headroom bound: realized keys ≤ origins × NSHIFT; origins ≤ N.
  const uint32_t NCap =
      CFLChannelCells ? N + std::max<uint32_t>(3 * N, 1u << 20) : N;
  std::unique_ptr<std::atomic<uint8_t>[]> classLk(
      new std::atomic<uint8_t>[NCap]);
  for (uint32_t i = 0; i < NCap; i++)
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
  if (lazyAddr) {
    sccIdOf.assign(N, UINT32_MAX);
    std::vector<uint32_t> idx(N, UINT32_MAX), low(N, 0), stk;
    std::vector<char> on(N, 0);
    uint32_t counter = 0, nscc = 0;
    auto succ = [&](uint32_t u, size_t i) -> uint32_t {
      return i < outA[u].size() ? find(outA[u][i]) : find(outF[u][i - outA[u].size()].first);
    };
    for (uint32_t s0 = 0; s0 < N; s0++) {
      if (find(s0) != s0 || idx[s0] != UINT32_MAX) continue;
      std::vector<std::pair<uint32_t, size_t>> cs{{s0, 0}};
      idx[s0] = low[s0] = counter++; stk.push_back(s0); on[s0] = 1;
      while (!cs.empty()) {
        uint32_t u = cs.back().first; size_t &i = cs.back().second;
        const size_t deg = outA[u].size() + outF[u].size();
        if (i < deg) {
          const uint32_t v = succ(u, i++);
          if (idx[v] == UINT32_MAX) {
            idx[v] = low[v] = counter++; stk.push_back(v); on[v] = 1;
            cs.push_back({v, 0});
          } else if (on[v]) low[u] = std::min(low[u], idx[v]);
        } else {
          if (low[u] == idx[u]) {
            uint32_t w;
            do { w = stk.back(); stk.pop_back(); on[w] = 0; sccIdOf[w] = nscc; } while (w != u);
            nscc++;
          }
          cs.pop_back();
          if (!cs.empty()) low[cs.back().first] = std::min(low[cs.back().first], low[u]);
        }
      }
    }
    for (uint32_t n2 = 0; n2 < N; n2++) if (find(n2) != n2) sccIdOf[n2] = sccIdOf[find(n2)];
    sccG.assign(nscc, 0); sccX.assign(nscc, 0);
    for (uint32_t u = 0; u < N; u++)
      for (auto [t, r] : outF[u]) {
        const uint32_t su = sccIdOf[u], st = sccIdOf[t];
        if (su != st) continue;
        const LazyLabel &L = lazyLabels[r];
        if (L.stride != 0 || L.off < 0) sccX[su] = 1;
        else if (L.off != 0) sccG[su] = std::gcd(sccG[su], L.off);
      }
    size_t nCyc = 0; for (uint32_t i2 = 0; i2 < nscc; i2++) nCyc += (sccG[i2] != 0 || sccX[i2]);
    CG_LOG("LazyAddr: " << nscc << " a/f SCCs, " << nCyc << " with a nonzero-shift cycle\n");
  }
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
      jdirty(N), dirtyBr(N), joined(N), cellJoined(N);
  for (uint32_t i = 0; i < N; i++) {
    R[i].resize(NSHIFT);
    RB[i].resize(NSHIFT);
    dirty[i].resize(NSHIFT);
    jdirty[i].resize(NSHIFT);
    dirtyBr[i].resize(NSHIFT);
    joined[i].resize(NSHIFT); // facts already pushed to ALL cells of class
    // cellJoined[c][s]: GLOBAL rids whose (o,s) cluster already
    // contains cell c — a monotone mirror of the clusterRep registry
    // outcome, indexed by the cell's class. Tested before the registry
    // probe: 99.8% of join lookups at km were redundant re-probes of
    // cold hash lines (36B cycles = 66% of the solve); a hit here is a
    // guaranteed registry no-op. Marks can only be MISSED (merges
    // release the loser's plane; the slow path re-derives) — never
    // wrongly present, because clusters and the registry are both
    // monotone. Persists across batches (the registry does too).
    cellJoined[i].resize(NSHIFT);
  }
  std::vector<std::vector<uint32_t>> bridgesOf(N); // VX partners (class ids)
  // Named cells: the shadows of a class's cells, one class per name
  // (name, a member of that name's shadow class). Merging two classes
  // merges their shadows name by name (attachShadow), so a merged class
  // keeps its content by name: NamedCells.lean's planes.
  std::vector<llvm::SmallVector<std::pair<uint32_t, uint32_t>, 2>> satOf(
      cellNameOf.empty() ? 0 : N);
  // Roots minted on a class that has no identity shadow yet: they enter
  // its identity plane when one joins (an identity shadow exists only at
  // named loads). (rid, plane)
  std::vector<llvm::SmallVector<std::pair<uint32_t, uint32_t>, 1>> pendingId(
      cellNameOf.empty() ? 0 : N);
  std::function<void(uint32_t, uint32_t, uint32_t)> addFactFn;
  std::function<uint32_t(uint32_t, uint32_t)> mergeFn;
  std::vector<char> wflag(N, 0);
  for (uint32_t w : wildcardNodes) wflag[w] = 1;
  // ---- Task #46: dense-plane intern sweep (hash-consing) ----
  // Periodically unify content-equal dense R/joined planes onto one
  // shared COW buffer. Buffer widths may differ (lazy widening), so
  // content identity is over the word prefix up to the last nonzero
  // word. The bucket map is sweep-local: buffers registered here hold
  // no extra refcount afterwards, so a canonical buffer that later
  // diverges COW-detaches like any other — no stale-hash hazard.
  uint64_t internUnified = 0, internSweeps = 0, internBytesFreed = 0;
  // virgin[n*NSHIFT+s]: dirty[n][s] content == R[n][s] content (the
  // whole plane is one un-consumed delta). Maintained exactly and O(1):
  // set when an arrival fills a previously empty (R,RB) pair — every
  // arrival appends to dirty and R equally, so equality persists until
  // a pop consumes dirty (or RB/merge traffic mixes kinds). Replaces
  // the popcount-equality probe, whose per-pop full-plane scans were
  // the fs-scale regression.
  std::vector<uint8_t> virginPl((size_t)N * NSHIFT, 0);
  // NOTE (2026-08-14 probe, do not rebuild): a per-class dirty-plane
  // bitmask skipping empty planes in the pop loop was implemented and
  // A/B'd byte-identical at km fs41 — and FLAT (-0.9%): occupancy is
  // 93% LIVE planes at pop time and empty-plane peeks measure 0.005%
  // of cycles (SolverProf scan). fs plane cost is real work, not
  // iteration overhead; the levers are fact-mass reduction (channels),
  // not plane skipping.
  auto internPlanes = [&]() {
    internSweeps++;
    auto prefixLen = [](const uint64_t *W, size_t n) {
      while (n && W[n - 1] == 0) n--;
      return n;
    };
    boost::unordered_flat_map<uint64_t, llvm::SmallVector<FactSet *, 2>>
        buckets;
    auto sweepPlane = [&](FactSet &P) {
      if (!P.isDense()) return;
      const uint64_t *W = P.denseData()->words();
      const size_t len = prefixLen(W, P.denseData()->numWords());
      if (!len) return; // empty planes: not worth an entry
      uint64_t h = 1469598103934665603ull ^ (uint64_t)len;
      for (size_t i = 0; i < len; i++) {
        h ^= W[i];
        h *= 1099511628211ull;
      }
      auto &vec = buckets[h];
      for (FactSet *C : vec) {
        if (C->sharesDense(P)) return; // already unified earlier
        const uint64_t *WC = C->denseData()->words();
        if (prefixLen(WC, C->denseData()->numWords()) != len ||
            !std::equal(W, W + len, WC))
          continue; // hash collision, different content
        internBytesFreed += P.denseCapBytes();
        P.adoptDense(*C);
        internUnified++;
        return;
      }
      vec.push_back(&P);
    };
    for (uint32_t n = 0; n < N; n++) {
      if (find(n) != n) continue; // losers' planes are released
      for (uint32_t s = 0; s < NSHIFT; s++) {
        sweepPlane(R[n][s]);
        sweepPlane(joined[n][s]);
      }
    }
  };
  // Wave scheduling: pop classes in topological order of the initial
  // propagation graph's condensation, so deltas flow downhill and each
  // plane is touched once per wave with its full accumulated delta,
  // instead of once per scattered arrival (a-prop is cold-miss latency
  // bound; access ORDER is the cheapest locality lever). Ranks are a
  // static heuristic — any pop order converges to the same fixpoint.
  std::vector<uint32_t> topoRank(N, 0);
  {
    uint32_t nComp = 0;
    ka::tarjanSCC(
        N, [](uint32_t) { return false; },
        [&](uint32_t u) { return outA[u].size() + outF[u].size(); },
        [&](uint32_t u, size_t i) -> uint32_t {
          if (i < outA[u].size()) return outA[u][i];
          return outF[u][i - outA[u].size()].first;
        },
        [&](const std::vector<uint32_t> &members) {
          for (uint32_t w : members) topoRank[w] = nComp;
          nComp++;
        });
    // Tarjan emits SCCs in reverse topological order: invert so sources
    // carry the smallest ranks.
    for (uint32_t i = 0; i < N; i++) topoRank[i] = nComp - 1 - topoRank[i];
  }
  std::vector<uint32_t> worklist;
  std::unique_ptr<std::atomic<uint8_t>[]> inWL(
      new std::atomic<uint8_t>[NCap]);
  for (uint32_t i = 0; i < NCap; i++)
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
    FactSet relabelS;                        // holder-identity relabel scratch
    FactSet d, todoS, dbS, dNatS, dBrS;      // pop-loop scratch
    FactSet pendS, todoGS;                   // cell-major sweep scratch
    std::vector<uint32_t> sweepElems;
    std::vector<uint32_t> localWork;
    uint64_t localFacts = 0, pops = 0;
    uint64_t cyJoin = 0, cyBridge = 0, cyScan = 0, cyW = 0, cyA = 0,
             cyF = 0;
    uint64_t nJoinLk = 0, nAOr = 0, nFOr = 0, orWords = 0;
    uint64_t sweepOffered = 0, sweepKept = 0;
    uint64_t internHits = 0; // sharesDense early-outs (skipped copy+diff)
    uint64_t internShares = 0; // share-on-full-arrival adoptions
    uint64_t cellSkips = 0; // cluster-mark join fast-path hits
    uint64_t wordSkips = 0; // whole-cell subset-certificate skips
    // occupancy probe (prof only): zero-word share of streamed planes
    uint64_t wordsScanned = 0, wordsNzSrc = 0, wordsNzNb = 0;
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
                     SolverCtx &ctx, bool srcStable = false) {
    if (src.none()) return;
    FactSet &nb = ctx.nbA;
    lockC(n);
    // Interned fast path: src and R[n][s] sharing one COW buffer proves
    // src \ R[n][s] = ∅ without touching a word (chains of duplicated
    // planes are the measured 60% row-duplication case).
    if (src.sharesDense(R[n][s])) {
      ctx.internHits++;
      unlockC(n);
      return;
    }
    // Share-on-full-arrival (task #46): an empty plane receiving a whole
    // STABLE dense plane (srcStable = the payload is a class R plane,
    // never scratch) adopts the buffer instead of copying it. The delta
    // planes share too, so the pop-time snapshot sees dirty==R
    // (pointer-equal), pushes R itself downstream, and the share walks
    // the whole copy chain — relay classes cost O(1) and re-offers hit
    // the pointer-equality skip above. COW detach on the first
    // divergent write keeps every plane exact.
    if (srcStable && FactSet::EnableShare && src.isDense() &&
        R[n][s].none() && RB[n][s].none()) {
      R[n][s].adoptDense(src);
      dirty[n][s].adoptDense(src);
      jdirty[n][s].adoptDense(src);
      dirtyBr[n][s].adoptDense(src);
      virginPl[(size_t)n * NSHIFT + s] = 1;
      ctx.localFacts += src.count();
      ctx.internShares++;
      if (traceAny) traceCheck(n, s, false, src);
      unlockC(n);
      push(n, ctx);
      return;
    }
    // FUSED dense tail (2026-08-15): the general path below costs ~16
    // plane streams per effective OR (copy, subtract, none, four
    // separate unions each with its own COW check, count). The common
    // case — dense src, no bridged bits to promote — does it in TWO
    // fused loops: pass A computes nb = src & ~R with inline any +
    // popcount; pass B ORs nb into R/dirty/jdirty/dirtyBr in one loop.
    // Same lock discipline, byte-identical state by construction; the
    // RB promotion split and sparse operands keep the general path.
    if (src.isDense() && RB[n][s].none() &&
        (R[n][s].isDense() || R[n][s].none())) {
      const ka::BitPlane &SV = *src.denseData();
      const uint64_t *sW = SV.words();
      const size_t swords = SV.numWords();
      ka::BitPlane &NB = nb.scratchDense(SV.size());
      uint64_t *nbW = NB.words();
      const ka::BitPlane *RD =
          R[n][s].isDense() ? R[n][s].denseData() : nullptr;
      const uint64_t *rW = RD ? RD->words() : nullptr;
      const size_t rwords = RD ? RD->numWords() : 0;
      uint64_t pop = 0;
      if (CFLSolverProfile) { // occupancy probe: zero-word share of streamed planes
        uint64_t nzS = 0, nzNb = 0;
        for (size_t i = 0; i < swords; i++) {
          const uint64_t sv = sW[i];
          const uint64_t w = sv & ~(i < rwords ? rW[i] : (uint64_t)0);
          nbW[i] = w;
          pop += (uint64_t)__builtin_popcountll(w);
          nzS += sv != 0;
          nzNb += w != 0;
        }
        ctx.wordsScanned += swords;
        ctx.wordsNzSrc += nzS;
        ctx.wordsNzNb += nzNb;
      } else
        for (size_t i = 0; i < swords; i++) {
          const uint64_t w = sW[i] & ~(i < rwords ? rW[i] : (uint64_t)0);
          nbW[i] = w;
          pop += (uint64_t)__builtin_popcountll(w);
        }
      if (!pop) { unlockC(n); return; }
      // Arrivals append to dirty and R equally, so a fill-from-empty
      // starts dirty==R — the virgin invariant (RB known empty here).
      if (R[n][s].none())
        virginPl[(size_t)n * NSHIFT + s] = 1;
      const uint32_t bits = SV.size();
      uint64_t *rW2 = R[n][s].mutDense(bits).words();
      uint64_t *dW2 = dirty[n][s].mutDense(bits).words();
      uint64_t *jW2 = jdirty[n][s].mutDense(bits).words();
      uint64_t *bW2 = dirtyBr[n][s].mutDense(bits).words();
      for (size_t i = 0; i < swords; i++) {
        const uint64_t w = nbW[i];
        if (!w) continue;
        rW2[i] |= w;
        dW2[i] |= w;
        jW2[i] |= w;
        bW2[i] |= w;
      }
      ctx.localFacts += pop;
      if (traceAny) traceCheck(n, s, false, nb);
      unlockC(n);
      push(n, ctx);
      return;
    }
    nb.copyFrom(src);
    nb.subtract(R[n][s]);
    if (nb.none()) { unlockC(n); return; }
    // Arrivals append to dirty and R equally, so a fill-from-empty
    // starts (and appends preserve) dirty==R — the virgin invariant.
    if (R[n][s].none() && RB[n][s].none())
      virginPl[(size_t)n * NSHIFT + s] = 1;
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
      if (traceAny) traceCheck(n, s, false, promoted); // bridged -> native
    }
    if (!nb.none()) {
      dirty[n][s].unionWith(nb);
      jdirty[n][s].unionWith(nb);
      dirtyBr[n][s].unionWith(nb);
      ctx.localFacts += nb.count();
      if (traceAny) traceCheck(n, s, false, nb);
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
      if (traceAny) traceCheckOne(n, s, o); // bridged -> native promotion
      unlockC(n);
      push(n, ctx);
      return;
    }
    if (R[n][s].none() && RB[n][s].none())
      virginPl[(size_t)n * NSHIFT + s] = 1;
    R[n][s].set(o);
    dirty[n][s].set(o);
    jdirty[n][s].set(o);
    dirtyBr[n][s].set(o);
    ctx.localFacts++;
    if (traceAny) traceCheckOne(n, s, o);
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
    if (src.sharesDense(R[n][s]) || src.sharesDense(RB[n][s])) {
      ctx.internHits++;
      unlockC(n);
      return;
    }
    // FUSED dense tail (see addBits): nb = src & ~RB & ~R in one pass,
    // then one OR loop into RB/dirty/jdirty.
    if (src.isDense() && (R[n][s].isDense() || R[n][s].none()) &&
        (RB[n][s].isDense() || RB[n][s].none())) {
      const ka::BitPlane &SV = *src.denseData();
      const uint64_t *sW = SV.words();
      const size_t swords = SV.numWords();
      ka::BitPlane &NB = nb.scratchDense(SV.size());
      uint64_t *nbW = NB.words();
      const ka::BitPlane *RD =
          R[n][s].isDense() ? R[n][s].denseData() : nullptr;
      const ka::BitPlane *BD =
          RB[n][s].isDense() ? RB[n][s].denseData() : nullptr;
      const uint64_t *rW = RD ? RD->words() : nullptr;
      const uint64_t *bW = BD ? BD->words() : nullptr;
      const size_t rwords = RD ? RD->numWords() : 0;
      const size_t bwords = BD ? BD->numWords() : 0;
      uint64_t pop = 0;
      for (size_t i = 0; i < swords; i++) {
        uint64_t w = sW[i];
        if (i < rwords) w &= ~rW[i];
        if (i < bwords) w &= ~bW[i];
        nbW[i] = w;
        pop += (uint64_t)__builtin_popcountll(w);
      }
      if (!pop) { unlockC(n); return; }
      const uint32_t bits = SV.size();
      uint64_t *bW2 = RB[n][s].mutDense(bits).words();
      uint64_t *dW2 = dirty[n][s].mutDense(bits).words();
      uint64_t *jW2 = jdirty[n][s].mutDense(bits).words();
      for (size_t i = 0; i < swords; i++) {
        const uint64_t w = nbW[i];
        if (!w) continue;
        bW2[i] |= w;
        dW2[i] |= w;
        jW2[i] |= w;
      }
      virginPl[(size_t)n * NSHIFT + s] = 0; // dirty gains RB bits
      ctx.localFacts += pop;
      if (traceAny) traceCheck(n, s, true, nb);
      unlockC(n);
      push(n, ctx);
      return;
    }
    nb.copyFrom(src);
    nb.subtract(RB[n][s]);
    nb.subtract(R[n][s]);
    if (nb.none()) { unlockC(n); return; }
    RB[n][s].unionWith(nb);
    dirty[n][s].unionWith(nb);
    jdirty[n][s].unionWith(nb);
    virginPl[(size_t)n * NSHIFT + s] = 0; // dirty gains RB bits: != R now
    ctx.localFacts += nb.count();
    if (traceAny) traceCheck(n, s, true, nb);
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
      new std::atomic<uint32_t>[NCap]);
  for (uint32_t i = 0; i < NCap; i++)
    keyCount[i].store(0, std::memory_order_relaxed);
  size_t transKeyMerges = 0;
  // Churn attribution: what triggers merges, how much join work is
  // merge-triggered re-offer, and which classes get re-popped — the data
  // that sizes the delta-precision fix and names summarization targets.
  size_t mergesFromJoin = 0, mergesFromSCC = 0, redundantJoins = 0;
  size_t nullKeyJoinsSkipped = 0; // null-cell join hygiene LEDGER
  // --cfl-root-relevance: (root, keeper class) per join-triggered merge —
  // joins are the only consumer of individual root bits besides the final
  // icall answer read, so these witnesses + function roots form a
  // sufficient root set for reproducing this run's answers.
  std::vector<std::pair<uint32_t, uint32_t>> mergeWitness;
  uint64_t reofferedFacts = 0, sweepOffered = 0, sweepKept = 0;
  std::vector<uint32_t> popCount(N, 0);
  FactSet mnbS, mprS; // merge scratch (merge never nests inside itself)
  uint64_t cyMerge = 0;
  // --cfl-channel-demand: relevance = "can reach an indirect call's callee
  // operand" (static reverse closure over a/f edges, extended through
  // every wired store). Reads outside it and stores to undemanded keys
  // are deferred and replayed when relevance or demand arrives.
  struct ChanPend {
    uint32_t cell, o, s;
  };
  const bool demandMode = CFLChannelCells && CFLChannelDemand;
  // --cfl-demand-site: a single-site query. Only matching indirect-call
  // sites seed relevance (demand mode and lazy-mint relevance), and the
  // widening report at the end walks the fact flow backward from their
  // callee operands.
  auto demSiteWanted = [&](const CallBase *CS) -> bool {
    if (CFLDemandSite.empty()) return true;
    const StringRef want(CFLDemandSite);
    if (const Function *PF = CS->getFunction())
      if (PF->getName() == want) return true;
    const DebugLoc &DL = CS->getDebugLoc();
    if (!DL) return false;
    const std::string key =
        (DL->getScope()->getFilename() + ":" + Twine(DL->getLine())).str();
    return StringRef(key).contains(want);
  };
  std::vector<char> demRelNode, demRelClass;
  std::vector<std::vector<uint32_t>> demRin;
  bool demInitDone = false;
  boost::unordered_flat_set<uint64_t> demandedKeys;
  std::unordered_map<uint64_t, std::vector<uint32_t>> demDeferredStores; // key -> pend idx
  std::unordered_map<uint32_t, std::vector<uint32_t>> demDeferredReads;  // cell -> pend idx
  std::unordered_map<uint32_t, std::vector<uint32_t>> demClassCells;     // class -> cells
  std::vector<uint32_t> demRelDirty;
  std::vector<ChanPend> demKeep; // deferred pends (chanPend is cleared per flush)
  size_t demDeferredR = 0, demDeferredS = 0, demReplayed = 0, demRelevantNodes = 0;
  auto demRelSize = [&](uint32_t x) {
    if (demRelClass.size() <= x) demRelClass.resize(x + 1024, 0);
  };
  // --cfl-dump-merges: every union with its cause, replayed offline to
  // answer "which union first put X and Y in one class, and why".
  struct MergeEv { uint32_t a, b, keyO, keyS, ptr; const char *why; uint32_t cell; };
  std::vector<MergeEv> mergeLog;
  // --cfl-dump-merges: first inserts of cluster keys (a class anchors
  // its first origin without any union), placed in the union order by
  // the number of unions logged before them.
  struct KeyEv { size_t seq; uint32_t cls, o, s, ptr, cell; };
  std::vector<KeyEv> keyLog;
  const char *mergeWhy = "other";
  auto merge = [&](uint32_t a, uint32_t b) -> uint32_t {
    a = find(a); b = find(b);
    if (a == b) return a;
    if (!CFLDumpMerges.empty())
      mergeLog.push_back({a, b, tKeyO, tKeyS, tPtr, mergeWhy, tCell});
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
    if (g_touchTrack) {
      g_touchLog.push_back(a);
      g_touchLog.push_back(b);
    }
    mergeCount++;
    mergeHits[a] += 1 + mergeHits[b];
    keyCount[a].fetch_add(keyCount[b].load(std::memory_order_relaxed),
                          std::memory_order_relaxed);
    keyCount[b].store(0, std::memory_order_relaxed);
    isRoot[a] |= isRoot[b];
    if (!wireCone.empty()) wireCone[a] |= wireCone[b];
    if (demandMode) {
      demRelSize(std::max(a, b));
      if (demRelClass[a] != demRelClass[b]) {
        demRelClass[a] = 1;
        demRelDirty.push_back(a); // deferred reads of the newly relevant side replay
      }
      auto dc = demClassCells.find(b);
      if (dc != demClassCells.end()) {
        auto &da = demClassCells[a];
        da.insert(da.end(), dc->second.begin(), dc->second.end());
        demClassCells.erase(dc);
      }
    }
    tHow = "merge"; tFrom = b;
    for (uint32_t s = 0; s < NSHIFT; s++) {
      // Propagation delta: only facts genuinely new to the keeper. The
      // keeper's old facts reach the loser's former neighbors via the
      // one-time direct push below, NOT via a full re-dirty (that made
      // every merge re-offer the whole fact set on the whole edge list).
      // Micro-fusion tombstone (2026-08-16): fusing blocks 1+2 below
      // into one word loop (addBits-style) was built, validated
      // byte-identical at km fs41, and REVERTED: wall flat, merge
      // cycles +14% (404B->462B). The merge bucket's mass is NOT this
      // move math — it is the jdirty re-offer / joined-intersect
      // unionWith traffic (whose COW adopt fast paths a word loop
      // destroys) plus the loser-list pushes (already fused via
      // addBits). Do not re-fuse here without profiling those first.
      if (R[b][s].any()) {
        FactSet &nb = mnbS;
        nb.copyFrom(R[b][s]);
        nb.subtract(R[a][s]);
        if (nb.any()) {
          if (traceAny) traceCheck(a, s, false, nb); // keeper gains b's facts
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
          if (traceAny) traceCheck(a, s, true, nb);
          RB[a][s].unionWith(nb);
          dirty[a][s].unionWith(nb);
        }
      }
      if (dirty[b][s].any()) dirty[a][s].unionWith(dirty[b][s]);
      if (dirtyBr[b][s].any()) dirtyBr[a][s].unionWith(dirtyBr[b][s]);
      // Merged planes mix kept and consumed content: virgin no more.
      virginPl[(size_t)a * NSHIFT + s] = 0;
      virginPl[(size_t)b * NSHIFT + s] = 0;
      R[b][s].release();
      RB[b][s].release();
      dirty[b][s].release();
      dirtyBr[b][s].release();
      // Loser's cluster-joined marks become unreachable via find():
      // drop them (missed marks are conservative — slow path re-probes;
      // keeper's marks stay valid because clusters only grow).
      cellJoined[b][s].release();
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
      if (lazyAddr) {
        FactSet &rm = remapScratch();
        if (R[a][0].any()) { remapPlane(R[a][0], r, b, t, rm); if (rm.any()) addBits(tt, 0, rm, ctx0); }
        if (RB[a][0].any()) { remapPlane(RB[a][0], r, b, t, rm); if (rm.any()) addBits(tt, 0, rm, ctx0); }
        continue;
      }
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
    if (!ownedMask.empty()) {
      mergeEvents++;
      const uint64_t na2 = ownedMask[a] & ~ownedMask[b];
      const uint64_t nb2 = ownedMask[b] & ~ownedMask[a];
      if (na2 && nb2) {
        // true cross-subsystem weld: blame the shared join origin (the
        // object whose cell keyed this union) when available
        weldEvents++;
        std::string who = "ctx:" + std::string(blobCtx);
        const uint32_t bOrig = blobCtxOrigin;
        if (bOrig != UINT32_MAX && bOrig < rootClassOf.size()) {
          const Value *wv = rootValue(bOrig);
          if (wv && wv->hasName())
            who = wv->getName().str();
          else if (wv) {
            if (const auto *wi = dyn_cast<Instruction>(wv))
              who = (wi->getFunction()->getName() + "::" +
                     wi->getOpcodeName()).str();
            else if (const auto *wa = dyn_cast<Argument>(wv))
              // unnamed formals are the junction carriers — name them
              // or the top blame bucket reads "ctx:join"
              who = (wa->getParent()->getName() + "::arg" +
                     Twine(wa->getArgNo())).str();
          } else {
            const NodeIndex bn = rootOrig(bOrig);
            auto pit = g_opaqueProvenance.find(bn);
            if (pit != g_opaqueProvenance.end()) {
              who = pit->second;
            } else if (bn < NF.getNumNodes() && NF.isObjectNode(bn) &&
                       NF.getObjectOffset(bn) > 0) {
              // struct-object FIELD node: no Value of its own — name
              // via the base object
              const NodeIndex base = bn - NF.getObjectOffset(bn);
              const Value *bv = NF.getValueForNode(base);
              who = (bv && bv->hasName() ? bv->getName().str()
                     : bv ? std::string("<anon-obj>")
                          : std::string("<synthetic-base>")) +
                    "+f" + std::to_string(NF.getObjectOffset(bn));
            } else if (bn == NF.getUniversalPtrNode() ||
                       bn == NF.getUniversalObjNode()) {
              // extern-boundary class: joins keyed here are the
              // REQUIRED unknown-memory over-approximation; the lever
              // is shrinking this class (extern summaries,
              // --cfl-census-extern-bound worklist), never skipping
              who = "<extern-boundary>";
            } else if (bn == NF.getNullPtrNode() ||
                       bn == NF.getNullObjectNode()) {
              who = "<null>"; // should not key joins (hygiene guard)
            } else {
              who = "<synthetic " +
                    std::string(bn < NF.getNumNodes() && NF.isObjectNode(bn)
                                    ? "obj"
                                    : "val") +
                    "#" + std::to_string(bn) + ">/" + std::string(blobCtx);
            }
          }
        }
        auto &bl2 = weldBlame[who];
        bl2.first++;
        bl2.second |= ownedMask[a] | ownedMask[b];
        g_weldRepOf[who] = a; // post-merge rep (re-find at report)
      }
      ownedMask[a] |= ownedMask[b];
    }
    if (CFLProbeBlobFormation &&
        blobEvents.size() < (blobLogAll ? 400000u : 60000u)) {
      const uint32_t sa = clsSize[a], sb = clsSize[b];
      // log when both sides are substantial, or a milestone is crossed
      if (blobLogAll || std::min(sa, sb) >= 64 ||
          (sa + sb >= 4096 && sa < 4096) || (sa + sb >= 65536 && sa < 65536))
        blobEvents.push_back(
            {a, sa, sb, protBlameName(a), protBlameName(b), blobCtx,
             // Mint-time class: the origin's CURRENT rep is the blob
             // itself once it has merged in, which names nothing.
             blobCtxOrigin == UINT32_MAX
                 ? std::string()
                 : protBlameName(rootClassOf[blobCtxOrigin]) +
                       (NSHIFT > 1 ? ",s" + std::to_string(blobCtxShift)
                                   : std::string()),
             iterations});
    }
    clsSize[a] += clsSize[b];
    push(a, ctx0);
    if (b < satOf.size() && !satOf[b].empty()) {
      auto moved = std::move(satOf[b]);
      satOf[b].clear();
      for (auto [nm, u] : moved) {
        bool found = false;
        for (auto &[nm2, v] : satOf[a])
          if (nm2 == nm) {
            found = true;
            if (find(u) != find(v)) mergeFn(v, u); // shadows have no satellites
            break;
          }
        if (!found) satOf[a].emplace_back(nm, u);
      }
    }
    if (b < pendingId.size() && !pendingId[b].empty()) {
      pendingId[a].append(pendingId[b].begin(), pendingId[b].end());
      pendingId[b].clear();
    }
    if (a < pendingId.size() && !pendingId[a].empty())
      for (auto &[nm, u] : satOf[a])
        if (nm == ka::AccessNames::Identity) {
          auto moved = std::move(pendingId[a]);
          pendingId[a].clear();
          for (auto [rid, pl] : moved)
            addFactFn(find(u), pl, rid);
          break;
        }
    return a;
  };
  mergeFn = merge;
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
    if (g_touchTrack) {
      g_touchLog.push_back(x); // restored facts must re-cross new bridges
      g_touchLog.push_back(y);
    }
    bridgesOf[x].push_back(y);
    bridgesOf[y].push_back(x);
    bridgeCount++;
    tHow = "bridge-init";
    for (uint32_t s = 0; s < NSHIFT; s++) {
      tFrom = x;
      if (R[x][s].any()) addBitsBridged(y, s, R[x][s], ctx0);
      tFrom = y;
      if (R[y][s].any()) addBitsBridged(x, s, R[y][s], ctx0);
    }
  };
  // --cfl-sink-instr needs no code here: the opaque-arena model (task
  // #34 v3) is applied structurally at graph-build time (visitCallBase
  // binds payload-accessor returns to shared arena objects), so the
  // solve runs unmodified. Contract gating is enforced at planting.

  // ---- Channel cells (docs/channel-cells-design.md): joins become
  // pendings during rounds; channel nodes + directional edges are
  // materialized at the drain barrier (node growth is barrier-serial,
  // no live references across it).
  std::vector<ChanPend> chanPend;
  // Record-time dedup: one pend per (raw cell, key) for the whole
  // solve — node ids are never reused, so raw ids are stable even
  // across merges (re-offers after merges re-call joinCluster).
  boost::unordered_flat_set<std::pair<uint64_t, uint32_t>,
                            boost::hash<std::pair<uint64_t, uint32_t>>>
      chanPendSeen;
  boost::unordered_flat_set<uint64_t> chanEdgeSeen; // (src<<32)|dst
  // cell -> its read half (UINT32_MAX: cell has no reads, no half made)
  boost::unordered_flat_map<uint32_t, uint32_t> chanReadHalf;
  size_t chanNodes = 0, chanEdges = 0, chanSplits = 0, chanConeSkipped = 0,
         chanConstSkipped = 0;
  // --cfl-alloc-origins: a cluster keyed by an environment root holds that
  // root's content root (environment data), seeded when the key is first
  // inserted. Named planes: into the class's identity shadow, or pending
  // until one joins (as the seeds of minted roots are).
  size_t envContentSeeded = 0, envContentMinted = 0;
  // The content root at key (o, s) of environment root o: a new root one
  // level deeper, or o itself at the depth bound (environment memory is
  // then summarized; any depth is sound, Keys.EnvInit).
  auto envContentFor = [&](uint32_t o, uint32_t cell) -> uint32_t {
    if (envDepth[o] >= CFLEnvDepth) return o;
    const uint32_t rid = nextRoot++;
    FactSet::Universe = nextRoot; // widen BEFORE the first set
    rootClassOf.push_back(find(cell)); // named after the cell it fills
    rootConstData.push_back(0);
    rootParkable.push_back(0);
    if (nexusGate) rootNexus.push_back(0);
    envRoot.push_back(1);
    envDepth.push_back(envDepth[o] + 1);
    envContentMinted++;
    return rid;
  };
  auto seedEnvContent = [&](uint32_t c, uint32_t rid) {
    const uint32_t pl =
        (nexusGate && !rootNexus[rid]) ? (uint32_t)SHIFT_X : 0u;
    envContentSeeded++;
    if (cellNameOf.empty()) {
      addFact(find(c), pl, rid, ctx0);
      return;
    }
    c = find(c);
    for (auto &[nm, u] : satOf[c])
      if (nm == ka::AccessNames::Identity) {
        addFact(find(u), pl, rid, ctx0);
        return;
      }
    pendingId[c].emplace_back(rid, pl);
  };
  auto joinCluster = [&](uint32_t cell, uint32_t o, uint32_t s) {
    // Null-cell join hygiene (2026-08-25): joins keyed by the NULL
    // pseudo-object's cells model store-through-null — UB, no real
    // execution stores at null and none loads from it — yet they act
    // as a universal rendezvous (x4 15-subsystem residual welds at the
    // attribution slice; null constants flow into every maybe-null
    // pointer class). Real targets of the same store still key their
    // own joins; ONLY the null member's cell is dropped. Universal
    // (#0/#1) joins are extern-boundary soundness and are NOT skipped.
    {
      const uint32_t rid0 = o;
      if (rid0 != UINT32_MAX && rid0 < rootClassOf.size()) {
        const NodeIndex on0 = rootOrig(rid0);
        if (on0 == NF.getNullPtrNode() || on0 == NF.getNullObjectNode()) {
          nullKeyJoinsSkipped++;
          return;
        }
      }
    }
    // A constant data-only global (string literal, lookup table) never
    // holds a pointer and cannot be stored into, so it witnesses no
    // pointer-carrying alias: a cluster keyed by it would only fuse the
    // cells of every char pointer that may point at it (nm-new: 1,236
    // joins under "\n" glued the literal soup to struct cells). Both
    // modes; channel mode adopted this rule first (2026-09-15).
    if (o < rootConstData.size() && rootConstData[o]) {
      chanConstSkipped++;
      return;
    }
    if (CFLChannelCells) {
      // Pairwise mode: record; the barrier flush wires the channel.
      // Cells outside the wiring cone cannot influence any answer.
      if (!wireCone.empty() && !wireCone[find(cell)]) {
        chanConeSkipped++;
        return;
      }
      if (chanPendSeen.emplace((uint64_t)o * NSHIFT + s, cell).second)
        chanPend.push_back({cell, o, s});
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
      blobCtx = "join"; blobCtxOrigin = o; blobCtxShift = s;
      tKeyO = o; tKeyS = s; tCell = cell;
      it->second = merge(it->second, cell);
      if (mergeCount > mc0) {
        mergesFromJoin++;
        if (CFLRootRelevance)
          mergeWitness.emplace_back(o, find(it->second));
      }
      return;
    }
    keyCount[find(cell)].fetch_add(1, std::memory_order_relaxed);
    if (!CFLDumpMerges.empty())
      keyLog.push_back({mergeLog.size(), find(cell), o, s, tPtr, cell});
    if (o < envRoot.size() && envRoot[o]) {
      tHow = "env-content"; tFrom = UINT32_MAX;
      const uint32_t c = envContentFor(o, cell);
      envContentOfKey[key] = c;
      seedEnvContent(cell, c);
    }
    if (g_batchRecord)
      g_batchEvts.push_back({0, cell, o, s}); // first insert of this key
    if (NB == 0) return;
    // VX linking: bridge the (o, X) cluster with each exact cluster of o.
    if (s == SHIFT_X) {
      for (uint64_t ek : shiftKeysOf[o]) {
        const uint32_t er = clusterFind(ek);
        assert(er != UINT32_MAX && "shiftKeysOf names a missing cluster");
        tKeyO = o; tKeyS = (uint32_t)(ek % NSHIFT);
        addBridge(it->second, er);
      }
    } else {
      shiftKeysOf[o].push_back(key);
      const uint32_t xr = clusterFind((uint64_t)o * NSHIFT + SHIFT_X);
      if (xr != UINT32_MAX) {
        tKeyO = o; tKeyS = s;
        addBridge(it->second, xr);
      }
    }
  };
  // Channel-node factory: append one node to every solve-time parallel
  // structure. Only called at the barrier flush (serial, no live refs).
  // Channels must never become union-find keepers (post-solve sweeps
  // and lazy-mint arrays are N-sized): rank stays 0 and the RMW merge
  // below always passes the cell as the keeper side.
  auto newSolverNode = [&]() -> uint32_t {
    const uint32_t id = (uint32_t)ufp.size();
    if (id >= NCap)
      report_fatal_error("channel-cells: node capacity exhausted "
                         "(raise the NCap headroom)");
    ufp.push_back(id);
    ufrank.push_back(0);
    R.emplace_back(NSHIFT);
    RB.emplace_back(NSHIFT);
    dirty.emplace_back(NSHIFT);
    jdirty.emplace_back(NSHIFT);
    dirtyBr.emplace_back(NSHIFT);
    joined.emplace_back(NSHIFT);
    cellJoined.emplace_back(NSHIFT);
    bridgesOf.emplace_back();
    if (!satOf.empty()) satOf.emplace_back();
    if (!pendingId.empty()) pendingId.emplace_back();
    wflag.push_back(0);
    cellsOf.emplace_back();
    outA.emplace_back();
    outF.emplace_back();
    popCount.push_back(0);
    topoRank.push_back(0);
    mergeHits.push_back(0);
    isRoot.push_back(0);
    compactMark.push_back(64);
    virginPl.insert(virginPl.end(), NSHIFT, 0);
    // merge() adds clsSize[b] into clsSize[a] for ANY keeper, channel
    // nodes included (the SCC collapse merges them): an ungrown
    // clsSize was an out-of-bounds write (fs13 channel segfaults,
    // 2026-09-15).
    clsSize.push_back(1);
    if (!ownedMask.empty()) ownedMask.push_back(0);
    if (!wireCone.empty()) wireCone.push_back(1); // made from an in-cone cell
    chanNodes++;
    return id;
  };
  // Barrier flush: materialize channels for pended (cell, o, s) joins
  // and wire directional edges. Store cell -> channel(o,s); channel ->
  // load cell. Content crosses store->load iff one shared witness key
  // (Lean: chanflow_iff_pairflow). Seeding mirrors the pop loop's
  // a-edge rule: emission is native (value flow launders bridge
  // provenance).
  // --cfl-key-identity: identity of never-written content, one origin
  // per channel key of an EXTERNAL origin (docs/channel-cells-design.md,
  // "Identity of unwritten content"). External = a formal without
  // callers (its own identity root), an extern global with its own
  // node, a synthetic (value-less) class, or a key identity itself.
  // Heap, stack and defined globals are internal: a field nobody
  // writes reads as empty (premise P2).
  boost::unordered_flat_set<uint32_t> keyIdentityRoots; // rids
  size_t keyIdentityMinted = 0, keyIdentitySelf = 0;
  auto isExternalOrigin = [&](uint32_t o) -> bool {
    if (keyIdentityRoots.count(o)) return true;
    if (o >= rootClassOf.size()) return false;
    const uint32_t rc = rootClassOf[o];
    if (rc >= toOrig.size()) return false; // solver plumbing: never
    if (funcRootOf.count(o)) return false;
    const NodeIndex canon = toOrig[rc];
    const Value *V = NF.getValueForNode(canon);
    if (!V) return !NF.isObjectNode(canon); // synthetic value class
    if (isa<Argument>(V)) return true;
    if (const auto *G = dyn_cast<GlobalVariable>(V))
      return Ctx->ExtGobjs.count(G->getGUID()) && NF.isExtGobjOverride(G->getGUID());
    return false;
  };
  // --cfl-holder-identity (docs/channel-cells-design.md, "Holder-keyed
  // object identity"): a fresh allocation stored through q becomes one
  // clone origin per holder key of q. The fresh pointer keeps the base
  // origin: its channels feed every clone (stores through it), its
  // readers are fed by every clone (loads through it); clones never
  // feed each other. State is written on the main thread (flush) only;
  // waves read it through holderRelabel.
  const bool holderMode = CFLHolderIdentity && CFLChannelCells;
  boost::unordered_flat_map<uint32_t, uint32_t> freshStoreCells; // cell -> base rid
  boost::unordered_flat_set<uint32_t> freshBases;                // rids with clones possible
  bool freshStoreBuilt = false;
  boost::unordered_flat_map<uint64_t, uint32_t> cloneOf;   // (base<<32|key) -> clone
  boost::unordered_flat_map<uint32_t, uint32_t> cloneBase; // clone -> base
  boost::unordered_flat_map<uint32_t, SmallVector<uint32_t, 4>> clonesOfBase;
  boost::unordered_flat_map<uint32_t, SmallVector<std::pair<uint32_t, uint32_t>, 2>>
      chanRelabel;                                            // channel -> (base, clone)
  boost::unordered_flat_map<uint64_t, SmallVector<uint32_t, 4>> baseReaders; // base key -> rh
  boost::unordered_flat_map<uint32_t, uint32_t> holderKeyCount;
  size_t holderClones = 0, holderCellsDisabled = 0;
  auto buildFreshStoreCells = [&]() {
    if (freshStoreBuilt || !holderMode) return;
    freshStoreBuilt = true;
    boost::unordered_flat_map<uint32_t, uint32_t> ridOfRep;
    for (uint32_t rid = 0; rid < rootClassOf.size(); rid++)
      if (rootClassOf[rid] < N) ridOfRep[find(rootClassOf[rid])] = rid;
    auto isAlloc = [&](const CallBase *CB) {
      return Ctx->AllocSites.count(CB) != 0;
    };
    for (auto &mp : Ctx->Modules)
      for (Function &F : *mp.first) {
        if (F.isDeclaration()) continue;
        for (auto &BB : F)
          for (auto &I : BB) {
            auto *SI = dyn_cast<StoreInst>(&I);
            if (!SI || !SI->getValueOperand()->getType()->isPointerTy())
              continue;
            const CallBase *AC =
                uniqueAllocSource(SI->getValueOperand(), isAlloc);
            if (!AC) continue;
            NodeIndex vN = getRepNodeForValue(AC);
            NodeIndex pN = getRepNodeForValue(SI->getPointerOperand());
            if (vN == AndersNodeFactory::InvalidIndex ||
                pN == AndersNodeFactory::InvalidIndex)
              continue;
            auto vit = toDense.find(getCanonicalNode(vN));
            if (vit == toDense.end()) continue;
            auto rit = ridOfRep.find(find(vit->second));
            if (rit == ridOfRep.end()) continue;
            auto cit = toDense.find(getCanonicalNode(getRepDerefNode(pN)));
            if (cit == toDense.end()) continue;
            freshStoreCells[cit->second] = rit->second;
            freshBases.insert(rit->second);
            if (!CFLTraceFunc.empty())
              CG_LOG("HolderIdentity: fresh-store cell c" << cit->second
                     << " " << protBlameName(cit->second).substr(0, 50)
                     << " <- r" << rit->second << " "
                     << F.getName() << "\n");
          }
      }
    CG_LOG("HolderIdentity: " << freshStoreCells.size()
           << " fresh-store cells over " << freshBases.size()
           << " allocation origins\n");
  };
  auto holderClone = [&](uint32_t b, uint64_t key) -> uint32_t {
    auto [it, ins] = cloneOf.try_emplace(((uint64_t)b << 32) | key, 0);
    if (!ins) return it->second;
    const uint32_t home = rootClassOf[b];
    const uint32_t rid = nextRoot++;
    FactSet::Universe = nextRoot; // widen BEFORE the first set
    rootClassOf.push_back(home);  // named/classified like its base
    rootConstData.push_back(0);
    rootParkable.push_back(0);
    if (nexusGate) rootNexus.push_back(0);
    it->second = rid;
    cloneBase[rid] = b;
    clonesOfBase[b].push_back(rid);
    holderClones++;
    return rid;
  };
  boost::unordered_flat_set<uint32_t> chanIds;        // channel nodes
  boost::unordered_flat_set<uint32_t> holderReleased; // keyless cells
  // Payload pushed out of fresh-store cell `src`. Into a holder channel
  // the base bit becomes that holder's clone bit. Along any other edge
  // (the pre-split direct edges to the same-pointer loads, the split
  // carry into the read half) the base bit is DROPPED: the object comes
  // back to those readers as clones through the holder channels — a
  // reload of *p after `*p = fresh` yields the object under whichever
  // holder p denotes. A cell whose owner never gets a key is released
  // (holderReleaseKeyless) so that same-pointer flow is not lost.
  // Scratch results are not adoptable.
  auto holderRelabel = [&](uint32_t src, uint32_t dst, const FactSet &pay,
                           SolverCtx &ctx, bool &relabeled) -> const FactSet & {
    relabeled = false;
    if (clsSize[src] != 1 || holderReleased.count(src)) return pay;
    auto fit = freshStoreCells.find(src);
    if (fit == freshStoreCells.end()) return pay;
    const uint32_t b = fit->second;
    if (!pay.test(b)) return pay;
    if (chanIds.count(dst)) {
      auto cit = chanRelabel.find(dst);
      if (cit == chanRelabel.end()) return pay; // past the key bound
      for (auto &[bb, c] : cit->second) {
        if (bb != b) continue;
        ctx.relabelS.copyFrom(pay);
        ctx.relabelS.reset(b);
        ctx.relabelS.set(c);
        relabeled = true;
        return ctx.relabelS;
      }
      return pay;
    }
    ctx.relabelS.copyFrom(pay);
    ctx.relabelS.reset(b);
    relabeled = true;
    return ctx.relabelS;
  };
  // A fresh-store cell whose owner has no holder key by the time the
  // flush runs dry: hand the base to its direct readers after all (the
  // same-pointer flow `*p = v; w = *p` with an unknown p stays).
  auto holderReleaseKeyless = [&]() -> size_t {
    if (!holderMode) return 0;
    size_t n = 0;
    for (auto &[cell, b] : freshStoreCells) {
      if (holderKeyCount.count(cell) || holderReleased.count(cell) ||
          clsSize[cell] != 1)
        continue;
      holderReleased.insert(cell);
      SmallVector<uint32_t, 8> targets(outA[cell].begin(), outA[cell].end());
      auto rhIt = chanReadHalf.find(cell);
      if (rhIt != chanReadHalf.end() && rhIt->second != UINT32_MAX)
        targets.push_back(rhIt->second);
      for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
        if (!R[cell][s2].test(b)) continue;
        for (uint32_t t : targets) {
          const uint32_t tt = find(t);
          if (tt != cell) addFact(tt, s2, b, ctx0);
        }
      }
      n++;
    }
    return n;
  };
  auto linkChan = [&](uint32_t x, uint32_t y) {
    x = find(x); y = find(y);
    if (x == y || !chanEdgeSeen.insert(((uint64_t)x << 32) | y).second) return;
    outA[x].push_back(y);
    chanEdges++;
    for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
      if (R[x][s2].any()) addBits(y, s2, R[x][s2], ctx0, true);
      if (RB[x][s2].any()) addBits(y, s2, RB[x][s2], ctx0);
    }
  };
  // Before the first wave: the pre-split direct edges out of a fresh-store
  // cell must already drop the base bit (holderRelabel), so the table is
  // built here, not at the first flush.
  buildFreshStoreCells();
  auto demMarkNode = [&](uint32_t x) -> bool {
    if (x >= demRelNode.size()) demRelNode.resize(x + 1024, 0);
    if (demRelNode[x]) return false;
    demRelNode[x] = 1;
    demRelevantNodes++;
    const uint32_t c = find(x);
    demRelSize(c);
    if (!demRelClass[c]) { demRelClass[c] = 1; demRelDirty.push_back(c); }
    return true;
  };
  auto demRelevantFrom = [&](uint32_t seed) {
    std::vector<uint32_t> q;
    if (demMarkNode(seed)) q.push_back(seed);
    while (!q.empty()) {
      const uint32_t x = q.back(); q.pop_back();
      if (x >= demRin.size()) continue;
      for (uint32_t y : demRin[x]) if (demMarkNode(y)) q.push_back(y);
    }
  };
  // Demand is per OBJECT (all keys of an object: exact, strided and range
  // overlap through bridges, so a store under one key must be wired when
  // a read of any key of the same object is relevant).
  auto demObjOf = [&](uint32_t o) -> uint64_t {
    if (lazyAddr) {
      addrGrow();
      if (o < addrIsObj.size() && addrIsObj[o]) return addrObj[o];
    }
    return o;
  };
  auto demInit = [&]() {
    demInitDone = true;
    demRin.assign(N, {});
    for (uint32_t n = 0; n < N; n++) {
      for (uint32_t t : outA[n]) if (t < N) demRin[t].push_back(n);
      for (auto [t, r] : outF[n]) if (t < N) demRin[t].push_back(n);
      // A relevant cell makes its owner pointer relevant: the owner's
      // facts select which keys the cell reads (owner-pointer hop).
      for (uint32_t c : cellsOf[n]) if (c < N) demRin[c].push_back(n);
    }
    size_t seeds = 0;
    for (auto *CS : Ctx->IndirectCallInsts) {
      if (!demSiteWanted(CS)) continue;
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto it = toDense.find(getCanonicalNode(fn));
      if (it != toDense.end()) { demRelevantFrom(it->second); seeds++; }
    }
    CG_LOG("ChannelDemand: " << demRelevantNodes << " nodes relevant at start ("
           << seeds << " seed sites)\n");
  };
  auto flushChannelPends = [&]() -> size_t {
    if (!CFLChannelCells) return 0;
    if (chanPend.empty() && demRelDirty.empty()) return holderReleaseKeyless();
    const auto tFlush0 = std::chrono::steady_clock::now();
    const size_t pendsIn = chanPend.size();
    size_t work = 0;
    if (demandMode && !demInitDone) demInit();
    auto demReplayDirty = [&]() {
      std::vector<uint32_t> dirty; dirty.swap(demRelDirty);
      for (uint32_t c : dirty) {
        auto it = demClassCells.find(c);
        if (it == demClassCells.end()) continue;
        std::vector<uint32_t> cells; cells.swap(it->second);
        demClassCells.erase(it);
        for (uint32_t cn : cells) {
          auto dr = demDeferredReads.find(cn);
          if (dr == demDeferredReads.end()) continue;
          for (uint32_t idx : dr->second) chanPend.push_back(demKeep[idx]);
          demReplayed += dr->second.size();
          demDeferredReads.erase(dr);
        }
      }
    };
    if (demandMode) demReplayDirty();
    for (size_t pi = 0; pi < chanPend.size(); pi++) {
      if (demandMode && pi + 1 == chanPend.size() && !demRelDirty.empty()) demReplayDirty();
      const ChanPend P = chanPend[pi]; // copy: replays append to the vector
      const uint32_t cell = find(P.cell);
      const uint64_t key = (uint64_t)P.o * NSHIFT + P.s;
      if (demandMode) {
        const bool isRead = !outA[cell].empty() || !outF[cell].empty() ||
                            !cellsOf[cell].empty() || chanReadHalf.count(cell);
        demRelSize(cell);
        const bool rel = demRelClass[cell];
        const uint64_t dkey = demObjOf(P.o);
        if (isRead && rel) {
          if (demandedKeys.insert(dkey).second) {
            auto ds = demDeferredStores.find(dkey);
            if (ds != demDeferredStores.end()) {
              for (uint32_t idx : ds->second) chanPend.push_back(demKeep[idx]);
              demReplayed += ds->second.size();
              demDeferredStores.erase(ds);
            }
          }
        } else if (!demandedKeys.count(dkey)) {
          demKeep.push_back(P);
          const uint32_t kidx = (uint32_t)demKeep.size() - 1;
          // A cell can be both a read and a store (an initializer cell
          // that is also loaded, RMW): defer it on both lists; whichever
          // arrives first, demand or relevance, replays it.
          if (isRead) {
            demDeferredReads[P.cell].push_back(kidx);
            demClassCells[cell].push_back(P.cell);
            demDeferredR++;
          }
          if (!isRead || (P.cell < N && hasIn[P.cell])) {
            demDeferredStores[dkey].push_back(kidx);
            demDeferredS++;
          }
          continue;
        }
        if (P.cell < N && hasIn[P.cell]) demRelevantFrom(P.cell); // wired store: its sources matter
      }
      uint32_t ch;
      auto [it, ins] = clusterRep.emplace(key, UINT32_MAX);
      if (ins) {
        ch = newSolverNode();
        it->second = ch;
        if (holderMode) chanIds.insert(ch);
        chanNodeName[ch] =
            "chan(r" + std::to_string(P.o) + " " +
            (P.o < rootClassOf.size()
                 ? protBlameName(rootClassOf[P.o]).substr(0, 40)
                 : std::string("?")) +
            ",s" + std::to_string(P.s) +
            (cloneBase.count(P.o) ? "[h])" : ")");
        // Tracer provenance for the bridge/wiring arrivals below: the
        // flush runs on the main thread between waves, so the stale
        // labels of the last wave step must not be inherited.
        tKeyO = P.o; tKeyS = P.s; tCell = cell;
        if (CFLKeyIdentity && isExternalOrigin(P.o)) {
          tHow = "key-identity"; tFrom = ch;
          if (keyIdentityRoots.count(P.o)) {
            // Fields of an external identity are the identity itself
            // (depth-one self loop keeps the identity set finite).
            addFact(ch, 0, P.o, ctx0);
            keyIdentitySelf++;
          } else {
            // Mint the channel's content identity (mirrors mintRoot for
            // a solver node: no hasIn/toOrig/ownedMask apply).
            isRoot[ch] = 1;
            const uint32_t rid = nextRoot++;
            FactSet::Universe = nextRoot; // widen BEFORE the first set
            rootClassOf.push_back(ch);
            rootConstData.push_back(0);
            rootParkable.push_back(0);
            if (nexusGate) rootNexus.push_back(0);
            keyIdentityRoots.insert(rid);
            keyIdentityMinted++;
            addFact(ch, 0, rid, ctx0);
            if (VerboseLevel >= 2) {
              // Census: which external origin kinds mint content
              // identities (attribution of the identity residue).
              const char *kind = "?";
              const uint32_t rc0 = P.o < rootClassOf.size() ? rootClassOf[P.o] : UINT32_MAX;
              if (rc0 != UINT32_MAX && rc0 < toOrig.size()) {
                const Value *OV = NF.getValueForNode(toOrig[rc0]);
                if (!OV) kind = NF.isObjectNode(toOrig[rc0]) ? "valueless-object" : "valueless-value";
                else if (isa<Argument>(OV)) kind = "formal";
                else if (isa<GlobalVariable>(OV)) kind = "ext-global";
                else kind = "other";
              } else kind = "key-identity";
              errs() << "KeyIdentity: mint r" << rid << " for key (r" << P.o
                     << " " << kind << " "
                     << (rc0 != UINT32_MAX ? protBlameName(rc0).substr(0, 70) : std::string("?"))
                     << ", s" << P.s << ") cell " << protBlameName(cell).substr(0, 60) << "\n";
            }
          }
        }
        if (holderMode) {
          // A clone's channel is fed by the base channel of the same
          // residue (stores through the fresh pointer) and feeds the
          // base key's readers (loads through the fresh pointer).
          auto cb = cloneBase.find(P.o);
          if (cb != cloneBase.end()) {
            const uint64_t bkey = (uint64_t)cb->second * NSHIFT + P.s;
            const uint32_t bch = clusterFind(bkey);
            if (bch != UINT32_MAX) linkChan(bch, ch);
            auto br = baseReaders.find(bkey);
            if (br != baseReaders.end())
              for (uint32_t rh2 : br->second) linkChan(ch, rh2);
          }
          // A base channel created after its clones feeds them.
          auto cl = clonesOfBase.find(P.o);
          if (cl != clonesOfBase.end())
            for (uint32_t c : cl->second) {
              const uint32_t cch = clusterFind((uint64_t)c * NSHIFT + P.s);
              if (cch != UINT32_MAX) linkChan(ch, cch);
            }
        }
        if (lazyAddr) {
          // Address overlap: bridge this channel with every channel of the
          // same object whose address set intersects (exact/strided/X).
          addrGrow();
          if (P.o < addrIsObj.size() && addrIsObj[P.o]) {
            auto &ks = addrKeysOfObj[addrObj[P.o]];
            for (uint32_t k2 : ks) {
              if (!addrOverlap(P.o, k2)) continue;
              const uint32_t ch2 = clusterFind((uint64_t)k2 * NSHIFT);
              if (ch2 == UINT32_MAX) continue;
              tKeyO = k2; tKeyS = 0;
              addBridge(ch, ch2);
              lazyOverlapBridges++;
            }
            ks.push_back(P.o);
          }
        } else if (NB > 0) { // VX linking between channel nodes (same scope)
          if (P.s == SHIFT_X) {
            for (uint64_t ek : shiftKeysOf[P.o]) {
              const uint32_t er = clusterFind(ek);
              if (er != UINT32_MAX) addBridge(ch, er);
            }
          } else {
            shiftKeysOf[P.o].push_back(key);
            const uint32_t xr =
                clusterFind((uint64_t)P.o * NSHIFT + SHIFT_X);
            if (xr != UINT32_MAX) addBridge(ch, xr);
          }
        }
        work++;
      } else {
        ch = find(it->second);
      }
      if (ch == cell) continue; // RMW-merged earlier under this key
      if (VerboseLevel >= 3) {
        errs() << "ChanFlush: cell c" << cell << " ("
               << protBlameName(cell).substr(0, 50) << ") key=(r" << P.o
               << " "
               << (P.o < rootClassOf.size()
                       ? protBlameName(rootClassOf[P.o]).substr(0, 40)
                       : "?")
               << ", s" << P.s << ") ch=c" << ch << "\n";
      }
      // Every cell is SPLIT, unconditionally: the cell itself is the
      // write half (it keeps the value edges stored INTO it and feeds
      // the channels of every key its owner may point to); a fresh
      // read half takes over the cell's outgoing edges (the loads it
      // feeds, GEPs on its content, its own downstream cells) and is
      // fed BY those channels. No access role is inferred from the
      // graph — direction is what the build-time edges already say:
      // in-edges are stores, out-edges are reads. A cell with no
      // out-edges (object storage, dead assistants) gets no read half.
      // Wiring one node both ways would relay content between the
      // owner's keys (Lean: rw_conduit_leaks); two nodes cannot: the
      // write half never receives channel content, the read half
      // never feeds a channel.
      auto [rhIt, rhNew] = chanReadHalf.try_emplace(cell, UINT32_MAX);
      if (rhNew) {
        if (!outA[cell].empty() || !outF[cell].empty() ||
            !cellsOf[cell].empty()) {
          const uint32_t rh = newSolverNode();
          rhIt->second = rh;
          chanNodeName[rh] = "rh(" + protBlameName(cell).substr(0, 50) + ")";
          outA[rh].swap(outA[cell]);
          outF[rh].swap(outF[cell]);
          cellsOf[rh].swap(cellsOf[cell]);
          // Content the cell accumulated before its split is a mix of
          // stored and (cluster-era) loaded facts; hand it to the read
          // half once so nothing already derived is lost. Future
          // arrivals route through the channels.
          // R planes are class planes (stable): let an empty target
          // adopt the buffer copy-on-write instead of streaming it, as
          // the wave does for full-plane pushes.
          tHow = "chan-carry"; tFrom = cell; tKeyO = UINT32_MAX; tCell = cell;
          for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
            if (R[cell][s2].any()) {
              bool rl = false; // holder rule: the base bit is not carried
              const FactSet &pay =
                  holderMode ? holderRelabel(cell, rh, R[cell][s2], ctx0, rl)
                             : R[cell][s2];
              addBits(rh, s2, pay, ctx0, !rl);
            }
            if (RB[cell][s2].any()) addBits(rh, s2, RB[cell][s2], ctx0);
          }
          chanSplits++;
        }
      }
      const uint32_t rh = rhIt->second;
      // write half -> channel
      if (chanEdgeSeen.insert(((uint64_t)cell << 32) | ch).second) {
        outA[cell].push_back(ch);
        chanEdges++;
        work++;
        tHow = "chan-in"; tFrom = cell; tKeyO = P.o; tKeyS = P.s; tCell = cell;
        // Holder rule: a fresh-store cell feeds this holder's channel
        // with the CLONE of its allocation, not the base. No clone for
        // X or constant-data holder keys, for a cell merged by the SCC
        // step, or past 32 holder keys (the base then flows, as today).
        if (holderMode) {
          auto fit = freshStoreCells.find(cell);
          if (fit != freshStoreCells.end() && !CFLTraceFunc.empty())
            CG_LOG("HolderIdentity: chan-in cell c" << cell << " size "
                   << clsSize[cell] << " key (r" << P.o << ",s" << P.s
                   << ") base r" << fit->second << " keys so far "
                   << holderKeyCount[cell] << "\n");
          if (fit != freshStoreCells.end() && clsSize[cell] == 1 &&
              P.s != SHIFT_X && fit->second != P.o &&
              !(P.o < rootConstData.size() && rootConstData[P.o])) {
            uint32_t &kc = holderKeyCount[cell];
            if (kc < 32) {
              kc++;
              const uint32_t c = holderClone(fit->second, key);
              auto &rl = chanRelabel[ch];
              const uint32_t base = fit->second;
              if (llvm::none_of(rl, [base](const std::pair<uint32_t, uint32_t> &pr) {
                    return pr.first == base;
                  }))
                rl.push_back({base, c});
            } else if (kc == 32) {
              kc++;
              holderCellsDisabled++;
            }
          }
        }
        for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
          if (R[cell][s2].any()) {
            bool rl = false;
            const FactSet &pay =
                holderMode ? holderRelabel(cell, ch, R[cell][s2], ctx0, rl)
                           : R[cell][s2];
            addBits(ch, s2, pay, ctx0, !rl);
          }
          if (RB[cell][s2].any()) addBits(ch, s2, RB[cell][s2], ctx0);
        }
      }
      // channel -> read half
      if (rh != UINT32_MAX &&
          chanEdgeSeen.insert(((uint64_t)ch << 32) | rh).second) {
        outA[ch].push_back(rh);
        chanEdges++;
        work++;
        tHow = "chan-out"; tFrom = ch; tKeyO = P.o; tKeyS = P.s; tCell = cell;
        for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
          if (R[ch][s2].any()) addBits(rh, s2, R[ch][s2], ctx0, true);
          if (RB[ch][s2].any()) addBits(rh, s2, RB[ch][s2], ctx0);
        }
      }
      if (holderMode && rh != UINT32_MAX && P.s != SHIFT_X &&
          freshBases.count(P.o)) {
        // A reader keyed by the BASE sees every clone's channel (the
        // fresh pointer may be any clone); remembered for clones whose
        // channel is created later.
        auto &rd = baseReaders[key];
        if (llvm::none_of(rd, [rh](uint32_t r2) { return r2 == rh; }))
          rd.push_back(rh);
        auto cl = clonesOfBase.find(P.o);
        if (cl != clonesOfBase.end())
          for (uint32_t c : cl->second) {
            const uint32_t cch = clusterFind((uint64_t)c * NSHIFT + P.s);
            if (cch != UINT32_MAX) linkChan(cch, rh);
          }
      }
    }
    if (VerboseLevel >= 2 && pendsIn >= 100000) {
      // Fan-out census: which cells (owners) carry the pend mass.
      std::unordered_map<uint32_t, uint32_t> perCell;
      for (const ChanPend &P : chanPend) perCell[find(P.cell)]++;
      std::vector<std::pair<uint32_t, uint32_t>> top(perCell.begin(), perCell.end());
      std::partial_sort(top.begin(), top.begin() + std::min<size_t>(8, top.size()),
                        top.end(), [](auto &a, auto &b) { return a.second > b.second; });
      errs() << "ChanFlush: " << perCell.size() << " distinct cells; top:";
      for (size_t i = 0; i < std::min<size_t>(8, top.size()); i++)
        errs() << " " << top[i].second << "x[" << protBlameName(top[i].first).substr(0, 40) << "]";
      errs() << "\n";
    }
    chanPend.clear();
    flushCtx(ctx0);
    if (demandMode)
      CG_LOG("ChannelDemand: relevant nodes " << demRelevantNodes << ", demanded keys "
             << demandedKeys.size() << ", deferred reads " << demDeferredR
             << " stores " << demDeferredS << ", replayed " << demReplayed << "\n");
    CG_LOG("ChanFlush: " << pendsIn << " pends, " << work << " new wirings; "
           << "channels " << chanNodes << " edges " << chanEdges
           << " splits " << chanSplits << ", "
           << std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - tFlush0).count()
           << " ms\n");
    return work;
  };
  // --cfl-demand-site widening report: walk the fact flow backward from
  // the site's callee operand over the reverse a/f graph (classes), and
  // find the widening points: classes whose fact count is at least twice
  // the largest count among their in-neighbours. A widening point with
  // many small in-neighbours is a confluence (a formal fed by many
  // callers, a cell fed by many stores); one inside a large merged class
  // is a cluster/SCC (the merge log says why it formed). The spine is
  // the greedy largest-in-neighbour walk from the operand to the first
  // widening point: the node where this site's answer became universal.
  auto wideningReport = [&]() {
    if (CFLDemandSite.empty()) return;
    const uint32_t NL = (uint32_t)std::min(ufp.size(), outA.size());
    std::vector<uint32_t> seeds;
    for (auto *CS : Ctx->IndirectCallInsts) {
      if (!demSiteWanted(CS)) continue;
      Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
      NodeIndex fn = NF.getValueNodeFor(fp);
      if (fn == AndersNodeFactory::InvalidIndex) continue;
      auto dIt = toDense.find(getCanonicalNode(fn));
      if (dIt == toDense.end()) continue;
      const uint32_t rep = find(dIt->second);
      if (std::find(seeds.begin(), seeds.end(), rep) == seeds.end())
        seeds.push_back(rep);
    }
    errs() << "WIDEN site '" << CFLDemandSite << "': " << seeds.size()
           << " callee-operand classes\n";
    if (seeds.empty()) return;
    // Reverse fact-flow graph over classes: (source class, kind) per
    // target class. Kind: 'a' edge, 'f' edge.
    std::vector<std::vector<std::pair<uint32_t, char>>> rin(NL);
    boost::unordered_flat_set<uint64_t> seenE;
    for (uint32_t n = 0; n < NL; n++) {
      const uint32_t sn = find(n);
      for (uint32_t t : outA[n]) {
        if (t >= NL) continue;
        const uint32_t tt = find(t);
        if (tt != sn && seenE.insert(((uint64_t)tt << 32) | sn).second)
          rin[tt].emplace_back(sn, 'a');
      }
      if (n < outF.size())
        for (auto [t, r] : outF[n]) {
          if (t >= NL) continue;
          const uint32_t tt = find(t);
          if (tt != sn && seenE.insert(((uint64_t)tt << 32) | sn).second)
            rin[tt].emplace_back(sn, 'f');
        }
      // VX bridge ('x'): facts cross between the (o,X) cluster and the
      // exact clusters of o in both directions (they land in RB).
      if (n < bridgesOf.size())
        for (uint32_t br : bridgesOf[n]) {
          if (br >= NL) continue;
          const uint32_t bb = find(br);
          if (bb == sn) continue;
          if (seenE.insert(((uint64_t)bb << 32) | sn).second) rin[bb].emplace_back(sn, 'x');
          if (seenE.insert(((uint64_t)sn << 32) | bb).second) rin[sn].emplace_back(bb, 'x');
        }
      // Owner hop ('o'): a cell's facts are selected by the keys its owner
      // pointer holds (cluster delivery / channel wiring), so the owner is
      // a fact-flow input of the cell even without an a/f edge.
      if (n < cellsOf.size())
        for (uint32_t c : cellsOf[n]) {
          if (c >= NL) continue;
          const uint32_t cc = find(c);
          if (cc != sn && seenE.insert(((uint64_t)cc << 32) | sn).second)
            rin[cc].emplace_back(sn, 'o');
        }
    }
    std::vector<uint32_t> members(NL, 0);
    for (uint32_t n = 0; n < NL; n++) members[find(n)]++;
    std::vector<int64_t> fc(NL, -1);
    auto factsOf = [&](uint32_t x) -> int64_t {
      if (fc[x] >= 0) return fc[x];
      int64_t c = 0;
      if (x < R.size())
        for (uint32_t s2 = 0; s2 < NSHIFT; s2++)
          c += (int64_t)R[x][s2].count() + (int64_t)RB[x][s2].count();
      return fc[x] = c;
    };
    // Backward closure from the seeds (the site's slice).
    std::vector<char> vis(NL, 0);
    std::vector<uint32_t> order, q;
    for (uint32_t sd : seeds) if (!vis[sd]) { vis[sd] = 1; q.push_back(sd); }
    while (!q.empty()) {
      const uint32_t x = q.back(); q.pop_back();
      order.push_back(x);
      for (auto [y, k] : rin[x]) if (!vis[y]) { vis[y] = 1; q.push_back(y); }
    }
    // Condense the slice into strongly connected components: a class
    // inside a cycle receives the cycle's whole fact set back, so per-class
    // in-neighbour counts see only the cycle. Widening is judged per
    // component against its inputs from OTHER components.
    std::unordered_map<uint32_t, uint32_t> comp; // class -> component
    {
      std::unordered_map<uint32_t, uint32_t> idx, low;
      std::vector<uint32_t> st; std::vector<char> onSt; onSt.assign(NL, 0);
      uint32_t counter = 0, ncomp = 0;
      struct Fr { uint32_t x; size_t i; };
      for (uint32_t root : order) {
        if (idx.count(root)) continue;
        std::vector<Fr> cs{{root, 0}};
        idx[root] = low[root] = counter++; st.push_back(root); onSt[root] = 1;
        while (!cs.empty()) {
          Fr &f = cs.back();
          if (f.i < rin[f.x].size()) {
            const uint32_t y = rin[f.x][f.i++].first;
            if (!vis[y]) continue;
            auto it = idx.find(y);
            if (it == idx.end()) {
              idx[y] = low[y] = counter++; st.push_back(y); onSt[y] = 1;
              cs.push_back({y, 0});
            } else if (onSt[y]) {
              low[f.x] = std::min(low[f.x], it->second);
            }
            continue;
          }
          if (low[f.x] == idx[f.x]) {
            for (;;) {
              const uint32_t y = st.back(); st.pop_back(); onSt[y] = 0;
              comp[y] = ncomp;
              if (y == f.x) break;
            }
            ncomp++;
          }
          const uint32_t x = f.x; cs.pop_back();
          if (!cs.empty()) low[cs.back().x] = std::min(low[cs.back().x], low[x]);
        }
      }
    }
    const uint32_t NC = comp.empty() ? 0 : 1 + std::max_element(
        comp.begin(), comp.end(), [](auto &a, auto &b) { return a.second < b.second; })->second;
    std::vector<int64_t> compF(NC, 0);
    std::vector<uint32_t> compCls(NC, 0), compMem(NC, 0), compRep(NC, UINT32_MAX);
    // inputs: component -> (source class, target class, kind) per source component
    std::vector<std::unordered_map<uint32_t, std::tuple<uint32_t, uint32_t, char>>> compIn(NC);
    std::vector<std::unordered_map<uint32_t, uint32_t>> entryEdges(NC); // member -> #external in-edges
    for (uint32_t x : order) {
      const uint32_t c = comp[x];
      compCls[c]++; compMem[c] += members[x];
      if (factsOf(x) > compF[c] || compRep[c] == UINT32_MAX) { compF[c] = factsOf(x); compRep[c] = x; }
      for (auto [y, k] : rin[x]) {
        const uint32_t cy = comp[y];
        if (cy == c) continue;
        entryEdges[c][x]++;
        auto it = compIn[c].find(cy);
        if (it == compIn[c].end() || factsOf(y) > factsOf(std::get<0>(it->second)))
          compIn[c][cy] = {y, x, k};
      }
    }
    std::vector<uint32_t> wcs; std::vector<char> isW(NC, 0);
    std::vector<int64_t> maxInF(NC, 0);
    for (uint32_t c = 0; c < NC; c++) {
      for (auto &[cy, e] : compIn[c]) maxInF[c] = std::max(maxInF[c], compF[cy]);
      if (compF[c] >= 16 && compF[c] >= 2 * maxInF[c]) { wcs.push_back(c); isW[c] = 1; }
    }
    std::sort(wcs.begin(), wcs.end(), [&](uint32_t a, uint32_t b) { return compF[a] > compF[b]; });
    errs() << "WIDEN slice: " << order.size() << " classes, " << NC
           << " components; " << wcs.size()
           << " widening components (F >= 2x every input component)\n";
    auto describe = [&](uint32_t x) {
      return "c" + std::to_string(x) + " " + nodeKind(x) + " members=" +
             std::to_string(members[x]) + " F=" + std::to_string(factsOf(x)) +
             " " + protBlameName(x).substr(0, 70);
    };
    auto showComp = [&](uint32_t c, size_t k) {
      std::vector<std::pair<int64_t, uint32_t>> ins;
      for (auto &[cy, e] : compIn[c]) ins.push_back({compF[cy], cy});
      std::sort(ins.begin(), ins.end(), [](auto &a, auto &b) { return a.first > b.first; });
      size_t small = 0, mid = 0, big = 0;
      for (auto &e : ins) (e.first < 16 ? small : e.first < 256 ? mid : big)++;
      errs() << "      inputs " << ins.size() << " components (F<16: " << small
             << ", 16..255: " << mid << ", >=256: " << big << ")\n";
      for (size_t i = 0; i < std::min(k, ins.size()); i++) {
        auto [y, x, kd] = compIn[c][ins[i].second];
        errs() << "      <-" << kd << "- " << describe(y) << "  into "
               << nodeKind(x) << " " << protBlameName(x).substr(0, 50) << "\n";
      }
      // entry classes of the component by kind: what shape of node lets
      // the outside in (formals = call confluence, cells = store confluence)
      std::map<std::string, std::pair<uint32_t, uint32_t>> byKind; // kind -> (#classes, #edges)
      std::vector<std::pair<uint32_t, uint32_t>> top;
      for (auto &[x, n] : entryEdges[c]) {
        auto &bk = byKind[nodeKind(x)]; bk.first++; bk.second += n;
        top.push_back({n, x});
      }
      if (compCls[c] > 1) {
        errs() << "      entry classes by kind:";
        for (auto &[kd, v] : byKind) errs() << " " << kd << "=" << v.first << "(" << v.second << " edges)";
        errs() << "\n";
        std::sort(top.begin(), top.end(), [](auto &a, auto &b) { return a.first > b.first; });
        for (size_t i = 0; i < std::min<size_t>(6, top.size()); i++)
          errs() << "      entry " << top[i].first << " edges: " << describe(top[i].second) << "\n";
      }
    };
    // Junction ranking: the edges INSIDE the widening component that pass
    // through a call boundary (into a formal, out of a return) are what
    // close its cycles. Rank functions by how many internal edges enter
    // their formals or leave through their returns: these are the
    // context-insensitive junctions where the union is formed.
    auto junctionRank = [&](uint32_t c) {
      struct J { uint32_t formalsIn = 0, retsOut = 0, formalCls = 0; };
      std::map<const Function *, J> jn;
      std::map<char, uint32_t> byKind;
      uint32_t internal = 0;
      for (uint32_t x : order) {
        if (comp[x] != c) continue;
        uint32_t inHere = 0;
        for (auto [y, k] : rin[x]) {
          if (comp[y] != c) continue;
          internal++; byKind[k]++; inHere++;
        }
        if (inHere == 0 || x >= toOrig.size()) continue;
        const Value *V = NF.getValueForNode(toOrig[x]);
        if (const auto *A = dyn_cast_or_null<Argument>(V)) {
          auto &j = jn[A->getParent()]; j.formalsIn += inHere; j.formalCls++;
        } else if (const auto *CB = dyn_cast_or_null<CallBase>(V)) {
          if (const Function *CF = CB->getCalledFunction()) {
            jn[getFuncDef(const_cast<Function *>(CF))].retsOut += inHere;
          } else {
            auto cit = Ctx->Callees.find(CB);
            if (cit != Ctx->Callees.end())
              for (const Function *T : cit->second) jn[T].retsOut += inHere;
          }
        }
      }
      errs() << "WIDEN-JUNCTIONS: " << internal << " internal edges (";
      for (auto &[k, n] : byKind) errs() << k << "=" << n << " ";
      errs() << "); functions ranked by internal edges into formals + out of returns:\n";
      std::vector<std::pair<uint32_t, const Function *>> rk;
      for (auto &[F, j] : jn) rk.push_back({j.formalsIn + j.retsOut, F});
      std::sort(rk.begin(), rk.end(), [](auto &a, auto &b) { return a.first > b.first; });
      for (size_t i = 0; i < std::min<size_t>(40, rk.size()); i++) {
        auto &j = jn[rk[i].second];
        errs() << "WIDEN-JUNCTION " << rk[i].first << " " << rk[i].second->getName()
               << " formals-in=" << j.formalsIn << " (" << j.formalCls
               << " formal classes) returns-out=" << j.retsOut << "\n";
      }
    };
    size_t shown = 0;
    for (uint32_t c : wcs) {
      if (shown++ >= 20) break;
      errs() << "WIDEN-COMP #" << shown << " classes=" << compCls[c] << " members="
             << compMem[c] << " F=" << compF[c] << " maxIn=" << maxInF[c]
             << " rep " << describe(compRep[c]) << "\n";
      showComp(c, 5);
      if (shown == 1) junctionRank(c);
    }
    // Spine per seed over the condensation: largest input component
    // until the first widening component.
    for (uint32_t sd : seeds) {
      errs() << "SPINE from callee operand " << describe(sd) << "\n";
      uint32_t cur = comp[sd];
      std::vector<char> onPath(NC, 0);
      for (int hop = 0; hop < 80; hop++) {
        onPath[cur] = 1;
        errs() << "  hop " << hop << " comp classes=" << compCls[cur] << " members="
               << compMem[cur] << " F=" << compF[cur] << " rep " << describe(compRep[cur]) << "\n";
        if (isW[cur]) {
          errs() << "  hop " << hop << " WIDENING COMPONENT\n";
          showComp(cur, 10);
          // Full entry dump: every member class that receives an edge
          // from outside the component, with its external in-degree by
          // edge kind. The formals here are the context-free confluences
          // that close the cycle; the cells are the store confluences.
          std::vector<std::tuple<uint32_t, uint32_t, uint32_t, uint32_t, uint32_t>> ent; // edgesA,F,O,X per member
          std::unordered_map<uint32_t, std::array<uint32_t, 4>> perKind;
          for (uint32_t x : order) {
            if (comp[x] != cur) continue;
            std::array<uint32_t, 4> k{0, 0, 0, 0};
            for (auto [y, kd] : rin[x])
              if (comp[y] != cur) k[kd == 'a' ? 0 : kd == 'f' ? 1 : kd == 'o' ? 2 : 3]++;
            if (k[0] + k[1] + k[2] + k[3]) perKind[x] = k;
          }
          std::vector<std::pair<uint32_t, uint32_t>> ord2;
          for (auto &[x, k] : perKind) ord2.push_back({k[0] + k[1] + k[2] + k[3], x});
          std::sort(ord2.begin(), ord2.end(), [](auto &a, auto &b) { return a.first > b.first; });
          errs() << "  WIDEN-ENTRIES " << ord2.size() << " member classes with external inputs (a/f/o/x edges)\n";
          for (auto &[n2, x] : ord2) {
            auto &k = perKind[x];
            errs() << "    entry a=" << k[0] << " f=" << k[1] << " o=" << k[2] << " x=" << k[3]
                   << " " << describe(x) << "\n";
            if (nodeKind(x).rfind("formal", 0) != 0) continue;
            // For a formal: the callers inside the component are what
            // make it universal; the callers outside are what it lets in.
            std::vector<std::pair<int64_t, uint32_t>> inside, outside;
            for (auto [y, kd] : rin[x])
              (comp[y] == cur ? inside : outside).push_back({factsOf(y), y});
            std::sort(inside.begin(), inside.end(), [](auto &a, auto &b) { return a.first > b.first; });
            std::sort(outside.begin(), outside.end(), [](auto &a, auto &b) { return a.first > b.first; });
            errs() << "      callers inside " << inside.size() << ", outside " << outside.size() << "\n";
            for (size_t i = 0; i < std::min<size_t>(4, inside.size()); i++)
              errs() << "        in  " << describe(inside[i].second) << "\n";
            for (size_t i = 0; i < std::min<size_t>(3, outside.size()); i++)
              errs() << "        out " << describe(outside[i].second) << "\n";
          }
          break;
        }
        int64_t mx = -1; uint32_t nxt = UINT32_MAX;
        for (auto &[cy, e] : compIn[cur])
          if (!onPath[cy] && compF[cy] > mx) { mx = compF[cy]; nxt = cy; }
        if (nxt == UINT32_MAX) { errs() << "  hop " << hop << " END (no input)\n"; break; }
        auto [y, x, kd] = compIn[cur][nxt];
        errs() << "      via <-" << kd << "- " << describe(y) << " into "
               << protBlameName(x).substr(0, 50) << "\n";
        cur = nxt;
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
    // Live node count: channel-cells appends nodes past N.
    const uint32_t NL = (uint32_t)ufp.size();
    std::vector<std::vector<uint32_t>> sccs;
    // Pairwise cells: memory nodes (cells, channels, read halves) are
    // never merged — an a-cycle through memory (a read-modify-write
    // through a wide pointer) is left to propagation, which reaches the
    // same fixpoint; merging it unified the slot cells of every object
    // the pointer may reach (cflow: yyin's FILE* cell with a list head's
    // free_data). Only value-to-value cycles collapse.
    auto isMemoryNode = [&](uint32_t v) -> bool {
      // A named shadow collapsed with values would take their content
      // under its name, and pour its own into every name.
      if (nameOfCell(v) != ka::AccessNames::Original) return true;
      if (!CFLChannelCells) return false;
      if (v >= N) return true; // channel / read half
      return NF.isDereferenceNode(toOrig[v]);
    };
    auto edgeAt = [&](uint32_t u, size_t i) -> uint32_t {
      // Unified edge index: outA first, then residue-0 outF entries.
      uint32_t v;
      if (i < outA[u].size()) v = find(outA[u][i]);
      else {
        auto &[t, r] = outF[u][i - outA[u].size()];
        v = r == 0 ? find(t) : UINT32_MAX;
      }
      return (v != UINT32_MAX && isMemoryNode(v)) ? UINT32_MAX : v;
    };
    ka::tarjanSCC(
        NL,
        [&](uint32_t v) { return find(v) != v || isMemoryNode(v); },
        [&](uint32_t u) { return outA[u].size() + outF[u].size(); },
        edgeAt,
        [&](const std::vector<uint32_t> &members) {
          if (members.size() > 1) sccs.push_back(members);
        });
    if (!CFLDumpSCC.empty()) {
      // --cfl-dump-scc: the shortest cycle through the named node, over
      // the very edges the collapse followed (a, residue-0 f; channel
      // wiring edges are a-edges), before the SCC is merged away.
      static size_t sccDumps = 0;
      // Resolve the named node by MEMBER name once per collapse: a node
      // merged earlier sits in a class named after its rep, so matching
      // SCC members (class reps) by name misses it.
      uint32_t target = UINT32_MAX;
      for (uint32_t n2 = 0; n2 < (uint32_t)toOrig.size() && target == UINT32_MAX;
           n2++)
        if (denseNameMatches(n2, CFLDumpSCC)) target = n2;
      if (target == UINT32_MAX)
        errs() << "DumpSCC: no node named like '" << CFLDumpSCC << "'\n";
      for (auto &scc : sccs) {
        if (sccDumps >= 4 || target == UINT32_MAX) break;
        boost::unordered_flat_set<uint32_t> in(scc.begin(), scc.end());
        const uint32_t hit = find(target);
        if (!in.count(hit)) continue;
        sccDumps++;
        size_t syn = 0;
        for (uint32_t m : scc) if (m >= N) syn++;
        errs() << "DumpSCC: size " << scc.size() << " (" << syn
               << " channel/read-half) contains "
               << protBlameName(hit).substr(0, 60) << "\n";
        std::unordered_map<uint32_t, std::pair<uint32_t, const char *>> pred;
        std::deque<uint32_t> q{hit};
        pred[hit] = {UINT32_MAX, ""};
        uint32_t back = UINT32_MAX;
        const char *backKind = "";
        while (!q.empty() && back == UINT32_MAX) {
          const uint32_t u = q.front();
          q.pop_front();
          const size_t na = outA[u].size();
          for (size_t i = 0; i < na + outF[u].size(); i++) {
            const uint32_t v = edgeAt(u, i);
            if (v == UINT32_MAX || !in.count(v)) continue;
            const char *kind = i < na ? "a" : "f0";
            if (v == u) continue; // a merged class's internal edge is not a cycle
            if (v == hit) { back = u; backKind = kind; break; }
            if (pred.emplace(v, std::make_pair(u, kind)).second) q.push_back(v);
          }
        }
        if (back == UINT32_MAX) continue;
        std::vector<std::pair<uint32_t, const char *>> path;
        for (uint32_t x = back; x != hit; x = pred[x].first)
          path.push_back({x, pred[x].second});
        std::reverse(path.begin(), path.end());
        errs() << "DumpSCC:   " << protBlameName(hit).substr(0, 70) << " ["
               << nodeKind(hit) << "]\n";
        for (auto &[x, k] : path)
          errs() << "DumpSCC:   -" << k << "-> " << protBlameName(x).substr(0, 70)
                 << " [" << nodeKind(x) << "]\n";
        errs() << "DumpSCC:   -" << backKind << "-> (back to the start)\n";
      }
    }
    size_t collapsed = 0;
    mergeWhy = "scc";
    for (auto &scc : sccs) {
      uint32_t rep = find(scc[0]);
      blobCtx = "a-scc"; blobCtxOrigin = UINT32_MAX; tKeyO = UINT32_MAX;
      for (size_t i = 1; i < scc.size(); i++) {
        rep = merge(rep, scc[i]);
        collapsed++;
      }
      compactLists(rep);
    }
    mergeWhy = "other";
    return collapsed;
  };
  // Named cells: hang every shadow on its cell's class; shadows of one
  // name on one class merge now (they are one plane of that class).
  if (!cellNameOf.empty()) {
    tHow = "named-satellite";
    for (uint32_t u = 0; u < N; u++) {
      const auto [cell, nm] = shadowInfoOf(toOrig[u]);
      if (nm == ka::AccessNames::Original) continue;
      auto d = toDense.find(getCanonicalNode(cell));
      assert(d != toDense.end() && "a shadow's cell is in the graph");
      const uint32_t c = find(d->second);
      bool found = false;
      for (auto &[nm2, v] : satOf[c])
        if (nm2 == nm) {
          found = true;
          if (find(v) != find(u)) merge(v, u);
          break;
        }
      if (!found) satOf[c].emplace_back(nm, u);
    }
  }
  tHow = "seed"; tFrom = UINT32_MAX;
  // Named cells: a root minted on a class is content of each cell in
  // the class that no program store wrote — content from outside, read
  // under whatever name: it goes to those cells' Identity shadows, which
  // every named load reads (NamedCells.lean: RDeriv.cid).
  std::vector<std::pair<uint32_t, uint32_t>> unnamedSeeds; // (shadow, rid)
  size_t pendingSeeds = 0;
  if (!cellNameOf.empty()) {
    addFactFn = [&](uint32_t n2, uint32_t pl, uint32_t rid) {
      addFact(n2, pl, rid, ctx0);
    };
    std::vector<NodeIndex> members;
    for (auto [n, rid] : seeds) {
      const uint32_t c = find(n);
      bool seeded = false;
      for (auto &[nm, u] : satOf[c])
        if (nm == ka::AccessNames::Identity) {
          unnamedSeeds.emplace_back(u, rid);
          seeded = true;
          break;
        }
      if (seeded) continue;
      collectCanonicalMembers(toOrig[n], members);
      for (NodeIndex m : members)
        if (isCellNode(m)) { // cell content from outside: wait for a reader
          pendingId[c].emplace_back(
              rid, (!nexusGate || rootNexus[rid]) ? 0u : (uint32_t)SHIFT_X);
          pendingSeeds++;
          break;
        }
    }
    CG_LOG("NamedCells: " << unnamedSeeds.size()
           << " roots seeded into identity shadows, " << pendingSeeds
           << " pending a reader\n");
  }
  if (CFLBatchRoots == 0) {
    size_t exactMint = 0, wildMint = 0;
    for (auto [n, rid] : seeds) {
      const bool exact = !nexusGate || rootNexus[rid];
      if (lazyAddr && !exact) addFact(find(n), 0, mintX(rid), ctx0);
      else addFact(find(n), exact ? 0 : SHIFT_X, rid, ctx0);
      (exact ? exactMint : wildMint)++;
    }
    for (auto [u, rid] : unnamedSeeds)
      addFact(find(u), (!nexusGate || rootNexus[rid]) ? 0 : SHIFT_X, rid,
              ctx0);
    if (nexusGate)
      CG_LOG("NexusFields: " << exactMint << " exact-minted roots (fn + "
             "nexus origins), " << wildMint << " wildcard-minted (FI)\n");
  } // batched mode seeds per batch inside the round driver (task #40)
  flushCtx(ctx0);

  auto originBearing = [&](NodeIndex canon) {
    if (valueIsOrigin(canon)) return true;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m : mit->second)
        if (valueIsOrigin(m)) return true;
    return false;
  };
  // Adoption-starved class: contains a formal (or vararg node) of a
  // SUMMARIZED fn and bears no real origin. Its in-degree-0-ness is
  // adoption-induced (the summary owns the callsite wiring) — minting
  // it creates a tracer-dye identity that rides the walked body's
  // value web and welds every deref cell it touches into one cluster.
  auto starvedFormalClass = [&](uint32_t cls) -> bool {
    NodeIndex canon = toOrig[find(cls)];
    if (originBearing(canon)) return false;
    auto chk = [&](NodeIndex m) -> bool {
      const Value *cv = NF.getValueForNode(m);
      const Function *PF = nullptr;
      if (const auto *A2 = dyn_cast_or_null<Argument>(cv))
        PF = A2->getParent();
      else if (cv && NF.isVarargNode(m))
        PF = dyn_cast<Function>(cv);
      return PF && Ctx->FuncSummaries.count(
                       getFuncDef(const_cast<Function *>(PF)));
    };
    if (chk(canon)) return true;
    auto mit = canonicalClassMembers.find(canon);
    if (mit != canonicalClassMembers.end())
      for (NodeIndex m : mit->second)
        if (chk(m)) return true;
    return false;
  };
  auto mintRoot = [&](uint32_t cls) {
    assert(cellNameOf.empty() && "named cells refuse lazy minting");
    uint32_t rep = find(cls);
    if (isRoot[rep]) return;
    // Channel nodes / read halves (ids past the dense graph) are solver
    // plumbing, never value origins: hasIn/toOrig do not cover them.
    if (rep >= N) return;
    if (CFLAdoptProposedSummaries && starvedFormalClass(rep)) return;
    isRoot[rep] = 1;
    uint32_t rid = nextRoot++;
    // widen BEFORE the first set of this bit
    FactSet::Universe = nextRoot;
    rootClassOf.push_back(rep);
    rootConstData.push_back(isConstDataRoot(rep));
    rootParkable.push_back(!hasIn[rep] && !originBearing(toOrig[rep]));
    if (lazyAddr) {
      addrGrow();
      addrObj[rid] = rid; addrOff[rid] = 0; addrStride[rid] = 0;
      addrIsObj[rid] = !funcOfCanon.count(toOrig[rep]);
      addrIndex[std::make_tuple(rid, (int64_t)0, (uint32_t)0, (uint32_t)0)] = rid;
    }
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
    // Batch mode: the live planes belong to whichever batch last ran
    // (local bit space) — the new rid seeds inside its own appended
    // batch on the next round instead.
    if (CFLBatchRoots == 0)
      addFact(rep, (nexusGate && !rootNexus[rid]) ? SHIFT_X : 0, rid,
              ctx0);
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
    const uint32_t NL = (uint32_t)ufp.size(); // channel nodes included
    std::vector<std::vector<uint32_t>> rin(NL);
    for (uint32_t n = 0; n < NL; n++) {
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
    std::vector<char> A(NL, 0);
    std::vector<uint32_t> bfs;
    for (auto *CS : Ctx->IndirectCallInsts) {
      if (!demSiteWanted(CS)) continue;
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
    if (find(n) != n) return; // merged away; keeper carries the state
    for (uint32_t s = 0; s < NSHIFT; s++) {
      if (jdirty[n][s].none()) continue;
      uint64_t tp0 = rd();
      FactSet &todo = ctx.todoS;
      todo.copyFrom(jdirty[n][s]);
      jdirty[n][s].clear();
      // Channel mode: bridged facts (o,s) exist only as VX images of a
      // native (o,X) or (o,s') fact, and the channel nodes of one
      // origin are bridged with each other at creation — so wiring the
      // cell to every residue's channel would repeat, per cell, what the
      // channel-level bridges already do (P-fold pend fan-out). Join on
      // native facts only.
      if (CFLChannelCells) todo.intersectWith(R[n][s]);
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
      const uint64_t todoCnt = todo.count();
      if (todoCnt == 0) { ctx.cyJoin += rd() - tp0; continue; }
      if (prof) ctx.sweepKept += todoCnt;
      // Fast path eligibility: the measurement flags reroute joins and
      // the prot path bypasses the registry — both must stay slow-path.
      // Batch mode INCLUDED (2026-08-15): marks live in GLOBAL grid
      // space — valid across batches and rounds because the cluster
      // registry is global and clusters only grow; the promote() fix
      // above retired the #48-era batch-local-width OOB. Workers set
      // marks for their own drain's lifetime (fork CoW starts empty:
      // conservative); sequential spill mode keeps them run-long.
      const bool fastJoinBase = CFLJoinFastpath;
      if (fastJoinBase) {
        // CELL-MAJOR sweep (fs-cost lever, 2026-08-14): the fact-major
        // loop paid ~350 cycles (find() chase + random bit probe) per
        // (fact, cell) visit and 99.98% of visits were proven no-ops
        // (km fs41: 9.0B skips vs 1.8M real joins — merge re-offers
        // re-confirming absorbed planes). Inverting the loop answers
        // the whole backlog per cell at word level: a read-only subset
        // scan certifies "cluster already absorbed all of todo" in one
        // pass, and the residual is a word-ANDN. Per-fact work remains
        // only for genuine first joins.
        // Batch workers run with a nonzero rid base: image the o-space
        // backlog into grid space ONCE per sweep (word-shifted copy) so
        // every per-cell filter runs against the grid-indexed marks.
        // Mono (base 0) uses todo directly.
        const FactSet *tgp = &todo;
        if (g_ridBase != 0) {
          ctx.todoGS.copyShifted(todo, g_ridBase);
          tgp = &ctx.todoGS;
        }
        const FactSet &todoG = *tgp;
        bool aborted = false;
        // The outer bound re-reads cellsOf[n].size(): cells appended by
        // mid-sweep merges (n as keeper) are swept with the same todo,
        // which is what makes the end-of-sweep joined union sound.
        for (size_t ci = 0; ci < cellsOf[n].size(); ci++) {
          // Value copy: joinCluster's merges can splice/clear this
          // very list — never index cellsOf[n] after the call.
          const uint32_t cell = cellsOf[n][ci];
          const uint32_t rep = find(cell);
          if (todoG.subsetOf(cellJoined[rep][s])) {
            ctx.cellSkips += todoCnt; // whole backlog proven no-op
            ctx.wordSkips++;
            continue;
          }
          FactSet &pending = ctx.pendS;
          pending.copyFrom(todoG);
          pending.subtract(cellJoined[rep][s]);
          // Snapshot: joinCluster can merge and mutate backing state.
          ctx.sweepElems.clear();
          pending.forEach([&](uint32_t g) { ctx.sweepElems.push_back(g); });
          ctx.cellSkips += todoCnt - ctx.sweepElems.size();
          for (uint32_t grid : ctx.sweepElems) {
            if (cellJoined[find(cell)][s].test(grid)) {
              ctx.cellSkips++; // mid-batch merge already carried the mark
              continue;
            }
            ctx.nJoinLk++;
            tPtr = n; mergeWhy = "join";
            joinCluster(cell, grid, s);
            tPtr = UINT32_MAX; tKeyO = UINT32_MAX; // stale keys must not label later merges
            mergeWhy = "other";
            cellJoined[find(cell)][s].set(grid);
            if (find(n) != n) { aborted = true; break; }
          }
          if (aborted) break;
        }
        // Every todo fact was offered to every (final) cell: one word-OR
        // replaces the per-fact joined marks. On abort n was absorbed —
        // its joined plane is released and the keeper re-offers its full
        // plane, so skipping the union loses nothing and must not
        // resurrect the dead plane.
        if (!aborted) joined[n][s].unionWith(todo);
        ctx.cyJoin += rd() - tp0;
        if (find(n) != n) return;
        continue;
      }
      // LEGACY fact-major sweep: the join-rerouting measurement flags
      // only (marks would record joins that were skipped/rerouted).
      ctx.sweepElems.clear();
      todo.forEach([&](uint32_t o) { ctx.sweepElems.push_back(o); });
      bool firstFact = true;
      for (uint32_t o : ctx.sweepElems) {
        const uint32_t grid = g_ridBase + o;
        bool aborted = false;
        for (size_t ci = 0; ci < cellsOf[n].size(); ci++) {
          // Value copy: joinCluster's merges can splice/clear this
          // very list — never index cellsOf[n] after the call.
          const uint32_t cell = cellsOf[n][ci];
          ctx.nJoinLk++;
          tPtr = n; mergeWhy = "join";
          joinCluster(cell, grid, s);
          tPtr = UINT32_MAX; tKeyO = UINT32_MAX; mergeWhy = "other";
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
      const bool wlazy = lazyAddr && wflag[n]; // fx: every object also at X
      lockC(n);
      const bool doBr = dirtyBr[n][s].any() && !bridgesOf[n].empty();
      if (doBr) db.copyFrom(dirtyBr[n][s]);
      dirtyBr[n][s].clear();
      const bool hasD = dirty[n][s].any();
      // Full-plane delta: the delta IS the plane, so push R itself
      // (stable payload -> downstream adoption) and skip the snapshot
      // copy. The virgin flag witnesses dirty==R exactly and O(1)
      // (arrivals append to both equally; consumption/RB/merge traffic
      // clears it) — an earlier popcount-equality probe here scanned
      // R on every pop and regressed fs-scale runs.
      const bool dFull = hasD && FactSet::EnableShare &&
                         (virginPl[(size_t)n * NSHIFT + s] != 0 ||
                          dirty[n][s].sharesDense(R[n][s]));
      if (hasD) {
        virginPl[(size_t)n * NSHIFT + s] = 0; // consuming dirty below
        if (dFull) {
          dirty[n][s].clear(); // drops the shared handle
        } else {
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
      }
      unlockC(n);
      // Bridge crossings: native backlog only, arriving bridged.
      if (doBr) {
        if (traceAny) { tHow = "bridge"; tFrom = n; }
        for (uint32_t br : bridgesOf[n]) {
          uint32_t bb = find(br);
          if (bb != n) addBitsBridged(bb, s, db, ctx);
        }
      }
      uint64_t tp2 = rd();
      ctx.cyBridge += tp2 - tp1;
      if (!hasD) { ctx.cyScan += rd() - tp2; continue; }
      uint64_t tp3 = rd();
      // Payload: the full R plane (stable, adoptable downstream) when
      // the delta is the whole plane, the scratch snapshot otherwise.
      const FactSet &pay = dFull ? R[n][s] : d;
      if (wproj) {
        if (traceAny) { tHow = "wflag"; tFrom = n; }
        if (dFull) {
          // Delta == R and RB empty: the native split is R itself.
          addBits(n, SHIFT_X, pay, ctx, true);
        } else {
          if (ctx.dNatS.any()) addBits(n, SHIFT_X, ctx.dNatS, ctx);
          if (ctx.dBrS.any()) addBitsBridged(n, SHIFT_X, ctx.dBrS, ctx);
        }
      }
      if (wlazy) {
        FactSet xs;
        pay.forEach([&](uint32_t bit) {
          const uint32_t x = mintX(bit);
          if (x != bit) xs.set(x);
        });
        if (xs.any()) { if (traceAny) { tHow = "wflag"; tFrom = n; } addBits(n, 0, xs, ctx); }
      }
      uint64_t tp4 = rd();
      ctx.cyW += tp4 - tp3;
      // Propagate the delta: whole-plane OR along a-edges, plane-rotated
      // OR along f-edges (X absorbs). Emission is native — value flow
      // launders bridge provenance, exactly like the grammar (M-hops
      // are separated by a-steps in every V derivation).
      if (traceAny) { tHow = "a-prop"; tFrom = n; }
      for (uint32_t t : outA[n]) {
        uint32_t tt = find(t);
        if (tt == n) continue;
        ctx.nAOr++;
        if (holderMode) { // fresh-store cell -> holder channel: clone bit
          bool rl = false;
          const FactSet &p2 = holderRelabel(n, tt, pay, ctx, rl);
          addBits(tt, s, p2, ctx, dFull && !rl);
        } else {
          addBits(tt, s, pay, ctx, dFull);
        }
      }
      uint64_t tp5 = rd();
      ctx.cyA += tp5 - tp4;
      if (prof) ctx.orWords += (uint64_t)pay.count() * outA[n].size();
      if (traceAny) { tHow = "f-prop"; tFrom = n; }
      for (auto [t, r] : outF[n]) {
        uint32_t tt = find(t);
        if (lazyAddr) { // exact remap per bit (mints addresses on demand)
          FactSet &rm = remapScratch();
          remapPlane(pay, r, n, t, rm);
          if (rm.any()) { ctx.nFOr++; addBits(tt, 0, rm, ctx); }
          continue;
        }
        uint32_t s2 = (NB == 0 || s == SHIFT_X) ? s : (s + r) % NB;
        if (tt != n || s2 != s) { ctx.nFOr++; addBits(tt, s2, pay, ctx, dFull); }
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
  // presolve-once: the wired graph's giant copy-SCC is discovered
  // in-drain instead of by the skipped pre-solve — pull the first
  // collapse sweep early so per-member plane duplication stays short.
  uint64_t nextSCC = (CFLPreSolveOnce && iteration > 0) ? (1u << 14)
                                                        : (1u << 18);
  uint64_t nextProg = 1u << 20, nextIntern = 1u << 16;
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
      if (internOK && CFLInternSweep && iterations >= nextIntern) {
        nextIntern += 1u << 16;
        const uint64_t u0 = internUnified;
        internPlanes();
        if (internUnified != u0)
          CG_LOG("FlowsTo: intern sweep unified " << (internUnified - u0)
                 << " planes at " << iterations << " pops ("
                 << (internBytesFreed >> 20) << " MB cumulative)\n");
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
    std::fill(virginPl.begin(), virginPl.end(), 0);
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
  // Batch bounds FREEZE at creation (spill headers reference them);
  // root growth appends new batches. hasFile/cursor/touch state
  // persists across resolution passes so spilled fixpoints carry over
  // wiring boundaries (batch spill/restore).
  std::vector<std::pair<uint32_t, uint32_t>> batchBounds;
  std::vector<char> batchHasFile;
  std::vector<size_t> batchCursor; // touch-log length at last save
  size_t touchRoundStart = 0;
  if (CFLBatchRoots && !CFLBatchSpill.empty()) {
    if (auto ec = llvm::sys::fs::create_directories(CFLBatchSpill))
      report_fatal_error("BatchSpill: cannot create spill dir: " +
                         llvm::Twine(ec.message()));
    g_touchTrack = true;
    g_touchLog.clear();
  }
  for (;;) {
  if (CFLBatchRoots == 0) {
  do { // lazy-mint: drain, expand deferred roots, drain again to stability
    drainWaves();
  // At every drain fixpoint, re-admit deferred roots whose classes
  // entered A on the merge-coarsened quotient, then drain the new
  // identity bits; stable A + empty backlog = restricted fixpoint.
  // Channel mode: also materialize pended channels/edges — new edges
  // seed facts, so drain again until neither expands.
  } while (lazyExpand() > 0 || flushChannelPends() > 0);
  } else {
    const uint32_t K = CFLBatchRoots;
    const unsigned P = std::max(1u, (unsigned)CFLBatchWorkers);
    size_t round = 0;
    const bool spillOn = !CFLBatchSpill.empty();
    auto spillPath = [&](uint32_t bi) {
      return CFLBatchSpill + "/b" + std::to_string(bi) + ".pl";
    };
    // Save every rep with any plane content: [blo bhi][nRec] then per
    // record [class][per shift: R-count R-bits RB-count RB-bits],
    // batch-local bits throughout.
    auto savePlanes = [&](uint32_t bi, uint32_t blo, uint32_t bhi) {
      // zstd stream: raw kernel-scale spill is ~8.7GB/batch (fact-mass
      // bound); sorted bit lists compress several-fold and -1 streams
      // faster than the drain produces them. Pipes cannot seek, so the
      // record count is pre-counted.
      FILE *f = popen(("zstd -q -f -1 -o '" + spillPath(bi) + "'").c_str(),
                      "w");
      if (!f)
        report_fatal_error("BatchSpill: cannot start zstd writer");
      auto wr = [&](const void *p, size_t sz, size_t cnt) {
        if (cnt && fwrite(p, sz, cnt, f) != cnt)
          report_fatal_error("BatchSpill: short write");
      };
      uint64_t nRec = 0;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n)
          continue;
        for (uint32_t s = 0; s < NSHIFT; s++)
          if (R[n][s].any() || RB[n][s].any()) {
            nRec++;
            break;
          }
      }
      const uint32_t hdr[2] = {blo, bhi};
      wr(hdr, 4, 2);
      wr(&nRec, 8, 1);
      std::vector<uint32_t> buf;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n)
          continue;
        bool anyP = false;
        for (uint32_t s = 0; s < NSHIFT && !anyP; s++)
          anyP = R[n][s].any() || RB[n][s].any();
        if (!anyP)
          continue;
        wr(&n, 4, 1);
        for (uint32_t s = 0; s < NSHIFT; s++)
          for (int k = 0; k < 2; k++) {
            const FactSet &S2 = k ? RB[n][s] : R[n][s];
            buf.clear();
            S2.forEach([&](uint32_t b) { buf.push_back(b); });
            const uint32_t c = (uint32_t)buf.size();
            wr(&c, 4, 1);
            wr(buf.data(), 4, c);
          }
      }
      const int rc = pclose(f);
      if (rc != 0)
        report_fatal_error("BatchSpill: zstd writer failed");
    };
    // Restore with fold-through-find(): R first (all records), then RB
    // guarded by final R, then quiescence — joined := R∪RB for
    // untouched reps; touched reps get the full re-offer (dirty/jdirty
    // = R∪RB, dirtyBr = R, joined empty) and a worklist push.
    auto restorePlanes = [&](uint32_t bi, uint32_t blo, uint32_t bhi) {
      // STREAMED two-pass restore: buffering a whole batch doubled the
      // fattest kernel batch (~9GB raw) on top of the 43GB floor and
      // blew the address-space cap mid-round-2. Re-decompressing costs
      // seconds; pass A applies R bits (RB blocks skipped), pass B
      // re-reads and applies RB guarded by the final R.
      auto openZ = [&]() {
        FILE *f =
            popen(("zstd -dqc '" + spillPath(bi) + "'").c_str(), "r");
        if (!f)
          report_fatal_error("BatchSpill: cannot start zstd reader");
        return f;
      };
      // Sequential mode gets the EXACT per-batch window [cursor, now):
      // the batch's own pre-save touches are already folded into its
      // file, and they are the majority of a round's log — this is
      // what deflates the round-2 re-offer hump. Worker mode keeps the
      // conservative round window (siblings' touches are not in any
      // one worker's history).
      const boost::unordered_flat_set<uint32_t> *dw = &g_dirtyRestore;
      boost::unordered_flat_set<uint32_t> exactWin;
      if (P <= 1) {
        for (size_t ti = batchCursor[bi]; ti < g_touchLog.size(); ti++)
          exactWin.insert(g_touchLog[ti]);
        dw = &exactWin;
      }
      boost::unordered_flat_set<uint32_t> touched;
      std::vector<uint32_t> repList; // insertion-ordered unique reps
      boost::unordered_flat_set<uint32_t> repSeen;
      std::vector<uint32_t> v;
      for (int pass = 0; pass < 2; pass++) {
        FILE *f = openZ();
        auto rd = [&](void *p, size_t sz, size_t cnt) {
          if (cnt && fread(p, sz, cnt, f) != cnt)
            report_fatal_error("BatchSpill: short read (missing or "
                               "truncated spill file?)");
        };
        uint32_t hdr[2];
        uint64_t nRec = 0;
        rd(hdr, 4, 2);
        if (hdr[0] != blo || hdr[1] != bhi)
          report_fatal_error("BatchSpill: stale spill file (batch "
                             "bounds mismatch — different K or "
                             "leftover dir?)");
        rd(&nRec, 8, 1);
        for (uint64_t i = 0; i < nRec; i++) {
          uint32_t n = 0;
          rd(&n, 4, 1);
          const uint32_t rep = find(n);
          if (pass == 0) {
            if (repSeen.insert(rep).second)
              repList.push_back(rep);
            if (dw->count(n) || dw->count(rep))
              touched.insert(rep);
          }
          for (uint32_t s = 0; s < NSHIFT; s++)
            for (int k = 0; k < 2; k++) {
              uint32_t c = 0;
              rd(&c, 4, 1);
              v.resize(c);
              rd(v.data(), 4, c);
              if (pass == 0 && k == 0)
                for (uint32_t b : v)
                  R[rep][s].set(b);
              else if (pass == 1 && k == 1)
                for (uint32_t b : v)
                  if (!R[rep][s].test(b))
                    RB[rep][s].set(b);
            }
        }
        pclose(f);
      }
      for (uint32_t rep : repList) {
        const bool hot = touched.count(rep) > 0;
        for (uint32_t s = 0; s < NSHIFT; s++) {
          if (R[rep][s].none() && RB[rep][s].none())
            continue;
          if (!hot) {
            joined[rep][s].copyFrom(R[rep][s]);
            joined[rep][s].unionWith(RB[rep][s]);
          } else {
            dirty[rep][s].copyFrom(R[rep][s]);
            dirty[rep][s].unionWith(RB[rep][s]);
            jdirty[rep][s].copyFrom(dirty[rep][s]);
            dirtyBr[rep][s].copyFrom(R[rep][s]);
          }
        }
        if (hot)
          push(rep, ctx0);
      }
    };
    // One batch: release planes, then either seed rids [blo, bhi) as
    // LOCAL bits under a batch-width universe (fresh) or restore the
    // spilled fixpoint and drain only the touch delta.
    auto runBatch = [&](uint32_t bi, uint32_t blo, uint32_t bhi,
                        bool fresh) {
      clearPlanes();
      g_ridBase = blo;
      FactSet::Universe = bhi - blo;
      if (fresh) {
        tHow = "batch-seed"; tFrom = UINT32_MAX;
        for (uint32_t rid = blo; rid < bhi; rid++) {
          const bool exact =
              !nexusGate || (rid < rootNexus.size() && rootNexus[rid]);
          addFact(find(rootClassOf[rid]), exact ? 0 : SHIFT_X, rid - blo,
                  ctx0);
        }
      } else {
        tHow = "batch-restore"; tFrom = UINT32_MAX;
        restorePlanes(bi, blo, bhi);
      }
      flushCtx(ctx0);
      const uint64_t f0 = factCount;
      const size_t m0 = mergeCount;
      drainWaves();
      // Skip-save: an unchanged restore leaves the on-disk fixpoint
      // valid (re-offers that derive nothing move no facts).
      const bool changed =
          fresh || factCount != f0 || mergeCount != m0;
      if (spillOn && changed) {
        savePlanes(bi, blo, bhi);
        batchHasFile[bi] = 1;
        batchCursor[bi] = g_touchLog.size();
      }
      g_ridBase = 0;
      FactSet::Universe = nextRoot;
    };
    // Harvest translation: plane bits are batch-local, answer bits are
    // global rids.
    auto pullPlane = [&](const FactSet &src, FactSet &dst, uint32_t base) {
      src.forEach([&](uint32_t b) { dst.set(b + base); });
    };
    for (;;) {
      const size_t mc0 = mergeCount;
      const uint32_t nR = nextRoot;
      const size_t kc0 = clusterCount();
      // Frozen batch bounds; growth appends new (fresh) batches.
      while ((batchBounds.empty() ? 0u : batchBounds.back().second) < nR) {
        const uint32_t lo =
            batchBounds.empty() ? 0u : batchBounds.back().second;
        batchBounds.push_back({lo, std::min(lo + K, nR)});
        batchHasFile.push_back(0);
        batchCursor.push_back(0);
      }
      const uint32_t nB = (uint32_t)batchBounds.size();
      for (auto &kv : fptrAcc) kv.second.release();
      fptrAcc.clear();
      // Restore window (worker mode): a batch saved during the previous
      // round missed every touch since that round began. Sequential
      // mode uses exact per-batch cursors inside restorePlanes instead.
      if (spillOn) {
        g_dirtyRestore.clear();
        for (size_t ti = touchRoundStart; ti < g_touchLog.size(); ti++)
          g_dirtyRestore.insert(g_touchLog[ti]);
        touchRoundStart = g_touchLog.size();
      }
      if (P > 1) {
        // Process-parallel round (task #41): fork W workers — the graph
        // and quotient arrive copy-on-write, so memory is graph(shared)
        // + W live batch plane-sets. Workers drain single-threaded,
        // record effectual events + harvest bits to scratch files, and
        // _exit without LLVM teardown. The parent replays the streams
        // in worker order: replayed first-inserts recreate keys and VX
        // bridges, cross-worker key collisions become the cross-batch
        // merges, and recorded merges cover SCC collapses.
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
            kaStartRssWatchdog(); // parent's watchdog thread died in fork
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
              const uint32_t blo = batchBounds[bi].first;
              const bool freshB = !spillOn || !batchHasFile[bi];
              runBatch(bi, blo, batchBounds[bi].second, freshB);
              for (uint32_t fc : fptrClsList) {
                const uint32_t rep = find(fc);
                FactSet &acc = hv[fc];
                pullPlane(R[rep][0], acc, blo);
                pullPlane(RB[rep][0], acc, blo);
                if (NB > 0) {
                  pullPlane(R[rep][SHIFT_X], acc, blo);
                  pullPlane(RB[rep][SHIFT_X], acc, blo);
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
        if (spillOn)
          for (uint32_t bi = 0; bi < nB; bi++)
            batchHasFile[bi] = 1; // workers saved (child-side flags died)
        CG_LOG("BatchWorkers: " << W << " workers, " << evReplayed
               << " events replayed\n");
      } else {
      for (uint32_t bi = 0; bi < nB; bi++) {
        const uint32_t blo = batchBounds[bi].first;
        const bool freshB = !spillOn || !batchHasFile[bi];
        runBatch(bi, blo, batchBounds[bi].second, freshB);
        // Harvest under the current quotient; only the stable round's
        // accumulation (no rep movement) is consumed by resolution.
        // Keyed by the STATIC fptr class id so worker-local reps never
        // leak across process boundaries; bits translate local->global.
        for (uint32_t fc : fptrClsList) {
          const uint32_t rep = find(fc);
          FactSet &acc = fptrAcc[fc];
          pullPlane(R[rep][0], acc, blo);
          pullPlane(RB[rep][0], acc, blo);
          if (NB > 0) {
            pullPlane(R[rep][SHIFT_X], acc, blo);
            pullPlane(RB[rep][SHIFT_X], acc, blo);
          }
        }
      }
      } // sequential-batch path
      round++;
      const size_t dm = mergeCount - mc0;
      // Key-insert term (proof-review #5): a single-member key insert
      // is alias-inert (joins need two co-clustered cells) and
      // self-batch-closed (a fact carries its own origin, so only the
      // batch that inserted the key could add its second member — and
      // that batch just closed over it), so dm==0 alone is arguably
      // sufficient. Until that argument is a Lean lemma, stability of
      // the retained WITNESS state — merges, mints, AND cluster keys —
      // is the stop condition, matching batched_exact's hclosed
      // hypothesis trivially.
      const size_t dk =
          dm == 0 ? clusterCount() - kc0 : (size_t)1; // merges shrink count
      CG_LOG("BatchRoots: round " << round << ": " << dm << " new merges, "
             << (nextRoot - nR) << " late mints, "
             << ((nR + K - 1) / K) << " batches"
             << (dm == 0 ? (", " + std::to_string(dk) + " new keys") : "")
             << "\n");
      if (dm == 0 && nextRoot == nR && dk == 0)
        break; // retained witness state stable: harvest is valid
    }
  }
  // --cfl-verify-closure: certify the fixpoint. One full non-delta scan of
  // every rule; any rule that would still fire is a violation. This checks
  // the closure property the delta/backlog machinery must maintain — the
  // Lean SolverModel's central assumption, and the layer where the
  // historical solver bugs (joined-marking, merge cascades) lived.
  // Called at the CONVERGED break only: intermediate drain rounds are
  // legitimately non-final (lazy-mint roots still deferred pre-catch-up),
  // and the certificate is defined over the answer-producing fixpoint.
  auto verifyClosure = [&]() {
    if (!CFLVerifyClosure) return;
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
            // Null-cell join hygiene: joinCluster refuses to key joins
            // for NULL-rooted facts (store-through-null is UB, and the
            // null constant is a universal rendezvous) — mirror it.
            if (o < rootClassOf.size()) {
              const NodeIndex on0 = rootOrig(o);
              if (on0 == NF.getNullPtrNode() || on0 == NF.getNullObjectNode())
                return;
            }
            // Constant data-only globals key no joins either (they hold
            // no pointer and cannot be stored into) — mirror it.
            if (o < rootConstData.size() && rootConstData[o])
              return;
            const uint32_t cr = clusterFind((uint64_t)o * NSHIFT + s);
            if (cr == UINT32_MAX) { report("C4-key", n, s, o); return; }
            uint32_t rep = find(cr);
            for (uint32_t c : cellsOf[n])
              if (find(c) != rep) { report("C4-cell", n, s, o); return; }
          });
        }
      }
    }
    // C6: seed presence — every minted root's seed fact survives in
    // the final planes under its mint policy (exact roots at shift 0,
    // wildcard-minted at SHIFT_X). Discharges SolverClosure.seed for
    // THIS run (proof-review finding #4: C0-C5 checked rule closure
    // only — an empty relation is closed).
    for (uint32_t rid = 0; rid < nextRoot; rid++) {
      // Environment content roots have no seed of their own: they are
      // seeded into the clusters their site keys (C6-env below).
      if (rid < envDepth.size() && envDepth[rid] > 0) continue;
      const uint32_t rep = find(rootClassOf[rid]);
      const uint32_t s0 =
          (nexusGate && !rootNexus[rid]) ? (uint32_t)SHIFT_X : 0u;
      if (!R[rep][s0].test(rid) && !RB[rep][s0].test(rid))
        report("C6-seed", rep, s0, rid);
    }
    // C6-env (--cfl-alloc-origins): every cluster keyed by an environment
    // root holds that root's content root. Checked where content lives
    // in the cluster class (named planes put it in the identity shadow).
    if (CFLAllocOrigins && cellNameOf.empty())
      for (auto &[key, cr] : clusterRep) {
        auto eit = envContentOfKey.find(key);
        if (eit == envContentOfKey.end()) continue;
        const uint32_t c = eit->second, rep = find(cr);
        const uint32_t pl = (nexusGate && !rootNexus[c]) ? (uint32_t)SHIFT_X : 0u;
        if (!R[rep][pl].test(c) && !RB[rep][pl].test(c))
          report("C6-env", rep, pl, c);
      }
    for (auto [u, rid] : unnamedSeeds) {
      const uint32_t rep = find(u);
      const uint32_t s0 =
          (nexusGate && !rootNexus[rid]) ? (uint32_t)SHIFT_X : 0u;
      if (!R[rep][s0].test(rid) && !RB[rep][s0].test(rid))
        report("C6-unnamed-seed", rep, s0, rid);
    }
    // C7: mint coverage — every class satisfying the origin criterion
    // at the FINAL quotient is minted, or is an intentionally pruned
    // bidi-irrelevant origin (tracked in bidiPrunedCls) or a still-
    // deferred lazy root (must be empty after catch-up). Discharges
    // origins_minted per run; both historical violations (July mint
    // bug, lazy-mint deficit) would have fired here.
    {
      boost::unordered_flat_set<uint32_t> pruned(bidiPrunedCls.begin(),
                                                 bidiPrunedCls.end());
      // Adoption-starved formals: the minter refuses these by design
      // (the summary owns the callsite wiring — see the mint loop's
      // starved-formal guard); the coverage criterion must mirror it.
      pruned.insert(starvedCls.begin(), starvedCls.end());
      for (uint32_t n : lazyDeferred) report("C7-lazy", find(n), 0, n);
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n || isRoot[n]) continue;
        // Named shadows never mint: their cell's roots are seeded into
        // them (C6-unnamed-seed).
        if (nameOfCell(n) != ka::AccessNames::Original) continue;
        // --cfl-alloc-origins mints no identity for what is no object.
        if (CFLAllocOrigins && !originBearing(toOrig[n]) &&
            !isEnvKind(identityKindOf(n)))
          continue;
        if ((originBearing(toOrig[n]) || !hasIn[n]) && !pruned.count(n))
          report("C7-mint", n, 0, n);
      }
    }
    if (viol) {
      errs() << "CLOSURE: " << viol << " violations — fixpoint NOT closed\n";
      assert(false && "flows-to fixpoint failed closure verification");
    } else {
      CG_LOG("Closure verified: all rules saturated + seeds present + "
             "mint coverage (0 violations)\n");
    }
  };

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
  if (internOK) {
    uint64_t internHitsTotal = 0, internSharesTotal = 0;
    for (auto &c : ctxs) {
      internHitsTotal += c.internHits;
      internSharesTotal += c.internShares;
    }
    CG_LOG("FlowsTo: intern " << internSweeps << " sweeps, "
           << internUnified << " planes unified, "
           << (internBytesFreed >> 20) << " MB freed, "
           << internSharesTotal << " arrival shares, "
           << internHitsTotal << " fast-path skips\n");
  }

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
  // --cfl-census-type-rej: reverse census of the type filter. For every
  // CFL-derived candidate that isCompatible drops, bucket the FIRST
  // failing check and track per-function accept/reject fates across all
  // deriving sites. A function derived somewhere but rejected at EVERY
  // deriving site lands in no target set at all — that set, crossed with
  // AddressTakenFuncs, is the "data-flow-feasible, type-invisible"
  // inventory (the ordinary-site analogue of the certified static_call
  // +29 pairs). Measurement only: answers are unchanged.
  size_t ctrSitesWithRej = 0, ctrPairsRej = 0, ctrExemplars = 0;
  std::map<std::string, size_t> ctrBuckets;
  boost::unordered_flat_map<const Function *, size_t> ctrRejFn;
  boost::unordered_flat_set<const Function *> ctrAccFn;
  // (rejected-here, CS, derived-here, kept-here) per site with rejections
  std::vector<std::tuple<size_t, const CallBase *, size_t, size_t>> ctrTop;
  auto ctrClassify = [&](const CallBase *CS2,
                         const Function *F2) -> std::string {
    if (F2->isIntrinsic()) return "intrinsic";
    const FunctionType *FTy = F2->getFunctionType();
    unsigned NP = FTy->getNumParams(), NA = CS2->arg_size();
    if (FTy->isVarArg()) {
      if (NA < NP) return "argc-vararg-short";
    } else if (NA != NP) {
      return NA < NP ? "argc-site-fewer" : "argc-site-more";
    }
    if (!CS2->use_empty() && !CS2->getType()->isVoidTy() &&
        !isCompatibleType(F2->getReturnType(), CS2->getType()))
      return "ret-only";
    auto AI = CS2->arg_begin();
    for (unsigned i = 0; i < NP; ++i, ++AI) {
      Type *FT = FTy->getParamType(i), *AT = (*AI)->getType();
      if (isCompatibleType(FT, AT)) continue;
      // ints are all mutually compatible, so are pointers (opaque) —
      // the reachable param mismatches are cross-kind or aggregate.
      if (FT->isPointerTy() && AT->isIntegerTy()) return "param:site-int-fn-ptr";
      if (FT->isIntegerTy() && AT->isPointerTy()) return "param:site-ptr-fn-int";
      if (FT->isStructTy() && AT->isStructTy()) return "param:struct-name";
      if (FT->isFloatingPointTy() || AT->isFloatingPointTy())
        return "param:fp";
      return "param:other";
    }
    // isCompatible said no but every check above passed: the only
    // remaining path is a check-order divergence — surface it loudly.
    return "UNCLASSIFIED";
  };
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

  // ---- per-witness answer read (rung 1, --cfl-witness-answers) ----
  // The pooled solve stays (memory-bearing over-approx); the LAST
  // M-hop is recomputed exactly at load-shaped icall sites from the
  // bipartite key×cell structure: the fptr cell's content =
  // seeds/store-inflow of exactly the cells that SHARE A KEY with it
  // (plus the VX wildcard mirror), not the whole union-find cluster.
  // Sound by construction: every earlier hop uses pooled planes
  // (⊇ truth), source planes are unioned across ALL shifts (⊇ any
  // residue composition), and the result is intersected with the
  // pooled answer bits. Any unresolvable piece falls back to the
  // pooled read for that site. Gate-0 census (km fs13): giant cells'
  // one-hop witness neighborhood is p50 = 0.01% of the cluster.
  struct WitnessRead {
    bool ready = false;
    // cell (fine dense) -> owner pointer class (fine dense)
    boost::unordered_flat_map<uint32_t, uint32_t> cellOwner;
    // owner REP -> fn-bit upper bound of the content of its cells
    // (union over a/f-in source planes, fn bits only, all shifts)
    boost::unordered_flat_map<uint32_t, FactSet> ownerFnUB;
    // owner REP -> all-shift plane union (lazy), for overlap tests
    boost::unordered_flat_map<uint32_t, ka::BitPlane> uCache;
    boost::unordered_flat_map<uint64_t, bool> overlapMemo;
    // src REP -> fn bits of its plane (memo for the content pass)
    boost::unordered_flat_map<uint32_t, FactSet> srcFnMemo;
  } WR;
  size_t g_witnessSites = 0, g_witnessFallback = 0;
  uint64_t g_witnessPooledPairs = 0, g_witnessRefinedPairs = 0;
  if (CFLWitnessAnswers) {
    if (CFLBatchRoots)
      report_fatal_error("--cfl-witness-answers requires a monolithic "
                         "unbatched solve (no --cfl-batch-roots): live "
                         "planes are read directly");
    // cell -> owner from the deref registry (deref nodes were created
    // per pointer node; canonicalize both sides into dense space).
    for (auto &[ptrN, derefN] : NF.getDerefMap()) {
      auto cIt2 = toDense.find(getCanonicalNode(derefN));
      if (cIt2 == toDense.end()) continue;
      auto oIt2 = toDense.find(getCanonicalNode(ptrN));
      if (oIt2 == toDense.end()) continue;
      WR.cellOwner.emplace(cIt2->second, oIt2->second);
    }
    // Content upper bound per owner rep: every a/f-edge into a cell
    // contributes the fn bits of its source's pooled plane — this
    // covers direct fn stores, initializer plants, summary-atom
    // relays AND multi-hop memory copies (the source plane is the
    // pooled ⊇-truth bound for the copied value).
    auto fnbitsOfRep = [&](uint32_t rep2) -> const FactSet & {
      auto pr3 = WR.srcFnMemo.try_emplace(rep2);
      FactSet &slot = pr3.first->second;
      if (pr3.second) {
        auto grab = [&](const FactSet &pl) {
          pl.forEach([&](uint32_t o3) {
            if (funcRootOf.count(o3)) slot.set(o3);
          });
        };
        for (uint32_t s3 = 0; s3 < NSHIFT; s3++) {
          grab(R[rep2][s3]);
          grab(RB[rep2][s3]);
        }
      }
      return slot;
    };
    auto addContent = [&](uint32_t srcFine, uint32_t dstFine) {
      auto co = WR.cellOwner.find(dstFine);
      if (co == WR.cellOwner.end()) return; // not a cell
      const FactSet &fb = fnbitsOfRep(find(srcFine));
      if (fb.none()) return;
      WR.ownerFnUB[find(co->second)].unionWith(fb);
    };
    for (auto [s2, t2] : aEdges) addContent(s2, t2);
    for (auto &[b2, r2, bk2] : fEdges) addContent(b2, r2);
    WR.ready = true;
  }
  auto witnessU = [&](uint32_t rep2) -> const ka::BitPlane & {
    auto pr3 = WR.uCache.try_emplace(rep2, FactSet::Universe);
    ka::BitPlane &u = pr3.first->second;
    if (pr3.second) {
      auto orIn = [&](const FactSet &pl) {
        if (const ka::BitPlane *bp = pl.denseData()) u |= *bp;
        else pl.forEach([&](uint32_t o3) {
          if (o3 < u.size()) u.set(o3);
        });
      };
      for (uint32_t s3 = 0; s3 < NSHIFT; s3++) {
        orIn(R[rep2][s3]);
        orIn(RB[rep2][s3]);
      }
    }
    return u;
  };
  auto witnessOverlap = [&](uint32_t a2, uint32_t b2) -> bool {
    if (a2 == b2) return true;
    if (a2 > b2) std::swap(a2, b2);
    const uint64_t k2 = ((uint64_t)a2 << 32) | b2;
    auto pr3 = WR.overlapMemo.try_emplace(k2, false);
    if (pr3.second) {
      const ka::BitPlane &ua = witnessU(a2), &ub = witnessU(b2);
      const size_t nw = std::min(ua.numWords(), ub.numWords());
      const uint64_t *wa = ua.words(), *wb = ub.words();
      bool hit = false;
      for (size_t i3 = 0; i3 < nw; i3++)
        if (wa[i3] & wb[i3]) { hit = true; break; }
      pr3.first->second = hit;
      return hit;
    }
    return pr3.first->second;
  };
  // Per distinct site-owner set: union of ownerFnUB over overlapping
  // owner reps (the expensive sweep, cached — pool sites share owners).
  if (traceRoot >= 0) {
    // Fixpoint census of the traced root: every class holding it,
    // channels included — locates the frontier where a flow stalls.
    size_t nHold = 0, shown = 0;
    const uint32_t NL2 = (uint32_t)ufp.size();
    for (uint32_t c = 0; c < NL2; c++) {
      if (find(c) != c) continue;
      bool has = false;
      for (uint32_t s3 = 0; s3 < NSHIFT && !has; s3++)
        has = R[c][s3].test((uint32_t)traceRoot) ||
              RB[c][s3].test((uint32_t)traceRoot);
      if (!has) continue;
      nHold++;
      if (shown++ < 20) {
        errs() << "TRACE-HOLD c" << c << " ";
        if (c >= N) {
          errs() << "<channel> outA=" << outA[c].size()
                 << " inWLseen popCount=" << popCount[c];
        } else {
          const Value *HV = NF.getValueForNode(toOrig[c]);
          if (HV && HV->hasName())
            errs() << HV->getName().substr(0, 60);
          else if (HV) {
            if (const auto *HI = dyn_cast<Instruction>(HV))
              errs() << HI->getFunction()->getName().substr(0, 40) << "::"
                     << HI->getOpcodeName();
          } else
            errs() << (NF.isObjectNode(toOrig[c]) ? "<obj>" : "<syn>");
        }
        errs() << "\n";
      }
    }
    errs() << "TRACE-HOLD total classes holding root: " << nHold << "\n";
  }
  boost::unordered_flat_map<uint32_t, FactSet> witnessSiteMemo;
  // --cfl-reachable processes newly reached bodies inside this loop,
  // which adds indirect-call sites; iterate a snapshot (new sites are
  // resolved in the next resolution pass).
  const std::vector<const CallBase *> icallSnapshot(
      Ctx->IndirectCallInsts.begin(), Ctx->IndirectCallInsts.end());
  for (const CallBase *CS : icallSnapshot) {
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
    const size_t ctrSiteC0 = filtCandidates, ctrSiteR0 = filtTypeRej;
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
        if (!V2) {
          auto pit = cls < N ? g_opaqueProvenance.find(toOrig[cls])
                             : g_opaqueProvenance.end();
          return pit != g_opaqueProvenance.end() ? pit->second
                                                 : "<synthetic>";
        }
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
        NodeIndex ocanon = rootOrig(o2);
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
      // Traced runs are diagnostic: print the whole reachable slice
      // (a giant cell cluster's root-carrying predecessor sat past the
      // old 300-node / 200-edge caps and cut the derivation witness).
      for (size_t qi = 0; qi < q.size() && printed < 50000; qi++) {
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
            if (shownE++ > 20000) { errs() << " ..."; break; }
            errs() << " " << e;
            uint32_t src2 = (uint32_t)std::stoul(e.substr(e.find("c") + 1));
            if (vis.insert(src2).second && q.size() < 500000)
              q.push_back(src2);
          }
        errs() << " ]\n";
        printed++;
      }
      // Giant-class membership: for slice classes with huge in-degree,
      // list what dense nodes they absorbed (kind + owning function).
      // Attribution by in-edge SOURCE functions misled once (the
      // byte-swapper story); membership is the ground truth.
      {
        std::vector<uint32_t> giants;
        for (uint32_t v : vis) {
          auto ie = inEdges.find(v);
          if (ie != inEdges.end() && ie->second.size() > 1000)
            giants.push_back(v);
        }
        for (uint32_t g : giants) {
          size_t mem = 0;
          std::map<std::string, size_t> kinds, funcs;
          for (uint32_t n2 = 0; n2 < N; n2++) {
            if (find(n2) != g) continue;
            mem++;
            const Value *MV = NF.getValueForNode(toOrig[n2]);
            std::string kind = "<syn>";
            if (MV) {
              if (isa<Argument>(MV)) {
                kind = "formal";
                funcs[cast<Argument>(MV)->getParent()->getName().str()]++;
              } else if (const auto *MI = dyn_cast<Instruction>(MV)) {
                kind = std::string("inst:") + MI->getOpcodeName();
                funcs[MI->getFunction()->getName().str()]++;
              } else if (isa<Function>(MV)) kind = "function";
              else if (isa<GlobalVariable>(MV)) kind = "global";
              else kind = "const";
            } else if (NF.isObjectNode(toOrig[n2])) kind = "<obj>";
            kinds[kind]++;
          }
          errs() << "TRACE-BWD   giant c" << g << " members=" << mem
                 << " kinds:";
          for (auto &[k, c] : kinds) errs() << " " << k << "=" << c;
          errs() << "\n";
          std::vector<std::pair<size_t, std::string>> top;
          for (auto &[f, c] : funcs) top.emplace_back(c, f);
          std::sort(top.rbegin(), top.rend());
          errs() << "TRACE-BWD   giant c" << g << " functions=" << funcs.size()
                 << " top:";
          for (size_t i = 0; i < top.size() && i < 12; i++)
            errs() << " " << top[i].second.substr(0, 40) << "(" << top[i].first
                   << ")";
          errs() << "\n";
        }
      }
      // Which (origin, shift) channels coalesced into the clusters this
      // slice reads: cluster keys anchored anywhere in the visited set.
      // One rep carrying keys at MANY shifts = cross-residue coalescence.
      size_t keyShown = 0;
      for (auto &[key2, crep2] : clusterRep) {
        if (!vis.count(find(crep2))) continue;
        if (keyShown++ > 400) { errs() << "TRACE-BWD   ...more keys\n"; break; }
        uint32_t o2 = (uint32_t)(key2 / NSHIFT), s2 = (uint32_t)(key2 % NSHIFT);
        errs() << "TRACE-BWD   slice-key c" << find(crep2) << " <- (r" << o2
               << " " << nameOfClass(rootClassOf[o2]).substr(0, 50) << ", s"
               << s2 << ")\n";
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
    auto collect = [&](const FactSet &plane, const char *planeTag) {
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
        if (!isCompatible(CS, F)) {
          filtTypeRej++;
          if (CFLCensusTypeRej) {
            ctrPairsRej++;
            ctrRejFn[F]++;
            std::string bk = ctrClassify(CS, F);
            ctrBuckets[bk]++;
            if (ctrExemplars < 40) {
              ctrExemplars++;
              errs() << "CENSUS-TYPEREJ [" << bk << "] "
                     << CS->getFunction()->getName() << " :: " << *CS
                     << " -/-> " << F->getName() << "\n";
            }
          }
          return;
        }
        if (CFLCensusTypeRej) ctrAccFn.insert(F);
        // FIELD FILTER RETIRED FROM THE ANSWER PATH (2026-08-11):
        // rejection soundness required a complete inventory of every
        // store key AND every field-to-field copy path a fn pointer
        // can take — alias analysis by syntax, undischargeable. It was
        // OBSERVED rejecting dynamically-true, graph-derived pairs
        // (GT process_one_work family: the worker->current_func cache
        // made it reject every WELL-TYPED work fn while passing
        // exactly the fns whose stores it failed to classify). Field
        // precision must come from provable structure: in-graph field
        // sensitivity (residue planes) and certified identity
        // channels. filtFieldRej now only counts what the retired
        // filter WOULD have rejected — exposure meter, answers
        // untouched.
        if (hasKey && !fieldFilterAccepts(F, csStruct, csField)) {
          filtFieldRej++;
          // Retired-filter vs fs census: a would-be rejection of an
          // EXACT-plane fact under NB>0 is the retired filter
          // contradicting the sound field-sensitive analysis — the
          // adjudication inventory justifying retirement (exact-plane
          // admission is not proof of true flow: mod-P residues can
          // collide; X-plane carries no field claim either way).
          if (CFLCensusTypeRej) {
            // Uncapped under the census flag: ranking WHERE the retired
            // filter used to trim (per-key/caller/target attribution)
            // needs the full stream, not a prefix sample. CLASS
            // decomposes the trim against the filter's own inventory:
            // XFIELD = target stored elsewhere in the SAME struct (FI
            // cross-field smear — fs residue planes address this
            // class in-graph); XSTRUCT = target stored only in OTHER
            // structs (pooled-origin/hub leakage — channels/rodata
            // territory). HOMES = up to 3 of the target's real store
            // keys.
            static size_t g_fieldRejExemplars = 0;
            if (g_fieldRejExemplars++ < 5000000) {
              const Function *canonF = F;
              auto itDef = Ctx->Funcs.find(F->getGUID());
              if (itDef != Ctx->Funcs.end())
                canonF = itDef->second;
              const char *cls = "XSTRUCT";
              std::string homes;
              auto fsIt = funcFieldStores.find(canonF);
              if (fsIt != funcFieldStores.end()) {
                int shown = 0;
                for (const auto &k : fsIt->second) {
                  if (k.first == csStruct)
                    cls = "XFIELD";
                  if (shown < 3) {
                    homes += ' ';
                    homes += k.first;
                    homes += '+';
                    homes += std::to_string(k.second);
                    shown++;
                  }
                }
              }
              errs() << "CENSUS-FIELDREJ(" << planeTag << ") [" << csStruct
                     << "+" << csField << "] "
                     << CS->getFunction()->getName() << " -/-> "
                     << F->getName() << " CLASS=" << cls << " HOMES:"
                     << homes << "\n";
            }
          }
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
    bool witnessOwned = false;
    if (CFLWitnessAnswers && WR.ready && !tpModelOwned && !sctModelOwned) {
      // IR-walk the called operand down to load cells (casts/phi/select
      // transparent; null/undef contribute nothing; anything else =
      // unrefinable site -> pooled fallback).
      SmallVector<uint32_t, 4> cells;
      bool refinable = true;
      {
        SmallVector<const Value *, 8> wl{CS->getCalledOperand()};
        SmallPtrSet<const Value *, 16> seen;
        unsigned steps = 0;
        while (!wl.empty() && refinable) {
          const Value *v = wl.pop_back_val()->stripPointerCasts();
          if (!seen.insert(v).second) continue;
          if (++steps > 32) { refinable = false; break; }
          if (const auto *LI = dyn_cast<LoadInst>(v)) {
            // Site owner = the LOAD POINTER's value class: its plane
            // is the exact key set of the loaded cell.
            NodeIndex pn = NF.getValueNodeFor(LI->getPointerOperand());
            if (pn == AndersNodeFactory::InvalidIndex) { refinable = false; break; }
            auto oIt2 = toDense.find(getCanonicalNode(pn));
            if (oIt2 == toDense.end()) { refinable = false; break; }
            cells.push_back(find(oIt2->second)); // owner rep, not cell
          } else if (const auto *PN = dyn_cast<PHINode>(v)) {
            for (const Value *iv : PN->incoming_values()) wl.push_back(iv);
          } else if (const auto *SEL = dyn_cast<SelectInst>(v)) {
            wl.push_back(SEL->getTrueValue());
            wl.push_back(SEL->getFalseValue());
          } else if (isa<ConstantPointerNull>(v) || isa<UndefValue>(v)) {
            // contributes nothing
          } else {
            refinable = false;
          }
        }
      }
      if (!refinable || cells.empty()) {
        g_witnessFallback++;
      } else {
        witnessOwned = true;
        g_witnessSites++;
        // refined UB = ∪ ownerFnUB[r] over owner reps r whose all-shift
        // plane overlaps ANY site owner's plane (shared key = the
        // grammar's V-witness; any-shift union ⊇ the exact shift
        // pairing — sound, and the pooled intersection below re-trims).
        FactSet refinedUB;
        for (uint32_t so : cells) {
          auto [mIt, mIns] = witnessSiteMemo.try_emplace(so);
          if (mIns) {
            for (auto &kv2 : WR.ownerFnUB)
              if (witnessOverlap(so, kv2.first))
                mIt->second.unionWith(kv2.second);
          }
          refinedUB.unionWith(mIt->second);
        }
        FactSet wf;
        size_t pooledFn = 0;
        auto pooledHas = [&](uint32_t o2) {
          return R[rep][0].test(o2) || RB[rep][0].test(o2) ||
                 (NB > 0 && (R[rep][SHIFT_X].test(o2) ||
                             RB[rep][SHIFT_X].test(o2)));
        };
        for (auto &[rid2, F2] : funcRootOf) {
          if (!pooledHas(rid2)) continue;
          pooledFn++;
          if (refinedUB.test(rid2)) wf.set(rid2);
        }
        g_witnessPooledPairs += pooledFn;
        g_witnessRefinedPairs += wf.count();
        if (!CFLTraceFunc.empty() &&
            CS->getFunction()->getName().contains(CFLTraceFunc)) {
          errs() << "WTRACE site in " << CS->getFunction()->getName()
                 << ": owners=" << cells.size() << " pooledFn=" << pooledFn
                 << " refined=" << wf.count() << "\n";
          for (auto &[rid2, F2] : funcRootOf) {
            if (!pooledHas(rid2) || refinedUB.test(rid2)) continue;
            errs() << "WTRACE   MISSING " << F2->getName() << " (r" << rid2
                   << ")\n";
          }
        }
        collect(wf, "witness");
      }
    }
    if (!witnessOwned && !tpModelOwned && !sctModelOwned && CFLBatchRoots) {
      // Batched mode: live planes hold only the last batch — read the
      // stable round's accumulated answer bits (static-id keyed).
      auto aIt = fptrAcc.find(dIt->second);
      if (aIt != fptrAcc.end())
        collect(aIt->second, "batch-acc");
    }
    if (!witnessOwned && !tpModelOwned && !sctModelOwned && !CFLBatchRoots) {
      collect(R[rep][0], NB > 0 ? "exact" : "fi");
      collect(RB[rep][0], NB > 0 ? "exact" : "fi");
    }
    const size_t exactTargets = targets.size();
    if (!witnessOwned && !tpModelOwned && !sctModelOwned && !CFLBatchRoots &&
        NB > 0) {
      collect(R[rep][SHIFT_X], "X");
      collect(RB[rep][SHIFT_X], "X");
    }
    topOnlyPairs += targets.size() - exactTargets;
    if (CFLCensusTypeRej && filtTypeRej > ctrSiteR0) {
      ctrSitesWithRej++;
      ctrTop.push_back({filtTypeRej - ctrSiteR0, CS,
                        filtCandidates - ctrSiteC0, targets.size()});
    }
    if (!targets.empty()) { resolved++; totalTargets += targets.size(); }
    for (const Function *F : targets) {
      if (!Ctx->Callees[CS].insert(F).second)
        continue; // wired in an earlier iteration
      newPairs++;
      // Wire the callee's flows exactly as the saturation fixpoint does;
      // the new edges enter the NEXT iteration's solve.
      Function *CF = const_cast<Function *>(F);
      reachFunction(CF); // --cfl-reachable: body (and its callees) first
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
        NodeIndex heapObj = NF.createOpaqueObjectNode(CS, true);
        Graph.addDeref(callNode, heapObj);
        auto sit = Ctx->FuncSummaries.find(CF);
        if (sit != Ctx->FuncSummaries.end() &&
            applySummaryAtoms(CS, *sit->second, nullptr, sit->first))
          wireCallArgs(CS, CF); // dynamic-fn INVOKE: feed the body pool
      } else if (Ctx->ContainerFuncs.count(CF)) {
        handleContainerCall(CS, CF);
      } else {
        handleCall(CS, CF);
      }
    }
  }
  if (NB > 0 && g_tagRoundTrips)
    CG_LOG("TagRoundTrip: " << g_tagRoundTrips
           << " ptrtoint wildcards suppressed (tag-bit-only closures)\n");
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
            const Value *ov3 = rootValue(rid3);
            const llvm::Module *om3 = nullptr;
            std::string on3 = "<synthetic>";
            if (!ov3) {
              auto pit3 =
                  g_opaqueProvenance.find(rootOrig(rid3));
              if (pit3 != g_opaqueProvenance.end()) on3 = pit3->second;
            }
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
          const Value *ov3 = rootValue(o3);
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
    // Q1 estimator: FINAL partition = the realized bidirected
    // quotient; Sigma|C|^2 here is the saturation V-mass per plane.
    {
      std::vector<uint64_t> szs;
      for (uint32_t n2 = 0; n2 < N; n2++)
        if (find(n2) == n2)
          szs.push_back(clsSize[n2]);
      cflDumpClassHist("FINAL", szs);
    }
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
    // Growth spine: in event order, print every lineage merge whose
    // result beats the largest lineage class seen so far by 25% (the
    // "record" merges), plus every merge with both sides >= 64. With
    // the full log this starts at the giant's first two-member merge.
    uint64_t record = 0;
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
      const uint64_t after = (uint64_t)ev.szA + ev.szB;
      const bool isRecord = after * 4 > record * 5;
      if (isRecord) record = after;
      if (shown < 300 && (isRecord || std::min(ev.szA, ev.szB) >= 64)) {
        shown++;
        errs() << "BlobForm: EV#" << giantEvents << " @" << ev.at << " "
               << ev.ctx << (ev.origin.empty() ? "" : (" origin=" + ev.origin))
               << " " << ev.szA << "<" << ev.nA.substr(0, 60) << "> + "
               << ev.szB << "<" << ev.nB.substr(0, 60) << ">"
               << (isRecord ? " =" + std::to_string(after) : "") << "\n";
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
  CG_LOG("FlowsTo: resolved " << resolved << " icalls, "
         << totalTargets << " targets (" << newPairs << " new pairs wired, "
         << topOnlyPairs << " via wildcard plane only), iteration "
         << (iteration + fpIter) << "\n");
  reachLedger();
  if (CFLWitnessAnswers)
    CG_LOG("WitnessAnswers: " << g_witnessSites << " sites refined ("
           << g_witnessFallback << " pooled fallbacks); fn-plane pairs "
           << g_witnessPooledPairs << " pooled -> " << g_witnessRefinedPairs
           << " per-witness\n");
  CG_LOG("FilterStats: " << filtCandidates << " CFL candidates, "
         << filtTypeRej << " type-rejected (unsoundness exposure; zero = "
         << "filter retirable), " << filtFieldRej
         << " field-flagged (filter RETIRED 2026-08-11 — count is what it "
         << "would have rejected; answers untouched)\n");
  if (CFLCensusTypeRej) {
    errs() << "=== CENSUS-TYPEREJ: reverse type-filter census ===\n";
    errs() << "CENSUS-TYPEREJ sites-with-rejections " << ctrSitesWithRej
           << " / " << Ctx->IndirectCallInsts.size() << " icalls, "
           << ctrPairsRej << " pairs rejected, " << ctrRejFn.size()
           << " distinct functions rejected somewhere, " << ctrAccFn.size()
           << " distinct functions type-accepted somewhere\n";
    for (auto &b : ctrBuckets)
      errs() << "CENSUS-TYPEREJ bucket " << b.first << " " << b.second
             << "\n";
    // Fate cross: derived by CFL somewhere yet type-rejected at EVERY
    // deriving site => in no target set via the graph. Split by whether
    // the function is address-taken (it should be, to have a root at
    // all) and report the inventory for manual review.
    std::vector<std::pair<size_t, const Function *>> ctrNever;
    for (auto &p : ctrRejFn)
      if (!ctrAccFn.count(p.first))
        ctrNever.push_back({p.second, p.first});
    std::sort(ctrNever.begin(), ctrNever.end(),
              [](auto &a, auto &b) { return a.first > b.first; });
    errs() << "CENSUS-TYPEREJ always-rejected fns " << ctrNever.size()
           << " (CFL-derived somewhere, type-rejected at every deriving "
           << "site — candidate missing targets)\n";
    // Acceptance via a model-owned channel (tpkeys/sct) bypasses
    // collect(), so cross against the ACTUAL answer map: a fn already
    // reached through an identity channel is modeled, not missing.
    boost::unordered_flat_set<const Function *> ctrAnswered;
    for (auto &ce : Ctx->Callees)
      ctrAnswered.insert(ce.second.begin(), ce.second.end());
    size_t ctrNeverModeled = 0, ctrNeverAbsent = 0, shown = 0;
    for (auto &p : ctrNever) {
      bool inAns = ctrAnswered.count(
          getFuncDef(const_cast<Function *>(p.second)));
      (inAns ? ctrNeverModeled : ctrNeverAbsent)++;
      if (shown >= 400) continue;
      shown++;
      errs() << "CENSUS-TYPEREJ   always-rej " << p.second->getName()
             << " x" << p.first << " ["
             << (Ctx->AddressTakenFuncs.count(
                    getFuncDef(const_cast<Function *>(p.second)))
                     ? "addr-taken"
                     : "NOT-addr-taken")
             << (inAns ? "|in-answer(modeled)" : "|ABSENT-from-answer")
             << "]\n";
    }
    if (shown < ctrNever.size()) errs() << "CENSUS-TYPEREJ   ...\n";
    errs() << "CENSUS-TYPEREJ always-rejected fate: " << ctrNeverModeled
           << " reached via model channels, " << ctrNeverAbsent
           << " ABSENT from the whole answer set\n";
    std::sort(ctrTop.begin(), ctrTop.end(),
              [](auto &a, auto &b) { return std::get<0>(a) > std::get<0>(b); });
    shown = 0;
    for (auto &t : ctrTop) {
      if (shown++ >= 20) break;
      const CallBase *CS2 = std::get<1>(t);
      errs() << "CENSUS-TYPEREJ   top-site " << std::get<0>(t) << " rej / "
             << std::get<2>(t) << " derived / " << std::get<3>(t)
             << " kept at " << CS2->getFunction()->getName() << " :: "
             << *CS2 << "\n";
    }
  }
  // Named cells: copies relay name by name (fileUnnamedWrite). A copy's
  // source holds name n when its cell's class has a shadow of name n;
  // wire shadow(src, n) -> shadow(dst, n) for each such name not yet
  // wired. The edges enter the next iteration's solve, like new callee
  // pairs; names only grow, so the outer fixpoint is reached when none
  // is new.
  size_t newCopyNames = 0, copiesInClass = 0;
  if (!cellNameOf.empty() && namedOpenEpoch != namedOpenEpoch0) {
    // Resolution wiring opened names: their loads read the unnamed
    // shadow from the next solve on.
    CG_LOG("NamedCells: " << (namedOpenEpoch - namedOpenEpoch0)
           << " names opened by resolution wiring\n");
    newCopyNames++;
  }
  if (!cellNameOf.empty()) {
    for (size_t ci = 0; ci < cellCopies.size(); ci++) {
      const auto [src, dst] = cellCopies[ci];
      auto d = toDense.find(getCanonicalNode(src));
      if (d == toDense.end()) continue; // cell not in this graph
      // A copy inside one class moves each plane onto itself: nothing to
      // relay. Classes only merge as iterations add edges, so it stays so.
      auto dd = toDense.find(getCanonicalNode(dst));
      if (dd != toDense.end() && find(dd->second) == find(d->second)) {
        copiesInClass++;
        continue;
      }
      for (auto [nm, u] : satOf[find(d->second)])
        if (nm >= ka::AccessNames::FirstName &&
            cellCopyNamed.insert(((uint64_t)ci << 32) | nm).second) {
          Graph.addCopy(namedShadow(src, nm), namedShadow(dst, nm));
          newCopyNames++;
        }
    }
    CG_LOG("NamedCells: " << newCopyNames
           << " new name relays across cell-to-cell copies ("
           << copiesInClass << " copies inside one class)\n");
  }
  if (newPairs == 0 && newCopyNames == 0) {
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
    wideningReport();
    verifyClosure(); // certificate over the answer-producing fixpoint
    if (CFLAllocOrigins) {
      // Reads that found nothing at convergence: a pointer load whose
      // class holds no fact. Under rule (a) each is unreachable, behind
      // a pointer that never resolved, or of a field never written.
      size_t emptyLoads = 0, loads = 0;
      std::map<std::string, size_t> byFn;
      std::vector<NodeIndex> members;
      for (uint32_t n = 0; n < N; n++) {
        const uint32_t c = find(n);
        bool any = false;
        for (uint32_t s2 = 0; s2 < NSHIFT && !any; s2++)
          any = R[c][s2].any() || RB[c][s2].any();
        collectCanonicalMembers(toOrig[n], members);
        if (members.empty()) members.push_back(toOrig[n]);
        for (NodeIndex m : members) {
          const auto *LI = dyn_cast_or_null<LoadInst>(NF.getValueForNode(m));
          if (!LI || !LI->getType()->isPointerTy() || NF.isDereferenceNode(m))
            continue;
          loads++;
          if (any) continue;
          emptyLoads++;
          byFn[LI->getFunction()->getName().str()]++;
        }
      }
      std::vector<std::pair<size_t, std::string>> top;
      for (auto &[f, k] : byFn) top.emplace_back(k, f);
      std::sort(top.rbegin(), top.rend());
      std::string line;
      for (size_t i = 0; i < top.size() && i < 8; i++)
        line += " " + top[i].second + " " + std::to_string(top[i].first);
      CG_LOG("AllocOrigins: " << emptyLoads << " of " << loads
             << " pointer loads read nothing at convergence; "
             << envContentSeeded << " environment-content seeds, "
             << envContentMinted << " content roots (depth "
             << CFLEnvDepth << "); top:"
             << line << "\n");
    }
    if (CFLCensusTypeLabels && !cellNameOf.empty())
      runTypeLabelCensus(
          [&](NodeIndex canon, std::vector<uint32_t> &out) {
            out.clear();
            auto d = toDense.find(canon);
            if (d == toDense.end()) return;
            const uint32_t c = find(d->second);
            for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
              auto add = [&](uint32_t r) {
                if (!funcRootOf.count(r)) out.push_back(r);
              };
              R[c][s2].forEach(add);
              RB[c][s2].forEach(add);
            }
            std::sort(out.begin(), out.end());
            out.erase(std::unique(out.begin(), out.end()), out.end());
          },
          [&](uint32_t rid, std::vector<const Value *> &out) {
            out.clear();
            std::vector<NodeIndex> members;
            const NodeIndex rn = rootOrig(rid);
            if (rn == AndersNodeFactory::InvalidIndex) return;
            collectCanonicalMembers(rn, members);
            for (NodeIndex m : members)
              if (const Value *V = NF.getValueForNode(m)) out.push_back(V);
          });
    // Named cells, measurement only: at an icall whose callee is loaded
    // through a name, the functions its name's plane holds and those
    // only the unnamed plane adds — what assuming that no unnamed write
    // reaches a named field (the field tables' blind spot) would remove.
    if (VerboseLevel >= 2) {
      // Fact mass by class size (log2 buckets of a class's fact count):
      // where a solve's facts live.
      uint64_t bn[64] = {0}, bm[64] = {0};
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n) continue;
        uint64_t f = 0;
        for (uint32_t s2 = 0; s2 < NSHIFT; s2++)
          f += R[n][s2].count() + RB[n][s2].count();
        if (!f) continue;
        const unsigned b = 63 - __builtin_clzll(f);
        bn[b]++;
        bm[b] += f;
      }
      for (unsigned b = 0; b < 64; b++)
        if (bn[b])
          CG_LOG("FactHist: facts 2^" << b << ": " << bn[b] << " classes, "
                 << bm[b] << " facts\n");
    }
    if (!cellNameOf.empty() && VerboseLevel >= 2) {
      // Where the facts are: shadow classes (by plane kind) vs the rest.
      uint64_t fShadowName = 0, fShadowU = 0, fShadowId = 0, fOther = 0;
      size_t cShadow = 0, cOther = 0;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n) continue;
        uint64_t f = 0;
        for (uint32_t s2 = 0; s2 < NSHIFT; s2++)
          f += R[n][s2].count() + RB[n][s2].count();
        const uint32_t nm = nameOfCell(n);
        if (nm == ka::AccessNames::Original) { fOther += f; cOther++; continue; }
        cShadow++;
        (nm == ka::AccessNames::Unnamed ? fShadowU
         : nm == ka::AccessNames::Identity ? fShadowId : fShadowName) += f;
      }
      CG_LOG("NamedCells: facts in " << cShadow << " shadow classes: names "
             << fShadowName << ", unnamed " << fShadowU << ", identity "
             << fShadowId << "; in " << cOther << " other classes: " << fOther
             << "\n");
      size_t sites = 0, namedFns = 0, unnamedOnly = 0;
      std::vector<std::tuple<size_t, size_t, const CallBase *>> top;
      auto fnsOf = [&](NodeIndex sh, FactSet &out) {
        auto d = toDense.find(sh);
        if (d == toDense.end()) return;
        const uint32_t c = find(d->second);
        for (uint32_t s2 = 0; s2 < NSHIFT; s2++) {
          out.unionWith(R[c][s2]);
          out.unionWith(RB[c][s2]);
        }
      };
      for (const CallBase *CS2 : Ctx->IndirectCallInsts) {
        const auto *LI = dyn_cast<LoadInst>(
            CS2->getCalledOperand()->stripPointerCasts());
        if (!LI) continue;
        NodeIndex v = getRepNodeForValue(LI);
        auto it = namedLoadCells.find(v);
        if (it == namedLoadCells.end()) continue;
        const NodeIndex cell = it->second;
        const uint32_t nm = accessNames->ofMemAccess(
            *LI, LI->getPointerOperand(),
            LI->getModule()->getDataLayout().getTypeStoreSize(LI->getType()),
            LI->getModule()->getDataLayout());
        if (!shadowOf.count((uint64_t)cell << 32 | nm)) continue;
        FactSet named, unnamed;
        fnsOf(shadowOf.at((uint64_t)cell << 32 | nm), named);
        if (auto uit = shadowOf.find((uint64_t)cell << 32 | ka::AccessNames::Unnamed);
            uit != shadowOf.end())
          fnsOf(uit->second, unnamed);
        size_t nf = 0, uf = 0;
        for (auto &[rid2, F2] : funcRootOf) {
          if (named.test(rid2)) nf++;
          else if (unnamed.test(rid2)) uf++;
        }
        sites++; namedFns += nf; unnamedOnly += uf;
        top.emplace_back(uf, nf, CS2);
      }
      std::sort(top.begin(), top.end(), [](auto &a, auto &b) {
        return std::get<0>(a) > std::get<0>(b);
      });
      CG_LOG("NamedCells: " << sites << " icalls load their callee through "
             "a name: " << namedFns << " targets in the name's plane, "
             << unnamedOnly << " more only through the unnamed plane\n");
      for (size_t i = 0; i < top.size() && i < 10; i++) {
        const CallBase *CS2 = std::get<2>(top[i]);
        std::string loc = "?";
        if (const DILocation *DL2 = CS2->getDebugLoc())
          loc = (DL2->getFilename() + ":" + Twine(DL2->getLine())).str();
        CG_LOG("NamedCells:   " << loc << " in "
               << CS2->getFunction()->getName() << ": name "
               << std::get<1>(top[i]) << ", unnamed-only "
               << std::get<0>(top[i]) << "\n");
      }
    }
    break; // converged: no callee flows were added
  }
  if (iteration + fpIter + 1 >= (int)CFLFlowsToMaxIters) {
    wideningReport();
    // A cap that fires before a no-change round is an unsound result,
    // not a warning condition (proof-review #7 / R2): refuse it unless
    // the user explicitly accepted capped output.
    if (!CFLIterCapOk) {
      errs() << "ERROR: FlowsTo fixpoint hit iteration cap ("
             << CFLFlowsToMaxIters.getValue() << ") with " << newPairs
             << " newly wired pairs and " << newCopyNames
             << " name relays unprocessed — result would be "
             << "unsound. Raise --cfl-flows-to-max-iters, or pass "
             << "--cfl-iter-cap-ok to accept UNSOUND capped output.\n";
      exit(1);
    }
    WARNING("[UNSOUND-RISK] FlowsTo fixpoint hit iteration cap ("
            << CFLFlowsToMaxIters.getValue() << ") with " << newPairs
            << " newly wired pairs unprocessed; results may miss flows "
            << "through those callees (--cfl-iter-cap-ok accepted)\n");
    break;
  }
  return true; // driver rebuilds and re-solves each resolution iteration
  } // outer resolution fixpoint

  // Reduce per-thread counters into the reporting totals.
  uint64_t cyJoin = 0, cyBridge = 0, cyScan = 0, cyW = 0, cyA = 0, cyF = 0;
  uint64_t nJoinLk = 0, nAOr = 0, nFOr = 0, orWords = 0, cellSkips = 0,
           wordSkips = 0, wordsScanned = 0, wordsNzSrc = 0, wordsNzNb = 0;
  for (auto &c : ctxs) {
    cyJoin += c.cyJoin; cyBridge += c.cyBridge; cyScan += c.cyScan;
    cyW += c.cyW; cyA += c.cyA; cyF += c.cyF;
    nJoinLk += c.nJoinLk; nAOr += c.nAOr; nFOr += c.nFOr;
    orWords += c.orWords;
    sweepOffered += c.sweepOffered;
    sweepKept += c.sweepKept;
    cellSkips += c.cellSkips;
    wordSkips += c.wordSkips;
    wordsScanned += c.wordsScanned;
    wordsNzSrc += c.wordsNzSrc;
    wordsNzNb += c.wordsNzNb;
  }
  if (prof) {
    const uint64_t cyTot = cyJoin + cyBridge + cyScan + cyW + cyA + cyF;
    auto pct = [&](uint64_t c) { return cyTot ? (double)c * 100.0 / cyTot : 0.0; };
    errs() << "SolverProf: total " << cyTot << " cycles in pop loop\n";
    errs() << "SolverProf: join   " << cyJoin << " (" << pct(cyJoin)
           << "%), lookups " << nJoinLk << ", cluster-mark skips "
           << cellSkips << ", whole-cell subset skips " << wordSkips
           << " (seq sub-phase " << seqJoinCy
           << ", merge " << cyMerge << " cycles)\n";
    errs() << "SolverProf: bridge " << cyBridge << " (" << pct(cyBridge) << "%)\n";
    errs() << "SolverProf: scan   " << cyScan << " (" << pct(cyScan) << "%)\n";
    errs() << "SolverProf: wflag  " << cyW << " (" << pct(cyW) << "%)\n";
    errs() << "SolverProf: a-prop " << cyA << " (" << pct(cyA)
           << "%), ORs " << nAOr << "\n";
    errs() << "SolverProf: f-prop " << cyF << " (" << pct(cyF)
           << "%), ORs " << nFOr << ", a-plane words " << orWords << "\n";
    if (wordsScanned)
      errs() << "SolverProf: occupancy — addBits src words " << wordsScanned
             << ", nonzero " << wordsNzSrc << " ("
             << (100.0 * wordsNzSrc / wordsScanned) << "%), delta nonzero "
             << wordsNzNb << " (" << (100.0 * wordsNzNb / wordsScanned)
             << "%)\n";
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
    // Mix census: of the classes that hold a function-pointer fact, how
    // many also point to something a function pointer can never
    // legitimately share a value with — a string literal, a heap object,
    // a stack object, a data global, an identity root. This is the
    // "what remains" inventory for the cell-model change: every such
    // class is a value where the analysis believes one pointer may be
    // a function or a byte buffer.
    if (!CFLDumpMerges.empty()) {
      // Node-name table (canonical name + presolve-class member aliases)
      // then every union of this solve in order, with its cause.
      std::error_code EC;
      raw_fd_ostream OS(CFLDumpMerges, EC, sys::fs::OF_Text);
      if (EC) {
        errs() << "FATAL: cannot write " << CFLDumpMerges << ": "
               << EC.message() << "\n";
        exit(1);
      }
      for (uint32_t d = 0; d < (uint32_t)toOrig.size(); d++) {
        const std::string n = protBlameName(d);
        if (!n.empty()) OS << "N\t" << d << "\t" << n << "\n";
        auto mit = canonicalClassMembers.find(toOrig[d]);
        if (mit != canonicalClassMembers.end())
          for (NodeIndex m2 : mit->second) {
            const std::string an = nodeNameOf(m2);
            if (!an.empty() && an != n) OS << "A\t" << d << "\t" << an << "\n";
          }
      }
      for (auto &[cn, cname] : chanNodeName) OS << "N\t" << cn << "\t" << cname << "\n";
      // T lines: the static type of a cell (what its owner pointer's
      // instruction says it dereferences): a GEP's source struct and
      // field, an alloca's type, a global's type. Untyped owners (formals,
      // loads, call results, casts) get no line. Lets a replay find the
      // first union that fused cells of two different struct types.
      {
        boost::unordered_flat_map<NodeIndex, NodeIndex> ownerOf;
        for (auto &[ptr, cell] : NF.getDerefMap()) ownerOf[cell] = ptr;
        auto tyName = [&](Type *T) -> std::string {
          std::string s2; raw_string_ostream os(s2); T->print(os); return os.str();
        };
        for (uint32_t d = 0; d < (uint32_t)toOrig.size(); d++) {
          const NodeIndex canon = toOrig[d];
          if (!NF.isDereferenceNode(canon)) continue;
          auto oit = ownerOf.find(canon);
          if (oit == ownerOf.end()) continue;
          const Value *V = NF.getValueForNode(oit->second);
          if (!V) continue;
          std::string ty;
          if (const auto *G = dyn_cast<GetElementPtrInst>(V)) {
            ty = tyName(G->getSourceElementType());
            if (G->getNumIndices() >= 2)
              if (const auto *CI = dyn_cast<ConstantInt>(G->getOperand(2)))
                ty += " field " + std::to_string(CI->getZExtValue());
          } else if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
            if (CE->getOpcode() == Instruction::GetElementPtr) {
              ty = tyName(cast<GEPOperator>(CE)->getSourceElementType());
              if (CE->getNumOperands() >= 3)
                if (const auto *CI = dyn_cast<ConstantInt>(CE->getOperand(2)))
                  ty += " field " + std::to_string(CI->getZExtValue());
            }
          } else if (const auto *A = dyn_cast<AllocaInst>(V)) {
            ty = tyName(A->getAllocatedType());
          } else if (const auto *GV = dyn_cast<GlobalVariable>(V)) {
            ty = tyName(GV->getValueType());
          }
          if (!ty.empty()) OS << "T\t" << d << "\t" << ty << "\n";
        }
      }
      // R lines: every origin with its kind and label, what the program
      // made it as: a function; a global or stack slot by its declared
      // type; a heap allocation by its site; an identity root (content
      // from outside) by the static type of the cell it was minted on,
      // or of the value. K lines: first key inserts.
      {
        boost::unordered_flat_map<NodeIndex, NodeIndex> ownerOf;
        for (auto &[ptr, cell] : NF.getDerefMap()) ownerOf[cell] = ptr;
        auto tyName = [&](Type *T) -> std::string {
          std::string s2; raw_string_ostream os(s2); T->print(os); return os.str();
        };
        auto cellTy = [&](NodeIndex canon) -> std::string {
          auto oit = ownerOf.find(canon);
          if (oit == ownerOf.end()) return "?";
          const Value *V = NF.getValueForNode(oit->second);
          if (!V) return "?";
          if (const auto *G = dyn_cast<GEPOperator>(V)) {
            std::string ty = tyName(G->getSourceElementType());
            if (G->getNumIndices() >= 2)
              if (const auto *CI = dyn_cast<ConstantInt>(G->getOperand(2)))
                ty += " field " + std::to_string(CI->getZExtValue());
            return ty;
          }
          if (const auto *A = dyn_cast<AllocaInst>(V))
            return tyName(A->getAllocatedType());
          if (const auto *GV = dyn_cast<GlobalVariable>(V))
            return tyName(GV->getValueType());
          if (const auto *LI = dyn_cast<LoadInst>(V))
            return "loaded " + tyName(LI->getType());
          return std::string("via ") +
                 (isa<Instruction>(V) ? cast<Instruction>(V)->getOpcodeName()
                  : isa<Argument>(V)  ? "arg"
                                      : "const");
        };
        for (uint32_t rid = 0; rid < nextRoot; rid++) {
          const uint32_t rc = rid < rootClassOf.size() ? rootClassOf[rid] : UINT32_MAX;
          if (rc >= toOrig.size()) continue;
          const NodeIndex canon = toOrig[rc];
          const Value *V = NF.getValueForNode(canon);
          std::string kind, label;
          if (funcRootOf.count(rid)) {
            kind = "fn";
            label = "fn";
          } else if (NF.isDereferenceNode(canon)) {
            kind = "cell-id";
            label = cellTy(canon);
          } else if (!V) {
            kind = "special";
            label = "?";
          } else if (const auto *GV = dyn_cast<GlobalVariable>(V)) {
            kind = "global";
            label = tyName(GV->getValueType());
          } else if (const auto *A = dyn_cast<AllocaInst>(V)) {
            kind = "alloca";
            label = tyName(A->getAllocatedType());
          } else if (const auto *CB = dyn_cast<CallBase>(V);
                     CB && Ctx->AllocSites.count(const_cast<CallBase *>(CB))) {
            kind = "heap";
            label = "heap";
          } else {
            kind = "val-id";
            label = tyName(V->getType());
            if (const auto *I = dyn_cast<Instruction>(V))
              label += std::string(" ") + I->getOpcodeName();
            else if (isa<Argument>(V))
              label += " arg";
          }
          if (addrIsObj.size() > rid && addrIsObj[rid] && addrObj[rid] != rid)
            kind += "+addr";
          OS << "R\t" << rid << "\t" << kind << "\t" << label << "\t"
             << protBlameName(rc).substr(0, 90) << "\n";
        }
      }
      {
        size_t ki = 0;
        auto flushKeys = [&](size_t upto) {
          for (; ki < keyLog.size() && keyLog[ki].seq <= upto; ki++)
            OS << "K\t" << keyLog[ki].cls << "\t" << keyLog[ki].o << "\t"
               << keyLog[ki].s << "\t" << keyLog[ki].ptr << "\t"
               << keyLog[ki].cell << "\n";
        };
        for (size_t mi = 0; mi < mergeLog.size(); mi++) {
          flushKeys(mi);
          const MergeEv &e = mergeLog[mi];
          OS << "M\t" << e.a << "\t" << e.b << "\t" << e.why << "\t";
          if (e.why == StringRef("join") && e.keyO != UINT32_MAX &&
              e.keyO < rootClassOf.size())
            OS << e.keyO << "\t" << protBlameName(rootClassOf[e.keyO]).substr(0, 50)
               << "\t" << e.keyS << "\t" << e.ptr << "\t" << e.cell;
          else
            OS << "-\t-\t-\t-\t-";
          OS << "\n";
        }
        flushKeys(SIZE_MAX);
      }
      CG_LOG("DumpMerges: " << mergeLog.size() << " unions -> " << CFLDumpMerges
             << "\n");
    }
    if (VerboseLevel >= 2) {
      FactSet mFn, mLit, mHeap, mAlloca, mGlob, mId;
      for (uint32_t rid = 0; rid < nextRoot; rid++) {
        if (funcRootOf.count(rid)) { mFn.set(rid); continue; }
        if (rid < rootConstData.size() && rootConstData[rid]) { mLit.set(rid); continue; }
        const uint32_t rc = rid < rootClassOf.size() ? rootClassOf[rid] : UINT32_MAX;
        const Value *V = rc < toOrig.size() ? NF.getValueForNode(toOrig[rc]) : nullptr;
        if (!V) mId.set(rid);
        else if (isa<AllocaInst>(V)) mAlloca.set(rid);
        else if (isa<GlobalVariable>(V)) mGlob.set(rid);
        else if (isa<Argument>(V) || (rc < toOrig.size() && NF.isDereferenceNode(toOrig[rc])))
          mId.set(rid);
        else mHeap.set(rid); // allocation-call results and other value origins
      }
      FactSet tmp;
      auto holds = [&](uint32_t c, const FactSet &mask) {
        for (uint32_t s = 0; s < NSHIFT; s++) {
          tmp.copyFrom(R[c][s]); tmp.intersectWith(mask); if (tmp.any()) return true;
          tmp.copyFrom(RB[c][s]); tmp.intersectWith(mask); if (tmp.any()) return true;
        }
        return false;
      };
      size_t nFn = 0, nLit = 0, nHeap = 0, nAlloca = 0, nGlob = 0, nId = 0, nPure = 0;
      std::vector<std::string> exLit, exHeap, exPure;
      for (uint32_t c = 0; c < N; c++) {
        if (find(c) != c || !holds(c, mFn)) continue;
        nFn++;
        const bool l = holds(c, mLit), h = holds(c, mHeap), a = holds(c, mAlloca),
                   g = holds(c, mGlob), i = holds(c, mId);
        nLit += l; nHeap += h; nAlloca += a; nGlob += g; nId += i;
        if (!(l || h || a || g || i)) {
          nPure++;
          if (exPure.size() < 6) exPure.push_back(protBlameName(c).substr(0, 45));
        }
        if (l && exLit.size() < 8) {
          std::string e = protBlameName(c).substr(0, 45);
          if (exLit.size() < 3) {
            // Name what it holds: two functions and two literals.
            int nf = 0, nl = 0;
            for (uint32_t s = 0; s < NSHIFT && (nf < 2 || nl < 2); s++)
              R[c][s].forEach([&](uint32_t o) {
                if (nf < 2 && funcRootOf.count(o)) {
                  e += " fn:" + funcRootOf[o]->getName().str(); nf++;
                } else if (nl < 2 && o < rootConstData.size() && rootConstData[o]) {
                  e += " lit:" + protBlameName(rootClassOf[o]).substr(0, 20) + "@s" +
                       std::to_string(s); nl++;
                }
              });
          }
          exLit.push_back(e);
        }
        if (h && exHeap.size() < 8) exHeap.push_back(protBlameName(c).substr(0, 45));
      }
      if (lazyAddr) typeConflictReport(60);
      if (lazyAddr) {
        errs() << "LazyAddr: " << lazyMinted << " addresses minted ("
               << lazyStrided << " strided, " << lazyX << " range), "
               << lazyOverlapBridges << " overlap bridges, "
               << lazyLabels.size() << " exact labels, " << lazyWidened
               << " progressions widened, " << lazyAbsorbed << " absorbed, "
               << lazyTypedDrops << " typed-access drops, "
               << lazyCapped << " capped mint attempts on "
               << lazyCappedObjs.size() << " objects\n";
        if (VerboseLevel >= 2 && !lazyCappedHits.empty()) {
          // Who is capped, by kind: the rule is right only if this list
          // holds byte buffers and arrays walked through memory.
          std::vector<std::pair<uint64_t, uint32_t>> top;
          for (auto &[o, c] : lazyCappedHits) top.emplace_back(c, o);
          std::sort(top.rbegin(), top.rend());
          std::map<std::string, std::pair<size_t, uint64_t>> byKind;
          for (auto &[c, o] : top) {
            const uint32_t rc = o < rootClassOf.size() ? rootClassOf[o] : UINT32_MAX;
            const Value *V = rc < toOrig.size() ? NF.getValueForNode(toOrig[rc]) : nullptr;
            std::string kind = !V ? (rc < toOrig.size() && NF.isDereferenceNode(toOrig[rc]) ? "identity-cell" : "synthetic")
                             : isa<GlobalVariable>(V) ? "global" : isa<AllocaInst>(V) ? "alloca"
                             : isa<Argument>(V) ? "identity-formal" : isa<CallBase>(V)
                             ? (cast<CallBase>(V)->getCalledFunction() ? "heap-call" : "icall-return") : "other";
            const StructType *T = declaredType(o);
            if (!T) { auto it = objPrimary.find(o); if (it != objPrimary.end()) T = it->second.ty; }
            auto &bk = byKind[kind + (T ? "/typed" : "/untyped")]; bk.first++; bk.second += c;
          }
          errs() << "LazyAddr: capped objects by kind:";
          for (auto &[k, v] : byKind) errs() << " " << k << " " << v.first << " objs/" << v.second << " mints;";
          errs() << "\n";
          size_t shown = 0;
          for (auto &[c, o] : top) {
            if (shown++ >= 25) break;
            const StructType *T = declaredType(o);
            if (!T) { auto it = objPrimary.find(o); if (it != objPrimary.end()) T = it->second.ty; }
            errs() << "LazyAddr:   capped r" << o << " " << protBlameName(rootClassOf[o]).substr(0, 60)
                   << " size " << objBytes(o) << " type "
                   << (T && T->hasName() ? stripStructNameSuffix(T->getName()).str() : std::string("-"))
                   << " refused " << c << "\n";
          }
        }
      }
      if (CFLKeyIdentity)
        errs() << "KeyIdentity: " << keyIdentityMinted
               << " channel identities minted, " << keyIdentitySelf
               << " self-loop wirings\n";
      if (holderMode)
        errs() << "HolderIdentity: " << holderClones << " clones over "
               << freshStoreCells.size() << " fresh-store cells; "
               << holderCellsDisabled << " cells past the key bound\n";
      if (!CFLDumpClass.empty()) {
        // Members of every class whose rep name matches, by function.
        std::unordered_map<uint32_t, std::vector<uint32_t>> members;
        for (uint32_t n2 = 0; n2 < (uint32_t)ufp.size(); n2++)
          members[find(n2)].push_back(n2);
        // Match on MEMBER names: a node merged early lives in a class
        // named after its rep, so matching reps alone misses it.
        boost::unordered_flat_set<uint32_t> wanted;
        for (uint32_t n2 = 0; n2 < (uint32_t)toOrig.size(); n2++)
          if (denseNameMatches(n2, CFLDumpClass))
            wanted.insert(find(n2));
        for (auto &[rep, mem] : members) {
          if (mem.size() < 2 || !wanted.count(rep)) continue;
          const std::string rn = protBlameName(rep);
          std::map<std::string, std::pair<size_t, std::string>> byFn;
          size_t synthetic = 0;
          for (uint32_t m2 : mem) {
            if (m2 >= toOrig.size()) { synthetic++; continue; }
            const Value *V2 = NF.getValueForNode(toOrig[m2]);
            std::string fnName = "<no fn>";
            if (const auto *I3 = dyn_cast_or_null<Instruction>(V2))
              fnName = I3->getFunction()->getName().str();
            else if (const auto *A3 = dyn_cast_or_null<Argument>(V2))
              fnName = A3->getParent()->getName().str();
            else if (V2 && isa<GlobalValue>(V2)) fnName = "<global>";
            else if (NF.isDereferenceNode(toOrig[m2])) fnName = "<cell>";
            auto &e = byFn[fnName];
            e.first++;
            if (e.second.size() < 120) e.second += " " + protBlameName(m2).substr(0, 28);
          }
          errs() << "DumpClass: c" << rep << " " << rn.substr(0, 60) << " size "
                 << mem.size() << " (" << synthetic << " channel/read-half)\n";
          std::vector<std::pair<size_t, std::string>> order;
          for (auto &[fn, e] : byFn) order.push_back({e.first, fn});
          std::sort(order.begin(), order.end(), std::greater<>());
          size_t shown = 0;
          for (auto &[cnt, fn] : order) {
            if (shown++ >= 40) { errs() << "DumpClass:   ... " << order.size() - 40 << " more functions\n"; break; }
            errs() << "DumpClass:   " << cnt << " " << fn << ":" << byFn[fn].second << "\n";
          }
        }
      }
      errs() << "MixCensus: classes holding fn facts " << nFn << ": pure-fn " << nPure
             << ", +literal " << nLit << ", +heap " << nHeap << ", +alloca " << nAlloca
             << ", +global " << nGlob << ", +identity " << nId << "\n";
      auto show = [&](const char *tag, const std::vector<std::string> &ex) {
        errs() << "MixCensus:   " << tag << ":";
        for (auto &e : ex) errs() << " [" << e << "]";
        errs() << "\n";
      };
      show("fn+literal e.g.", exLit);
      show("fn+heap e.g.", exHeap);
      show("pure-fn e.g.", exPure);
    }
    // Cluster-transitivity audit: union-find clusters are coarser-or-equal
    // vs the grammar's per-witness M; multi-key clusters and transitive
    // key-coalescing merges bound the over-approximation (Lean gap F3).
    {
      std::unordered_map<uint32_t, uint32_t> keysPer;
      std::unordered_map<uint32_t, uint64_t> shiftsPer; // rep -> residue mask
      for (auto &[k, rep] : clusterRep) {
        keysPer[find(rep)]++;
        shiftsPer[find(rep)] |= 1ull << (k % NSHIFT);
      }
      uint64_t multi = 0, maxK = 0, mixed = 0, mixedKeys = 0;
      uint32_t giantRep = UINT32_MAX;
      for (auto &[cls, kc] : keysPer) {
        if (kc > 1) multi++;
        if (kc > maxK) { maxK = kc; giantRep = cls; }
        // A cluster holding keys at more than one residue reads and
        // writes across fields: the field split is lost inside it.
        if (__builtin_popcountll(shiftsPer[cls]) > 1) { mixed++; mixedKeys += kc; }
      }
      errs() << "ClusterTrans: " << clusterCount() << " keys in "
             << keysPer.size() << " clusters, multi-key clusters " << multi
             << ", max keys/cluster " << maxK
             << ", transitive key-coalescing merges " << transKeyMerges
             << "\n";
      if (NSHIFT > 1) {
        errs() << "ClusterTrans: residue-mixed clusters " << mixed << " holding "
               << mixedKeys << " keys; largest cluster spans "
               << (giantRep == UINT32_MAX
                       ? 0 : __builtin_popcountll(shiftsPer[giantRep]))
               << " of " << NSHIFT << " residues\n";
        // Which POINTER classes carry facts at several residues: each
        // such class welds every key it holds into one cluster, so
        // these are the cross-field couplers. Histogram + top classes.
        std::vector<uint32_t> hist(NSHIFT + 1, 0);
        std::vector<std::pair<uint32_t, uint32_t>> top; // (#residues, class)
        for (uint32_t c = 0; c < N; c++) {
          if (find(c) != c) continue;
          uint32_t k = 0;
          for (uint32_t s = 0; s < NSHIFT; s++)
            if (R[c][s].any() || RB[c][s].any()) k++;
          hist[k]++;
          if (k >= 2) top.emplace_back(k, c);
        }
        errs() << "ResidueSpread: classes by #residues carrying facts:";
        for (uint32_t k = 0; k <= NSHIFT; k++)
          if (hist[k]) errs() << " " << k << ":" << hist[k];
        errs() << "\n";
        std::sort(top.rbegin(), top.rend());
        for (size_t i = 0; i < std::min<size_t>(25, top.size()); i++) {
          const uint32_t c = top[i].second;
          errs() << "ResidueSpread: " << top[i].first << " residues, class c" << c
                 << " size=" << clsSize[c] << " " << protBlameName(c).substr(0, 70)
                 << "\n";
        }
      }
    }
    errs() << "ChurnStats: merges join=" << mergesFromJoin
           << " scc=" << mergesFromSCC
           << ", redundant join lookups " << redundantJoins
           << ", null-key joins skipped " << nullKeyJoinsSkipped
           << (CFLChannelCells
                   ? (", CHANNELS " + std::to_string(chanNodes) + " nodes " +
                      std::to_string(chanEdges) + " edges " +
                      std::to_string(chanSplits) + " split cells " +
                      std::to_string(chanConeSkipped) + " pends outside cone " +
                      std::to_string(chanConstSkipped) + " const-data keys")
                   : std::string())
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
          size_t fShown = 0, fTotal = 0;
          auto rootName = [&](uint32_t o4) -> std::string {
            if (o4 >= rootClassOf.size()) return "?";
            const uint32_t rc4 = rootClassOf[o4];
            if (rc4 >= toOrig.size()) return "?";
            const Value *OV = NF.getValueForNode(toOrig[rc4]);
            if (OV && OV->hasName()) return OV->getName().str();
            if (OV)
              if (const auto *OI = dyn_cast<Instruction>(OV))
                return (OI->getFunction()->getName() + "::" +
                        OI->getOpcodeName()).str();
            return NF.isObjectNode(toOrig[rc4]) ? "<obj>" : "<syn>";
          };
          for (uint32_t s4 = 0; s4 < NSHIFT; s4++) {
            R[cl2][s4].forEach([&](uint32_t o4) {
              fTotal++;
              if (fShown > 40) return;
              if (fShown++ == 40) { errs() << " ..."; return; }
              errs() << " (r" << o4 << "=" << rootName(o4).substr(0, 36)
                     << ",s" << s4 << ")";
            });
          }
          errs() << " [total " << fTotal << "]";
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
    // CONE-ACTIVE set: origins with >=1 fact on some fptr-ancestor
    // class. THE sound fs-prune criterion (all-derivations-closed):
    // any fs derivation of an answer maps through the FI quotient onto
    // ancestor classes only, so an origin absent from every ancestor
    // class's planes can appear in NO fs answer derivation. (The
    // SUFFICIENT set above is single-witness-closed — sound for FI
    // re-derivation, NOT for fs pruning.)
    {
      std::vector<char> coneAct(nextRoot, 0);
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n || !anc[n]) continue;
        for (uint32_t s = 0; s < NSHIFT; s++) {
          auto mk = [&](const FactSet &pl) {
            pl.forEach([&](uint32_t o) { coneAct[o] = 1; });
          };
          mk(R[n][s]);
          mk(RB[n][s]);
        }
      }
      size_t nCone = 0;
      for (uint32_t o = 0; o < nextRoot; o++) nCone += coneAct[o];
      uint64_t factsCone = 0;
      for (uint32_t n = 0; n < N; n++) {
        if (find(n) != n) continue;
        for (uint32_t s = 0; s < NSHIFT; s++) {
          auto tly = [&](const FactSet &pl) {
            pl.forEach([&](uint32_t o) { factsCone += coneAct[o]; });
          };
          tly(R[n][s]);
          tly(RB[n][s]);
        }
      }
      errs() << "RootRel: CONE-ACTIVE " << nCone << "/" << nextRoot
             << " roots ("
             << (nextRoot ? 100.0 * nCone / nextRoot : 0.0)
             << "%), fact mass " << factsCone << "/" << factsTotal
             << " (" << (factsTotal ? 100.0 * factsCone / factsTotal : 0.0)
             << "%) — sound fs-prune keep-set\n";
    }
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
      const uint32_t NL = (uint32_t)ufp.size(); // channel nodes included
      std::vector<uint32_t> comp(NL, UINT32_MAX);
      uint32_t nComp = 0;
      std::unordered_map<uint32_t, uint64_t> compSize;
      ka::tarjanSCC(
          NL, [&](uint32_t v) { return find(v) != v; },
          [&](uint32_t u) { return outA[u].size(); },
          [&](uint32_t u, size_t i) { return find(outA[u][i]); },
          [&](const std::vector<uint32_t> &members) {
            const uint32_t c = nComp++;
            for (uint32_t w : members) comp[w] = c;
            compSize[c] = members.size();
          });
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
// O0 spill slots, shared by the wrapper confirmer and the holder-identity
// rule: a local alloca whose only users are loads, stores INTO it and
// debug/lifetime markers never escapes; a load from it reads the stores
// that REACH it — the last store before it in its block, else the last
// store on each predecessor path (the mem2reg answer, on demand).
const AllocaInst *spillSlotOf(const Value *v) {
  const auto *AI = dyn_cast<AllocaInst>(v);
  if (!AI) return nullptr;
  for (const User *U : AI->users()) {
    if (isa<LoadInst>(U)) continue;
    if (const auto *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getPointerOperand() == AI && SI->getValueOperand() != AI)
        continue;
      return nullptr;
    }
    if (const auto *II = dyn_cast<IntrinsicInst>(U)) {
      switch (II->getIntrinsicID()) {
      case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
      case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
        continue;
      default: break;
      }
    }
    return nullptr;
  }
  return AI;
}
void reachingSlotStoresOf(const LoadInst *L, const AllocaInst *AI,
                                 SmallVectorImpl<const StoreInst *> &out) {
  auto lastStoreBefore = [&](const BasicBlock *BB,
                             const Instruction *upto) -> const StoreInst * {
    const StoreInst *last = nullptr;
    for (const Instruction &I : *BB) {
      if (&I == upto) break;
      if (const auto *SI = dyn_cast<StoreInst>(&I))
        if (SI->getPointerOperand() == AI) last = SI;
    }
    return last;
  };
  if (const StoreInst *S0 = lastStoreBefore(L->getParent(), L)) {
    out.push_back(S0);
    return;
  }
  SmallVector<const BasicBlock *, 8> wl(pred_begin(L->getParent()),
                                        pred_end(L->getParent()));
  SmallPtrSet<const BasicBlock *, 16> seen;
  while (!wl.empty()) {
    const BasicBlock *B = wl.pop_back_val();
    if (!seen.insert(B).second) continue;
    if (const StoreInst *S = lastStoreBefore(B, nullptr)) {
      out.push_back(S);
      continue;
    }
    for (const BasicBlock *P : predecessors(B)) wl.push_back(P);
  }
}
// The unique allocation call a pointer value descends from, through
// casts and spill reloads; nullptr when any path yields anything else.
static const CallBase *
uniqueAllocSource(const Value *v,
                  const std::function<bool(const CallBase *)> &isAlloc) {
  const CallBase *found = nullptr;
  SmallVector<const Value *, 8> wl{v->stripPointerCasts()};
  SmallPtrSet<const Value *, 16> seen;
  while (!wl.empty()) {
    const Value *x = wl.pop_back_val();
    if (!seen.insert(x).second) continue;
    if (const auto *CB = dyn_cast<CallBase>(x)) {
      if (!isAlloc(CB) || (found && found != CB)) return nullptr;
      found = CB;
      continue;
    }
    if (const auto *C = dyn_cast<CastInst>(x)) {
      wl.push_back(C->getOperand(0)->stripPointerCasts());
      continue;
    }
    if (const auto *L = dyn_cast<LoadInst>(x)) {
      if (const AllocaInst *AI = spillSlotOf(L->getPointerOperand())) {
        SmallVector<const StoreInst *, 4> defs;
        reachingSlotStoresOf(L, AI, defs);
        if (defs.empty()) return nullptr;
        for (const StoreInst *D : defs)
          wl.push_back(D->getValueOperand()->stripPointerCasts());
        continue;
      }
    }
    return nullptr;
  }
  return found;
}
