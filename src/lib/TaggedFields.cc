//===-- TaggedFields.cc - keys for fields tagged by a sibling (plan 3.51) -===//
//
// A tagged field is the union rule of plan 3.18/3.31 where only the program
// shows the slot has several meanings: a pointer field F of struct S whose
// meaning is decided by a sibling field D (the discriminator) the program
// writes with it and tests before reading it (sqlite3: Mem.z by Mem.flags).
// Under --cfl-cells (union keys "tag"):
// - a writer is a store to F whose function also stores D on the same
//   object; its tags are the constants it stores into D;
// - a store to D on an object whose F the function does not write is a
//   retag (set c, or v -> (v & a) | o); a non-constant retag leaves the
//   pair unkeyed;
// - a read of F is keyed by the tests of D (loaded from the same object)
//   that dominate it: it admits a writer iff some tag reachable from the
//   writer's tags through the retags satisfies every test;
// - untagged writers (no co-written D) are plain stores, which every keyed
//   read includes; a read with no dominating test reads every key.
//
//===----------------------------------------------------------------------===//

#include "CallGraph.h"
#include "CallGraphInternal.h"
#include <llvm/IR/Dominators.h>
#include <chrono>

using namespace llvm;

namespace {
// The object an access belongs to: the struct GEP's base, through -O0
// local slots by reaching definitions: a reload of a slot is the value of
// the one store reaching it (two reloads name one object only when they
// read the same store's value, never because they read the same slot: a
// slot reassigned between two accesses holds two objects); a reload with
// several reaching stores is its own identity, shared only with the
// reloads before it in its block with no store between.
struct ObjIds {
  struct SlotInfo {
    bool escapes = false;
    std::map<const LoadInst *, const Value *> id;
  };
  std::map<const AllocaInst *, SlotInfo> slots;
  // The values stored into a non-escaping local slot (null: it escapes).
  std::map<const AllocaInst *, std::optional<std::vector<const Value *>>> stored;
  const std::vector<const Value *> *storedInto(const AllocaInst *A) {
    auto [it, ins] = stored.try_emplace(A);
    if (ins) {
      std::vector<const Value *> vals;
      bool esc = false;
      for (const User *U : A->users()) {
        if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == A && S->getValueOperand() != A) {
          vals.push_back(S->getValueOperand());
          continue;
        }
        if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == A) continue;
        if (isa<DbgInfoIntrinsic>(U)) continue;
        esc = true;
        break;
      }
      if (!esc) it->second = std::move(vals);
    }
    return it->second ? &*it->second : nullptr;
  }
  const SlotInfo &slot(const AllocaInst *A) {
    auto [it, ins] = slots.try_emplace(A);
    SlotInfo &SI = it->second;
    if (!ins) return SI;
    std::vector<const StoreInst *> stores;
    std::vector<const LoadInst *> loads;
    for (const User *U : A->users()) {
      if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == A && S->getValueOperand() != A) {
        stores.push_back(S);
        continue;
      }
      if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == A) {
        loads.push_back(L);
        continue;
      }
      if (isa<DbgInfoIntrinsic>(U)) continue;
      SI.escapes = true;
      return SI;
    }
    if (loads.empty()) return SI;
    // Reaching stores per block (bit k: stores[k]; bit n: the entry value).
    const Function &F = *A->getFunction();
    const unsigned n = stores.size();
    std::map<const StoreInst *, unsigned> idx;
    for (unsigned k = 0; k < n; k++) idx[stores[k]] = k;
    std::map<const BasicBlock *, const StoreInst *> lastIn;
    for (const StoreInst *S : stores) {
      const StoreInst *&L = lastIn[S->getParent()];
      if (!L || L->comesBefore(S)) L = S;
    }
    std::map<const BasicBlock *, BitVector> in, out;
    for (const BasicBlock &BB : F) in[&BB] = BitVector(n + 1), out[&BB] = BitVector(n + 1);
    in[&F.getEntryBlock()].set(n);
    for (bool changed = true; changed;) {
      changed = false;
      for (const BasicBlock &BB : F) {
        BitVector I = in[&BB];
        for (const BasicBlock *P : predecessors(&BB)) I |= out[P];
        if (&BB == &F.getEntryBlock()) I.set(n);
        BitVector O(n + 1);
        if (auto lit = lastIn.find(&BB); lit != lastIn.end()) O.set(idx[lit->second]);
        else O = I;
        if (I != in[&BB] || O != out[&BB]) {
          in[&BB] = std::move(I);
          out[&BB] = std::move(O);
          changed = true;
        }
      }
    }
    std::set<const BasicBlock *> blocks;
    for (const LoadInst *L : loads) blocks.insert(L->getParent());
    for (const BasicBlock *BB : blocks) {
      BitVector cur = in[BB];
      const LoadInst *runHead = nullptr; // first reload since the last store
      for (const Instruction &I : *BB) {
        if (const auto *S = dyn_cast<StoreInst>(&I); S && idx.count(S)) {
          cur.reset();
          cur.set(idx[S]);
          runHead = nullptr;
          continue;
        }
        const auto *L = dyn_cast<LoadInst>(&I);
        if (!L || L->getPointerOperand() != A) continue;
        if (cur.count() == 1 && cur.find_first() < (int)n) SI.id[L] = stores[cur.find_first()]->getValueOperand();
        else {
          if (!runHead) runHead = L;
          SI.id[L] = runHead;
        }
      }
    }
    return SI;
  }
  // objSize: the accessed struct's size (a -O3 byte offset inside it is a
  // field of the base; past it, another element).
  const Value *of(const Value *Addr, int64_t objSize = 0, int depth = 0) {
    const Value *B = Addr->stripPointerCasts();
    // A field of the object (constant indices from element 0); another
    // element of an array is another object.
    if (const GEPOperator *G = structGEP(Addr)) {
      const auto *I0 = G->getNumIndices() ? dyn_cast<ConstantInt>(*G->idx_begin()) : nullptr;
      if (G->hasAllConstantIndices() && I0) {
        const bool bytes = G->getSourceElementType()->isIntegerTy(8) && G->getNumIndices() == 1;
        if (bytes ? (I0->getSExtValue() >= 0 && I0->getSExtValue() < objSize) : I0->isZero())
          B = G->getPointerOperand()->stripPointerCasts();
      }
    }
    if (depth > 8) return B;
    if (const auto *L = dyn_cast<LoadInst>(B))
      if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
        const SlotInfo &SI = slot(A);
        if (SI.escapes) return L; // a slot written elsewhere: this reload only
        auto it = SI.id.find(L);
        assert(it != SI.id.end() && "every reload of a non-escaping slot has an identity");
        if (isa<LoadInst>(it->second) && it->second->getType()->isPointerTy() &&
            cast<LoadInst>(it->second)->getPointerOperand() == A)
          return it->second; // a run of reloads
        return of(it->second, 0, depth + 1);
      }
    return B;
  }
};
std::string locOf(const Instruction *I) {
  if (!I) return "?";
  std::string s = I->getFunction()->getName().str();
  if (const DILocation *L = I->getDebugLoc()) s += ":" + std::to_string(L->getLine());
  return s;
}
} // namespace

void CallGraphPass::computeTaggedFields() {
  ObjIds ids;
  auto objKey = [&](const Instruction *I, const Value *Addr, StructType *S) {
    const DataLayout &DL = I->getModule()->getDataLayout();
    return ids.of(Addr, S && S->isSized() ? (int64_t)DL.getTypeAllocSize(S) : 0);
  };
  taggedReport.clear();
  taggedPairs.clear();
  taggedWatches.clear();
  const auto t0 = std::chrono::steady_clock::now();
  if (!CFLCells || CFLUnionKeys != "tag") return;
  // The value a tag store writes, as terms (v & a) | f | s, s any
  // submask of m: v a constant 0 ('c'), this object's tag before the store
  // ('s'), or any object's tag ('x'); a term set stands for the union.
  // Evaluated through casts, phis, selects, -O0 local slots (fixpoint),
  // and/or with anything (a side that is not kept symbolic becomes free
  // bits: a superset), xor/shifts/add on enumerated values (MemCast's
  // `f |= (f & MEM_Blob) >> 3` is s|{0,2}), and, under
  // --cfl-whole-program, a parameter of a function whose address is not
  // taken, by the arguments at its call sites (each bound reported).
  struct Term { char src; int64_t a, f, m; };
  struct TagStore {
    const StoreInst *I;
    const Value *obj;
    bool unknown = false;
    std::vector<Term> terms;
    std::vector<std::string> via; // interprocedural bounds used
  };
  struct FAccess { const Instruction *I; const Value *obj; };
  using Field = std::pair<std::string, int64_t>; // (struct, offset)
  std::map<Field, std::vector<FAccess>> fStores, fLoads;
  std::map<Field, std::vector<TagStore>> dStores;
  // Every value a term set may take (a symbolic tag's bits free).
  auto concretize = [](const std::vector<Term> &ts, std::set<int64_t> &out) {
    for (const Term &t : ts) {
      const uint64_t fr = (uint64_t)((t.src == 'c' ? 0 : t.a) | t.m) & ~(uint64_t)t.f;
      if (llvm::popcount(fr) > 12) return false;
      for (uint64_t sub = fr;; sub = (sub - 1) & fr) { // every submask
        out.insert((int64_t)sub | t.f);
        if (!sub) break;
      }
      if (out.size() > 4096) return false;
    }
    return true;
  };
  // A term with its symbolic part made free bits (a superset).
  auto freeOf = [](const Term &t) {
    const int64_t fr = (t.src == 'c' ? 0 : t.a) | t.m;
    return Term{'c', 0, t.f, fr & ~t.f};
  };
  auto analyzeTag = [&](const StoreInst *S, const Value *obj, const Field &D, TagStore &T) {
    // Memoized per value. A local slot and a parameter are the cycle
    // points (a loop variable, mutual recursion): each is solved as a
    // fixpoint over its definitions (stores, call-site arguments); a use
    // inside its own definition sees the current approximation, and what
    // was computed from an approximation is recomputed until it is stable.
    constexpr size_t kMaxTerms = 4096;
    std::map<const Value *, std::optional<std::vector<Term>>> memo;
    std::vector<const Value *> memoLog;
    size_t budget = 1 << 16;
    struct Fix { bool busy = false, done = false, failed = false; std::vector<Term> terms; };
    std::map<const Value *, Fix> fix;
    std::vector<std::set<const Value *>> touched; // per open fixpoint: busy points it read
    auto norm = [](std::vector<Term> &ts) {
      std::sort(ts.begin(), ts.end(), [](const Term &a, const Term &b) {
        return std::tie(a.src, a.a, a.f, a.m) < std::tie(b.src, b.a, b.f, b.m);
      });
      ts.erase(std::unique(ts.begin(), ts.end(), [](const Term &a, const Term &b) {
        return a.src == b.src && a.a == b.a && a.f == b.f && a.m == b.m;
      }), ts.end());
    };
    auto fixpoint = [&](const Value *key, const std::function<bool(std::vector<Term> &)> &body,
                        std::vector<Term> &out) -> bool {
      {
        Fix &st = fix[key];
        if (st.failed) return false;
        if (st.done || st.busy) {
          if (st.busy)
            for (auto &t : touched) t.insert(key);
          out.insert(out.end(), st.terms.begin(), st.terms.end());
          return out.size() <= kMaxTerms;
        }
        st.busy = true;
      }
      const size_t mark = memoLog.size();
      bool ok = false;
      std::set<const Value *> reads;
      for (int it = 0; it < 16; it++) {
        touched.emplace_back();
        std::vector<Term> acc;
        const bool good = body(acc);
        reads = std::move(touched.back());
        touched.pop_back();
        if (!good || acc.size() > kMaxTerms) break;
        norm(acc);
        Fix &st = fix[key];
        const bool same = acc.size() == st.terms.size() &&
                          std::equal(acc.begin(), acc.end(), st.terms.begin(), [](const Term &a, const Term &b) {
                            return a.src == b.src && a.a == b.a && a.f == b.f && a.m == b.m;
                          });
        st.terms = std::move(acc);
        if (same || !reads.count(key)) { ok = true; break; }
        for (size_t k = mark; k < memoLog.size(); k++) memo.erase(memoLog[k]);
        memoLog.resize(mark);
      }
      Fix &st = fix[key];
      st.busy = false;
      if (!ok) { st.failed = true; return false; }
      reads.erase(key);
      if (reads.empty()) st.done = true; // else: solved under an enclosing approximation
      else {
        for (auto &t : touched) t.insert(reads.begin(), reads.end());
        std::vector<Term> r = std::move(st.terms);
        st = Fix();
        out.insert(out.end(), r.begin(), r.end());
        return out.size() <= kMaxTerms;
      }
      out.insert(out.end(), st.terms.begin(), st.terms.end());
      return out.size() <= kMaxTerms;
    };
    auto slotOf = [&](const Value *V) -> const AllocaInst * {
      if (const auto *L = dyn_cast<LoadInst>(V))
        if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          if (ids.storedInto(A)) return A;
      return nullptr;
    };
    std::function<bool(const Value *, int, std::vector<Term> &)> ev1;
    std::function<bool(const Value *, int, std::vector<Term> &)> ev =
        [&](const Value *V, int depth, std::vector<Term> &out) -> bool {
      if (isa<ConstantInt>(V) || isa<Argument>(V) || slotOf(V)) return ev1(V, depth, out);
      auto [mit, ins] = memo.try_emplace(V);
      if (!ins) {
        if (!mit->second) return false; // failed (or a cycle not through a slot or parameter)
        out.insert(out.end(), mit->second->begin(), mit->second->end());
        return out.size() <= kMaxTerms;
      }
      memoLog.push_back(V);
      if (!budget || !budget--) return false;
      std::vector<Term> mine;
      if (!ev1(V, depth, mine)) return false; // memo stays empty: failed
      memo[V] = mine;
      out.insert(out.end(), mine.begin(), mine.end());
      return out.size() <= kMaxTerms;
    };
    ev1 = [&](const Value *V, int depth, std::vector<Term> &out) -> bool {
      if (depth > 24 || out.size() > kMaxTerms) return false;
      if (const auto *K = dyn_cast<ConstantInt>(V)) {
        out.push_back({'c', 0, K->getSExtValue(), 0});
        return true;
      }
      auto mask = [](unsigned bits) { return bits >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << bits) - 1); };
      if (const auto *C = dyn_cast<CastInst>(V)) {
        if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) return false;
        std::vector<Term> in;
        if (!ev(C->getOperand(0), depth + 1, in)) return false;
        const unsigned sb = C->getOperand(0)->getType()->getIntegerBitWidth(), db = C->getType()->getIntegerBitWidth();
        if (isa<TruncInst>(C) || isa<ZExtInst>(C)) {
          const int64_t m = mask(isa<TruncInst>(C) ? db : sb);
          for (Term t : in) out.push_back({t.src, t.a & m, t.f & m, t.m & m});
          return true;
        }
        if (isa<SExtInst>(C)) {
          std::set<int64_t> cs;
          if (!concretize(in, cs)) return false;
          for (int64_t c : cs) out.push_back({'c', 0, APInt(sb, (uint64_t)c).sext(64).getSExtValue(), 0});
          return true;
        }
        return false;
      }
      if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
        std::vector<Term> x, y;
        if (!ev(BO->getOperand(0), depth + 1, x) || !ev(BO->getOperand(1), depth + 1, y)) return false;
        auto exact = [](const std::vector<Term> &ts) { // constants, no free bits
          for (const Term &t : ts) if ((t.src != 'c' && t.a != 0) || t.m != 0) return false;
          return true;
        };
        const auto op = BO->getOpcode();
        if ((op == Instruction::And || op == Instruction::Or) && !(exact(x) && exact(y))) {
          // Bitwise on terms (a, f, m disjoint): a bit is the tag's, fixed
          // one, free, or zero. Terms over the same tag pair exactly (this
          // object's tag on both sides, or a tag with constants); any other
          // object's tag on both sides cannot be paired (two objects): one
          // side becomes free bits.
          auto srcs = [](const std::vector<Term> &ts) {
            std::set<char> r;
            for (const Term &t : ts) if (t.src != 'c' && t.a != 0) r.insert(t.src);
            return r;
          };
          auto combine = [&](Term p, Term q) {
            if (p.src == 'c') p.a = 0;
            if (q.src == 'c') q.a = 0;
            const char src = p.a ? p.src : q.a ? q.src : 'c';
            Term r{'c', 0, 0, 0};
            if (op == Instruction::Or) {
              r.f = p.f | q.f;
              r.m = (p.m | q.m) & ~r.f;
              r.a = (p.a | q.a) & ~r.f & ~r.m;
            } else {
              r.a = (p.a & q.a) | (p.a & q.f) | (q.a & p.f);
              r.f = p.f & q.f;
              r.m = (((p.a | p.f | p.m) & q.m) | ((q.a | q.f | q.m) & p.m)) & ~r.f & ~r.a;
            }
            r.src = r.a ? src : 'c';
            return r;
          };
          const std::set<char> sx = srcs(x), sy = srcs(y);
          const bool pairable = sx.empty() || sy.empty() || (sx == std::set<char>{'s'} && sy == sx);
          if (!pairable) { // free the side holding another object's tag (y if both)
            std::vector<Term> &K = sy.count('x') ? y : x;
            for (Term &t : K) t = freeOf(t);
          }
          if (x.size() * y.size() > kMaxTerms) return false;
          for (const Term &p : x)
            for (const Term &q : y) out.push_back(combine(p, q));
          return out.size() <= kMaxTerms;
        }
        std::set<int64_t> xs, ys;
        if (!concretize(x, xs) || !concretize(y, ys) || xs.size() * ys.size() > 4096) return false;
        for (int64_t a : xs)
          for (int64_t b : ys) {
            int64_t r;
            switch (op) {
            case Instruction::And: r = a & b; break;
            case Instruction::Or: r = a | b; break;
            case Instruction::Xor: r = a ^ b; break;
            case Instruction::Add: r = (int64_t)((uint64_t)a + (uint64_t)b); break;
            case Instruction::Sub: r = (int64_t)((uint64_t)a - (uint64_t)b); break;
            case Instruction::Shl: if (b < 0 || b > 63) return false; r = (int64_t)((uint64_t)a << b); break;
            case Instruction::LShr: {
              if (b < 0 || b > 63) return false;
              const unsigned w = BO->getType()->getIntegerBitWidth();
              r = (int64_t)(((uint64_t)a & (uint64_t)mask(w)) >> b);
              break;
            }
            case Instruction::AShr: {
              if (b < 0 || b > 63) return false;
              const unsigned w = BO->getType()->getIntegerBitWidth();
              r = APInt(w, (uint64_t)a).ashr((unsigned)b).getSExtValue();
              break;
            }
            default: return false;
            }
            out.push_back({'c', 0, r, 0});
          }
        return out.size() <= 4096;
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        for (const Value *In : PN->incoming_values())
          if (!ev(In, depth + 1, out)) return false;
        return true;
      }
      if (const auto *SI = dyn_cast<SelectInst>(V))
        return ev(SI->getTrueValue(), depth + 1, out) && ev(SI->getFalseValue(), depth + 1, out);
      if (const auto *L = dyn_cast<LoadInst>(V)) {
        if (const AllocaInst *A = slotOf(L)) {
          const auto *vals = ids.storedInto(A);
          if (vals->empty()) return false;
          return fixpoint(A, [&](std::vector<Term> &acc) {
            for (const Value *X : *vals)
              if (!ev(X, depth + 1, acc)) return false;
            return true;
          }, out);
        }
        StructType *S2 = nullptr;
        int64_t off2 = 0;
        if (L->getType()->isIntegerTy() &&
            accessSlot(L, L->getPointerOperand(), L->getModule()->getDataLayout(), S2, off2) && S2 &&
            S2->hasName() && stripStructNameSuffix(S2->getName()) == D.first && off2 == D.second) {
          out.push_back({objKey(L, L->getPointerOperand(), S2) == obj ? 's' : 'x', -1, 0});
          return true;
        }
        return false;
      }
      if (const auto *Ar = dyn_cast<Argument>(V)) {
        const Function *F = Ar->getParent();
        if (!CFLWholeProgram || F->hasAddressTaken()) return false;
        size_t sites = 0;
        const bool ok = fixpoint(Ar, [&](std::vector<Term> &acc) {
          sites = 0;
          for (const User *U : F->users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (!CB || CB->getCalledOperand() != F) return false;
            sites++;
            if (!ev(CB->getArgOperand(Ar->getArgNo()), depth + 1, acc)) return false;
          }
          return true;
        }, out);
        if (ok && sites)
          T.via.push_back(F->getName().str() + " arg" + std::to_string(Ar->getArgNo()) + " from " +
                          std::to_string(sites) + " call sites");
        return ok;
      }
      return false;
    };
    std::vector<Term> ts;
    if (!ev(S->getValueOperand(), 0, ts)) { T.unknown = true; return; }
    // The store keeps the tag's width.
    const unsigned w = S->getValueOperand()->getType()->getIntegerBitWidth();
    const int64_t m = w >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << w) - 1);
    std::set<std::tuple<char, int64_t, int64_t, int64_t>> seen;
    for (const Term &t : ts) {
      const bool c = t.src == 'c' || (t.a & m) == 0;
      const int64_t f = t.f & m;
      const Term n{c ? 'c' : t.src, c ? 0 : t.a & m & ~f, f, t.m & m & ~f};
      if (seen.insert({n.src, n.a, n.f, n.m}).second) T.terms.push_back(n);
    }
  };
  // ---- scan ----
  // The certificate a tag needs (plan 3.51 ruling A/B): every write to its
  // bytes is named or checked. Every store (atomics too) is classified by
  // the provenance of its pointer: named (a struct GEP or struct-path TBAA:
  // it covers those bytes of that struct), into a declared object (an
  // alloca or global: the bytes of its type, char data when no struct is
  // nested there), or from a root whose provenance is not local (a
  // parameter, a loaded or returned pointer): watched in the solve. A cover
  // of a tag's bytes by a store that is not one of its own (co-)writes
  // refuses the pair; memset fill bytes are constant retags.
  struct Cover { int64_t lo, hi; const Instruction *I; };
  std::map<std::string, std::vector<Cover>> covers; // by struct name
  std::vector<TaggedWatch> watchCand;
  size_t storesNamed = 0, storesChar = 0, storesStruct = 0, storesWatched = 0, storesUnwatchable = 0;
  std::string unwatchableAt;
  using Field0 = std::pair<std::string, int64_t>;
  std::map<Field0, std::string> escapedAt; // fields whose address escapes
  std::set<int64_t> memsetFills;
  bool memsetUnknown = false;
  std::string memsetUnknownAt;
  std::function<bool(Type *)> nestsStruct = [&](Type *T) {
    if (auto *ST = dyn_cast<StructType>(T)) return ST->hasName() || !ST->isOpaque();
    if (auto *AT = dyn_cast<ArrayType>(T)) return nestsStruct(AT->getElementType());
    return false;
  };
  // Store I writes w bytes at start positions [lo, hi] of an L (an array of
  // L: positions fold modulo its size; unb: anywhere). True if a named
  // struct lies under them.
  auto addCover = [&](Type *L, int64_t lo, int64_t hi, bool unb, int64_t w, const Instruction *I,
                      const DataLayout &DL) {
    const int64_t sz = L->isSized() ? (int64_t)DL.getTypeAllocSize(L) : 0;
    if (sz == 0) return false;
    int64_t a = 0, b = sz;
    if (!unb && hi + w - lo < sz) {
      a = ((lo % sz) + sz) % sz;
      b = a + (hi - lo) + w;
    }
    bool any = false;
    auto visit = [&](StructType *ST, int64_t l, int64_t h) {
      covers[stripStructNameSuffix(ST->getName()).str()].push_back({l, h, I});
      any = true;
    };
    structCover(L, a, std::min(b, sz), DL, visit);
    if (b > sz) structCover(L, 0, b - sz, DL, visit);
    return any;
  };
  // The roots a pointer comes from, with the byte range relative to each:
  // a typed object or struct GEP ('o', a cover of L), a watched root
  // ('w'), or none the solver could tell ('u'). The roots of an -O0 local
  // slot are computed once and shifted per use.
  struct WPos { int64_t lo, hi; bool unb; };
  struct Leaf { char kind; const Value *V; Type *L; WPos P; };
  std::map<const AllocaInst *, std::vector<Leaf>> slotLeaves;
  std::set<const AllocaInst *> slotBusy;
  std::function<void(std::vector<std::pair<const Value *, WPos>>, const DataLayout &, std::vector<Leaf> &)> walk =
      [&](std::vector<std::pair<const Value *, WPos>> work, const DataLayout &DL, std::vector<Leaf> &out) {
    std::map<const Value *, WPos> seenW;
    std::map<const AllocaInst *, WPos> seenSlot;
    auto shifted = [](WPos Q, WPos P) { return WPos{Q.lo + P.lo, Q.hi + P.hi, Q.unb || P.unb}; };
    while (!work.empty()) {
      auto [V, P] = work.back();
      work.pop_back();
      auto [sit, ins] = seenW.try_emplace(V, P);
      if (!ins) {
        WPos &Q = sit->second;
        if (Q.unb || (!P.unb && P.lo >= Q.lo && P.hi <= Q.hi)) continue;
        Q.unb = P.unb = true; // around a cycle (a pointer walk): anywhere
      }
      if (seenW.size() > 4096) { out.push_back({'u', V, nullptr, P}); return; }
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) continue;
      if (const auto *GA = dyn_cast<GlobalAlias>(V)) { work.push_back({GA->getAliasee(), P}); continue; }
      if (const auto *G = dyn_cast<GEPOperator>(V)) {
        if (G->getType()->isVectorTy()) { out.push_back({'u', V, nullptr, P}); continue; }
        Type *Src = G->getSourceElementType();
        int64_t off = 0, span = 0, first = 0;
        bool vunb = false, firstVar = false;
        Type *cur = Src;
        unsigned k = 0;
        for (auto It = G->idx_begin(); It != G->idx_end(); ++It, ++k) {
          const auto *C = dyn_cast<ConstantInt>(*It);
          if (k == 0) {
            if (C) first = C->getSExtValue();
            else firstVar = true;
            continue;
          }
          if (auto *ST = dyn_cast<StructType>(cur)) {
            const unsigned fi = (unsigned)C->getZExtValue();
            off += (int64_t)DL.getStructLayout(ST)->getElementOffset(fi);
            cur = ST->getElementType(fi);
            continue;
          }
          Type *E = nullptr;
          uint64_t n = 0;
          if (auto *AT = dyn_cast<ArrayType>(cur)) E = AT->getElementType(), n = AT->getNumElements();
          else if (auto *VT = dyn_cast<FixedVectorType>(cur)) E = VT->getElementType(), n = VT->getNumElements();
          if (!E) { vunb = true; break; }
          const int64_t es = (int64_t)DL.getTypeAllocSize(E);
          if (C) off += C->getSExtValue() * es;
          else if (n) span += (int64_t)(n - 1) * es;
          else vunb = true;
          cur = E;
        }
        if (nestsStruct(Src)) { // typed: the base is a Src (array): class (ii)
          out.push_back({'o', V, Src, {P.lo + off, P.hi + off + span, P.unb || vunb}});
          continue;
        }
        const int64_t srcSz = Src->isSized() ? (int64_t)DL.getTypeAllocSize(Src) : 0;
        work.push_back({G->getPointerOperand(),
                        {P.lo + off + first * srcSz, P.hi + off + span + first * srcSz,
                         P.unb || vunb || (firstVar && srcSz != 0)}});
        continue;
      }
      if (isa<BitCastOperator>(V) || isa<AddrSpaceCastOperator>(V) || isa<FreezeInst>(V)) {
        work.push_back({cast<User>(V)->getOperand(0), P});
        continue;
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        for (const Value *In : PN->incoming_values()) work.push_back({In, P});
        continue;
      }
      if (const auto *SI = dyn_cast<SelectInst>(V)) {
        work.push_back({SI->getTrueValue(), P});
        work.push_back({SI->getFalseValue(), P});
        continue;
      }
      if (const auto *L = dyn_cast<LoadInst>(V)) {
        // A non-escaping local slot (the -O0 pointer variable): the roots
        // of the values stored into it, computed once per slot.
        if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          if (const auto *vals = ids.storedInto(A)) {
            auto lit = slotLeaves.find(A);
            if (lit == slotLeaves.end() && slotBusy.insert(A).second) {
              std::vector<std::pair<const Value *, WPos>> w0;
              for (const Value *X : *vals) w0.push_back({X, {0, 0, false}});
              std::vector<Leaf> ls;
              walk(std::move(w0), DL, ls);
              slotBusy.erase(A);
              std::set<std::tuple<char, const Value *, int64_t, int64_t, bool>> dd;
              std::vector<Leaf> uniq;
              for (const Leaf &l : ls)
                if (dd.insert({l.kind, l.V, l.P.lo, l.P.hi, l.P.unb}).second) uniq.push_back(l);
              lit = slotLeaves.emplace(A, std::move(uniq)).first;
            }
            if (lit != slotLeaves.end()) {
              for (const Leaf &l : lit->second) out.push_back({l.kind, l.V, l.L, shifted(l.P, P)});
              continue;
            }
            // On the slot's own definition cycle: expanded here, once.
            auto [qit, qins] = seenSlot.try_emplace(A, P);
            if (!qins) {
              WPos &Q = qit->second;
              if (Q.unb || (!P.unb && P.lo >= Q.lo && P.hi <= Q.hi)) continue;
              Q.unb = P.unb = true;
            }
            for (const Value *X : *vals) work.push_back({X, P});
            continue;
          }
      }
      if (isa<AllocaInst>(V) || isa<GlobalVariable>(V)) {
        Type *L = isa<AllocaInst>(V) ? cast<AllocaInst>(V)->getAllocatedType()
                                     : cast<GlobalVariable>(V)->getValueType();
        out.push_back({'o', V, L, P});
        continue;
      }
      if (isa<Argument>(V) || isa<LoadInst>(V) || isa<CallBase>(V) || isa<ExtractValueInst>(V)) {
        out.push_back({'w', V, nullptr, P});
        continue;
      }
      out.push_back({'u', V, nullptr, P}); // inttoptr, or another pointer source the solver has no facts for
    }
  };
  auto classify = [&](const Instruction *I, const Value *Addr, int64_t w, const DataLayout &DL) {
    StructType *S0 = nullptr;
    int64_t o0 = 0;
    if (accessSlot(I, Addr, DL, S0, o0) && S0 && S0->hasName()) {
      addCover(S0, o0, o0, false, w, I, DL);
      storesNamed++;
      return;
    }
    std::vector<Leaf> leaves;
    walk({{Addr, {0, 0, false}}}, DL, leaves);
    bool unwatch = false, anyStruct = false, anyWatch = false;
    for (const Leaf &l : leaves) {
      if (l.kind == 'u') unwatch = true;
      else if (l.kind == 'o') anyStruct |= addCover(l.L, l.P.lo, l.P.hi, l.P.unb, w, I, DL);
      else {
        watchCand.push_back({l.V, l.P.lo, l.P.hi, l.P.unb, (unsigned)w, I});
        anyWatch = true;
      }
    }
    if (unwatch) {
      if (!storesUnwatchable++) unwatchableAt = locOf(I);
      return;
    }
    if (anyWatch) storesWatched++;
    else if (anyStruct) storesStruct++;
    else storesChar++;
  };
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        if (const auto *MS = dyn_cast<MemSetInst>(&I)) {
          if (const auto *K = dyn_cast<ConstantInt>(MS->getValue())) memsetFills.insert(K->getZExtValue() & 0xff);
          else if (!memsetUnknown) { memsetUnknown = true; memsetUnknownAt = locOf(&I); }
          continue;
        }
        if (const auto *SI = dyn_cast<StoreInst>(&I))
          classify(SI, SI->getPointerOperand(), (int64_t)DL.getTypeStoreSize(SI->getValueOperand()->getType()), DL);
        else if (const auto *RMW = dyn_cast<AtomicRMWInst>(&I))
          classify(RMW, RMW->getPointerOperand(), (int64_t)DL.getTypeStoreSize(RMW->getValOperand()->getType()), DL);
        else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(&I))
          classify(CX, CX->getPointerOperand(), (int64_t)DL.getTypeStoreSize(CX->getNewValOperand()->getType()), DL);
        // A field whose address escapes (used other than as a load or store
        // address) may be written unnamed.
        if (const GEPOperator *FG = dyn_cast<GEPOperator>(&I); FG && structGEP(&I) == FG) {
          StructType *S0 = dyn_cast<StructType>(FG->getSourceElementType());
          APInt Ap(64, 0);
          if (S0 && S0->hasName() && FG->accumulateConstantOffset(DL, Ap))
            for (const User *U : I.users()) {
              if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == &I) continue;
              if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand() == &I) continue;
              if (isa<DbgInfoIntrinsic>(U)) continue;
              const Field ef{stripStructNameSuffix(S0->getName()).str(), Ap.getSExtValue()};
              if (escapedAt.emplace(ef, locOf(&I)).second) {}
              break;
            }
        }
        const Value *Addr = nullptr;
        Type *T = nullptr;
        if (const auto *L = dyn_cast<LoadInst>(&I)) Addr = L->getPointerOperand(), T = L->getType();
        else if (const auto *S = dyn_cast<StoreInst>(&I)) Addr = S->getPointerOperand(), T = S->getValueOperand()->getType();
        else continue;
        StructType *ST = nullptr;
        int64_t off = 0;
        if (!accessSlot(&I, Addr, DL, ST, off) || !ST || !ST->hasName()) continue;
        const Field fld{stripStructNameSuffix(ST->getName()).str(), off};
        const Value *obj = objKey(&I, Addr, ST);
        if (T->isPointerTy()) (isa<StoreInst>(&I) ? fStores : fLoads)[fld].push_back({&I, obj});
        else if (T->isIntegerTy() && isa<StoreInst>(&I)) {
          TagStore TS{cast<StoreInst>(&I), obj};
          analyzeTag(cast<StoreInst>(&I), obj, fld, TS);
          dStores[fld].push_back(std::move(TS));
        }
      }
  }
  // ---- per (S, F, D): writers, retags, reads ----
  size_t pairsUncertified = 0;
  size_t pairsKeyed = 0, readsKeyed = 0, readsNoTest = 0, readsAll = 0, pairsNonConst = 0,
         writersUntagged = 0, writersTagged = 0;
  std::map<const Function *, std::unique_ptr<DominatorTree>> doms;
  auto domOf = [&](const Function *F) -> DominatorTree & {
    auto &P = doms[F];
    if (!P) P = std::make_unique<DominatorTree>(const_cast<Function &>(*F));
    return *P;
  };
  // Per function, once: conditional branches whose condition's only leaf
  // is one load of a struct field (the candidate tag tests).
  struct FnTest { const BranchInst *Br; const LoadInst *dl; std::string S; int64_t off; const Value *obj; };
  std::map<const Function *, std::vector<FnTest>> fnTests;
  auto fnTestsOf = [&](const Function *Fn) -> const std::vector<FnTest> & {
    auto [it, ins] = fnTests.try_emplace(Fn);
    if (!ins) return it->second;
    for (const BasicBlock &BB : *Fn) {
      const auto *Br = dyn_cast<BranchInst>(BB.getTerminator());
      if (!Br || !Br->isConditional()) continue;
      const LoadInst *dl = nullptr;
      bool clean = true;
      std::vector<const Value *> work{Br->getCondition()};
      std::set<const Value *> seen;
      while (!work.empty() && clean) {
        const Value *X = work.back();
        work.pop_back();
        if (!seen.insert(X).second) continue;
        if (isa<ConstantInt>(X)) continue;
        if (const auto *L = dyn_cast<LoadInst>(X)) {
          if (dl && dl != L) clean = false;
          dl = L;
          continue;
        }
        if (isa<ICmpInst>(X) || isa<CastInst>(X) ||
            (isa<BinaryOperator>(X) && (cast<BinaryOperator>(X)->getOpcode() == Instruction::And ||
                                        cast<BinaryOperator>(X)->getOpcode() == Instruction::Or ||
                                        cast<BinaryOperator>(X)->getOpcode() == Instruction::Xor))) {
          for (const Value *Op : cast<User>(X)->operands()) work.push_back(Op);
          continue;
        }
        clean = false;
      }
      if (!clean || !dl) continue;
      StructType *S2 = nullptr;
      int64_t o2 = 0;
      if (!accessSlot(dl, dl->getPointerOperand(), dl->getModule()->getDataLayout(), S2, o2) || !S2 ||
          !S2->hasName())
        continue;
      it->second.push_back({Br, dl, stripStructNameSuffix(S2->getName()).str(), o2, objKey(dl, dl->getPointerOperand(), S2)});
    }
    return it->second;
  };
  for (auto &[Ff, fs] : fStores) {
    const std::string &S = Ff.first;
    // Candidate discriminators: integer fields of S stored in a function
    // that also stores F on the same object.
    std::set<int64_t> dOffs;
    for (const FAccess &w : fs)
      for (auto &[Df, ds] : dStores)
        if (Df.first == S && Df.second != Ff.second)
          for (const TagStore &t : ds)
            if (t.I->getFunction() == w.I->getFunction() && t.obj == w.obj) dOffs.insert(Df.second);
    for (int64_t dOff : dOffs) {
      const Field Df{S, dOff};
      const auto &ds = dStores[Df];
      // Writers and their tags; retags.
      std::set<std::pair<const Function *, const Value *>> coWriting;
      for (const FAccess &w : fs) coWriting.insert({w.I->getFunction(), w.obj});
      // A writer's tags: its constants, and the images of every reachable
      // tag under its terms over a tag (its object's previous one, or
      // another object's).
      struct Writer {
        const Instruction *I;
        std::set<int64_t> tags;
        std::vector<Term> fromAny; // maps of a tag: (u & a) | f | sub(m)
        bool unknown = false;
      };
      std::vector<Writer> writers;
      std::vector<const TagStore *> retags;
      bool nonConstRetag = false;
      for (const TagStore &t : ds)
        if (!coWriting.count({t.I->getFunction(), t.obj})) {
          retags.push_back(&t);
          nonConstRetag |= t.unknown;
        }
      std::set<std::string> via;
      for (const FAccess &w : fs) {
        Writer W{w.I};
        bool co = false;
        for (const TagStore &t : ds)
          if (t.I->getFunction() == w.I->getFunction() && t.obj == w.obj) {
            co = true;
            if (t.unknown) W.unknown = true;
            via.insert(t.via.begin(), t.via.end());
            for (const Term &tm : t.terms)
              if (tm.src != 'c') W.fromAny.push_back(tm);
              else if (!concretize({tm}, W.tags)) W.unknown = true;
          }
        if (!co) W.unknown = true;
        writers.push_back(std::move(W));
      }
      // The tag must be certified: every store covering its bytes is one
      // of its own named writes, or watched in the solve.
      unsigned dWidth = 0;
      for (const TagStore &t : ds) dWidth = t.I->getValueOperand()->getType()->getIntegerBitWidth();
      const int64_t dBytes = dWidth / 8;
      std::set<const Instruction *> own;
      for (const TagStore &t : ds) own.insert(t.I);
      const Instruction *coveredBy = nullptr;
      if (auto cit = covers.find(S); cit != covers.end())
        for (const Cover &c : cit->second)
          if (c.lo < dOff + dBytes && dOff < c.hi && !(c.lo == dOff && c.hi == dOff + dBytes && own.count(c.I))) {
            coveredBy = c.I;
            break;
          }
      if (coveredBy || storesUnwatchable || escapedAt.count(Df)) {
        pairsUncertified++;
        if (fs.size() >= 10)
          taggedReport.push_back("UNKEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                                 std::to_string(dOff) + ": tag not certified (" +
                                 (escapedAt.count(Df) ? "its address escapes at " + escapedAt[Df]
                                  : coveredBy ? "an unnamed or wider store covers it at " + locOf(coveredBy)
                                              : "a store with no watchable pointer, e.g. " + unwatchableAt) + ")");
        continue;
      }
      if (memsetUnknown) {
        pairsNonConst++;
        continue;
      }
      if (nonConstRetag) {
        pairsNonConst++;
        if (fs.size() >= 10) {
          const Instruction *at = nullptr;
          for (const TagStore *t : retags) if (t->unknown) { at = t->I; break; }
          taggedReport.push_back("UNKEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                                 std::to_string(dOff) + " (" + std::to_string(fs.size()) +
                                 " writes): non-constant retag at " + locOf(at) + " (" +
                                 std::to_string(std::count_if(retags.begin(), retags.end(),
                                     [](const TagStore *t) { return t->unknown; })) + " of " +
                                 std::to_string(retags.size()) + " retags)");
          if (VerboseLevel >= 2)
            for (const TagStore *t : retags)
              if (t->unknown) {
                std::string v;
                raw_string_ostream os(v);
                t->I->getValueOperand()->print(os);
                taggedReport.push_back("    non-constant retag " + locOf(t->I) + ": " + os.str().substr(0, 90));
              }
        }
        continue;
      }
      // Tags reachable from each writer through the retags: constants,
      // transforms of the object's own tag, images of any object's tag.
      // U: every tag the field can hold (the closure of all constants under
      // every transform and image).
      std::set<int64_t> sets;
      std::vector<Term> xforms, anyImgs;
      std::vector<std::string> xformAt;
      bool setsAll = false;
      auto termStr = [](const Term &tm) {
        std::string d = tm.src == 'c' ? "" : std::string(1, tm.src) + "&" + std::to_string(tm.a) + "|";
        d += std::to_string(tm.f);
        if (tm.m) d += "|free " + std::to_string(tm.m);
        return d;
      };
      for (const TagStore *t : retags) {
        via.insert(t->via.begin(), t->via.end());
        bool sym = false;
        for (const Term &tm : t->terms) {
          if (tm.src == 'c') setsAll |= !concretize({tm}, sets);
          else (tm.src == 's' ? xforms : anyImgs).push_back(tm), sym = true;
        }
        if (sym && xformAt.size() < 4) {
          std::string d = locOf(t->I) + " {";
          for (const Term &tm : t->terms) d += std::string(d.back() == '{' ? "" : ", ") + termStr(tm);
          xformAt.push_back(d + "}");
        }
      }
      for (int64_t b : memsetFills) { // the fill byte repeated over the tag
        int64_t v = 0;
        for (unsigned k = 0; k < dWidth / 8; k++) v = (v << 8) | b;
        sets.insert(v);
      }
      // The images of v under a map (u & a) | f | sub(m).
      auto images = [](int64_t v, const Term &t, std::vector<int64_t> &out) {
        const uint64_t fr = (uint64_t)t.m;
        if (llvm::popcount(fr) > 12) return false;
        for (uint64_t sub = fr;; sub = (sub - 1) & fr) {
          out.push_back((v & t.a) | t.f | (int64_t)sub);
          if (!sub) break;
        }
        return true;
      };
      auto closure = [&](std::set<int64_t> R, const std::vector<Term> &maps, bool &all) {
        std::vector<int64_t> work(R.begin(), R.end()), img;
        while (!work.empty() && !all) {
          const int64_t v = work.back();
          work.pop_back();
          for (const Term &t : maps) {
            img.clear();
            if (!images(v, t, img)) { all = true; break; }
            for (int64_t w : img)
              if (R.insert(w).second) work.push_back(w);
            if (R.size() > 4096) all = true;
          }
        }
        return R;
      };
      std::set<int64_t> U0 = sets;
      std::vector<Term> allMaps = xforms;
      allMaps.insert(allMaps.end(), anyImgs.begin(), anyImgs.end());
      for (const Writer &W : writers) {
        U0.insert(W.tags.begin(), W.tags.end());
        allMaps.insert(allMaps.end(), W.fromAny.begin(), W.fromAny.end());
      }
      bool uAll = setsAll;
      const std::set<int64_t> U = closure(U0, allMaps, uAll);
      std::set<int64_t> base = sets; // what retags may set on any object
      {
        std::vector<int64_t> img;
        for (const Term &t : anyImgs)
          for (int64_t u : U) {
            img.clear();
            if (!images(u, t, img)) uAll = true;
            base.insert(img.begin(), img.end());
          }
      }
      std::vector<std::set<int64_t>> wTags(writers.size());
      std::vector<bool> wAll(writers.size(), false);
      for (size_t i = 0; i < writers.size(); i++) {
        if (writers[i].unknown || setsAll || (uAll && (!writers[i].fromAny.empty() || !anyImgs.empty()))) {
          wAll[i] = true;
          continue;
        }
        std::set<int64_t> from = writers[i].tags;
        from.insert(base.begin(), base.end());
        std::vector<int64_t> img;
        bool imgAll = false;
        for (const Term &t : writers[i].fromAny)
          for (int64_t u : U) {
            img.clear();
            imgAll |= !images(u, t, img);
            from.insert(img.begin(), img.end());
          }
        if (imgAll) { wAll[i] = true; continue; }
        bool all = false;
        wTags[i] = closure(from, xforms, all);
        wAll[i] = all;
      }
      // Reads: the tests of D (same object) dominating them.
      struct Test { const Value *cond; const LoadInst *d; bool onTrue; };
      std::vector<std::pair<const Instruction *, std::vector<size_t>>> keyed;
      size_t pairReadsKeyed = 0;
      for (const FAccess &r : fLoads[Ff]) {
        const Function *Fn = r.I->getFunction();
        DominatorTree &DT = domOf(Fn);
        std::vector<Test> tests;
        for (const FnTest &ft : fnTestsOf(Fn)) {
          if (ft.S != S || ft.off != dOff || ft.obj != r.obj) continue;
          for (unsigned si = 0; si < 2; si++) {
            const BasicBlock *Succ = ft.Br->getSuccessor(si);
            if (Succ->getSinglePredecessor() == ft.Br->getParent() && DT.dominates(Succ, r.I->getParent()))
              tests.push_back({ft.Br->getCondition(), ft.dl, si == 0});
          }
        }
        if (tests.empty()) { readsNoTest++; continue; }
        // Evaluate a test with the tag = v.
        std::function<std::optional<int64_t>(const Value *, const LoadInst *, int64_t)> eval =
            [&](const Value *X, const LoadInst *dl, int64_t v) -> std::optional<int64_t> {
          if (X == dl) return v;
          if (const auto *K = dyn_cast<ConstantInt>(X)) return K->getSExtValue();
          if (const auto *C = dyn_cast<CastInst>(X)) {
            auto a = eval(C->getOperand(0), dl, v);
            if (!a) return std::nullopt;
            if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) return std::nullopt;
            const unsigned bw = C->getType()->getIntegerBitWidth(),
                           sb = C->getOperand(0)->getType()->getIntegerBitWidth();
            if (isa<TruncInst>(C)) return bw < 64 ? *a & ((int64_t(1) << bw) - 1) : *a;
            if (isa<ZExtInst>(C)) return sb < 64 ? *a & ((int64_t(1) << sb) - 1) : *a;
            if (isa<SExtInst>(C)) return APInt(sb, (uint64_t)*a).sext(64).getSExtValue();
            return std::nullopt;
          }
          if (const auto *BO = dyn_cast<BinaryOperator>(X)) {
            auto a = eval(BO->getOperand(0), dl, v), b = eval(BO->getOperand(1), dl, v);
            if (!a || !b) return std::nullopt;
            switch (BO->getOpcode()) {
            case Instruction::And: return *a & *b;
            case Instruction::Or: return *a | *b;
            case Instruction::Xor: return *a ^ *b;
            default: return std::nullopt;
            }
          }
          if (const auto *IC = dyn_cast<ICmpInst>(X)) {
            auto a = eval(IC->getOperand(0), dl, v), b = eval(IC->getOperand(1), dl, v);
            if (!a || !b) return std::nullopt;
            const unsigned bw = IC->getOperand(0)->getType()->getIntegerBitWidth();
            const APInt A(bw, (uint64_t)*a, true), B(bw, (uint64_t)*b, true);
            return (int64_t)ICmpInst::compare(A, B, IC->getPredicate());
          }
          return std::nullopt;
        };
        auto holds = [&](int64_t v) {
          for (const Test &t : tests) {
            auto r2 = eval(t.cond, t.d, v);
            if (!r2) continue; // not evaluable: no constraint
            if ((*r2 != 0) != t.onTrue) return false;
          }
          return true;
        };
        std::vector<size_t> adm;
        for (size_t i = 0; i < writers.size(); i++) {
          if (wAll[i]) { adm.push_back(i); continue; }
          for (int64_t v : wTags[i])
            if (holds(v)) { adm.push_back(i); break; }
        }
        if (adm.size() == writers.size()) { readsAll++; continue; }
        keyed.push_back({r.I, adm});
        pairReadsKeyed++;
      }
      if (keyed.empty()) {
        if (fs.size() >= 10) {
          size_t nAll = std::count(wAll.begin(), wAll.end(), true);
          std::string d = "PLAIN " + S + "+" + std::to_string(Ff.second) + " by +" + std::to_string(dOff) + " (" +
                          std::to_string(fs.size()) + " writes): every tested read admits every writer; " +
                          std::to_string(U.size()) + (uAll ? "+ (capped)" : "") + " tags, " +
                          std::to_string(nAll) + " writers with any tag";
          for (const std::string &x : xformAt) d += "; retag " + x;
          taggedReport.push_back(d);
        }
        continue;
      }
      // Install: each tagged writer its key; each keyed read the keys of the
      // writers it admits (untagged writers are plain stores every key reads).
      const std::string prefix = S + "+" + std::to_string(Ff.second) + "#";
      bool any = false;
      for (size_t i = 0; i < writers.size(); i++) {
        if (writers[i].unknown || unionKeyNames.count(writers[i].I)) { writersUntagged += writers[i].unknown; continue; }
        unionKeyNames[writers[i].I] = {prefix + "t" + std::to_string(dOff) + "w" + std::to_string(i)};
        writersTagged++;
        any = true;
      }
      for (auto &[I, adm] : keyed) {
        if (unionKeyNames.count(I)) continue;
        std::vector<std::string> ks;
        for (size_t i : adm)
          if (!writers[i].unknown) ks.push_back(prefix + "t" + std::to_string(dOff) + "w" + std::to_string(i));
        if (ks.empty()) ks.push_back(prefix + "t" + std::to_string(dOff) + "none");
        unionKeyNames[I] = ks;
        readsKeyed++;
      }
      if (!any) continue;
      pairsKeyed++;
      cellUnionSlots.insert({S.substr(S.rfind('.') + 1), Ff.second, 8});
      taggedPairs.push_back({S, Ff.second, dOff, (int64_t)(dWidth / 8)});
      std::string extra;
      for (const std::string &d : xformAt) extra += "; retag " + d;
      for (const std::string &v : via) extra += "; bound " + v;
      taggedReport.push_back("KEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                               std::to_string(dOff) + ": " + std::to_string(writers.size()) + " writers, " +
                               std::to_string(pairReadsKeyed) + " reads keyed, " +
                               std::to_string(retags.size()) + " retags, " + std::to_string(U.size()) +
                               " tags" + extra);
    }
  }
  if (pairsKeyed) {
    std::set<std::tuple<const Value *, int64_t, int64_t, bool, unsigned>> seenWatch;
    for (const TaggedWatch &w : watchCand)
      if (seenWatch.insert({w.root, w.lo, w.hi, w.unb, w.w}).second) taggedWatches.push_back(w);
  }
  CG_LOG("TaggedFields: stores by pointer provenance: " << storesNamed << " named, " << storesStruct
         << " into struct objects, " << storesChar << " char/scalar data, " << storesWatched << " watched ("
         << taggedWatches.size() << " watches installed), " << storesUnwatchable << " unwatchable"
         << (storesUnwatchable ? " (e.g. " + unwatchableAt + ")" : std::string()) << "\n");
  CG_LOG("TaggedFields: " << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count()
         << " s; " << pairsKeyed << " pairs keyed (" << writersTagged << " tagged writers, "
         << writersUntagged << " untagged: no co-written tag in the writer's function); reads: "
         << readsKeyed << " keyed, " << readsNoTest << " with no dominating test, " << readsAll
         << " admitting every writer; " << pairsNonConst << " pairs unkeyed by a non-constant retag, "
         << pairsUncertified << " by an uncertified tag\n");
  if (VerboseLevel >= 2)
    for (const std::string &l : taggedReport) CG_LOG("TaggedFields:   " << l << "\n");
  taggedCounts = {pairsKeyed, writersTagged, writersUntagged, readsKeyed, readsNoTest, readsAll, pairsNonConst};
}
