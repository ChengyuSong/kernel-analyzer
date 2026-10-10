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
#include <llvm/Support/KnownBits.h>
#include <chrono>
#include <deque>

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
    std::map<const LoadInst *, const StoreInst *> def; // the one store a reload reads
  };
  std::map<const AllocaInst *, SlotInfo> slots;
  std::map<const Value *, const BasicBlock *> phiBlock; // a merge's name -> the block it is at
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
    // The definition each reload reads, as mem2reg would build it: a store,
    // the entry value, or a merge of different definitions (a phi at the
    // block where they meet). Reloads reading the same definition read the
    // same value; a phi is named by its first reload.
    const Function &F = *A->getFunction();
    const int n = (int)stores.size();
    std::map<const StoreInst *, int> idx;
    for (int k = 0; k < n; k++) idx[stores[k]] = k;
    std::map<const BasicBlock *, int> bix;
    for (const BasicBlock &BB : F) bix[&BB] = (int)bix.size();
    std::map<const BasicBlock *, const StoreInst *> lastIn;
    for (const StoreInst *S : stores) {
      const StoreInst *&L = lastIn[S->getParent()];
      if (!L || L->comesBefore(S)) L = S;
    }
    constexpr int kBot = -2, kEntry = -1; // not reached yet; the entry value
    std::map<const BasicBlock *, int> in, out;
    for (const BasicBlock &BB : F) in[&BB] = out[&BB] = kBot;
    for (bool changed = true; changed;) {
      changed = false;
      for (const BasicBlock &BB : F) {
        int I;
        if (&BB == &F.getEntryBlock()) I = kEntry;
        else {
          const int phi = n + bix[&BB];
          I = in[&BB] == phi ? phi : kBot;
          if (I != phi)
            for (const BasicBlock *P : predecessors(&BB)) {
              const int d = out[P];
              if (d == kBot) continue;
              if (I == kBot) I = d;
              else if (I != d) { I = phi; break; }
            }
        }
        const int O = lastIn.count(&BB) ? idx[lastIn[&BB]] : I;
        if (I != in[&BB] || O != out[&BB]) {
          in[&BB] = I;
          out[&BB] = O;
          changed = true;
        }
      }
    }
    std::map<int, const LoadInst *> phiRep;
    std::vector<const BasicBlock *> blockAt(bix.size());
    for (auto &[B, k] : bix) blockAt[k] = B;
    for (const BasicBlock &BB : F) {
      int cur = in[&BB];
      for (const Instruction &I : BB) {
        if (const auto *S = dyn_cast<StoreInst>(&I); S && idx.count(S)) {
          cur = idx[S];
          continue;
        }
        const auto *L = dyn_cast<LoadInst>(&I);
        if (!L || L->getPointerOperand() != A) continue;
        if (cur >= 0 && cur < n) SI.id[L] = stores[cur]->getValueOperand(), SI.def[L] = stores[cur];
        else if (cur >= n) {
          auto [pit, pins] = phiRep.try_emplace(cur, L);
          SI.id[L] = pit->second;
          if (pins) phiBlock[L] = blockAt[cur - n];
        } else SI.id[L] = L; // the entry value (or unreachable): this reload only
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
        if (SI.escapes) { // a slot written elsewhere: the reloads since the last write that may reach it
          const LoadInst *head = L;
          for (const Instruction *I = L->getPrevNode(); I; I = I->getPrevNode()) {
            if (const auto *L2 = dyn_cast<LoadInst>(I);
                L2 && L2->getPointerOperand()->stripPointerCasts() == A && !L2->isVolatile())
              head = L2;
            else if (I->mayWriteToMemory())
              break;
          }
          return head;
        }
        auto it = SI.id.find(L);
        assert(it != SI.id.end() && "every reload of a non-escaping slot has an identity");
        if (isa<LoadInst>(it->second) && it->second->getType()->isPointerTy() &&
            cast<LoadInst>(it->second)->getPointerOperand() == A)
          return it->second; // a run of reloads
        return of(it->second, 0, depth + 1);
      }
    // An element address (a variable index): the same base object and the
    // same index values name one element, whichever GEP computes it.
    if (const auto *G = dyn_cast<GEPOperator>(B)) {
      std::vector<std::pair<int, int64_t>> key;
      std::vector<const Value *> parts{of(G->getPointerOperand(), 0, depth + 1)};
      for (auto It = G->idx_begin(); It != G->idx_end(); ++It) {
        if (const auto *C = dyn_cast<ConstantInt>(*It)) key.push_back({0, C->getSExtValue()});
        else {
          const Value *iv = intId(*It, depth + 1);
          key.push_back({1, (int64_t)(intptr_t)iv});
          parts.push_back(iv);
        }
      }
      auto [it, ins] = gepRep.try_emplace({G->getSourceElementType(), parts[0], key}, B);
      if (ins) gepParts[B] = parts;
      return it->second;
    }
    return B;
  }
  // The identity of an integer value (an index): through casts and -O0
  // slots by their definitions.
  const Value *intId(const Value *V, int depth) {
    while (const auto *C = dyn_cast<CastInst>(V)) {
      if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) break;
      V = C->getOperand(0);
    }
    if (const auto *L = dyn_cast<LoadInst>(V))
      if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
        const SlotInfo &SI = slot(A);
        if (SI.escapes) return L;
        auto it = SI.id.find(L);
        if (it == SI.id.end()) return L;
        if (isa<LoadInst>(it->second) && cast<LoadInst>(it->second)->getPointerOperand() == A) return it->second;
        return depth < 8 ? intId(it->second, depth + 1) : it->second;
      }
    return V;
  }
  std::map<std::tuple<Type *, const Value *, std::vector<std::pair<int, int64_t>>>, const Value *> gepRep;
  std::map<const Value *, std::vector<const Value *>> gepParts; // an element's base and index identities
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
  // Where an identity's value is defined: an instruction (each execution
  // names another object), or a merge block (a phi). A walk that crosses
  // it meets another object under the same name: a barrier.
  // An element identity (a GEP over a base and indices) is defined where
  // any of its parts is.
  struct Defs { std::set<const Instruction *> insts; std::set<const BasicBlock *> blocks; };
  std::map<const Value *, Defs> defsMemo;
  std::function<const Defs &(const Value *)> defsOf = [&](const Value *id) -> const Defs & {
    auto [it, ins] = defsMemo.try_emplace(id);
    if (!ins) return it->second;
    Defs D;
    if (auto pit = ids.gepParts.find(id); pit != ids.gepParts.end()) {
      for (const Value *pv : pit->second)
        if (pv != id) {
          const Defs &P = defsOf(pv);
          D.insts.insert(P.insts.begin(), P.insts.end());
          D.blocks.insert(P.blocks.begin(), P.blocks.end());
        }
    } else if (auto bit = ids.phiBlock.find(id); bit != ids.phiBlock.end()) D.blocks.insert(bit->second);
    else if (const auto *I = dyn_cast<Instruction>(id)) D.insts.insert(I);
    return defsMemo[id] = std::move(D);
  };
  auto objKey = [&](const Instruction *I, const Value *Addr, StructType *S) {
    const DataLayout &DL = I->getModule()->getDataLayout();
    return ids.of(Addr, S && S->isSized() ? (int64_t)DL.getTypeAllocSize(S) : 0);
  };
  // Pointer-equality identity merges (plan 3.51): inside the blocks
  // dominated by the equal edge of a test `X == Y` (the true successor of
  // icmp eq, the false one of icmp ne, entered only from the test), the two
  // identities name one object. Operands must be identity pointers (by
  // reaching definitions), not derived ones (a GEP).
  struct EqRegion { const Value *X, *Y; const BasicBlock *succ; const Instruction *site; };
  std::map<const Function *, std::vector<EqRegion>> eqRegionsMemo;
  std::map<const Function *, std::unique_ptr<DominatorTree>> eqDoms;
  std::set<const Instruction *> eqMergeSites;
  auto eqRegionsOf = [&](const Function *Fn) -> const std::vector<EqRegion> & {
    auto [it, ins] = eqRegionsMemo.try_emplace(Fn);
    if (!ins) return it->second;
    auto idOfPtr = [&](const Value *V) -> const Value * {
      V = V->stripPointerCasts();
      if (isa<GEPOperator>(V) || isa<Constant>(V)) return nullptr;
      return ids.of(V, 0);
    };
    for (const BasicBlock &BB : *Fn) {
      const auto *Br = dyn_cast<BranchInst>(BB.getTerminator());
      if (!Br || !Br->isConditional()) continue;
      const auto *IC = dyn_cast<ICmpInst>(Br->getCondition());
      if (!IC || !IC->getOperand(0)->getType()->isPointerTy() || !IC->isEquality()) continue;
      const Value *X = idOfPtr(IC->getOperand(0)), *Y = idOfPtr(IC->getOperand(1));
      if (!X || !Y || X == Y) continue;
      const BasicBlock *Succ = Br->getSuccessor(IC->getPredicate() == ICmpInst::ICMP_EQ ? 0 : 1);
      if (Succ->getSinglePredecessor() != &BB) continue;
      it->second.push_back({X, Y, Succ, Br});
    }
    return it->second;
  };
  // Do a and b name one object at I?
  auto sameObj = [&](const Value *a, const Value *b, const Instruction *I) {
    if (a == b) return true;
    if (!a || !b || !I) return false;
    const Function *Fn = I->getFunction();
    for (const EqRegion &R : eqRegionsOf(Fn))
      if ((R.X == a && R.Y == b) || (R.X == b && R.Y == a)) {
        auto &DT = eqDoms[Fn];
        if (!DT) DT = std::make_unique<DominatorTree>(const_cast<Function &>(*Fn));
        if (DT->dominates(R.succ, I->getParent())) {
          eqMergeSites.insert(R.site);
          return true;
        }
      }
    return false;
  };
  taggedReport.clear();
  taggedPairs.clear();
  taggedPairAssumes.clear();
  taggedAssumes.clear();
  taggedAccessSets.clear();
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
  struct Term {
    char src;
    int64_t a, f, m;
    const Value *who = nullptr; // evaluation only: the object a symbolic term's tag was read from
  };
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
          for (Term t : in) out.push_back({t.src, t.a & m, t.f & m, t.m & m, t.who});
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
            r.who = p.a ? p.who : q.who;
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
          // The one store reaching this reload, when there is one.
          const ObjIds::SlotInfo &SI = ids.slot(A);
          // A value stored inside a pointer-equality region carries the merge
          // out of it: a tag read from one of the two names is the other's.
          auto relabel = [&](std::vector<Term> &ts, size_t from, const Instruction *St) {
            for (size_t q = from; q < ts.size(); q++)
              if (ts[q].src == 'x' && ts[q].who && sameObj(ts[q].who, obj, St)) ts[q].src = 's';
          };
          if (auto dit = SI.def.find(L); dit != SI.def.end()) {
            const size_t mark = out.size();
            if (!ev(dit->second->getValueOperand(), depth + 1, out)) return false;
            relabel(out, mark, dit->second);
            return true;
          }
          if (auto it = SI.id.find(L); it != SI.id.end() &&
              !(isa<LoadInst>(it->second) && cast<LoadInst>(it->second)->getPointerOperand() == A))
            return ev(it->second, depth + 1, out);
          const auto *vals = ids.storedInto(A);
          if (vals->empty()) return false;
          return fixpoint(A, [&](std::vector<Term> &acc) {
            for (const User *U : A->users())
              if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand() == A &&
                                                          St->getValueOperand() != A) {
                const size_t mark = acc.size();
                if (!ev(St->getValueOperand(), depth + 1, acc)) return false;
                relabel(acc, mark, St);
              }
            return true;
          }, out);
        }
        StructType *S2 = nullptr;
        int64_t off2 = 0;
        if (L->getType()->isIntegerTy() &&
            accessSlot(L, L->getPointerOperand(), L->getModule()->getDataLayout(), S2, off2) && S2 &&
            S2->hasName() && stripStructNameSuffix(S2->getName()) == D.first && off2 == D.second) {
          const Value *who = objKey(L, L->getPointerOperand(), S2);
          out.push_back({sameObj(who, obj, L) ? 's' : 'x', -1, 0, 0, who});
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
  // memset fills, by the struct bytes they may cover (classified like
  // stores: typed objects and struct GEPs cover, char data is ignored,
  // other roots are watched in the solve); fill -1: not a constant.
  struct Fill { int64_t lo, hi; int fill; const Instruction *I; };
  std::map<std::string, std::vector<Fill>> fillsOf;
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
          const auto *K = dyn_cast<ConstantInt>(MS->getValue());
          const int fill = K ? (int)(K->getZExtValue() & 0xff) : -1;
          const auto *LN = dyn_cast<ConstantInt>(MS->getLength());
          const int64_t len = LN ? (int64_t)LN->getZExtValue() : -1;
          std::vector<Leaf> leaves;
          walk({{MS->getDest(), {0, 0, false}}}, DL, leaves);
          bool unwatch = false;
          for (const Leaf &l : leaves) {
            if (l.kind == 'u') { unwatch = true; continue; }
            if (l.kind == 'w') {
              watchCand.push_back({l.V, l.P.lo, l.P.hi, l.P.unb || len < 0, (unsigned)std::max<int64_t>(len, 1), &I});
              continue;
            }
            const int64_t sz = l.L->isSized() ? (int64_t)DL.getTypeAllocSize(l.L) : 0;
            if (sz == 0) continue;
            int64_t a = 0, b = sz;
            if (!l.P.unb && len >= 0 && l.P.hi + len - l.P.lo < sz) {
              a = ((l.P.lo % sz) + sz) % sz;
              b = a + (l.P.hi - l.P.lo) + len;
            }
            auto visit = [&](StructType *ST, int64_t lo, int64_t hi) {
              fillsOf[stripStructNameSuffix(ST->getName()).str()].push_back({lo, hi, fill, &I});
            };
            structCover(l.L, a, std::min(b, sz), DL, visit);
            if (b > sz) structCover(l.L, 0, b - sz, DL, visit);
          }
          if (unwatch && !storesUnwatchable++) unwatchableAt = locOf(&I);
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
  // Path stability (plan 3.51, ruling beta): a test of D speaks for an
  // access only if no write to D can come between them. May-write-D per
  // function: a store named (S, D), or a direct call of such a function,
  // or an indirect call when such a function's address is taken (least
  // fixpoint). Calls of bodiless functions are assumed to write no struct
  // slot (the holder-guard premise, reported there); byte copies over D
  // flip the pair in the solve.
  std::map<const Function *, std::vector<const CallBase *>> callsOf;
  std::map<const Function *, std::vector<const Function *>> callersOf;
  std::vector<const Function *> indirectCallers;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M) {
      bool ind = false;
      for (Instruction &I : instructions(F))
        if (const auto *CB = dyn_cast<CallBase>(&I); CB && !isa<IntrinsicInst>(CB)) {
          callsOf[&F].push_back(CB);
          if (const Function *C = CB->getCalledFunction()) callersOf[C].push_back(&F);
          else if (!CB->isInlineAsm()) ind = true;
        }
      if (ind) indirectCallers.push_back(&F);
    }
  struct MayWrite { std::set<const Function *> fns; bool viaIndirect = false; std::set<const Instruction *> stores; };
  // The functions that may execute one of `seeds` (directly, through
  // direct callees, or through an indirect call once a function on the way
  // has its address taken).
  auto closureOf = [&](const std::vector<const Instruction *> &seeds, MayWrite &MW) {
    std::vector<const Function *> work;
    auto add = [&](const Function *F) { if (MW.fns.insert(F).second) work.push_back(F); };
    for (const Instruction *I : seeds) {
      MW.stores.insert(I);
      add(I->getFunction());
    }
    while (!work.empty()) {
      const Function *G = work.back();
      work.pop_back();
      for (const Function *C : callersOf[G]) add(C);
      if (G->hasAddressTaken() && !MW.viaIndirect) {
        MW.viaIndirect = true;
        for (const Function *C : indirectCallers) add(C);
      }
    }
  };
  std::map<Field, MayWrite> mayWriteOf;
  auto mayWrite = [&](const Field &Df) -> const MayWrite & {
    auto [it, ins] = mayWriteOf.try_emplace(Df);
    if (ins) {
      std::vector<const Instruction *> seeds;
      for (const TagStore &t : dStores[Df]) seeds.push_back(t.I);
      closureOf(seeds, it->second);
    }
    return it->second;
  };
  const bool outsideRoots = CFLOutside == "roots";
  // The identity of a call argument: through casts and zero-offset GEPs;
  // a field address is its own object.
  auto argId = [&](const Value *V) -> const Value * {
    for (int d = 0; d < 8; d++) {
      V = V->stripPointerCasts();
      const auto *G = dyn_cast<GEPOperator>(V);
      if (!G) break;
      APInt Ap(64, 0);
      if (!G->accumulateConstantOffset(Ctx->Modules.begin()->first->getDataLayout(), Ap) || !Ap.isZero()) return V;
      V = G->getPointerOperand();
    }
    return ids.of(V, 0);
  };
  // Alias assumptions (plan 3.51): where a walk would give up because a
  // call (or a store, or a read of another identity) might touch the
  // walked object's field through an alias, it records an assumption
  // instead: the object `id` points to is not one the accesses in an
  // access set reach. The solver checks it with its own facts (an object
  // arriving at both, at the same field) and flips the pair otherwise.
  // An access set holds the field accesses of every function a call's
  // possible targets may run (address-taken functions for an indirect
  // call), computed here and never narrowed by the solver's call graph.
  std::vector<const Function *> addrTaken;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      if (!F.isDeclaration() && F.hasAddressTaken()) addrTaken.push_back(&F);
  std::map<const Function *, std::set<const Function *>> reachMemo;
  auto reachOf = [&](const Function *H) -> const std::set<const Function *> & { // H null: indirect
    auto [it, ins] = reachMemo.try_emplace(H);
    if (!ins) return it->second;
    std::set<const Function *> &R = it->second;
    std::vector<const Function *> work;
    bool indirectAdded = false;
    auto add = [&](const Function *F) { if (!F->isDeclaration() && R.insert(F).second) work.push_back(F); };
    auto addIndirect = [&]() {
      if (indirectAdded) return;
      indirectAdded = true;
      for (const Function *F : addrTaken) add(F);
    };
    if (H) add(H);
    else addIndirect();
    while (!work.empty()) {
      const Function *G = work.back();
      work.pop_back();
      for (const CallBase *CB : callsOf[G]) {
        if (const Function *C = CB->getCalledFunction()) add(C);
        else if (!CB->isInlineAsm()) addIndirect();
      }
    }
    return R;
  };
  auto accessOf = [&](const Instruction *I) {
    const Value *P = isa<StoreInst>(I) ? cast<StoreInst>(I)->getPointerOperand() : cast<LoadInst>(I)->getPointerOperand();
    const DataLayout &DL = I->getModule()->getDataLayout();
    TaggedAccess A{nullptr, 0, false};
    for (int d = 0; d < 32; d++) {
      P = P->stripPointerCasts();
      const auto *G = dyn_cast<GEPOperator>(P);
      if (!G) break;
      APInt Ap(64, 0);
      if (G->accumulateConstantOffset(DL, Ap)) A.k += Ap.getSExtValue();
      else A.var = true;
      P = G->getPointerOperand();
    }
    A.base = P;
    return A;
  };
  std::map<std::tuple<std::string, int64_t, char, const void *>, uint32_t> accessSetIdx;
  // kind 's': stores of X in the reach of H; 'r': named loads of X there;
  // '1': the one access `key`.
  auto accessSet = [&](const Field &X, char kind, const void *key) -> uint32_t {
    auto [it, ins] = accessSetIdx.try_emplace({X.first, X.second, kind, key}, (uint32_t)taggedAccessSets.size());
    if (!ins) return it->second;
    std::vector<TaggedAccess> acc;
    if (kind == '1') acc.push_back(accessOf(static_cast<const Instruction *>(key)));
    else {
      const std::set<const Function *> &R = reachOf(static_cast<const Function *>(key));
      if (kind == 's') {
        for (const FAccess &a : fStores[X]) if (R.count(a.I->getFunction())) acc.push_back(accessOf(a.I));
        for (const TagStore &t : dStores[X]) if (R.count(t.I->getFunction())) acc.push_back(accessOf(t.I));
      } else
        for (const FAccess &a : fLoads[X]) if (R.count(a.I->getFunction())) acc.push_back(accessOf(a.I));
    }
    taggedAccessSets.push_back(std::move(acc));
    return it->second;
  };
  std::map<std::tuple<const Value *, int64_t, uint32_t>, uint32_t> assumeIdx;
  auto assume = [&](const Value *id, const Field &X, uint32_t set, const Instruction *at) -> uint32_t {
    auto [it, ins] = assumeIdx.try_emplace({id, X.second, set}, (uint32_t)taggedAssumes.size());
    if (ins) taggedAssumes.push_back({id, X.second, set, locOf(at)});
    return it->second;
  };
  std::map<const Instruction *, const Value *> dObjOf;
  for (auto &[X, ts] : dStores)
    for (const TagStore &t : ts) dObjOf[t.I] = t.obj;
  struct FieldCtx {
    Field X;
    std::map<const Instruction *, const Value *> stores; // named stores of X -> object identity
    MayWrite mw;                                        // functions that may write X
  };
  // Per field: its named stores (F: pointer stores; D: tag stores).
  std::map<Field, std::unique_ptr<FieldCtx>> ctxCache;
  auto ctxOf = [&](const Field &X, bool isD) -> const FieldCtx & {
    auto &P = ctxCache[X];
    if (!P) {
      P = std::make_unique<FieldCtx>();
      P->X = X;
      std::vector<const Instruction *> seeds;
      if (isD)
        for (const TagStore &t : dStores[X]) P->stores[t.I] = t.obj, seeds.push_back(t.I);
      else
        for (const FAccess &w : fStores[X]) P->stores[w.I] = w.obj, seeds.push_back(w.I);
      closureOf(seeds, P->mw);
    }
    return *P;
  };
  // ---- Callee D-effects (plan 3.51, composition ruling) ----
  // The effect of a call on D of the object a parameter points to: a set
  // of term maps, one per return path (the composed D writes on the path,
  // the identity for a path with none). Closed iff every write on every
  // path is evaluable and nothing on the way may write D unseen (an
  // unmapped or indirect call that may write it is an alias assumption,
  // as in the walks; a bodiless call under roots, the walk bound, or too
  // many maps open it). Callee guards are not threaded (a superset).
  // Recursion: one worklist from "no path returns" (the empty set).
  struct Eff {
    std::vector<Term> maps;
    bool open = false;
    std::string why;
    std::set<uint32_t> assumes;
  };
  const Term idTerm{'s', -1, 0, 0};
  // p then q (q over p's output).
  auto composeT = [](const Term &p, const Term &q) -> Term {
    if (q.src != 's') return q;
    Term r{p.src, 0, 0, 0};
    const int64_t pa = p.src == 'c' ? 0 : p.a;
    r.f = (p.f & q.a) | q.f;
    r.m = ((p.m & q.a) | q.m) & ~r.f;
    r.a = pa & q.a & ~r.f & ~r.m;
    if (!r.a) r.src = 'c';
    return r;
  };
  auto dedupT = [](std::vector<Term> &ts) {
    std::sort(ts.begin(), ts.end(), [](const Term &a, const Term &b) {
      return std::tie(a.src, a.a, a.f, a.m) < std::tie(b.src, b.a, b.f, b.m);
    });
    ts.erase(std::unique(ts.begin(), ts.end(), [](const Term &a, const Term &b) {
      return a.src == b.src && a.a == b.a && a.f == b.f && a.m == b.m;
    }), ts.end());
  };
  using EffKey = std::tuple<std::string, int64_t, const Function *, unsigned>;
  std::map<EffKey, Eff> effs;
  std::map<EffKey, std::set<EffKey>> effReaders;
  std::vector<EffKey> effStack;
  std::deque<EffKey> effWl;
  std::set<EffKey> effInWl;
  std::map<EffKey, const FieldCtx *> effCtx;
  bool effSolving = false;
  size_t effComputes = 0;
  std::function<const Eff &(const FieldCtx &, const Function *, unsigned)> effOf;
  using EffMemo = std::map<const Instruction *, std::pair<int, Eff>>; // 0 busy, 1 done; cyclic reads
  std::function<Eff(const FieldCtx &, const Function *, const Value *, const Instruction *, const BasicBlock *,
                    EffMemo &, std::set<const Instruction *> &)>
      effectBefore;
  // The composed effect on D of object `id` from `stop`'s start (or the
  // entry) to just before `at`.
  effectBefore = [&](const FieldCtx &Dc, const Function *Fn, const Value *id, const Instruction *at,
                     const BasicBlock *stop, EffMemo &memo, std::set<const Instruction *> &cyc) -> Eff {
    Eff R;
    auto openWhy = [&](const std::string &w) {
      if (!R.open) R.why = w;
      R.open = true;
    };
    // The effect just before instruction I, composed with maps after it.
    auto before = [&](const Instruction *I) -> Eff {
      auto it = memo.find(I);
      if (it != memo.end()) {
        if (it->second.first == 0) cyc.insert(I); // on a loop: the current value
        return it->second.second;
      }
      memo[I] = {0, Eff()};
      Eff E;
      for (int round = 0; round < 8; round++) {
        cyc.erase(I);
        E = effectBefore(Dc, Fn, id, I, stop, memo, cyc);
        dedupT(E.maps);
        const bool again = cyc.count(I) && (E.maps.size() != memo[I].second.maps.size() || E.open != memo[I].second.open);
        memo[I].second = E;
        if (!again) break;
        if (round == 7) { E.open = true; E.why = "a loop that does not settle"; }
      }
      memo[I] = {1, E};
      return E;
    };
    auto composeInto = [&](const Eff &prev, const std::vector<Term> &qs) {
      for (const Term &p : prev.maps)
        for (const Term &q : qs) R.maps.push_back(composeT(p, q));
      if (prev.open) openWhy(prev.why);
      R.assumes.insert(prev.assumes.begin(), prev.assumes.end());
    };
    std::set<const BasicBlock *> seen;
    std::vector<std::pair<const BasicBlock *, const Instruction *>> work{{at->getParent(), at->getPrevNode()}};
    size_t blocks = 0;
    const Defs &idDefs = defsOf(id);
    while (!work.empty()) {
      auto [B, I] = work.back();
      work.pop_back();
      bool stopped = false;
      for (; I && !stopped; I = I->getPrevNode()) {
        if (idDefs.insts.count(I)) {
          openWhy("the object's pointer is defined at " + locOf(I));
          stopped = true;
          continue;
        }
        if (auto sit = Dc.stores.find(I); sit != Dc.stores.end()) {
          if (!sameObj(sit->second, id, I)) {
            R.assumes.insert(assume(id, Dc.X, accessSet(Dc.X, '1', I), I));
            continue;
          }
          const TagStore *t = nullptr;
          for (const TagStore &x : dStores[Dc.X]) if (x.I == I) { t = &x; break; }
          if (t->unknown) openWhy("an unevaluable tag write at " + locOf(I));
          composeInto(before(I), t->terms);
          stopped = true;
          continue;
        }
        const auto *CB = dyn_cast<CallBase>(I);
        if (!CB || isa<IntrinsicInst>(CB) || CB->isInlineAsm()) continue;
        const Function *H = CB->getCalledFunction();
        if (!H) {
          if (Dc.mw.viaIndirect) R.assumes.insert(assume(id, Dc.X, accessSet(Dc.X, 's', nullptr), I));
          continue;
        }
        if (H->isDeclaration()) {
          if (outsideRoots) openWhy("a bodiless call at " + locOf(I));
          continue;
        }
        if (!Dc.mw.fns.count(H)) continue;
        int mk = -1;
        for (unsigned k = 0; k < CB->arg_size() && k < H->arg_size(); k++)
          if (CB->getArgOperand(k)->getType()->isPointerTy() && argId(CB->getArgOperand(k)) == id) {
            if (mk >= 0) { openWhy("the object passed twice at " + locOf(I)); break; }
            mk = (int)k;
          }
        if (mk < 0) {
          R.assumes.insert(assume(id, Dc.X, accessSet(Dc.X, 's', H), I));
          continue;
        }
        const Eff &E = effOf(Dc, H, (unsigned)mk);
        const std::vector<Term> qs = E.maps; // copy: the map may move
        const bool eo = E.open;
        const std::string ew = E.why;
        const std::set<uint32_t> ea = E.assumes;
        if (eo) openWhy(ew.empty() ? "in " + H->getName().str() : ew);
        R.assumes.insert(ea.begin(), ea.end());
        composeInto(before(I), qs);
        stopped = true;
      }
      if (stopped) continue;
      if (B == stop || B == &B->getParent()->getEntryBlock()) {
        R.maps.push_back(idTerm);
        continue;
      }
      if (idDefs.blocks.count(B)) {
        openWhy("the object's pointer merges at " + B->getParent()->getName().str());
        continue;
      }
      for (const BasicBlock *P : predecessors(B)) {
        if (!seen.insert(P).second) continue;
        if (++blocks > 20000) {
          openWhy("the walk bound in " + Fn->getName().str());
          work.clear();
          break;
        }
        work.push_back({P, &P->back()});
      }
    }
    dedupT(R.maps);
    if (R.maps.size() > 256) openWhy("too many maps");
    return R;
  };
  auto sameEff = [](const Eff &a, const Eff &b) {
    if (a.open != b.open || a.maps.size() != b.maps.size() || a.assumes != b.assumes) return false;
    for (size_t i = 0; i < a.maps.size(); i++)
      if (a.maps[i].src != b.maps[i].src || a.maps[i].a != b.maps[i].a || a.maps[i].f != b.maps[i].f ||
          a.maps[i].m != b.maps[i].m)
        return false;
    return true;
  };
  effOf = [&](const FieldCtx &Dc, const Function *H, unsigned k) -> const Eff & {
    const EffKey key{Dc.X.first, Dc.X.second, H, k};
    effCtx[key] = &Dc;
    if (!effStack.empty()) effReaders[key].insert(effStack.back());
    if (!effs.count(key)) {
      effs[key] = Eff();
      if (effInWl.insert(key).second) effWl.push_back(key);
    }
    if (!effSolving) {
      effSolving = true;
      while (!effWl.empty()) {
        const EffKey q = effWl.front();
        effWl.pop_front();
        effInWl.erase(q);
        const FieldCtx &QC = *effCtx[q];
        const Function *QH = std::get<2>(q);
        const unsigned qk = std::get<3>(q);
        effComputes++;
        effStack.push_back(q);
        Eff R;
        for (const BasicBlock &B : *QH)
          if (const auto *Ret = dyn_cast<ReturnInst>(B.getTerminator())) {
            EffMemo memo;
            std::set<const Instruction *> cyc;
            Eff e = effectBefore(QC, QH, QH->getArg(qk), Ret, nullptr, memo, cyc);
            R.maps.insert(R.maps.end(), e.maps.begin(), e.maps.end());
            R.assumes.insert(e.assumes.begin(), e.assumes.end());
            if (e.open && !R.open) R.why = e.why;
            R.open |= e.open;
          }
        effStack.pop_back();
        dedupT(R.maps);
        if (R.maps.size() > 256 && !R.open) { R.open = true; R.why = "too many maps in " + QH->getName().str(); }
        if (sameEff(R, effs[q])) continue;
        effs[q] = std::move(R);
        for (const EffKey &r : effReaders[q])
          if (effInWl.insert(r).second) effWl.push_back(r);
      }
      effSolving = false;
    }
    return effs[key];
  };
  size_t effClosed = 0, effOpen = 0, ceRounds = 0, ceUnsettled = 0;
  double ceSecs = 0;
  std::vector<std::string> effOpenAt;
  // Can D be written between the test (its load dl, its branch into Succ)
  // and the access at `at`? The last passage: blocks reachable from Succ
  // and reaching `at` without re-entering the test's block.
  // Is a test (its load dl, its branch into Succ) still about the content
  // the access at `at` sees? For a read (isD false): no write to F of the
  // object can come between them (a D write leaves the content the test
  // spoke for in place). For a retag (isD true): the D writes between are
  // composed, E = the maps from the test to the access; unstable when that
  // effect is open. The last passage: from Succ to `at` without
  // re-entering the test's block.
  std::string unstableWhy; // why the last test was dropped (reports)
  auto stableBetween = [&](const LoadInst *dl, const BranchInst *Br, const BasicBlock *Succ, const Instruction *at,
                           const Field &X, bool isD, const Value *obj, std::set<uint32_t> &as,
                           std::vector<Term> *E) {
    if (dl->getParent() != Br->getParent()) { unstableWhy = "the test's load is in another block"; return false; }
    const FieldCtx &C = ctxOf(X, isD);
    auto writes = [&](const Instruction &I) {
      if (&I == at) return false;
      if (auto sit = C.stores.find(&I); sit != C.stores.end()) {
        if (sameObj(sit->second, obj, &I)) return true;
        as.insert(assume(obj, X, accessSet(X, '1', &I), &I)); // another identity
        return false;
      }
      if (const auto *CB = dyn_cast<CallBase>(&I); CB && !isa<IntrinsicInst>(CB)) {
        if (CB->isInlineAsm()) return false;
        const Function *G = CB->getCalledFunction();
        if (!G) {
          if (C.mw.viaIndirect) as.insert(assume(obj, X, accessSet(X, 's', nullptr), &I));
          return false;
        }
        if (G->isDeclaration()) return outsideRoots;
        if (!C.mw.fns.count(G)) return false;
        for (unsigned k = 0; k < CB->arg_size(); k++)
          if (CB->getArgOperand(k)->getType()->isPointerTy() && argId(CB->getArgOperand(k)) == obj) return true;
        as.insert(assume(obj, X, accessSet(X, 's', G), &I));
      }
      return false;
    };
    for (const Instruction *I = dl->getNextNode(); I && I != Br; I = I->getNextNode())
      if (writes(*I)) { unstableWhy = "a write at " + locOf(I) + " between the test's load and its branch"; return false; }
    if (isD) {
      EffMemo memo;
      std::set<const Instruction *> cyc;
      Eff e = effectBefore(C, at->getFunction(), obj, at, Succ, memo, cyc);
      as.insert(e.assumes.begin(), e.assumes.end());
      if (e.open) { unstableWhy = "an open D effect: " + e.why; return false; }
      if (E) *E = std::move(e.maps);
      return true;
    }
    const BasicBlock *TB = Br->getParent();
    std::set<const BasicBlock *> fwd, bwd;
    std::vector<const BasicBlock *> work{Succ};
    fwd.insert(Succ);
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      for (const BasicBlock *N : successors(B))
        if (N != TB && fwd.insert(N).second) work.push_back(N);
    }
    work = {at->getParent()};
    bwd.insert(at->getParent());
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (B == Succ) continue;
      for (const BasicBlock *P : predecessors(B))
        if (P != TB && fwd.count(P) && bwd.insert(P).second) work.push_back(P);
    }
    const Defs &idDefs = defsOf(obj);
    // Is `at`'s block on a cycle inside the region (so the code after `at`
    // in it can come between)?
    bool atCycle = false;
    {
      std::set<const BasicBlock *> sn;
      std::vector<const BasicBlock *> w2(succ_begin(at->getParent()), succ_end(at->getParent()));
      while (!w2.empty() && !atCycle) {
        const BasicBlock *B = w2.back();
        w2.pop_back();
        if (B == TB || !sn.insert(B).second) continue;
        if (B == at->getParent()) atCycle = true;
        for (const BasicBlock *N : successors(B)) w2.push_back(N);
      }
    }
    for (const BasicBlock *B : bwd)
      if (fwd.count(B)) {
        if (idDefs.blocks.count(B) && (B != at->getParent() || atCycle)) { unstableWhy = "the object's pointer merges between"; return false; }
        for (const Instruction &I : *B) {
          if (idDefs.insts.count(&I) && !(B == at->getParent() && at->comesBefore(&I) && !atCycle)) {
            unstableWhy = "the object's pointer is defined between";
            return false;
          }
          if (writes(I)) { unstableWhy = "a write at " + locOf(&I); return false; }
        }
      }
    return true;
  };
  // A test of D on the access's object dominating it, stable up to it.
  struct Test { const Value *cond; const LoadInst *d; bool onTrue; };
  size_t testsUnstable = 0;
  // Reads (Ef null): stable against F writes. Retags (Ef set): each
  // test's composed D effect up to the access, parallel to tests.
  std::string lastTestsWhy; // the last testsAt's reason for dropping tests
  auto testsAt = [&](const Instruction *at, const Value *obj, const Field &Df, const Field &Ff,
                     std::vector<Test> &tests, std::set<uint32_t> &as,
                     std::vector<std::vector<Term>> *Ef = nullptr) {
    lastTestsWhy = "no dominating test of the tag on this object";
    const Function *Fn = at->getFunction();
    DominatorTree &DT = domOf(Fn);
    for (const FnTest &ft : fnTestsOf(Fn)) {
      if (ft.S != Df.first || ft.off != Df.second || ft.obj != obj) continue;
      for (unsigned si = 0; si < 2; si++) {
        const BasicBlock *Succ = ft.Br->getSuccessor(si);
        if (Succ->getSinglePredecessor() != ft.Br->getParent() || !DT.dominates(Succ, at->getParent())) continue;
        std::set<uint32_t> a2;
        std::vector<Term> E;
        if (!stableBetween(ft.dl, ft.Br, Succ, at, Ef ? Df : Ff, Ef != nullptr, obj, a2, &E)) {
          testsUnstable++;
          lastTestsWhy = "test at " + locOf(ft.Br) + " dropped: " + unstableWhy;
          continue;
        }
        as.insert(a2.begin(), a2.end());
        tests.push_back({ft.Br->getCondition(), ft.dl, si == 0});
        if (Ef) Ef->push_back(std::move(E));
      }
    }
  };
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
  // The same tests over a widened tag (plan 3.51, ruling gamma): bits
  // known or free; a test that may hold does not exclude.
  std::function<std::optional<KnownBits>(const Value *, const LoadInst *, const KnownBits &)> evalKB =
      [&](const Value *X, const LoadInst *dl, const KnownBits &kb) -> std::optional<KnownBits> {
    if (X == dl) {
      const unsigned w = dl->getType()->getIntegerBitWidth();
      return w == 64 ? kb : kb.trunc(w);
    }
    if (const auto *K = dyn_cast<ConstantInt>(X)) return KnownBits::makeConstant(K->getValue());
    if (const auto *C = dyn_cast<CastInst>(X)) {
      if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) return std::nullopt;
      auto a = evalKB(C->getOperand(0), dl, kb);
      if (!a) return std::nullopt;
      const unsigned bw = C->getType()->getIntegerBitWidth();
      if (isa<TruncInst>(C)) return a->trunc(bw);
      if (isa<ZExtInst>(C)) return a->zext(bw);
      if (isa<SExtInst>(C)) return a->sext(bw);
      return std::nullopt;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(X)) {
      auto a = evalKB(BO->getOperand(0), dl, kb), b = evalKB(BO->getOperand(1), dl, kb);
      if (!a || !b || a->getBitWidth() != b->getBitWidth()) return std::nullopt;
      switch (BO->getOpcode()) {
      case Instruction::And: return *a & *b;
      case Instruction::Or: return *a | *b;
      case Instruction::Xor: return *a ^ *b;
      default: return std::nullopt;
      }
    }
    if (const auto *IC = dyn_cast<ICmpInst>(X)) {
      auto a = evalKB(IC->getOperand(0), dl, kb), b = evalKB(IC->getOperand(1), dl, kb);
      if (!a || !b || a->getBitWidth() != b->getBitWidth()) return std::nullopt;
      std::optional<bool> r;
      switch (IC->getPredicate()) {
      case ICmpInst::ICMP_EQ: r = KnownBits::eq(*a, *b); break;
      case ICmpInst::ICMP_NE: r = KnownBits::ne(*a, *b); break;
      case ICmpInst::ICMP_UGT: r = KnownBits::ugt(*a, *b); break;
      case ICmpInst::ICMP_UGE: r = KnownBits::uge(*a, *b); break;
      case ICmpInst::ICMP_ULT: r = KnownBits::ult(*a, *b); break;
      case ICmpInst::ICMP_ULE: r = KnownBits::ule(*a, *b); break;
      case ICmpInst::ICMP_SGT: r = KnownBits::sgt(*a, *b); break;
      case ICmpInst::ICMP_SGE: r = KnownBits::sge(*a, *b); break;
      case ICmpInst::ICMP_SLT: r = KnownBits::slt(*a, *b); break;
      case ICmpInst::ICMP_SLE: r = KnownBits::sle(*a, *b); break;
      default: break;
      }
      if (!r) return KnownBits(1);
      return KnownBits::makeConstant(APInt(1, *r ? 1 : 0));
    }
    return std::nullopt;
  };
  // The bits of the tag a test can observe (tests read masks of it; an
  // expression this does not follow observes every bit).
  std::function<bool(const Value *, const LoadInst *, uint64_t, uint64_t &)> demand =
      [&](const Value *X, const LoadInst *dl, uint64_t want, uint64_t &acc) -> bool {
    if (X == dl) { acc |= want; return true; }
    if (isa<ConstantInt>(X)) return true;
    auto maskOf = [](unsigned w) { return w >= 64 ? ~uint64_t(0) : ((uint64_t(1) << w) - 1); };
    if (const auto *C = dyn_cast<CastInst>(X)) {
      if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) return false;
      const unsigned sb = C->getOperand(0)->getType()->getIntegerBitWidth();
      if (isa<TruncInst>(C)) return demand(C->getOperand(0), dl, want, acc);
      if (isa<ZExtInst>(C)) return demand(C->getOperand(0), dl, want & maskOf(sb), acc);
      if (isa<SExtInst>(C))
        return demand(C->getOperand(0), dl,
                      (want & maskOf(sb)) | ((want & ~maskOf(sb)) ? (uint64_t(1) << (sb - 1)) : 0), acc);
      return false;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(X)) {
      const Value *A = BO->getOperand(0), *B = BO->getOperand(1);
      if (BO->getOpcode() == Instruction::And) {
        if (const auto *K = dyn_cast<ConstantInt>(B)) return demand(A, dl, want & K->getZExtValue(), acc);
        if (const auto *K = dyn_cast<ConstantInt>(A)) return demand(B, dl, want & K->getZExtValue(), acc);
        return demand(A, dl, want, acc) && demand(B, dl, want, acc);
      }
      if (BO->getOpcode() == Instruction::Or || BO->getOpcode() == Instruction::Xor)
        return demand(A, dl, want, acc) && demand(B, dl, want, acc);
      return false;
    }
    if (const auto *IC = dyn_cast<ICmpInst>(X)) {
      const uint64_t all = maskOf(IC->getOperand(0)->getType()->getIntegerBitWidth());
      return demand(IC->getOperand(0), dl, all, acc) && demand(IC->getOperand(1), dl, all, acc);
    }
    return false;
  };
  auto mayHold = [&](const std::vector<Test> &tests, const KnownBits &kb) {
    for (const Test &t : tests) {
      auto r = evalKB(t.cond, t.d, kb);
      if (!r || !r->isConstant()) continue; // may hold
      if ((!r->getConstant().isZero()) != t.onTrue) return false;
    }
    return true;
  };
  auto holds = [&](const std::vector<Test> &tests, int64_t v) {
    for (const Test &t : tests) {
      auto r2 = eval(t.cond, t.d, v);
      if (!r2) continue; // not evaluable: no constraint
      if ((*r2 != 0) != t.onTrue) return false;
    }
    return true;
  };
  // ---- The co-write rule: last writers (plan 3.51) ----
  // Invariant: a writer W's tag set is the set of D values that can hold
  // while W's content is in F and F is read; a read under test P admits W
  // iff some value in that set satisfies P. A D store t gives its values
  // to the last F writers of its object before it, L(t) (they hold F when
  // the tag becomes t's). L(t) is a backward walk that stops at F stores of
  // the object and at direct calls whose summary must-writes F of the
  // parameter the object is passed in; it is open when it reaches the
  // entry, an F store of another identity, a call that may write F not
  // through that mapping (an object reached by a load in the callee is
  // another identity), an indirect call that may write F, a bodiless call
  // under --cfl-outside=roots, or the walk bound. An open t is also a
  // retag: its map applies to every writer. A writer whose content can be
  // read (a tested read, a call that may make one, a return) before its
  // object's D or F is rewritten is observed under the tag it found: the
  // values of the last D writers before it, or every tag when that set is
  // open. Identity through calls is by direct-call parameter mapping only.
  struct Walk {
    std::set<const Instruction *> W;
    bool open = false, entry = false;
    std::string why;
    std::set<uint32_t> assumes; // alias assumptions it rests on
  };
  using SumKey = std::tuple<std::string, int64_t, const Function *, unsigned>;
  std::map<SumKey, Walk> sums;
  size_t walkBounds = 0;
  constexpr size_t kWalkBlocks = 20000;
  std::function<const Walk &(const FieldCtx &, const Function *, unsigned)> sumOf;
  // The last writers of field C.X of object `id` before `at` in Fn.
  size_t walksBack = 0, walksFwd = 0, walkBlocks = 0;
  std::map<const Function *, size_t> walkBlocksBy;
  auto walkBack = [&](const FieldCtx &C, const Function *Fn, const Value *id, const Instruction *at) {
    walksBack++;
    Walk R;
    auto openWhy = [&](const std::string &w) {
      if (!R.open) R.why = w;
      R.open = true;
    };
    std::set<const BasicBlock *> seen;
    std::vector<std::pair<const BasicBlock *, const Instruction *>> work{{at->getParent(), at->getPrevNode()}};
    size_t blocks = 0;
    const Defs &idDefs = defsOf(id);
    while (!work.empty()) {
      auto [B, I] = work.back();
      work.pop_back();
      bool stopped = false;
      for (; I && !stopped; I = I->getPrevNode()) {
        if (idDefs.insts.count(I)) { // before this, the name was another object
          openWhy("the object's pointer is defined at " + locOf(I));
          stopped = true;
          continue;
        }
        if (auto sit = C.stores.find(I); sit != C.stores.end()) {
          if (sameObj(sit->second, id, I)) { R.W.insert(I); stopped = true; }
          else R.assumes.insert(assume(id, C.X, accessSet(C.X, '1', I), I));
          continue;
        }
        const auto *CB = dyn_cast<CallBase>(I);
        if (!CB || isa<IntrinsicInst>(CB) || CB->isInlineAsm()) continue;
        const Function *H = CB->getCalledFunction();
        if (!H) {
          if (C.mw.viaIndirect) R.assumes.insert(assume(id, C.X, accessSet(C.X, 's', nullptr), I));
          continue;
        }
        if (H->isDeclaration()) {
          if (outsideRoots) openWhy("a bodiless call at " + locOf(I));
          continue;
        }
        bool mapped = false, must = false;
        for (unsigned k = 0; k < CB->arg_size() && k < H->arg_size(); k++)
          if (CB->getArgOperand(k)->getType()->isPointerTy() && argId(CB->getArgOperand(k)) == id) {
            mapped = true;
            const Walk &Sm = sumOf(C, H, k);
            R.W.insert(Sm.W.begin(), Sm.W.end());
            R.assumes.insert(Sm.assumes.begin(), Sm.assumes.end());
            if (Sm.open) openWhy(Sm.why);
            must |= !Sm.entry;
          }
        if (!mapped && C.mw.fns.count(H)) R.assumes.insert(assume(id, C.X, accessSet(C.X, 's', H), I));
        stopped = must;
      }
      if (stopped) continue;
      if (idDefs.blocks.count(B)) { // the merge that names the object
        openWhy("the object's pointer merges at " + B->getParent()->getName().str());
        continue;
      }
      if (B == &B->getParent()->getEntryBlock()) { R.entry = true; continue; }
      for (const BasicBlock *P : predecessors(B)) {
        if (!seen.insert(P).second) continue;
        walkBlocks++;
        walkBlocksBy[Fn]++;
        if (++blocks > kWalkBlocks) {
          if (!R.open) walkBounds++;
          openWhy("the walk bound in " + Fn->getName().str());
          work.clear();
          break;
        }
        work.push_back({P, &P->back()});
      }
    }
    return R;
  };
  // Recursion: summaries are solved by one worklist (chaotic iteration
  // from "no path returns": nothing written, nothing open, no entry). A
  // summary read before it is final answers with its current value and
  // records the reader, which is recomputed when it grows. Every summary
  // only grows (unions), so the iteration ends at the least fixpoint.
  auto sameWalk = [](const Walk &a, const Walk &b) {
    return a.W == b.W && a.open == b.open && a.entry == b.entry && a.assumes == b.assumes;
  };
  std::map<SumKey, std::set<SumKey>> sumReaders;
  std::map<SumKey, const FieldCtx *> sumCtx;
  std::vector<SumKey> sumStack;
  std::deque<SumKey> sumWl;
  std::set<SumKey> sumInWl;
  bool sumSolving = false;
  size_t sumComputes = 0;
  sumOf = [&](const FieldCtx &C, const Function *H, unsigned k) -> const Walk & {
    const SumKey key{C.X.first, C.X.second, H, k};
    sumCtx[key] = &C;
    if (!sumStack.empty()) sumReaders[key].insert(sumStack.back());
    if (!sums.count(key)) {
      sums[key] = Walk();
      if (sumInWl.insert(key).second) sumWl.push_back(key);
    }
    if (!sumSolving) {
      sumSolving = true;
      while (!sumWl.empty()) {
        const SumKey q = sumWl.front();
        sumWl.pop_front();
        sumInWl.erase(q);
        const FieldCtx &QC = *sumCtx[q];
        const Function *QH = std::get<2>(q);
        const unsigned qk = std::get<3>(q);
        sumComputes++;
        sumStack.push_back(q);
        Walk R;
        for (const BasicBlock &B : *QH)
          if (const auto *Ret = dyn_cast<ReturnInst>(B.getTerminator())) {
            Walk w = walkBack(QC, QH, QH->getArg(qk), Ret);
            R.W.insert(w.W.begin(), w.W.end());
            R.assumes.insert(w.assumes.begin(), w.assumes.end());
            if (w.open && !R.open) R.why = w.why;
            R.open |= w.open;
            R.entry |= w.entry;
          }
        sumStack.pop_back();
        if (sameWalk(R, sums[q])) continue;
        sums[q] = std::move(R);
        for (const SumKey &r : sumReaders[q])
          if (sumInWl.insert(r).second) sumWl.push_back(r);
      }
      sumSolving = false;
    }
    return sums[key];
  };
  // Can W's content be read before its object's D or F is rewritten?
  auto observed = [&](const FieldCtx &Fc, const FieldCtx &Dc, const MayWrite &mrF,
                      const std::map<const Instruction *, const Value *> &reads, const Value *id,
                      const Instruction *W, std::set<uint32_t> &as) {
    walksFwd++;
    std::set<const BasicBlock *> seen;
    std::vector<std::pair<const BasicBlock *, const Instruction *>> work{{W->getParent(), W->getNextNode()}};
    size_t blocks = 0;
    const Defs &idDefs = defsOf(id);
    while (!work.empty()) {
      auto [B, I] = work.back();
      work.pop_back();
      if (idDefs.blocks.count(B) && I == &B->front()) return true; // the name becomes another object
      bool stopped = false;
      for (; I && !stopped; I = I->getNextNode()) {
        if (isa<ReturnInst>(I) || idDefs.insts.count(I)) return true;
        if (auto rit = reads.find(I); rit != reads.end()) {
          if (sameObj(rit->second, id, I)) return true;
          as.insert(assume(id, Fc.X, accessSet(Fc.X, '1', I), I)); // a read of another identity
          continue;
        }
        if (isa<UnreachableInst>(I)) { stopped = true; break; }
        if (auto dit = Dc.stores.find(I); dit != Dc.stores.end() && sameObj(dit->second, id, I)) { stopped = true; break; }
        if (auto fit = Fc.stores.find(I); fit != Fc.stores.end() && sameObj(fit->second, id, I)) { stopped = true; break; }
        const auto *CB = dyn_cast<CallBase>(I);
        if (!CB || isa<IntrinsicInst>(CB) || CB->isInlineAsm()) continue;
        const Function *H = CB->getCalledFunction();
        if (!H) {
          if (mrF.viaIndirect) as.insert(assume(id, Fc.X, accessSet(Fc.X, 'r', nullptr), I));
          continue;
        }
        if (H->isDeclaration()) {
          if (outsideRoots) return true;
          continue;
        }
        bool mapped = false;
        for (unsigned k = 0; k < CB->arg_size() && k < H->arg_size(); k++)
          if (CB->getArgOperand(k)->getType()->isPointerTy() && argId(CB->getArgOperand(k)) == id) {
            mapped = true;
            if (mrF.fns.count(H)) return true; // it may read it through the parameter
            const Walk &Sm = sumOf(Dc, H, k);
            if (!Sm.entry) {
              stopped = true; // the callee must-write D of it
              as.insert(Sm.assumes.begin(), Sm.assumes.end());
            }
          }
        if (!mapped && mrF.fns.count(H)) as.insert(assume(id, Fc.X, accessSet(Fc.X, 'r', H), I));
      }
      if (stopped) continue;
      for (const BasicBlock *N : successors(B)) {
        if (!seen.insert(N).second) continue;
        if (++blocks > kWalkBlocks) return true;
        work.push_back({N, &N->front()});
      }
    }
    return false;
  };
  // A function whose every caller is a direct call (whole program, address
  // not taken): an effect on its parameter's object is accounted at its
  // call sites.
  auto absorbable = [&](const Function *G) {
    if (!CFLWholeProgram || G->hasAddressTaken()) return false;
    for (const User *U : G->users()) {
      const auto *CB = dyn_cast<CallBase>(U);
      if (!CB || CB->getCalledOperand() != G) return false;
    }
    return true;
  };
  // Settled results, memoized: walks and tests outside summary solving
  // are final (every summary they read was solved before they returned).
  std::map<std::tuple<std::string, int64_t, const Instruction *, const Value *>, Walk> walkMemo;
  auto walkBackM = [&](const FieldCtx &C, const Function *Fn, const Value *id, const Instruction *at) -> Walk {
    const auto key = std::make_tuple(C.X.first, C.X.second, at, id);
    if (auto it = walkMemo.find(key); it != walkMemo.end()) return it->second;
    Walk w = walkBack(C, Fn, id, at);
    walkMemo[key] = w;
    return w;
  };
  struct TestsAt { std::vector<Test> tests; std::set<uint32_t> as; std::vector<std::vector<Term>> Es; std::string why; };
  std::map<std::tuple<const Instruction *, const Value *, std::string, int64_t, int64_t, bool>, TestsAt> testsMemo;
  auto testsAtM = [&](const Instruction *at, const Value *obj, const Field &Df, const Field &Ff,
                      std::vector<Test> &tests, std::set<uint32_t> &as,
                      std::vector<std::vector<Term>> *Ef = nullptr) {
    const auto key = std::make_tuple(at, obj, Df.first, Df.second, Ff.second, Ef != nullptr);
    auto [it, ins] = testsMemo.try_emplace(key);
    if (ins) {
      testsAt(at, obj, Df, Ff, it->second.tests, it->second.as, Ef ? &it->second.Es : nullptr);
      it->second.why = lastTestsWhy;
    }
    lastTestsWhy = it->second.why;
    tests.insert(tests.end(), it->second.tests.begin(), it->second.tests.end());
    as.insert(it->second.as.begin(), it->second.as.end());
    if (Ef) Ef->insert(Ef->end(), it->second.Es.begin(), it->second.Es.end());
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
      // Writers and their tag sets (the last-writer rule above); retags.
      struct Writer {
        const Instruction *I;
        std::set<int64_t> tags;      // constants
        std::vector<Term> fromAny;   // images of every tag: (u & a) | f | sub(m)
        std::vector<Term> ownMaps;   // maps of its own tag (a later tag store)
        std::vector<std::vector<Test>> ownGuards; // per own map: the tests it runs under (none: always)
        std::vector<std::string> ownLab;          // per own map: where it comes from (reports)
        bool unknown = false;
        std::string why; // why unknown (reports)
      };
      std::vector<Writer> writers;
      std::map<const Instruction *, size_t> wIdx;
      for (const FAccess &w : fs) {
        wIdx[w.I] = writers.size();
        writers.push_back({w.I});
      }
      const FieldCtx &Fc = ctxOf(Ff, false), &Dc = ctxOf(Df, true);
      // The reads that matter: those with a stable test (the others read
      // every writer).
      std::set<uint32_t> pas; // the alias assumptions the pair's keys rest on
      std::map<const Instruction *, const Value *> tested;
      std::vector<const Instruction *> testedV;
      for (const FAccess &r : fLoads[Ff]) {
        std::vector<Test> tt;
        testsAtM(r.I, r.obj, Df, Ff, tt, pas);
        if (!tt.empty()) tested[r.I] = r.obj, testedV.push_back(r.I);
      }
      if (tested.empty()) { // no read with a stable test: no read can be keyed
        readsNoTest += fLoads[Ff].size();
        continue;
      }
      MayWrite mrF;
      closureOf(testedV, mrF);
      std::map<std::pair<const Instruction *, const Value *>, std::pair<bool, std::set<uint32_t>>> obsMemo;
      auto obsM = [&](const Value *id, const Instruction *W, std::set<uint32_t> &as) {
        auto [it, ins] = obsMemo.try_emplace({W, id});
        if (ins) it->second.first = observed(Fc, Dc, mrF, tested, id, W, it->second.second);
        as.insert(it->second.second.begin(), it->second.second.end());
        return it->second.first;
      };
      std::set<std::string> via;
      auto give = [&](Writer &W, const TagStore &t, bool prior) {
        if (t.unknown && !W.unknown) W.why = "unevaluable tag write at " + locOf(t.I);
        if (t.unknown) W.unknown = true;
        via.insert(t.via.begin(), t.via.end());
        for (const Term &tm : t.terms)
          if (tm.src == 'c') { if (!concretize({tm}, W.tags)) W.unknown = true; }
          else if (tm.src == 's' && !prior)
            W.ownMaps.push_back(tm), W.ownGuards.push_back({}), W.ownLab.push_back("tag write " + locOf(t.I));
          else W.fromAny.push_back(tm);
      };
      std::vector<const TagStore *> retags;
      bool nonConstRetag = false;
      size_t closedStores = 0, openStores = 0, observedWriters = 0, openPrior = 0;
      std::string openAt;
      std::map<const TagStore *, std::string> openWhyOf;
      size_t unseenStores = 0, absorbedStores = 0;
      for (const TagStore &t : ds) {
        // A tag its object's content is never read under (F or D is
        // rewritten first on every path) meets no content: it gives
        // nothing and retags nothing.
        {
          std::set<uint32_t> a2;
          if (!obsM(t.obj, t.I, a2)) {
            unseenStores++;
            pas.insert(a2.begin(), a2.end());
            continue;
          }
        }
        const Walk L = walkBackM(Fc, t.I->getFunction(), t.obj, t.I);
        pas.insert(L.assumes.begin(), L.assumes.end());
        for (const Instruction *w : L.W)
          if (auto it = wIdx.find(w); it != wIdx.end()) give(writers[it->second], t, false);
        if (!L.open && L.entry && isa<Argument>(t.obj) &&
            absorbable(cast<Argument>(t.obj)->getParent())) {
          absorbedStores++; // its effect reaches the callers' writers at the call sites
          continue;
        }
        if (L.open || L.entry) {
          retags.push_back(&t);
          nonConstRetag |= t.unknown;
          openStores++;
          openWhyOf[&t] = L.open ? L.why : "the function entry (F from before it)";
          if (openAt.empty() && L.open) openAt = locOf(t.I) + ": " + L.why;
        } else closedStores++;
      }
      // Call sites. What a call does to the tag of the content its object
      // holds when it is called: the tag writes in the callee that the
      // incoming content can be read under (L reaches the callee's entry),
      // each composed with the D effect before it, and recursively through
      // the calls that hand the object on. Those maps go to the last F
      // writers before the call; when those are open at the caller's
      // entry, the maps are the caller's own (absorbed) or a retag.
      // The (function, parameter) pairs that can carry an effect: a tag
      // write of the parameter's object, or a call handing it to one.
      std::set<std::pair<const Function *, unsigned>> carriers;
      {
        std::vector<std::pair<const Function *, unsigned>> work;
        for (const TagStore &t : ds)
          if (const auto *A = dyn_cast<Argument>(t.obj))
            if (carriers.insert({A->getParent(), A->getArgNo()}).second) work.push_back({A->getParent(), A->getArgNo()});
        while (!work.empty()) {
          auto [G, k] = work.back();
          work.pop_back();
          for (const User *U : G->users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (!CB || CB->getCalledOperand() != G || k >= CB->arg_size()) continue;
            if (const auto *A = dyn_cast<Argument>(argId(CB->getArgOperand(k))))
              if (carriers.insert({A->getParent(), A->getArgNo()}).second) work.push_back({A->getParent(), A->getArgNo()});
          }
        }
      }
      // A callee's maps on the incoming content: each absorbed tag write's
      // map, composed after the D effect from its stable test (if any) and
      // guarded by that test; intermediate tags are covered by the
      // closure, since every write on the way contributes its own map.
      struct CEff { std::vector<Term> maps; std::vector<std::vector<Test>> guards; bool open = false; };
      std::map<std::pair<const Function *, unsigned>, CEff> ceMemo, cePrev;
      std::set<std::pair<const Function *, unsigned>> ceBusy;
      bool ceCycle = false;
      std::function<CEff(const Function *, unsigned)> contentEff = [&](const Function *G, unsigned k) -> CEff {
        const auto key = std::make_pair(G, k);
        if (auto it = ceMemo.find(key); it != ceMemo.end()) return it->second;
        if (!ceBusy.insert(key).second) { // recursion: the previous round's value
          ceCycle = true;
          auto pit = cePrev.find(key);
          return pit != cePrev.end() ? pit->second : CEff();
        }
        CEff R;
        const Value *id = G->getArg(k);
        for (const TagStore &t : ds) {
          if (t.I->getFunction() != G || t.obj != id) continue;
          std::set<uint32_t> a2;
          if (!obsM(t.obj, t.I, a2)) continue;
          const Walk L = walkBackM(Fc, G, id, t.I);
          if (!L.entry) continue; // only content written in G is under it
          pas.insert(a2.begin(), a2.end());
          pas.insert(L.assumes.begin(), L.assumes.end());
          if (t.unknown) R.open = true;
          std::vector<Test> all, g;
          std::vector<std::vector<Term>> Es;
          testsAtM(t.I, id, Df, Ff, all, pas, &Es);
          std::vector<Term> pre{idTerm};
          if (!all.empty()) g.push_back(all.back()), pre = Es.back();
          for (const Term &q : t.terms)
            for (const Term &p : pre) {
              R.maps.push_back(q.src == 's' ? composeT(p, q) : q);
              R.guards.push_back(q.src == 'x' ? std::vector<Test>{} : g);
            }
        }
        for (const CallBase *CB : callsOf[G]) {
          const Function *H = CB->getCalledFunction();
          if (!H || H->isDeclaration()) continue;
          for (unsigned j = 0; j < CB->arg_size() && j < H->arg_size(); j++) {
            if (!carriers.count({H, j}) || argId(CB->getArgOperand(j)) != id) continue;
            const Walk L = walkBackM(Fc, G, id, CB);
            if (!L.entry) continue;
            pas.insert(L.assumes.begin(), L.assumes.end());
            const CEff inner = contentEff(H, j);
            R.open |= inner.open;
            R.maps.insert(R.maps.end(), inner.maps.begin(), inner.maps.end());
            R.guards.insert(R.guards.end(), inner.guards.begin(), inner.guards.end());
          }
        }
        { // canonical order, no duplicates (rounds compare values)
          using K = std::tuple<char, int64_t, int64_t, int64_t, std::vector<std::pair<const Value *, bool>>>;
          std::map<K, size_t> uniq;
          for (size_t q = 0; q < R.maps.size(); q++) {
            std::vector<std::pair<const Value *, bool>> gk;
            for (const Test &t : R.guards[q]) gk.push_back({t.cond, t.onTrue});
            uniq.try_emplace(K{R.maps[q].src, R.maps[q].a, R.maps[q].f, R.maps[q].m, gk}, q);
          }
          CEff D;
          D.open = R.open;
          for (auto &[k2, q] : uniq) D.maps.push_back(R.maps[q]), D.guards.push_back(R.guards[q]);
          R = std::move(D);
        }
        if (R.maps.size() > 256) R.open = true;
        ceBusy.erase(key);
        ceMemo[key] = R;
        return R;
      };
      std::vector<Term> effMaps; // effects that act as retags
      std::vector<std::vector<Test>> effGuards;
      std::vector<std::string> effLab;
      bool effUnknownRetag = false;
      size_t effSites = 0, effAbsorbed = 0;
      // Recursion: rounds from the empty effect, each starting where the
      // last one ended, until no value changes (maps only grow).
      auto sameCE = [&](const CEff &a, const CEff &b) {
        if (a.open != b.open || a.maps.size() != b.maps.size()) return false;
        for (size_t q = 0; q < a.maps.size(); q++)
          if (a.maps[q].src != b.maps[q].src || a.maps[q].a != b.maps[q].a || a.maps[q].f != b.maps[q].f ||
              a.maps[q].m != b.maps[q].m)
            return false;
        return true;
      };
      const auto tce = std::chrono::steady_clock::now();
      for (int round = 0; round < 12; round++) {
        ceRounds++;
        ceCycle = false;
        cePrev = std::move(ceMemo);
        ceMemo.clear();
        for (auto [G, k] : carriers) contentEff(G, k);
        if (!ceCycle) break;
        bool same = cePrev.size() == ceMemo.size();
        for (auto it = ceMemo.begin(); same && it != ceMemo.end(); ++it) {
          auto pit = cePrev.find(it->first);
          same = pit != cePrev.end() && sameCE(it->second, pit->second);
        }
        if (same) break;
        if (round == 11) {
          ceUnsettled++;
          for (auto &[key, ce] : ceMemo) ce.open = true; // did not settle: unknown
        }
      }
      ceSecs += std::chrono::duration<double>(std::chrono::steady_clock::now() - tce).count();
      for (auto [G, k] : carriers) {
        for (const User *U : G->users()) {
          const auto *CB = dyn_cast<CallBase>(U);
          if (!CB || CB->getCalledOperand() != G || k >= CB->arg_size()) continue;
          {
            const CEff E = contentEff(G, k);
            if (E.maps.empty() && !E.open) continue; // the incoming content is never retagged
            effSites++;
            (E.open ? effOpen : effClosed)++;
            if (E.open && effOpenAt.size() < 8) effOpenAt.push_back(locOf(CB) + " -> " + G->getName().str());
            const Value *id = argId(CB->getArgOperand(k));
            const Walk L = walkBackM(Fc, CB->getFunction(), id, CB);
            pas.insert(L.assumes.begin(), L.assumes.end());
            for (const Instruction *w : L.W)
              if (auto it = wIdx.find(w); it != wIdx.end()) {
                Writer &W = writers[it->second];
                if (E.open && !W.unknown) W.why = "open call-site effect at " + locOf(CB);
                if (E.open) W.unknown = true;
                for (size_t q = 0; q < E.maps.size(); q++) {
                  const Term &tm = E.maps[q];
                  if (tm.src == 'c' && !E.guards[q].empty())
                    W.ownMaps.push_back(Term{'s', 0, tm.f, tm.m}), W.ownGuards.push_back(E.guards[q]),
                    W.ownLab.push_back("call " + locOf(CB) + " -> " + G->getName().str() + " (guarded constant)");
                  else if (tm.src == 'c') { if (!concretize({tm}, W.tags)) W.unknown = true; }
                  else if (tm.src == 's')
                    W.ownMaps.push_back(tm), W.ownGuards.push_back(E.guards[q]),
                    W.ownLab.push_back("call " + locOf(CB) + " -> " + G->getName().str() +
                                       (E.guards[q].empty() ? "" : " (guarded)"));
                  else W.fromAny.push_back(tm);
                }
              }
            if (!L.open && !L.entry) continue;
            if (!L.open && isa<Argument>(id) && absorbable(cast<Argument>(id)->getParent())) {
              effAbsorbed++;
              continue;
            }
            effUnknownRetag |= E.open;
            effMaps.insert(effMaps.end(), E.maps.begin(), E.maps.end());
            effGuards.insert(effGuards.end(), E.guards.begin(), E.guards.end());
            for (size_t q = 0; q < E.maps.size(); q++) effLab.push_back("call " + locOf(CB) + " -> " + G->getName().str());
          }
        }
      }
      nonConstRetag |= effUnknownRetag;
      for (size_t i = 0; i < writers.size(); i++) {
        const FAccess &w = fs[i];
        if (!obsM(w.obj, w.I, pas)) continue;
        observedWriters++;
        const Walk LD = walkBackM(Dc, w.I->getFunction(), w.obj, w.I);
        pas.insert(LD.assumes.begin(), LD.assumes.end());
        if (LD.open || LD.entry) {
          if (!writers[i].unknown) writers[i].why = "read under the tag it found, which is open (" +
                                                    (LD.open ? LD.why : std::string("the entry")) + ")";
          writers[i].unknown = true;
          openPrior++;
          continue;
        }
        for (const Instruction *d : LD.W)
          for (const TagStore &t : ds)
            if (t.I == d) give(writers[i], t, true);
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
      // memset fills that may cover the tag: constant retags, or (a
      // non-constant fill) an unevaluable one.
      std::set<int64_t> pairFills;
      const Instruction *fillUnknownAt = nullptr;
      if (auto fit = fillsOf.find(S); fit != fillsOf.end())
        for (const Fill &f : fit->second)
          if (f.lo < dOff + dBytes && dOff < f.hi) {
            if (f.fill < 0) { if (!fillUnknownAt) fillUnknownAt = f.I; }
            else pairFills.insert(f.fill);
          }
      if (fillUnknownAt) {
        pairsNonConst++;
        if (fs.size() >= 10)
          taggedReport.push_back("UNKEYED " + S + "+" + std::to_string(Ff.second) + " by +" + std::to_string(dOff) +
                                 ": a non-constant memset may cover the tag at " + locOf(fillUnknownAt));
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
                taggedReport.push_back("    non-constant retag " + locOf(t->I) + ": " + os.str().substr(0, 90) +
                                       " [open: " + openWhyOf[t] + "]");
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
      std::vector<std::vector<Test>> xformGuard; // per xform: the stable tests it runs under
      std::vector<std::string> xformLab;         // per xform: where it comes from (reports)
      size_t guarded = 0, unguarded = 0;
      std::vector<std::string> unguardedAt, allRetagAt;
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
        std::vector<Test> g;
        std::vector<std::vector<Term>> Es;
        bool hasS = false;
        for (const Term &tm : t->terms) hasS |= tm.src == 's';
        if (hasS) {
          std::vector<Test> all;
          testsAtM(t->I, t->obj, Df, Ff, all, pas, &Es);
          // Tests with no D write since them guard together; otherwise one
          // test (the last) with its composed effect: the retag is then
          // (its map after the effect), applied to tags the test admits.
          std::vector<size_t> plain;
          for (size_t q = 0; q < all.size(); q++)
            if (Es[q].size() == 1 && Es[q][0].src == 's' && Es[q][0].a == -1 && !Es[q][0].f && !Es[q][0].m)
              plain.push_back(q);
          std::vector<Term> pre{idTerm};
          if (!plain.empty()) for (size_t q : plain) g.push_back(all[q]);
          else if (!all.empty()) g.push_back(all.back()), pre = Es.back();
          (g.empty() ? unguarded : guarded)++;
          if (g.empty() && unguardedAt.size() < 40) unguardedAt.push_back(locOf(t->I) + ": " + lastTestsWhy);
          for (const Term &tm : t->terms)
            if (tm.src == 's')
              for (const Term &e : pre) {
                const Term c = composeT(e, tm);
                if (c.src == 's') xforms.push_back(c), xformGuard.push_back(g), xformLab.push_back(locOf(t->I) + (g.empty() ? " unguarded" : " guarded"));
                else if (c.src == 'c' && !g.empty()) // a constant under a guard: a map with no input bits
                  xforms.push_back(Term{'s', 0, c.f, c.m}), xformGuard.push_back(g), xformLab.push_back(locOf(t->I) + " guarded constant");
                else if (c.src == 'c') setsAll |= !concretize({c}, sets);
                else anyImgs.push_back(c);
              }
        }
        for (const Term &tm : t->terms) {
          if (tm.src == 'c') setsAll |= !concretize({tm}, sets);
          else if (tm.src == 's') sym = true;
          else anyImgs.push_back(tm), sym = true;
        }
        if (sym && VerboseLevel >= 2) {
          std::string d = locOf(t->I) + " {";
          for (const Term &tm : t->terms) d += std::string(d.back() == '{' ? "" : ", ") + termStr(tm);
          allRetagAt.push_back(d + "}");
        }
        if (sym && xformAt.size() < 4) {
          std::string d = locOf(t->I) + " {";
          for (const Term &tm : t->terms) d += std::string(d.back() == '{' ? "" : ", ") + termStr(tm);
          xformAt.push_back(d + "}");
        }
      }
      for (size_t q = 0; q < effMaps.size(); q++) { // call-site effects that act as retags
        const Term &tm = effMaps[q];
        if (tm.src == 'c' && !effGuards[q].empty()) // a constant under a guard
          xforms.push_back(Term{'s', 0, tm.f, tm.m}), xformGuard.push_back(effGuards[q]), xformLab.push_back(effLab[q] + " guarded constant");
        else if (tm.src == 'c') setsAll |= !concretize({tm}, sets);
        else if (tm.src == 's') xforms.push_back(tm), xformGuard.push_back(effGuards[q]), xformLab.push_back(effLab[q] + (effGuards[q].empty() ? " unguarded" : " guarded"));
        else anyImgs.push_back(tm);
      }
      for (int64_t b : pairFills) { // the fill byte repeated over the tag
        int64_t v = 0;
        for (unsigned k = 0; k < dWidth / 8; k++) v = (v << 8) | b;
        sets.insert(v);
      }
      // Projection (precision only): tag sets may be computed on the bits a
      // read's tests observe, R; tests and guards are then judged with the
      // other bits unknown (may hold), which is sound for any R, and every
      // map is bitwise, so it commutes with the projection. Used when the
      // full-width sets widen: each read gets the sets for its own R.
      std::vector<std::string> wideTests, witnessLines;
      const int64_t wmask = dWidth >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << dWidth) - 1);
      auto observedBits = [&](const std::vector<Test> &g) -> int64_t {
        int64_t r = 0;
        for (const Test &t : g) {
          uint64_t acc = 0;
          const bool ok = demand(t.cond, t.d, 1, acc);
          if (ok && llvm::popcount(acc) <= 12) r |= (int64_t)acc;
          else { // an equality or an unfollowed test: the bits of its constants
            std::vector<const Value *> work{t.cond};
            std::set<const Value *> seen;
            while (!work.empty()) {
              const Value *X = work.back();
              work.pop_back();
              if (!seen.insert(X).second || X == t.d) continue;
              if (const auto *K = dyn_cast<ConstantInt>(X)) r |= (int64_t)K->getZExtValue();
              else if (const auto *U = dyn_cast<User>(X); U && isa<Instruction>(X))
                for (const Value *Op : U->operands()) work.push_back(Op);
            }
            if (VerboseLevel >= 2 && fs.size() >= 20 && wideTests.size() < 12) {
              std::string v;
              raw_string_ostream os(v);
              t.cond->print(os);
              wideTests.push_back((ok ? "" : "(unfollowed) ") + locOf(t.d) + ": " + os.str().substr(0, 100));
            }
          }
        }
        return r & wmask;
      };
      int64_t guardBits = 0;
      for (const auto &g : xformGuard) guardBits |= observedBits(g);
      for (const Writer &W : writers) for (const auto &g : W.ownGuards) guardBits |= observedBits(g);
      int64_t curR = wmask; // the projection in force
      auto holdsP = [&](const std::vector<Test> &tests, int64_t v) {
        if (curR == wmask) return holds(tests, v);
        KnownBits kb(64);
        kb.One = APInt(64, (uint64_t)(v & curR));
        kb.Zero = APInt(64, (uint64_t)(~v & curR));
        return mayHold(tests, kb);
      };
      int64_t projR = wmask; // reported: the widest projection used
      // Tag sets: explicit up to 4096 values; past that (or a map with
      // more than 12 free bits), widened to the known bits that agree
      // across the set, the rest free (ruling gamma: a sound superset).
      struct TagSet {
        std::set<int64_t> vals;
        bool wide = false;
        KnownBits kb{64};
        std::string why; // what widened it (reports)
      };
      bool anyWide = false;
      auto kbOf = [](int64_t v) { return KnownBits::makeConstant(APInt(64, (uint64_t)v)); };
      auto widen = [&](TagSet &T) {
        if (T.wide) return;
        T.wide = anyWide = true;
        bool first = true;
        for (int64_t v : T.vals) {
          T.kb = first ? kbOf(v) : T.kb.intersectWith(kbOf(v));
          first = false;
        }
        if (first) { // empty: the bottom (a conflict joins to anything)
          T.kb = KnownBits(64);
          T.kb.Zero.setAllBits();
          T.kb.One.setAllBits();
        }
        T.vals.clear();
      };
      auto joinKB = [](TagSet &T, const KnownBits &k) { T.kb = T.kb.intersectWith(k); };
      // The known bits of a map's image of kb: (u & a) | f | free(m).
      auto applyKB = [](const KnownBits &kb, const Term &t) {
        const APInt A(64, (uint64_t)t.a), F(64, (uint64_t)t.f), M(64, (uint64_t)t.m);
        KnownBits r(64);
        r.One = (kb.One & A & ~M) | F;
        r.Zero = ((kb.Zero & A) | ~(A | F | M)) & ~F & ~M;
        return r;
      };
      auto termKB = [](const Term &t) { // a constant term with free bits
        const APInt F(64, (uint64_t)t.f), M(64, (uint64_t)t.m);
        KnownBits r(64);
        r.One = F;
        r.Zero = ~(F | M);
        return r;
      };
      auto add = [&](TagSet &T, int64_t v) {
        if (T.wide) return joinKB(T, kbOf(v));
        T.vals.insert(v);
        if (T.vals.size() > 4096) widen(T);
      };
      auto addTerm = [&](TagSet &T, const Term &t) { // a 'c' term
        std::set<int64_t> cs;
        if (concretize({t}, cs)) for (int64_t v : cs) add(T, v);
        else { widen(T); joinKB(T, termKB(t)); }
      };
      auto addImages = [&](TagSet &T, const TagSet &From, const Term &t) {
        // From widened: the images lie among (sub of a) | f | (sub of m),
        // enumerable when a and m have few bits (a superset, kept exact).
        if (From.wide && llvm::popcount((uint64_t)(t.a | t.m)) <= 12) {
          const uint64_t fr = (uint64_t)(t.a | t.m) & ~(uint64_t)t.f;
          for (uint64_t sub = fr;; sub = (sub - 1) & fr) {
            add(T, (int64_t)sub | t.f);
            if (!sub) break;
          }
          return;
        }
        if (From.wide || llvm::popcount((uint64_t)t.m) > 12) {
          if (!T.wide) T.why = "an image " + termStr(t) + (From.wide ? " of a widened set" : "");
          widen(T);
          if (From.wide) joinKB(T, applyKB(From.kb, t));
          else for (int64_t v : From.vals) joinKB(T, applyKB(kbOf(v), t));
          return;
        }
        for (int64_t v : From.vals)
          for (uint64_t fr = (uint64_t)t.m, sub = fr;; sub = (sub - 1) & fr) {
            add(T, (v & t.a) | t.f | (int64_t)sub);
            if (!sub) break;
          }
      };
      // Close T under maps; a map applies to v only when v (may) satisfy
      // its guard.
      std::map<int64_t, std::pair<int64_t, std::string>> *prov = nullptr; // reports: how each tag arose
      const std::vector<std::string> *provLab = nullptr;
      auto closure = [&](TagSet &T, const std::vector<Term> &maps, const std::vector<std::vector<Test>> *guards) {
        auto guarded = [&](size_t mi) { return guards && mi < guards->size() && !(*guards)[mi].empty(); };
        if (!T.wide) {
          std::vector<int64_t> work(T.vals.begin(), T.vals.end());
          while (!work.empty() && !T.wide) {
            const int64_t v = work.back();
            work.pop_back();
            for (size_t mi = 0; mi < maps.size() && !T.wide; mi++) {
              const Term &t = maps[mi];
              if (guarded(mi) && !holdsP((*guards)[mi], v)) continue;
              if (llvm::popcount((uint64_t)t.m) > 12) {
                T.why = "a map with " + std::to_string(llvm::popcount((uint64_t)t.m)) + " free bits: " + termStr(t);
                widen(T);
                break;
              }
              for (uint64_t fr = (uint64_t)t.m, sub = fr;; sub = (sub - 1) & fr) {
                const int64_t w = (v & t.a) | t.f | (int64_t)sub;
                if (!T.vals.count(w)) {
                  if (prov && provLab && mi < provLab->size()) (*prov)[w] = {v, (*provLab)[mi]};
                  add(T, w);
                  if (T.wide) { T.why = "more than 4096 tags (last map " + termStr(t) + ")"; break; }
                  work.push_back(w);
                }
                if (!sub) break;
              }
            }
          }
          if (!T.wide) return;
        }
        for (bool changed = !T.kb.hasConflict(); changed;) {
          changed = false;
          for (size_t mi = 0; mi < maps.size(); mi++) {
            if (guarded(mi) && !mayHold((*guards)[mi], T.kb)) continue;
            const KnownBits before = T.kb;
            joinKB(T, applyKB(T.kb, maps[mi]));
            changed |= T.kb.Zero != before.Zero || T.kb.One != before.One;
          }
        }
      };
      struct Tags {
        std::vector<TagSet> w;
        bool wide = false, uWide = false;
        size_t uSize = 0;
        std::vector<std::map<int64_t, std::pair<int64_t, std::string>>> prov; // reports
      };
      const bool provOn = VerboseLevel >= 2 && fs.size() >= 20;
      std::map<int64_t, Tags> tagsByR;
      std::vector<bool> wAll(writers.size(), false);
      for (size_t i = 0; i < writers.size(); i++) wAll[i] = writers[i].unknown;
      auto computeTags = [&](int64_t R) -> const Tags & {
        auto [it, ins] = tagsByR.try_emplace(R);
        if (!ins) return it->second;
        curR = R;
        anyWide = false;
        auto pv = [&](int64_t v) { return v & R; };
        auto pt = [&](Term t) { t.a &= R; t.f &= R; t.m &= R; return t; };
        auto pts = [&](const std::vector<Term> &ts) {
          std::vector<Term> r;
          for (const Term &t : ts) r.push_back(pt(t));
          return r;
        };
        const std::vector<Term> xf = pts(xforms), ai = pts(anyImgs);
        TagSet sets2;
        for (int64_t v : sets) add(sets2, pv(v));
        if (setsAll)
          for (const TagStore *t : retags)
            for (const Term &tm : t->terms)
              if (tm.src == 'c') addTerm(sets2, pt(tm));
        TagSet U = sets2;
        std::vector<Term> allMaps = xf;
        std::vector<std::vector<Test>> allGuards = xformGuard;
        allMaps.insert(allMaps.end(), ai.begin(), ai.end());
        allGuards.resize(allMaps.size());
        for (const Writer &W : writers) {
          for (int64_t v : W.tags) add(U, pv(v));
          for (const Term &t : W.fromAny) allMaps.push_back(pt(t));
          allGuards.resize(allMaps.size());
          for (const Term &t : W.ownMaps) allMaps.push_back(pt(t));
          allGuards.insert(allGuards.end(), W.ownGuards.begin(), W.ownGuards.end());
        }
        closure(U, allMaps, &allGuards);
        TagSet base = sets2; // what retags may set on any object
        for (const Term &t : ai) addImages(base, U, t);
        Tags &T = it->second;
        T.w.resize(writers.size());
        for (size_t i = 0; i < writers.size(); i++) {
          if (wAll[i]) continue;
          TagSet from;
          for (int64_t v : writers[i].tags) add(from, pv(v));
          if (base.wide) { from.why = "the retag base widened (" + base.why + ")"; widen(from); joinKB(from, base.kb); }
          else for (int64_t v : base.vals) add(from, v);
          for (const Term &t : writers[i].fromAny) addImages(from, U, pt(t));
          std::vector<Term> maps = xf;
          for (const Term &t : writers[i].ownMaps) maps.push_back(pt(t));
          std::vector<std::vector<Test>> gs = xformGuard;
          gs.insert(gs.end(), writers[i].ownGuards.begin(), writers[i].ownGuards.end());
          std::vector<std::string> labs = xformLab;
          labs.insert(labs.end(), writers[i].ownLab.begin(), writers[i].ownLab.end());
          if (provOn) {
            T.prov.resize(writers.size());
            prov = &T.prov[i];
            provLab = &labs;
          }
          closure(from, maps, &gs);
          prov = nullptr;
          provLab = nullptr;
          T.wide |= from.wide;
          T.w[i] = std::move(from);
        }
        T.uWide = U.wide;
        T.uSize = U.vals.size();
        curR = wmask;
        return T;
      };
      const Tags &full = computeTags(wmask);
      const bool uAll = full.uWide;
      const std::vector<TagSet> &wTags = full.w;
      // The sets a read is judged on: full width, unless they widened; then
      // its own projection (its tests' bits, the guards' too if they fit).
      auto tagsFor = [&](const std::vector<Test> &tests) -> std::pair<const Tags *, int64_t> {
        if (!full.wide) return {&full, wmask};
        int64_t R = observedBits(tests);
        if (llvm::popcount((uint64_t)(R | guardBits)) <= 12) R |= guardBits;
        if (llvm::popcount((uint64_t)R) > 12) return {&full, wmask};
        if (projR == wmask || llvm::popcount((uint64_t)R) > llvm::popcount((uint64_t)projR)) projR = R;
        return {&computeTags(R), R};
      };
      // Reads: the stable tests of D (same object) dominating them.
      std::vector<std::pair<const Instruction *, std::vector<size_t>>> keyed;
      size_t pairReadsKeyed = 0;
      for (const FAccess &r : fLoads[Ff]) {
        std::vector<Test> tests;
        testsAtM(r.I, r.obj, Df, Ff, tests, pas);
        if (tests.empty()) { readsNoTest++; continue; }
        std::vector<size_t> adm;
        const auto [TT, R] = tagsFor(tests);
        curR = R;
        for (size_t i = 0; i < writers.size(); i++) {
          if (wAll[i]) { adm.push_back(i); continue; }
          const TagSet &ws = TT->w[i];
          if (ws.wide) {
            if (!ws.kb.hasConflict() && mayHold(tests, ws.kb)) adm.push_back(i);
            continue;
          }
          for (int64_t v : ws.vals)
            if (holdsP(tests, v)) {
              adm.push_back(i);
              if (VerboseLevel >= 2 && fs.size() >= 20 && witnessLines.size() < 60)
              {
                std::string chain;
                if (provOn && i < TT->prov.size()) {
                  int64_t cur = v;
                  for (int d = 0; d < 12; d++) {
                    auto pit = TT->prov[i].find(cur);
                    if (pit == TT->prov[i].end()) break;
                    chain += " <- 0x" + utohexstr((uint64_t)pit->second.first) + " by " + pit->second.second;
                    cur = pit->second.first;
                  }
                }
                witnessLines.push_back("    read " + locOf(r.I) + " (R 0x" + utohexstr((uint64_t)R) + ", " +
                                       std::to_string(ws.vals.size()) + " tags) admits " + locOf(writers[i].I) +
                                       " by tag 0x" + utohexstr((uint64_t)v) + chain);
              }
              break;
            }
        }
        curR = wmask;
        if (adm.size() == writers.size()) { readsAll++; continue; }
        keyed.push_back({r.I, adm});
        pairReadsKeyed++;
      }
      if (keyed.empty()) {
        if (fs.size() >= 10) {
          size_t nAll = std::count(wAll.begin(), wAll.end(), true);
          std::string d = "PLAIN " + S + "+" + std::to_string(Ff.second) + " by +" + std::to_string(dOff) + " (" +
                          std::to_string(fs.size()) + " writes): every tested read admits every writer; " +
                          (uAll ? std::string("widened") : std::to_string(full.uSize)) + " tags, " +
                          std::to_string(nAll) + " writers with any tag; bits observed " +
                          std::to_string(llvm::popcount((uint64_t)projR)) + "; call-site effects " + std::to_string(effSites) +
                          " (" + std::to_string(effAbsorbed) + " absorbed by callers); tag stores " +
                          std::to_string(absorbedStores) + " accounted at call sites, " + std::to_string(unseenStores) +
                          " never read under, " + std::to_string(closedStores) +
                          " closed, " + std::to_string(openStores) + " open (retags" +
                          (openAt.empty() ? std::string() : ", e.g. " + openAt) + "); " +
                          std::to_string(observedWriters) + " writers read under their prior tag (" +
                          std::to_string(openPrior) + " of any tag); transforms " + std::to_string(guarded) +
                          " guarded, " + std::to_string(unguarded) + " unguarded";
          for (const std::string &x : xformAt) d += "; retag " + x;
          taggedReport.push_back(d);
          if (VerboseLevel >= 2) {
            for (const std::string &u : unguardedAt) taggedReport.push_back("    unguarded transform " + u);
            for (const std::string &u : allRetagAt) taggedReport.push_back("    open retag " + u);
            for (const std::string &u : wideTests) taggedReport.push_back("    test observing many bits " + u);
            for (const std::string &u : witnessLines) taggedReport.push_back(u);
            {
              std::string d = "    retag constants:";
              for (int64_t v : sets) d += " " + std::to_string(v);
              d += "; U " + std::string(full.uWide ? "widened" : std::to_string(full.uSize));
              d += "; anyImgs " + std::to_string(anyImgs.size()) + ":";
              for (const Term &t : anyImgs) d += " " + termStr(t);
              taggedReport.push_back(d);
              for (const TagStore *t : retags) {
                bool c = false;
                for (const Term &tm : t->terms) c |= tm.src == 'c';
                if (!c) continue;
                std::string e = "    constant retag " + locOf(t->I) + " {";
                for (const Term &tm : t->terms) e += std::string(e.back() == '{' ? "" : ", ") + termStr(tm);
                taggedReport.push_back(e + "}");
              }
            }
            for (size_t q = 0; q < writers.size(); q++) {
              std::string d = "    writer " + locOf(writers[q].I) + ": ";
              if (wAll[q]) d += "any tag (" + writers[q].why + ")";
              else if (wTags[q].wide) {
                SmallString<80> z, o;
                wTags[q].kb.Zero.toStringUnsigned(z, 16);
                wTags[q].kb.One.toStringUnsigned(o, 16);
                d += "widened, known zero 0x" + std::string(z) + ", known one 0x" + std::string(o) + " (" +
                     wTags[q].why + ")";
              } else {
                d += std::to_string(wTags[q].vals.size()) + " tags:";
                size_t c = 0;
                for (int64_t v : wTags[q].vals) { if (c++ == 8) { d += " ..."; break; } d += " " + std::to_string(v); }
              }
              taggedReport.push_back(d);
            }
            for (size_t q = 0; q < effMaps.size(); q++)
              taggedReport.push_back("    call-site retag map " + termStr(effMaps[q]) +
                                     (effGuards[q].empty() ? " (unguarded)" : " (guarded)"));
          }
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
      taggedPairAssumes.push_back(std::vector<uint32_t>(pas.begin(), pas.end()));
      std::string extra;
      for (const std::string &d : xformAt) extra += "; retag " + d;
      for (const std::string &v : via) extra += "; bound " + v;
      taggedReport.push_back("KEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                               std::to_string(dOff) + ": " + std::to_string(writers.size()) + " writers, " +
                               std::to_string(pairReadsKeyed) + " reads keyed, " +
                               std::to_string(retags.size()) + " retags, bits observed " + std::to_string(llvm::popcount((uint64_t)projR)) + " (" + std::to_string(closedStores) +
                               " tag stores closed; " + std::to_string(observedWriters) + " writers read under their prior tag; " +
                               std::to_string(guarded) +
                               " guarded, " + std::to_string(unguarded) + " unguarded transforms), " +
                               (uAll ? std::string("widened") : std::to_string(full.uSize)) + " tags" + extra);
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
  {
    const Function *top = nullptr;
    for (auto &[F, n] : walkBlocksBy) if (!top || n > walkBlocksBy[top]) top = F;
    {
      std::string sites;
      for (const Instruction *I : eqMergeSites) if (sites.size() < 300) sites += " " + locOf(I);
      CG_LOG("TaggedFields: pointer-equality identity merges: " << eqMergeSites.size() << " (" << sites << " )\n");
    }
    CG_LOG("TaggedFields: callee D-effects composed: " << effClosed << " closed, " << effOpen << " open ("
           << effComputes << " effect computations; content effects " << ceRounds << " rounds, " << ceUnsettled
           << " pairs unsettled, " << ceSecs << " s)\n");
    if (VerboseLevel >= 2)
      for (const std::string &d : effOpenAt) CG_LOG("TaggedFields:   open D-effect at " << d << "\n");
    CG_LOG("TaggedFields: walks " << walksBack << " backward, " << walksFwd << " forward, " << walkBlocks
           << " blocks (most in " << (top ? top->getName().str() : std::string("-")) << ": "
           << (top ? walkBlocksBy[top] : 0) << "); " << sumComputes << " summary computations, "
           << walkBounds << " walks at the bound; " << taggedAssumes.size() << " alias assumptions\n");
  }
  CG_LOG("TaggedFields: " << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count()
         << " s; " << pairsKeyed << " pairs keyed (" << writersTagged << " tagged writers, "
         << writersUntagged << " untagged: no co-written tag in the writer's function); reads: "
         << readsKeyed << " keyed, " << readsNoTest << " with no stable dominating test (" << testsUnstable
         << " tests dropped: D may be written before the access), " << readsAll
         << " admitting every writer; " << pairsNonConst << " pairs unkeyed by a non-constant retag, "
         << pairsUncertified << " by an uncertified tag\n");
  if (VerboseLevel >= 2)
    for (const std::string &l : taggedReport) CG_LOG("TaggedFields:   " << l << "\n");
  taggedCounts = {pairsKeyed, writersTagged, writersUntagged, readsKeyed, readsNoTest, readsAll, pairsNonConst};
}
