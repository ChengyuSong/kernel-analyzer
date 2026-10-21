// Allocation sizes and the IR helpers of the extent rules (AllocExtents.h).

#include "AllocExtents.h"
#include "Annotation.h"
#include "CallGraphInternal.h"
#include "NamedCells.h"
#include "StructAnalyzer.h"
#include <llvm/IR/Dominators.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <numeric>
#include <optional>

using namespace llvm;

namespace ka {

// Does a struct named like S start at offset `off` of T (through nested
// members and array elements)? An anonymous struct's name names nothing
// (isAnonStruct): it is found only as the type Same itself, or one of its
// layout.
bool structStartsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL,
                    const StructType *Same) {
  const bool anon = isAnonStructName(S);
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (anon ? ST == Same : ST->hasName() && stripStructNameSuffix(ST->getName()) == S)
        return true;
      // Layout-identical types are one type to -O3 (it indexes a
      // TermOffsetCtx as a SnippetIter): the same struct here.
      if (Same && ST != Same && !ST->isOpaque() &&
          ST->isLayoutIdentical(const_cast<StructType *>(Same)))
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


// The element type of the trailing array T ends in, or null: its last
// member, recursively, an array of 0 or 1 elements ending at T's end (the
// flexible-array idiom `x[0]` / `x[1]`; an array declared longer is a
// field of its own, and what follows it is a segment, labeled by its use).
Type *trailingArrayElem(Type *T, const DataLayout &DL, uint64_t *n) {
  for (int depth = 0; depth < 64 && T; depth++) {
    if (auto *AT = dyn_cast<ArrayType>(T)) {
      if (AT->getNumElements() > 1) return nullptr;
      if (n) *n = AT->getNumElements();
      return AT->getElementType();
    }
    auto *ST = dyn_cast<StructType>(T);
    if (!ST || ST->isOpaque() || ST->getNumElements() == 0) return nullptr;
    const StructLayout *SL = DL.getStructLayout(ST);
    const unsigned i = ST->getNumElements() - 1;
    if (SL->getElementOffset(i) + DL.getTypeAllocSize(ST->getElementType(i)) != SL->getSizeInBytes()) return nullptr;
    T = ST->getElementType(i);
  }
  return nullptr;
}

// The last store into slot S at or before I, walking back in I's block.
const StoreInst *lastStoreFrom(const Instruction *I, const AllocaInst *S) {
  for (; I; I = I->getPrevNode())
    if (const auto *SI = dyn_cast<StoreInst>(I); SI && SI->getPointerOperand() == S) return SI;
  return nullptr;
}
// The last store into S in BB, and the last one before L in L's block.
const StoreInst *lastStoreIn(const BasicBlock *BB, const AllocaInst *S) { return lastStoreFrom(&BB->back(), S); }
const StoreInst *lastStoreBefore(const Instruction *L, const AllocaInst *S) {
  return lastStoreFrom(L->getPrevNode(), S);
}

// The store into S reaching BB's end: BB's last, else up a chain of single
// predecessors (not through `stop`, the block a load is in).
const StoreInst *storeAtEnd(const BasicBlock *BB, const AllocaInst *S, const BasicBlock *stop) {
  std::set<const BasicBlock *> walked{stop};
  for (; BB && walked.insert(BB).second; BB = BB->getSinglePredecessor())
    if (const StoreInst *SI = lastStoreIn(BB, S)) return SI;
  return nullptr;
}

// Is A a slot (only loaded, and stored into by value)? *several: stored
// more than once; *only: its store when once.
bool sizeSlot(const AllocaInst *A, bool &several, const StoreInst *&only) {
  several = false;
  only = nullptr;
  for (const User *U : A->users()) {
    if (isa<LoadInst>(U)) continue;
    const auto *SI = dyn_cast<StoreInst>(U);
    if (!SI || SI->getPointerOperand() != A || SI->getValueOperand() == A) return false;
    several |= only != nullptr;
    only = SI;
  }
  return only != nullptr;
}

// The one store reaching load L of slot S stored several times: the last
// store before L in its block, else in the nearest block up a chain of
// single predecessors, else the store every predecessor's chain reaches
// (all the same one), else, when every store is in the entry block, the
// last one there. Null when none of these decides it.
const StoreInst *reachingStore(const LoadInst *L, const AllocaInst *S) {
  const BasicBlock *B = L->getParent();
  if (const StoreInst *SI = lastStoreBefore(L, S)) return SI;
  if (const BasicBlock *P = B->getSinglePredecessor()) return storeAtEnd(P, S, B);
  const StoreInst *agreed = nullptr;
  bool all = !pred_empty(B);
  for (const BasicBlock *P : predecessors(B)) {
    const StoreInst *SI = storeAtEnd(P, S, B);
    all &= SI && (!agreed || SI == agreed);
    agreed = SI;
  }
  if (all && agreed) return agreed;
  const BasicBlock *E = &L->getFunction()->getEntryBlock();
  if (B == E) return nullptr;
  for (const User *U : S->users())
    if (const auto *SI = dyn_cast<StoreInst>(U); SI && SI->getParent() != E) return nullptr;
  return lastStoreIn(E, S);
}

// An allocation size's source: through casts, and at -O0 a local slot that
// never escapes (its only users are direct loads and stores into it: no
// call can write it through its address) forwards the stored value
// reaching the load (sqlite3: nByte = sizeof(Fts3SegReader) +
// (nElem+1)*sizeof(Fts3HashElem *); malloc(nByte); fts3InitVtab reuses
// nByte; newchunk rounds n at entry).
const Value *sizeThrough(const Value *V) {
  for (int d = 0; d < 8; d++) {
    if (const auto *CI = dyn_cast<CastInst>(V)) { V = CI->getOperand(0); continue; }
    if (const auto *L = dyn_cast<LoadInst>(V))
      if (const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
        bool several = false;
        const StoreInst *only = nullptr;
        if (sizeSlot(S, several, only)) {
          if (!several) { V = only->getValueOperand(); continue; }
          if (const StoreInst *SI = reachingStore(L, S)) { V = SI->getValueOperand(); continue; }
        }
      }
    break;
  }
  return V;
}

// Is size expression X a multiple of sz: a constant multiple (nonzero: a
// size, not a flag), or a product (or shift) with one?
bool isMultipleOf(const Value *X, uint64_t sz, bool nonzero) {
  X = sizeThrough(X);
  if (const auto *B = dyn_cast<BinaryOperator>(X)) {
    if (B->getOpcode() == Instruction::Mul)
      for (const Value *Op : B->operands())
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(Op)))
          return (!nonzero || K->getZExtValue()) && K->getZExtValue() % sz == 0;
    if (B->getOpcode() == Instruction::Shl)
      if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(B->getOperand(1))))
        return K->getZExtValue() < 63 && (1ULL << K->getZExtValue()) % sz == 0;
  }
  if (const auto *K = dyn_cast<ConstantInt>(X))
    return (!nonzero || K->getZExtValue()) && K->getZExtValue() % sz == 0;
  return false;
}

// Does an allocation call's size argument say "a T followed by trailing
// data": a constant larger than T and not a multiple of it, or a sum (any
// depth: -O3 chains `sizeof(T) + 8*n + 40*m + k`) with a constant term of
// at least sizeof(T) and some other term that is not a multiple of it
// (`n*sizeof(T) + sizeof(T)` is an array of n+1)? The size is add + the
// product of ops (a wrapper's term `n + 16` at its call `w(len)`: len
// read as above, 16 one more constant term).
bool headerPlusTail(const std::vector<const Value *> &ops, uint64_t sz, int64_t add) {
  auto lookThrough = sizeThrough;
  auto multipleOf = [&](const Value *X) { return isMultipleOf(X, sz); };
  if (add) {
    uint64_t prod = 1;
    bool allConst = true, multiple = false;
    for (const Value *A : ops) {
      const auto *K = dyn_cast<ConstantInt>(lookThrough(A));
      if (K) prod *= K->getZExtValue();
      else allConst = false;
      multiple |= isMultipleOf(A, sz);
    }
    if (allConst) {
      const int64_t k = (int64_t)prod + add;
      return k > (int64_t)sz && k % (int64_t)sz != 0;
    }
    if (add < (int64_t)sz) return false; // no header among the constants
    if (ops.size() != 1) return !multiple; // add + a product
  }
  if (ops.size() != 1) return false; // a product (calloc) is an array or one, not T plus data
  for (const Value *A : ops) {
    const Value *V = lookThrough(A);
    if (!V->getType()->isIntegerTy()) continue;
    if (const auto *K = dyn_cast<ConstantInt>(V)) {
      const uint64_t k = K->getZExtValue();
      if (k > sz && k % sz != 0) return true;
      continue;
    }
    std::vector<const Value *> terms, work{V};
    while (!work.empty() && terms.size() < 32) {
      const Value *X = lookThrough(work.back());
      work.pop_back();
      const auto *B = dyn_cast<BinaryOperator>(X);
      if (B && B->getOpcode() == Instruction::Add) {
        work.push_back(B->getOperand(0));
        work.push_back(B->getOperand(1));
      } else {
        terms.push_back(X);
      }
    }
    if (terms.size() < 2 && !add) continue;
    bool header = add >= (int64_t)sz, other = false;
    for (const Value *T : terms) {
      const auto *K = dyn_cast<ConstantInt>(T);
      // A constant term is a header size only when it is positive: the -O3
      // sum `nsymz * 16 + (len - 8 * nsymz - 8) + 1` carries -8, which read
      // unsigned (2^64 - 8) was "a header" at every offset.
      if (K && !K->isNegative() && K->getZExtValue() >= sz) header = true;
      else if (!multipleOf(T)) other = true;
    }
    if (header && other) return true;
  }
  return false;
}

// Does an allocation call allocate exactly sz bytes (its integer
// arguments all constants, multiplying to sz: malloc(64), calloc(1, 64))?
// Then it is one T, not an array of T.
bool exactlyOne(const std::vector<const Value *> &ops, uint64_t sz, int64_t add) {
  uint64_t prod = 1;
  bool any = false;
  for (const Value *V : ops) {
    V = sizeThrough(V);
    const auto *K = dyn_cast<ConstantInt>(V);
    if (!K) return false;
    prod *= K->getZExtValue();
    any = true;
  }
  return any && (int64_t)prod + add == (int64_t)sz;
}

// Does an allocation call's size say "an array of T": an integer argument
// that is a multiple of sizeof(T) (calloc(n, sizeof T), malloc(n * sizeof
// T), realloc(p, k * sizeof T))?
bool sizeIsMultiple(const std::vector<const Value *> &ops, uint64_t sz, int64_t add) {
  if (add % (int64_t)sz) return false;
  for (const Value *V : ops)
    if (isMultipleOf(V, sz, true)) return true;
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


} // namespace ka

using namespace ka;

CallGraphPass::SizeTerms::SizeTerms(CallGraphPass &Pass, const DataLayout &Layout) : P(Pass), DL(Layout) {
  // Is every value of t nonzero (a formal read k > 0 when 0, scaled and
  // shifted up, or rounded)?
  nonzero = [](const SizeTerm &t) {
    if (!t.known || t.partial) return false;
    if (t.isConst()) return t.c != 0;
    return t.zeroK > 0 && !t.formals.empty() && t.c > 0 && t.add >= 0;
  };
  constT = [](uint64_t k) { SizeTerm t; t.known = true; t.c = k; return t; };
  // What every value of t is a multiple of.
  multOf = [](const SizeTerm &t) -> uint64_t {
    if (t.align) return t.align;
    if (t.isConst()) return t.c;
    return std::gcd(t.c, (uint64_t)(t.add < 0 ? -t.add : t.add));
  };
  multiple = [](uint64_t m) {
    SizeTerm t;
    if (m <= 1) return t;
    t.known = true;
    t.c = m;
    t.partial = true;
    return t;
  };
  // A constant's add folds into c (a size below 0 is no size).
  norm = [](SizeTerm t) {
    if (t.formals.empty()) t.zeroK = -1;
    if (t.known && t.formals.empty() && !t.partial && !t.align) {
      const int64_t v = (int64_t)t.c + t.add;
      if (v < 0) return SizeTerm{};
      t.c = (uint64_t)v;
      t.add = 0;
    }
    return t;
  };
  plusT = [&](SizeTerm a, const SizeTerm &b) -> SizeTerm {
    if (!a.known || !b.known) return {};
    if (!a.isConst() && b.isConst() && !a.partial && !a.align) { a.add += (int64_t)b.c; return norm(a); }
    if (a.isConst() && !b.isConst() && !b.partial && !b.align) { SizeTerm r = b; r.add += (int64_t)a.c; return norm(r); }
    if (a.isConst() && b.isConst()) return constT(a.c + b.c);
    return multiple(std::gcd(multOf(a), multOf(b)));
  };
  plusK = [&](const SizeTerm &a, int64_t k) -> SizeTerm {
    if (!a.known) return {};
    if (a.isConst()) return norm(SizeTerm{true, a.c, {}, false, k, 0});
    if (a.partial || a.align) return multiple(std::gcd(multOf(a), (uint64_t)(k < 0 ? -k : k)));
    SizeTerm r = a;
    r.add += k;
    return norm(r);
  };
  timesT = [&](SizeTerm a, SizeTerm b) -> SizeTerm {
    if (!a.known && !b.known) return {};
    if (!a.known) std::swap(a, b);
    if (!b.known) { // a further unknown factor
      if (a.add || a.align || a.zeroK >= 0 || a.formals.empty()) return multiple(multOf(a));
      a.partial = true;
      return a;
    }
    if (a.isConst()) std::swap(a, b);
    if (b.isConst() && b.c == 1) return a;
    if (b.isConst()) {
      if (a.align) return multiple(a.align * b.c);
      a.c *= b.c;
      a.add *= (int64_t)b.c;
      if (a.zeroK >= 0) a.zeroK *= (int64_t)b.c; // the zero case scales too
      return norm(a);
    }
    if (a.add || b.add || a.align || b.align || a.zeroK >= 0 || b.zeroK >= 0 ||
        a.formals.size() + b.formals.size() > 2)
      return multiple(multOf(a) * multOf(b));
    a.c *= b.c;
    a.partial |= b.partial;
    a.formals.insert(a.formals.end(), b.formals.begin(), b.formals.end());
    return a;
  };
  alignT = [&](SizeTerm x, uint64_t al) -> SizeTerm {
    if (x.isConst()) return constT((x.c + al - 1) & ~(al - 1));
    if (x.known && x.align && x.align % al == 0) return x; // already rounded to al
    // A multiple of al rounded to al is itself (row (2): round8(72 n) is
    // 72 n); its zero case rounds.
    if (x.known && !x.align && !x.add && x.c % al == 0 && (x.partial || !x.formals.empty())) {
      if (x.zeroK >= 0) x.zeroK = (int64_t)(((uint64_t)x.zeroK + al - 1) & ~(al - 1));
      return x;
    }
    if (!x.known || x.partial || x.align) return multiple(std::max(al, x.align));
    x.align = al;
    return x;
  };
  // Two returns' terms: equal, or the gcd fact.
  joinT = [&](const SizeTerm &a, const SizeTerm &b) -> SizeTerm {
    if (!a.known || !b.known) return {};
    if (a == b) return a;
    return multiple(std::gcd(multOf(a), multOf(b)));
  };
  sigOf = [](StringRef N, std::vector<unsigned> &idx) {
    idx.clear();
    if (N == "calloc") idx = {0, 1};
    else if (N == "realloc" || N == "aligned_alloc" || N == "memalign") idx = {1};
    else if (N == "reallocarray") idx = {1, 2};
    else if (N == "malloc" || N == "valloc" || N == "pvalloc") idx = {0};
    else {
      int size = -1, flag = -1;
      if (isAllocFn(N, &size, &flag) && size >= 0) idx = {(unsigned)size};
    }
    return !idx.empty();
  };
  // A2' (4): masks 2^k - al read as -al
  // V's term in F's formals.
  termIn =
      [&](const Value *V, const Function *F, int d) -> SizeTerm {
    if (d > 12) return {};
    V = sizeThrough(V);
    if (const auto *K = dyn_cast<ConstantInt>(V)) return K->isNegative() ? SizeTerm{} : constT(K->getZExtValue());
    if (const auto *A = dyn_cast<Argument>(V); A && A->getParent() == F) return {true, 1, {A->getArgNo()}};
    // "x, k when zero": x's term with zeroK, or x's own when it is nonzero.
    auto whenZero = [&](const Value *X, const ConstantInt *K) -> SizeTerm {
      if (!K || K->isNegative()) return {};
      SizeTerm t = termIn(X, F, d + 1);
      if (nonzero(t)) return t;
      if (t.known && !t.partial && !t.align && t.zeroK < 0 && t.formals.size() == 1 && t.c == 1 && !t.add) {
        t.zeroK = K->getSExtValue();
        return t;
      }
      return {};
    };
    // Is C `x == 0` (eq) or `x != 0` (!eq)? Returns x.
    auto zeroTest = [](const Value *C, bool &eq) -> const Value * {
      const auto *Cmp = dyn_cast<ICmpInst>(C);
      const auto *Z = Cmp ? dyn_cast<ConstantInt>(Cmp->getOperand(1)) : nullptr;
      if (!Z || !Z->isZero()) return nullptr;
      if (Cmp->getPredicate() != ICmpInst::ICMP_EQ && Cmp->getPredicate() != ICmpInst::ICMP_NE) return nullptr;
      eq = Cmp->getPredicate() == ICmpInst::ICMP_EQ;
      return Cmp->getOperand(0);
    };
    if (const auto *II = dyn_cast<IntrinsicInst>(V); II && II->getIntrinsicID() == Intrinsic::umax)
      for (unsigned o = 0; o < 2; o++) // -O2: umax(x, 1) is x ? x : 1, the same function
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(II->getArgOperand(o))); K && K->isOne())
          return whenZero(II->getArgOperand(1 - o), K);
    if (const auto *Sel = dyn_cast<SelectInst>(V)) { // -O3: select (x == 0), k, x
      bool eq = false;
      const Value *X = zeroTest(Sel->getCondition(), eq);
      const Value *KV = eq ? Sel->getTrueValue() : Sel->getFalseValue();
      const Value *XV = eq ? Sel->getFalseValue() : Sel->getTrueValue();
      const auto *K = dyn_cast<ConstantInt>(sizeThrough(KV));
      if (X && sizeThrough(X) == sizeThrough(XV)) return whenZero(XV, K);
      // The test before a rounding of the same formal (-O3 bfd_alloc:
      // select (n == 0), 8, (n + 7) & -8): the rounded formal reading K
      // when zero, K a multiple of the rounding (round(K) is K).
      const SizeTerm tx = X ? termIn(X, F, d + 1) : SizeTerm{};
      SizeTerm ty = termIn(XV, F, d + 1);
      if (K && !K->isNegative() && tx.known && tx.formals.size() == 1 && tx.c == 1 && !tx.add && !tx.align &&
          !tx.partial && tx.zeroK < 0 && ty.known && ty.formals == tx.formals && ty.c == 1 && !ty.add &&
          ty.align && !ty.partial && ty.zeroK < 0 && K->getZExtValue() % ty.align == 0) {
        ty.zeroK = K->getSExtValue();
        return ty;
      }
      return {};
    }
    if (const auto *L = dyn_cast<LoadInst>(V)) { // -O0: the slot form of the same
      const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
      bool several = false;
      const StoreInst *only = nullptr;
      const BasicBlock *B = L->getParent();
      if (!S || !sizeSlot(S, several, only) || lastStoreBefore(L, S) || pred_size(B) != 2) return {};
      const BasicBlock *P = nullptr, *Q = nullptr;
      for (const BasicBlock *X : predecessors(B))
        if (const BasicBlock *XP = X->getSinglePredecessor(); XP && XP != X && is_contained(predecessors(B), XP))
          P = X, Q = XP;
      if (!P) return {};
      const auto *BrP = dyn_cast<BranchInst>(P->getTerminator());
      const auto *Br = dyn_cast<BranchInst>(Q->getTerminator());
      const StoreInst *SK = lastStoreIn(P, S);
      const StoreInst *SQ = storeAtEnd(Q, S, B);
      if (!BrP || BrP->isConditional() || !Br || !Br->isConditional() || !SK || !SQ) return {};
      bool eq = false;
      const Value *X = zeroTest(Br->getCondition(), eq);
      if (!X || Br->getSuccessor(eq ? 0 : 1) != P || Br->getSuccessor(eq ? 1 : 0) != B) return {};
      if (sizeThrough(X) != sizeThrough(SQ->getValueOperand())) return {};
      return whenZero(SQ->getValueOperand(), dyn_cast<ConstantInt>(SK->getValueOperand()));
    }
    const auto *B = dyn_cast<BinaryOperator>(V);
    if (!B) return {};
    const auto *K1 = dyn_cast<ConstantInt>(sizeThrough(B->getOperand(1)));
    switch (B->getOpcode()) {
    case Instruction::Mul:
      return timesT(termIn(B->getOperand(0), F, d + 1), termIn(B->getOperand(1), F, d + 1));
    case Instruction::Shl:
      if (K1 && K1->getZExtValue() < 63)
        return timesT(termIn(B->getOperand(0), F, d + 1), constT(1ULL << K1->getZExtValue()));
      return {};
    case Instruction::Add:
      if (K1) return plusK(termIn(B->getOperand(0), F, d + 1), K1->getSExtValue());
      return plusT(termIn(B->getOperand(0), F, d + 1), termIn(B->getOperand(1), F, d + 1));
    case Instruction::Sub:
      if (K1) return plusK(termIn(B->getOperand(0), F, d + 1), -K1->getSExtValue());
      return {};
    case Instruction::And: {
      // x & -al: a multiple of al whatever x is; (n + al - 1) & -al is n
      // rounded up. A mask 2^k - al is the same when x < 2^k, which the IR
      // bounds for zext_iN(y) + c with 2^N - 1 + c < 2^k (-O3 bfd_hash_allocate:
      // (zext_i32(n) + 7) & 0x1fffffff8).
      uint64_t al = 0;
      if (K1 && K1->isNegative() && (-K1->getValue()).isPowerOf2()) al = (-K1->getValue()).getZExtValue();
      else if (K1 && !K1->isZero() && K1->getBitWidth() == 64) {
        const uint64_t m = K1->getZExtValue(), lo = m & (~m + 1);
        const auto *A = dyn_cast<BinaryOperator>(B->getOperand(0));
        const auto *Z = dyn_cast<ZExtInst>(A && A->getOpcode() == Instruction::Add ? A->getOperand(0) : B->getOperand(0));
        const auto *C = A && A->getOpcode() == Instruction::Add ? dyn_cast<ConstantInt>(A->getOperand(1)) : nullptr;
        const uint64_t c = C && !C->isNegative() ? C->getZExtValue() : 0;
        if (lo > 1 && llvm::isPowerOf2_64(m + lo) && Z && (!A || A->getOpcode() != Instruction::Add || C)) {
          const unsigned N = Z->getSrcTy()->getIntegerBitWidth();
          if (N < 63 && (1ULL << N) - 1 + c < m + lo) {
            al = lo;
            sizeZextMask.insert(B);
          }
        }
      }
      if (al) {
        // (y + al - 1) & -al, also ((y + al) - 1) & -al: y rounded up, read
        // from the sum's own operand (y may itself be rounded).
        int64_t k = 0;
        const Value *Y = sizeThrough(B->getOperand(0));
        for (int i = 0; i < 2; i++) {
          const auto *S = dyn_cast<BinaryOperator>(Y);
          const auto *C = S ? dyn_cast<ConstantInt>(sizeThrough(S->getOperand(1))) : nullptr;
          if (!C || (S->getOpcode() != Instruction::Add && S->getOpcode() != Instruction::Sub)) break;
          k += S->getOpcode() == Instruction::Add ? C->getSExtValue() : -C->getSExtValue();
          Y = sizeThrough(S->getOperand(0));
        }
        if (k == (int64_t)al - 1)
          if (const SizeTerm y = termIn(Y, F, d + 1); y.known) return alignT(y, al);
        SizeTerm x = termIn(B->getOperand(0), F, d + 1);
        if (x.isConst()) return constT(x.c & ~(al - 1));
        if (x.known && !x.partial && !x.align && x.add == (int64_t)al - 1) {
          x.add = 0;
          return alignT(x, al);
        }
        return multiple(al);
      }
      return {};
    }
    default:
      return {};
    }
  };
  // A2' counters: carves sized by "n, K when n == 0", by header-then-store,
  // carve phis read by their carve term, zext masks read as -al.
  // The term of call C expressed in F's formals (F null: C's own operands
  // are not classified, the callee's term is returned as is).
  callTerm = [&](const CallBase *C, const Function *F) -> SizeTerm {
    const Function *CF = C->getCalledFunction();
    if (!CF) return {};
    std::vector<unsigned> idx;
    SizeTerm inner;
    auto sit = P.Ctx->FuncSummaries.find(CF);
    const GlobalContext::FuncSummary *FS = sit != P.Ctx->FuncSummaries.end() ? sit->second : nullptr;
    // A row's SIZE is read before the allocator table (GAPS "Size label"):
    // an explicit row beats the table's prefix guess (kmalloc* takes arg0,
    // the cache, in kmalloc_trace(s, flags, size)).
    if (FS && FS->fresh && !FS->sizeArgs.empty()) inner = {true, 1, FS->sizeArgs};
    else if (sigOf(CF->getName(), idx)) inner = {true, 1, idx};
    else if (FS && FS->fresh && !CF->isDeclaration())
      inner = termOfFn(CF);
    if (!inner.known) return {};
    if (!F) return inner;
    SizeTerm out = constT(inner.c);
    for (unsigned k : inner.formals) {
      if (k >= C->arg_size()) return {};
      out = timesT(out, termIn(C->getArgOperand(k), F, 0));
    }
    if (inner.zeroK >= 0) { // "the product, zeroK when zero" at these actuals
      const int64_t zk = inner.zeroK;
      if (out.isConst() && out.c == 0) out = constT((uint64_t)zk);
      else if (out.known && !nonzero(out)) {
        if (!out.align && !out.add && out.zeroK < 0 && (!out.formals.empty() || out.partial))
          out.zeroK = zk; // carried up: a product of F's formals, or a multiple (row (2))
        else
          out = multiple(std::gcd(multOf(out), (uint64_t)zk)); // the join with zeroK
      }
    }
    if (inner.partial) out = timesT(out, SizeTerm{});
    if (inner.add) out = plusK(out, inner.add);
    if (inner.align) out = alignT(out, inner.align);
    if (out.partial && out.c == 1 && out.formals.empty()) return {}; // no known factor
    return out;
  };
  // A pool carve's term in its function's formals (CarveSize).
  carveTerm = [&](const Instruction *I) -> SizeTerm {
    auto it = P.poolCarveSizes.find(I);
    const Function *F = I->getFunction();
    SizeTerm t;
    if (it != P.poolCarveSizes.end() && it->second.n) {
      t = timesT(termIn(it->second.n, F, 0), constT(it->second.scale));
      // "n, zeroK when n == 0" (A2' (1)): n's own term when it is never
      // zero or already reads zeroK there; one formal takes the zero case.
      if (const int64_t zk = it->second.zeroK; zk >= 0 && t.known) {
        const int64_t zks = zk * (int64_t)it->second.scale;
        if (t.isConst()) t = t.c ? t : constT((uint64_t)zks);
        else if (nonzero(t) || t.zeroK == zks) {
        } else if (!t.partial && !t.align && t.zeroK < 0 && t.formals.size() == 1 && t.c == 1 && !t.add)
          t.zeroK = zks;
        else
          t = {};
      }
      if (t.known && it->second.how == 'z') sizeWhenZero.insert(I);
      if (t.known && it->second.how == 'h') sizeHeaderStore.insert(I);
    }
    else if (it != P.poolCarveSizes.end() && it->second.chunk) {
      // malloc(HDR + n) carved at HDR is n (the sum's own operand, not the
      // sum's term less HDR: a rounded n stays exact).
      const CallBase *CC = it->second.chunk;
      std::vector<unsigned> idx;
      const Function *CF = CC->getCalledFunction();
      if (CF && sigOf(CF->getName(), idx) && idx.size() == 1 && idx[0] < CC->arg_size())
        if (const auto *B = dyn_cast<BinaryOperator>(sizeThrough(CC->getArgOperand(idx[0])));
            B && B->getOpcode() == Instruction::Add)
          for (unsigned o = 0; o < 2 && !t.known; o++)
            if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(B->getOperand(o)));
                K && K->getSExtValue() == it->second.off)
              t = termIn(B->getOperand(1 - o), F, 0);
      if (!t.known) t = plusK(callTerm(CC, F), -it->second.off);
    }
    if (!t.known) carveUnknownSize.insert(I);
    return t;
  };
  termOfFn = [&](const Function *F) -> SizeTerm {
    if (auto it = termMemo.find(F); it != termMemo.end()) return it->second;
    if (!termBusy.insert(F).second) return {};
    std::optional<SizeTerm> agreed;
    bool bad = false;
    std::vector<const Value *> work;
    std::vector<const CallBase *> selfCalls;
    std::set<const Value *> seen;
    for (const BasicBlock &BB : *F)
      if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
        if (RI->getReturnValue()) work.push_back(RI->getReturnValue());
    while (!work.empty() && !bad) {
      const Value *V = work.back()->stripPointerCasts();
      work.pop_back();
      if (!seen.insert(V).second || isa<ConstantPointerNull>(V)) continue;
      // A phi that is itself a certified carve (A2' (2), -O3 bfd_alloc's
      // return): its carve term, joined with its incoming carves' terms; an
      // incoming load of its pool's fields (through phis) is the before-bump
      // result the certification names, covered by the phi's own term. An
      // incoming constant carve on the true edge of `n == 0`, n the phi's
      // bump, is n's zero case: it joins when the term reads it there.
      if (const auto *PC = dyn_cast<PHINode>(V); PC && P.poolCarves.count(PC)) {
        SizeTerm own = carveTerm(PC);
        if (!own.known) { bad = true; break; }
        const auto pit = P.poolCarvePool.find(PC);
        const auto zit = P.poolCarveSizes.find(PC);
        const Value *bump = zit != P.poolCarveSizes.end() ? zit->second.n : nullptr;
        std::unique_ptr<DominatorTree> DT;
        auto onZeroEdge = [&](const Instruction *J) {
          if (!bump) return false;
          if (!DT) DT = std::make_unique<DominatorTree>(const_cast<Function &>(*F));
          for (const User *U : bump->users())
            if (const auto *Cmp = dyn_cast<ICmpInst>(U); Cmp && Cmp->getPredicate() == ICmpInst::ICMP_EQ &&
                                                        Cmp->getOperand(0) == bump && isa<ConstantInt>(Cmp->getOperand(1)) &&
                                                        cast<ConstantInt>(Cmp->getOperand(1))->isZero())
              for (const User *CU : Cmp->users())
                if (const auto *Br = dyn_cast<BranchInst>(CU); Br && Br->isConditional() && Br->getCondition() == Cmp &&
                                                               DT->dominates(BasicBlockEdge(Br->getParent(), Br->getSuccessor(0)), J->getParent()))
                  return true;
          return false;
        };
        std::vector<const Value *> in(PC->incoming_values().begin(), PC->incoming_values().end());
        std::set<const Value *> inSeen;
        for (size_t i = 0; i < in.size() && !bad; i++) {
          const Value *X = in[i]->stripPointerCasts();
          if (!inSeen.insert(X).second || isa<ConstantPointerNull>(X)) continue;
          const auto *XI = dyn_cast<Instruction>(X);
          if (const auto *P2 = dyn_cast<PHINode>(X); P2 && !P.poolCarves.count(P2)) {
            in.insert(in.end(), P2->incoming_values().begin(), P2->incoming_values().end());
            continue;
          }
          if (const auto *L = dyn_cast<LoadInst>(X); L && pit != P.poolCarvePool.end()) {
            const auto fa = P.poolFieldAccess.find(L);
            if (fa != P.poolFieldAccess.end() && fa->second == pit->second) continue; // the bump base
          }
          if (!XI || !P.poolCarves.count(XI)) { bad = true; break; }
          SizeTerm t = carveTerm(XI);
          // The term's value in its zero case: zeroK, rounded when the term
          // is (round8(n ? n : 1) reads 8 there).
          if (t.isConst() && own.known && own.zeroK >= 0 && !own.add && !own.partial && onZeroEdge(XI)) {
            const uint64_t zv = own.align ? (((uint64_t)own.zeroK + own.align - 1) & ~(own.align - 1)) : (uint64_t)own.zeroK;
            if (t.c == zv) t = own;
          }
          own = joinT(own, t);
          bad = !own.known;
        }
        if (bad) break;
        sizeCarvePhi.insert(PC);
        agreed = agreed ? joinT(*agreed, own) : own;
        bad = !agreed->known;
        continue;
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) { for (const Value *In : PN->incoming_values()) work.push_back(In); continue; }
      if (const auto *SI = dyn_cast<SelectInst>(V)) { work.push_back(SI->getTrueValue()); work.push_back(SI->getFalseValue()); continue; }
      if (const auto *L = dyn_cast<LoadInst>(V)) // -O0: a slot only loaded and stored: every value stored
        if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          std::vector<const Value *> stored;
          bool slot = true;
          for (const User *U : A->users()) {
            if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand() == A && St->getValueOperand() != A)
              stored.push_back(St->getValueOperand());
            else if (!(isa<LoadInst>(U) && cast<LoadInst>(U)->getPointerOperand() == A) && !isa<DbgInfoIntrinsic>(U))
              slot = false;
          }
          if (slot && !stored.empty()) { work.insert(work.end(), stored.begin(), stored.end()); continue; }
        }
      const auto *C = dyn_cast<CallBase>(V);
      if (C && C->getCalledFunction() == F) { selfCalls.push_back(C); continue; } // below
      const auto *I = dyn_cast<Instruction>(V);
      const SizeTerm t = C ? callTerm(C, F) : I && P.poolCarves.count(I) ? carveTerm(I) : SizeTerm{};
      if (!t.known) { bad = true; break; }
      agreed = agreed ? joinT(*agreed, t) : t;
      bad = !agreed->known;
    }
    // A self call returns F's own term at its arguments: assumed, checked
    // against the other returns until it holds (the gcd fact descends).
    for (int round = 0; !bad && agreed && !selfCalls.empty(); round++) {
      termMemo[F] = *agreed;
      SizeTerm next = *agreed;
      for (const CallBase *C : selfCalls) next = joinT(next, callTerm(C, F));
      if (next == *agreed) break;
      agreed = next;
      bad = !next.known || round == 4;
    }
    termBusy.erase(F);
    const SizeTerm out = (bad || !agreed) ? SizeTerm{} : *agreed;
    if (VerboseLevel >= 3) {
      std::string ts = "unknown";
      if (out.known) {
        ts = std::to_string(out.c);
        for (unsigned k : out.formals) ts += " x arg" + std::to_string(k);
        if (out.zeroK >= 0) ts += " (" + std::to_string(out.zeroK) + " when zero)";
        if (out.add) ts += (out.add > 0 ? " + " : " - ") + std::to_string(out.add > 0 ? out.add : -out.add);
        if (out.align) ts = "round" + std::to_string(out.align) + "(" + ts + ")";
        if (out.partial) ts = "a multiple of " + ts;
      }
      CG_DEBUG("Cells: size term of " << F->getName() << ": " << ts << "\n");
    }
    return termMemo[F] = out;
  };
  // Allocations sized by a product through a zero-guarded wrapper (row
  // (2): bfd_alloc2(abfd, n, 72) = a multiple of 72).
  // The size of an allocation site V as operands and an addend (size =
  // add + the product of ops; an undef operand is a factor not known),
  // false when the size is unknown. A call's inner term is evaluated at
  // its own operands (their sums read by headerPlusTail); a rounding is
  // folded when its input is constant at the call, else it is a multiple.
  // A carve's term only when it is constant or a multiple.
  sizeOps = [&](const Value *V, std::vector<const Value *> &ops, int64_t &add) {
    ops.clear();
    add = 0;
    LLVMContext &Cx = V->getContext();
    // A term at the site: a constant, a multiple; a product of the site's
    // own formals (values unknown here) is a multiple of c (its zero case
    // names no element, row (2)).
    auto fromTerm = [&](const SizeTerm &t) {
      if (!t.known || t.align || (!t.formals.empty() && t.add)) return false;
      ops.push_back(ConstantInt::get(Type::getInt64Ty(Cx), t.c));
      if (t.partial || !t.formals.empty()) ops.push_back(UndefValue::get(Type::getInt64Ty(Cx)));
      return true;
    };
    if (const auto *I = dyn_cast<Instruction>(V); I && P.poolCarves.count(I)) return fromTerm(carveTerm(I));
    const auto *C = dyn_cast<CallBase>(V);
    if (!C) return false;
    const SizeTerm t = callTerm(C, nullptr);
    if (!t.known) return false;
    if (t.align || t.zeroK >= 0) {
      const SizeTerm e = callTerm(C, C->getFunction());
      if (fromTerm(e)) {
        if (t.zeroK >= 0 && !e.isConst()) { // row (2)
          zeroProductSites.insert(C);
          if (zeroNote) zeroNote->push_back(C);
        }
        return true;
      }
      return t.align && fromTerm(multiple(t.align));
    }
    for (unsigned k : t.formals) {
      if (k >= C->arg_size()) { ops.clear(); return false; }
      ops.push_back(C->getArgOperand(k));
    }
    if (t.c != 1 || ops.empty())
      ops.push_back(ConstantInt::get(Type::getInt64Ty(Cx), t.c));
    if (t.partial) ops.push_back(UndefValue::get(Type::getInt64Ty(Cx))); // an unknown factor
    add = t.add;
    return true;
  };
  // The size label (GAPS "Size label"): a heap object whose allocation
  // size is a constant k larger than its label S takes the struct of size
  // k that embeds S at offset 0 (the struct analyzer's embedding table,
  // transitive); one such struct names it, several leave S (counted with
  // the candidates), none leaves S. A multiple of S's size is an array of
  // S (plan 3.53, rule 1), not a container.
  // "S at k: {candidates}" -> objects
  containerOfSize = [&](const CallBase *C, const StructType *S, int64_t sz,
                             size_t &n) -> StructType * {
    n = 0;
    uint64_t k = 0;
    std::vector<const Value *> ops;
    int64_t add = 0;
    if (sizeOps(C, ops, add)) {
      uint64_t prod = 1;
      bool allConst = true;
      for (const Value *V : ops)
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(V))) prod *= K->getZExtValue();
        else allConst = false;
      prod += add;
      if (allConst && prod > (uint64_t)sz && prod % sz) k = prod;
    }
    if (!k) return nullptr;
    const StructInfo *SI =
        P.Ctx->structAnalyzer.getStructInfo(S, const_cast<Module *>(C->getModule()));
    if (!SI) return nullptr;
    StructType *one = nullptr;
    std::set<std::string> cands;
    for (auto &[ct, offs] : SI->getContainers())
      if (offs.count(0) && ct->isSized() && DL.getTypeAllocSize(const_cast<StructType *>(ct)) == k) {
        n++;
        one = const_cast<StructType *>(ct);
        cands.insert(typeLabel(one));
      }
    if (n > 1) {
      std::string c;
      for (const std::string &x : cands) c += (c.empty() ? "" : ", ") + x;
      const std::string key = typeLabel(const_cast<StructType *>(S)) + " at " + std::to_string(k) + " bytes: {" + c + "}";
      sizeLabelAmbiguous[key]++;
      if (ambiguousNote) ambiguousNote->push_back(key);
    }
    return n == 1 ? one : nullptr;
  };
}

CallGraphPass::SizeTerms::Extent CallGraphPass::SizeTerms::extentOf(Type *layout, uint64_t at, const Value *V) {
  Extent E;
  const auto *C = dyn_cast_or_null<CallBase>(V);
  std::vector<const Value *> ops;
  int64_t add = 0;
  const bool sized = V && sizeOps(V, ops, add);
  if (C && !sized)
    if (const Function *CF = C->getCalledFunction())
      if (auto sit = P.Ctx->FuncSummaries.find(CF); sit != P.Ctx->FuncSummaries.end() && sit->second && sit->second->fresh)
        E.promotedUnknown = true;
  if (sized && headerPlusTail(ops, at, add)) {
    E.tail = true;
    E.kind = 'h';
  } else if (sized && exactlyOne(ops, at, add)) {
    E.kind = '1';
  } else if (sized && sizeIsMultiple(ops, at, add)) {
    // A struct ending in a flexible array member (`E a[]`, [0] in the IR)
    // has no arrays (C11 6.7.2.1p3): a multiple of its size is the header
    // and its trailing array's elements, never an array of T (gap 2).
    uint64_t n = 2;
    if (layout && trailingArrayElem(layout, DL, &n) && n == 0) {
      E.tail = true;
      E.kind = 'f';
    } else {
      E.repeats = true;
      E.kind = 'a';
    }
  } else {
    E.tail = true;
    E.tailUnsized = true;
    E.kind = 'u';
  }
  return E;
}

CallGraphPass::SizeTerms::HeapMint CallGraphPass::SizeTerms::heapMint(const CallBase *C, std::set<std::string> *L) {
  HeapMint H;
  assert(!zeroNote && !ambiguousNote && "a mint does not nest");
  zeroNote = &H.zeroProduct;
  ambiguousNote = &H.ambiguous;
  struct Unnote {
    SizeTerms &T;
    ~Unnote() { T.zeroNote = nullptr, T.ambiguousNote = nullptr; }
  } unnote{*this};
  // Labels of one object at its start, one embedding the other at
  // offset 0 (my_memory_mgr and its first member jpeg_memory_mgr:
  // `mem->pub.f = ..`): the container is the object's type.
  if (L && L->size() > 1) {
    std::set<std::string> outer;
    for (const std::string &a : *L) {
      bool embedded = false;
      for (const std::string &b : *L) {
        if (a == b) continue;
        StructType *SB = StructType::getTypeByName(C->getContext(), b);
        if (SB && !SB->isOpaque() && structStartsAt(SB, 0, stripStructNameSuffix(a), DL))
          embedded = true;
      }
      if (!embedded) outer.insert(a);
    }
    if (outer.size() == 1) *L = std::move(outer);
  }
  if (L && L->size() == 1 && StringRef(*L->begin()).starts_with("ptr[]:")) {
    // The site's variable declares an array of pointer slots (T **):
    // element = one pointer, its extent from the size below.
    H.layout = PointerType::get(C->getContext(), 0);
    H.repeats = true;
    H.declArray = true;
    H.ident = StringRef(*L->begin()).drop_front(6).str() + "[]";
    H.labelKind = 'p';
  } else if (L && L->size() == 1 && StringRef(*L->begin()).starts_with("scal[]:")) {
    // Ruling A: every creating site declares and uses one scalar (a
    // float table): an array of it, labeled at mint.
    const StringRef e = StringRef(*L->begin()).drop_front(7);
    LLVMContext &Cx = C->getContext();
    unsigned bits = 0;
    H.layout = e == "float" ? Type::getFloatTy(Cx)
               : e == "double" ? Type::getDoubleTy(Cx)
               : e == "half" ? Type::getHalfTy(Cx)
               : e.drop_front(1).getAsInteger(10, bits) ? nullptr
                                                        : (Type *)IntegerType::get(Cx, bits);
    assert(H.layout && "a scalar label names a scalar type");
    H.repeats = true;
    H.declScalar = true;
    H.declArray = true;
    H.ident = e.str() + "[]";
    H.labelKind = 's';
  } else if (L && L->size() == 1) {
    H.layout = StructType::getTypeByName(C->getContext(), *L->begin());
    H.repeats = true;
    H.labelKind = H.layout ? 'l' : 'x';
  } else if (L && L->size() > 1) {
    H.labelKind = 'c';
  } else {
    // Ruling A: every creating site uses it only as bytes (sdup's
    // string): used as bytes from mint, so a struct write arriving
    // through an imprecise pointer is a rule (b) row, not its label.
    if (P.allocBytesOnly.count(C)) {
      H.byteAccessed = true;
      H.bytesMarked = true;
    }
  }
  if (H.layout && H.layout->isSized()) H.size = (int64_t)DL.getTypeAllocSize(H.layout);
  if (H.size <= 0) H.layout = nullptr; // opaque or empty: unlabeled
  else H.label = typeLabel(H.layout);
  if (H.layout) {
    Type *E = H.layout;
    while (auto *AT = dyn_cast<ArrayType>(E)) E = AT->getElementType();
    if (isAnonStruct(dyn_cast<StructType>(E))) {
      H.layout = nullptr;
      H.label.clear();
      H.anon = true;
    }
  }
  // A constant size larger than the label where some struct of exactly
  // that size starts with the label: the label is the first member of a
  // container (C inheritance: the allocating code writes only `pub`),
  // not a header before trailing data (GAPS "Size label"). One such
  // container: its type; several (cjpeg -O3: huff and phuff encoders are
  // both 200 bytes): the label stays, counted with the candidates.
  if (H.layout && H.repeats)
    if (const auto *ST = dyn_cast<StructType>(H.layout)) {
      size_t n = 0;
      if (StructType *CT = containerOfSize(C, ST, H.size, n)) {
        H.layout = CT;
        H.size = (int64_t)DL.getTypeAllocSize(CT);
        H.label = typeLabel(H.layout);
        H.repeats = false;
        H.containerRelabeled = true;
      } else if (n > 1) {
        H.containerAmbiguous = true; // the label stays
      }
    }
  // A5a (Fable 2026-10-21): a constant size S = k x sizeof(L), k >= 2, is
  // an array of L by rule 1, and it is also any struct C that embeds L at
  // offset 0 with sizeof(C) = S (the embedding table): C inheritance whose
  // container happens to be a multiple of its head (-O3
  // _bfd_x86_elf_link_hash_table_create: 2088 = 29 x bfd_link_hash_table).
  // The site's own receivers select: a declaration naming one such C names
  // the object C; a declaration naming L is in both readings and selects
  // nothing. Not selected: a conflict, unlabeled, with its row.
  if (H.layout && H.repeats && !H.declArray)
    if (auto *LS = dyn_cast<StructType>(H.layout)) {
      std::vector<const Value *> ops;
      int64_t add = 0;
      uint64_t prod = 1;
      bool known = sizeOps(C, ops, add);
      for (const Value *X : ops)
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(X))) prod *= K->getZExtValue();
        else known = false;
      const uint64_t S = prod + add, sz = (uint64_t)H.size;
      const StructInfo *SI =
          known && S > sz && S % sz == 0 && extentOf(LS, sz, C).kind == 'a'
              ? P.Ctx->structAnalyzer.getStructInfo(LS, const_cast<Module *>(C->getModule()))
              : nullptr;
      std::map<std::string, std::vector<StructType *>> cands; // container name -> its IR types
      if (SI)
        for (auto &[ct, offs] : SI->getContainers())
          if (offs.count(0) && ct->isSized() && DL.getTypeAllocSize(const_cast<StructType *>(ct)) == S)
            cands[stripStructNameSuffix(ct->getName()).str()].push_back(const_cast<StructType *>(ct));
      if (!cands.empty()) {
        std::vector<StructType *> picked;
        size_t names = 0;
        if (auto dit = P.allocDeclStructs.find(C); dit != P.allocDeclStructs.end())
          for (auto &[cn, ts] : cands)
            if (dit->second.count(cn)) names++, picked = ts;
        // One named container; its IR copies (the linker's suffixes) one layout.
        bool one = names == 1;
        for (StructType *T2 : picked) one &= T2 == picked[0] || T2->isLayoutIdentical(picked[0]);
        if (one) {
          H.layout = picked[0];
          H.size = (int64_t)S;
          H.label = typeLabel(H.layout);
          H.repeats = false;
          H.readings = 'r';
        } else {
          std::string row = std::to_string(S / sz) + " x " + typeLabel(LS) + " (" + std::to_string(sz) + ")";
          for (auto &[cn, ts] : cands) row += " vs " + cn + " (" + std::to_string(S) + ")";
          H.readingsRow = row;
          H.readings = 'c';
          H.layout = nullptr;
          H.label.clear();
          H.size = 0;
          H.repeats = false;
          H.labelKind = 'c';
        }
      }
    }
  // A4 (Fable 2026-10-20): a heap struct label whose receivers declare a
  // struct the linked IR merged away, of the label's size, carries that
  // debug identity (rndx_ext read as Elf_External_Sym_Shndx).
  if (H.layout && isa<StructType>(H.layout) && H.ident.empty()) {
    if (auto mi = P.allocMergedIdent.find(C); mi != P.allocMergedIdent.end()) {
      if (mi->second.second == (uint64_t)DL.getTypeAllocSize(H.layout)) {
        const std::string &id = mi->second.first;
        if (!id.empty() && id != H.label) {
          H.ident = id;
          H.identNoted = true;
        }
        H.a4 = 'm';
        H.merged = H.ident == id;
      } else
        H.a4 = 'd';
    } else if (P.allocNoDI.count(C))
      H.a4 = 'n';
  }
  // A declared array (of a scalar, ruling A; of pointer slots, 1b) is an
  // array of its element whatever the size says: no header, no trailing
  // object.
  if (H.layout && H.repeats && !H.declArray) {
    H.extent = extentOf(H.layout, (uint64_t)H.size, C);
    H.extentSet = true;
    H.tail = H.extent.tail;
    H.repeats = H.extent.repeats;
    H.tailUnsized = H.extent.tailUnsized;
  }
  return H;
}

void CallGraphPass::buildMintTable() {
  const DataLayout &DL = Ctx->Modules.front().first->getDataLayout();
  std::unordered_map<const Value *, std::set<std::string>> labels;
  // The labels read every module's access bases; the graph build scans
  // them module by module after this point, so the table reads its own.
  auto own = std::make_unique<ka::AccessNames>();
  for (auto &[M, _] : Ctx->Modules) own->scanBases(*M);
  std::swap(accessNames, own);
  // The labels read the allocation calls the graph build marks as it
  // emits each body (GraphBuild.cc: a call of an allocator, not its own
  // self call inside a kept body; the bodies doModulePass emits): marked
  // here for the table's labels only, then the build's own set is back.
  const auto buildSites = Ctx->AllocSites;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty() ||
          (Ctx->AllocFuncs.count(&F) && !summaryKeepsBody(Ctx, &F)) || Ctx->ContainerFuncs.count(&F) ||
          shouldSkipFunction(&F))
        continue;
      for (Instruction &I : instructions(F))
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (const Function *CF = CB->getCalledFunction()) {
            const bool selfInBody = summaryKeepsBody(Ctx, CF) && CF->getGUID() == F.getGUID();
            if (Ctx->AllocFuncs.count(CF) && !selfInBody) Ctx->AllocSites.insert(CB);
          }
    }
  labelsQuiet = true;
  staticLabels(labels);
  labelsQuiet = false;
  const auto marked = Ctx->AllocSites;
  Ctx->AllocSites = buildSites;
  std::swap(accessNames, own);
  // Its own evaluator; the solve's (CellSolver.cc) evaluates the carves.
  auto T = std::make_shared<MintTable>();
  T->terms = std::make_unique<SizeTerms>(*this, DL);
  SizeTerms &ST = *T->terms;
  // Every call the solve may mint a heap object for (a marked allocation
  // site, a labeled call, a call whose result is used as bytes only), in IR
  // order, so the evaluator's memo fills the same way in every run.
  for (auto &[M, _] : Ctx->Modules)
    for (const Function &F : *M)
      for (const Instruction &I : instructions(F)) {
        const auto *C = dyn_cast<CallBase>(&I);
        if (!C) continue;
        if (auto lit = labels.find(C); lit != labels.end()) {
          std::set<std::string> l = lit->second;
          T->at.emplace(C, ST.heapMint(C, &l));
        } else if (allocBytesOnly.count(C) || marked.count(const_cast<CallBase *>(C))) {
          T->at.emplace(C, ST.heapMint(C, nullptr));
        } else
          continue;
        T->order.push_back(C);
      }
  mintTable = T;
}
