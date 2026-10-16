/*
 * Call graph construction
 *
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// ContainerOwnerCode.cc: values and slots derived from a container's owner
// in owner code (plan 3.55 R3 D5, Fable 2026-10-15), for the container
// report. In a function that passes owner value o to a row, a value or SLOT
// is derived from o when it is: o's handle-field address or load; the
// address or load of a link field (or a link word, decoded) of a derived
// value; a phi or select all of whose entries are derived or null (a
// greatest fixpoint, so loop-carried descents close: `p = &root->rb_node;
// while (*p) p = &(*p)->rb_left`); a row's result on a derived argument.
// An element argument of a remove row on o is derived too.

#include "CallGraphInternal.h"
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/IR/CFG.h>

// A pointer's object and constant byte offset from it (casts and constant
// GEPs folded).
static std::pair<const Value *, int64_t> rootOff(const Value *V, const DataLayout &DL) {
  int64_t o = 0;
  for (int i = 0; i < 16; i++) {
    V = V->stripPointerCasts();
    const auto *G = dyn_cast<GEPOperator>(V);
    APInt A(64, 0);
    if (!G || !G->accumulateConstantOffset(DL, A)) break;
    o += A.getSExtValue();
    V = G->getPointerOperand();
  }
  return {V, o};
}

std::map<const Value *, uint8_t> deriveOwnerCode(const Function &F, const std::vector<const Value *> &owners,
                                                 const std::vector<const Value *> &elems,
                                                 const std::function<char(const Instruction *, const Value *)> &slotOf,
                                                 const std::function<bool(const CallBase *, const OwnerClassFn &)> &rowRet,
                                                 const DataLayout &DL, StructType *elemT,
                                                 std::vector<const Value *> *assumed,
                                                 const std::function<int64_t(const Value *)> &slotStart) {
  std::vector<const Value *> grown(elems.begin(), elems.end());
  // Nodes assumed elements under the link invariant, by object and offset.
  std::set<std::pair<const Value *, int64_t>> linkObj;
  const int64_t elemSize = elemT && !elemT->isOpaque() ? (int64_t)DL.getTypeAllocSize(elemT) : 0;
  for (int outer = 0;; outer++) {
    assert(outer < 64 && "owner-code derivation (link invariant) did not settle");
  std::map<const Value *, uint8_t> cls, assume;
  const uint8_t TOP = OC_SLOT | OC_VAL | OC_WORD;
  for (const Instruction &I : instructions(F))
    if (isa<PHINode>(I) || isa<SelectInst>(I)) assume[&I] = TOP;
  const std::set<const Value *> ownerSet(owners.begin(), owners.end()), elemSet(grown.begin(), grown.end());
  // Elements by object and offset: a step from the object into an
  // element's declared field is that element's slot.
  std::set<std::pair<const Value *, int64_t>> objAt;
  for (const Value *O : owners) objAt.insert(rootOff(O, DL));
  if (elemSize)
    for (const Value *E : grown) objAt.insert(rootOff(E, DL));
  objAt.insert(linkObj.begin(), linkObj.end());
  auto look = [](const Value *V) {
    for (int i = 0; i < 8; i++) {
      if (const auto *BC = dyn_cast<BitCastOperator>(V)) V = BC->getOperand(0);
      else if (const auto *AC = dyn_cast<AddrSpaceCastOperator>(V)) V = AC->getOperand(0);
      else break;
    }
    return V;
  };
  // An owner or element whose own address names a declared slot (rb_root's
  // handle at +0, llist_node's link at +0) is that slot's address too.
  std::map<const Value *, bool> slotMemo;
  auto isSlot = [&](const Value *V) {
    auto [it, fresh] = slotMemo.try_emplace(V, false);
    if (fresh) it->second = slotOf(nullptr, V) != 0;
    return it->second;
  };
  OwnerClassFn get = [&](const Value *V) -> uint8_t {
    V = look(V);
    uint8_t m = 0;
    if (ownerSet.count(V)) m |= OC_OWNER;
    if (elemSet.count(V)) m |= OC_VAL;
    if (!linkObj.empty() && V->getType()->isPointerTy() && linkObj.count(rootOff(V, DL))) m |= OC_VAL;
    if (auto it = assume.find(V); it != assume.end()) return m | it->second;
    if (auto it = cls.find(V); it != cls.end()) m |= it->second;
    if ((m & (OC_OWNER | OC_VAL)) && !(m & OC_SLOT) && isSlot(V)) m |= OC_SLOT;
    return m;
  };
  // Null, undef and a link word's null plus tag join anything.
  auto isNull = [](const Value *V) {
    if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return true;
    const auto *CI = dyn_cast<ConstantInt>(V);
    return CI && CI->getValue().ult(8);
  };
  auto transfer = [&](const Instruction &I) -> uint8_t {
    if (const auto *GEP = dyn_cast<GEPOperator>(&I)) {
      const uint8_t b = get(GEP->getPointerOperand());
      if ((b & (OC_OWNER | OC_VAL)) && slotOf(nullptr, &I)) return OC_SLOT;
      if (const int64_t k = slotStart(&I); k >= 0) {
        const auto [r, o] = rootOff(&I, DL);
        if (objAt.count({r, o - k})) return OC_SLOT;
      }
      return GEP->hasAllZeroIndices() ? b & OC_SLOT : 0;
    }
    if (isa<BitCastInst>(&I) || isa<AddrSpaceCastInst>(&I)) return get(I.getOperand(0)) & ~OC_OWNER;
    if (isa<PtrToIntInst>(&I)) return get(I.getOperand(0)) & (OC_VAL | OC_OWNER) ? OC_WORD : 0;
    if (isa<IntToPtrInst>(&I)) return get(I.getOperand(0)) & OC_WORD ? OC_VAL : 0;
    if (isa<ZExtInst>(&I) || isa<TruncInst>(&I) || isa<FreezeInst>(&I)) return get(I.getOperand(0)) & OC_WORD;
    if (const auto *BO = dyn_cast<BinaryOperator>(&I)) {
      // A tag set or cleared on a link word: or/and/xor/add with a constant,
      // or with another word's tag extract (`(old & 1) | (unsigned long)p`).
      const Value *A = BO->getOperand(0), *B = BO->getOperand(1);
      auto tagOf = [](const Value *X) {
        if (const auto *C = dyn_cast<ConstantInt>(X)) return C->getValue().ult(8);
        const auto *AN = dyn_cast<BinaryOperator>(X);
        if (!AN || AN->getOpcode() != Instruction::And) return false;
        for (const Value *Op : AN->operands())
          if (const auto *C = dyn_cast<ConstantInt>(Op); C && C->getValue().ult(8)) return true;
        return false;
      };
      if (isa<Constant>(B) || tagOf(B)) return get(A) & OC_WORD;
      if (isa<Constant>(A) || tagOf(A)) return get(B) & OC_WORD;
      return 0;
    }
    if (const auto *L = dyn_cast<LoadInst>(&I)) {
      const Value *A = L->getPointerOperand();
      const uint8_t a = get(A);
      const char k = (a & OC_SLOT) ? 's' : (a & (OC_OWNER | OC_VAL)) ? slotOf(L, A) : 0;
      if (!k) return 0;
      if (L->getType()->isPointerTy()) return OC_VAL;
      return L->getType()->isIntegerTy() ? OC_WORD : 0;
    }
    if (const auto *CB = dyn_cast<CallBase>(&I))
      return CB->getType()->isPointerTy() && rowRet(CB, get) ? OC_VAL : 0;
    return 0;
  };
  auto meet = [&](const Instruction *I) -> uint8_t {
    uint8_t m = TOP;
    bool any = false;
    auto in = [&](const Value *V) {
      if (V == I || isNull(V)) return;
      any = true;
      m &= get(V);
    };
    if (const auto *PN = dyn_cast<PHINode>(I))
      for (const Value *V : PN->incoming_values()) in(V);
    else if (const auto *SL = dyn_cast<SelectInst>(I))
      in(SL->getTrueValue()), in(SL->getFalseValue());
    return any ? m : 0;
  };
  ReversePostOrderTraversal<const Function *> RPOT(&F);
  for (int round = 0;; round++) {
    assert(round < 256 && "owner-code derivation did not settle");
    cls.clear();
    for (const BasicBlock *BB : RPOT)
      for (const Instruction &I : *BB)
        if (!assume.count(&I))
          if (const uint8_t m = transfer(I)) cls[&I] = m;
    bool changed = false;
    for (auto &[V, a] : assume) {
      const uint8_t m = meet(cast<Instruction>(V)) & a; // only ever shrinks
      if (m != a) a = m, changed = true;
    }
    if (!changed) break;
  }
  for (auto &[V, a] : assume)
    if (a) cls[V] = a;
  // Constant addresses (`&L.tree[0]` as a constant GEP): a declared slot of
  // an owner or element by object and offset.
  for (const Instruction &I : instructions(F))
    for (const Value *Op : I.operands())
      if (const auto *CE = dyn_cast<ConstantExpr>(Op); CE && isa<GEPOperator>(CE) && !cls.count(CE))
        if (const int64_t k = slotStart(CE); k >= 0) {
          const auto [r, o] = rootOff(CE, DL);
          if (objAt.count({r, o - k})) cls[CE] = OC_SLOT;
        }
  if (!elemSize) return cls;
  // Backward: what an element was read from. Through phis and selects (each
  // entry, on its path), casts, a link word's decode (inttoptr of tag ops
  // over a LINKWORD load), and a LINK load: the node read from is an element
  // under the link invariant.
  auto isVal = [&](const Value *V) {
    V = look(V);
    if (elemSet.count(V)) return true;
    if (V->getType()->isPointerTy() && objAt.count(rootOff(V, DL)) && !ownerSet.count(V)) return true;
    auto it = cls.find(V);
    return it != cls.end() && (it->second & OC_VAL);
  };
  std::vector<const Value *> wl;
  std::set<const Value *> seen;
  for (const Value *E : grown) wl.push_back(look(E)), seen.insert(look(E));
  for (auto &[V, c] : cls)
    if ((c & OC_VAL) && seen.insert(V).second) wl.push_back(V);
  std::vector<std::pair<std::pair<const Value *, int64_t>, const Value *>> found; // node, its link read
  auto reach = [&](const Value *X) {
    X = look(X);
    if (isNull(X) || !seen.insert(X).second) return;
    wl.push_back(X);
  };
  for (size_t k = 0; k < wl.size(); k++) {
    const Value *X = wl[k];
    if (const auto *PN = dyn_cast<PHINode>(X)) {
      for (const Value *In : PN->incoming_values()) reach(In);
      continue;
    }
    if (const auto *SL = dyn_cast<SelectInst>(X)) {
      reach(SL->getTrueValue()), reach(SL->getFalseValue());
      continue;
    }
    const Value *W = nullptr; // a link word, decoded
    if (const auto *IP = dyn_cast<IntToPtrInst>(X)) W = IP->getOperand(0);
    for (int d = 0; W && d < 8; d++) {
      if (const auto *BO = dyn_cast<BinaryOperator>(W); BO && isa<ConstantInt>(BO->getOperand(1))) W = BO->getOperand(0);
      else if (isa<ZExtInst>(W) || isa<TruncInst>(W) || isa<FreezeInst>(W)) W = cast<Instruction>(W)->getOperand(0);
      else break;
    }
    const auto *L = dyn_cast_or_null<LoadInst>(W ? W : X);
    if (!L) continue;
    const char k2 = slotOf(L, L->getPointerOperand());
    if (!(W ? k2 == 'w' : k2 == 'l')) continue;
    // The node: the slot's address less the slot's offset in its struct.
    const int64_t ks = slotStart(L->getPointerOperand());
    if (ks < 0) continue;
    auto [r, o] = rootOff(L->getPointerOperand(), DL);
    const std::pair<const Value *, int64_t> N{r, o - ks};
    if (objAt.count(N) || linkObj.count(N)) continue;
    bool dup = false;
    for (auto &f : found) dup |= f.first == N;
    if (dup) continue;
    found.push_back({N, L});
  }
  if (found.empty()) return cls;
  for (auto &[N, L] : found) {
    linkObj.insert(N);
    if (assumed) assumed->push_back(L);
  }
  }
}
