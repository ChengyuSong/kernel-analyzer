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
#include <optional>

// A pointer's object and constant byte offset from it (casts and constant
// GEPs folded; a phi or select whose entries agree on object and offset is
// that object and offset, Fable 2026-10-16 S3: rb_add_cached's
// `&root->rb_root` computed on both paths).
std::pair<const Value *, int64_t> rootOff(const Value *V, const DataLayout &DL, int depth) {
  int64_t o = 0;
  for (int i = 0; i < 16; i++) {
    V = V->stripPointerCasts();
    if (const auto *G = dyn_cast<GEPOperator>(V)) {
      APInt A(64, 0);
      if (!G->accumulateConstantOffset(DL, A)) break;
      o += A.getSExtValue();
      V = G->getPointerOperand();
      continue;
    }
    if (depth >= 4 || !(isa<PHINode>(V) || isa<SelectInst>(V))) break;
    std::vector<const Value *> ins;
    if (const auto *PN = dyn_cast<PHINode>(V)) ins.assign(PN->incoming_values().begin(), PN->incoming_values().end());
    else ins = {cast<SelectInst>(V)->getTrueValue(), cast<SelectInst>(V)->getFalseValue()};
    std::optional<std::pair<const Value *, int64_t>> agreed;
    bool ok = true;
    for (const Value *In : ins) {
      if (In->stripPointerCasts() == V) continue;
      const auto ro = rootOff(In, DL, depth + 1);
      if (agreed && *agreed != ro) ok = false;
      agreed = ro;
    }
    if (ok && agreed && agreed->first != V) V = agreed->first, o += agreed->second;
    break;
  }
  return {V, o};
}

// The byte steps a GEP may take: one offset when every index is constant,
// one per constant when exactly one index is a select or phi of constants
// (interval_tree_generic's `&parent->rb_left / rb_right` as a word index);
// empty otherwise. By bytes, the GEP's types irrelevant (Fable 2026-10-16 S4).
static std::vector<int64_t> gepSteps(const GEPOperator *G, const DataLayout &DL) {
  std::vector<int64_t> outs{0};
  for (gep_type_iterator GTI = gep_type_begin(G), E = gep_type_end(G); GTI != E; ++GTI) {
    const Value *Idx = GTI.getOperand();
    if (StructType *ST = GTI.getStructTypeOrNull()) {
      const int64_t a = (int64_t)DL.getStructLayout(ST)->getElementOffset(cast<ConstantInt>(Idx)->getZExtValue());
      for (int64_t &o : outs) o += a;
      continue;
    }
    const int64_t sz = (int64_t)DL.getTypeAllocSize(GTI.getIndexedType());
    std::vector<const Value *> alts{Idx};
    if (const auto *S = dyn_cast<SelectInst>(Idx)) alts = {S->getTrueValue(), S->getFalseValue()};
    else if (const auto *PN = dyn_cast<PHINode>(Idx)) alts.assign(PN->incoming_values().begin(), PN->incoming_values().end());
    std::vector<int64_t> cs;
    for (const Value *A : alts) {
      const auto *C = dyn_cast<ConstantInt>(A);
      if (!C) return {};
      cs.push_back(C->getSExtValue());
    }
    if (cs.size() > 1 && outs.size() > 1) return {}; // one variable index only
    std::vector<int64_t> next;
    for (int64_t o : outs)
      for (int64_t c : cs) next.push_back(o + c * sz);
    outs = next;
  }
  return outs;
}

std::map<const Value *, uint8_t> deriveOwnerCode(const Function &F, const std::vector<const Value *> &owners,
                                                 const std::vector<const Value *> &elems,
                                                 const std::function<char(const Instruction *, const Value *)> &slotOf,
                                                 const std::function<bool(const CallBase *, const OwnerClassFn &)> &rowRet,
                                                 const DataLayout &DL, StructType *elemT,
                                                 std::vector<const Value *> *assumed,
                                                 const std::function<int64_t(const Value *)> &slotStart,
                                                 const std::set<int64_t> &elemSlots,
                                                 std::map<const Value *, std::vector<int64_t>> *byteSlots,
                                                 OwnerCodeExtra *X) {
  std::vector<const Value *> grown(elems.begin(), elems.end());
  std::map<const Value *, std::pair<const Value *, int64_t>> roMemo;
  std::map<const Value *, const Value *> reread; // a value whose object is a re-read: that load (S6)
  auto ro = [&](const Value *V) {
    auto it = roMemo.find(V);
    if (it != roMemo.end()) return it->second;
    auto r = rootOff(V, DL);
    if (X && X->canon)
      if (const Value *c = X->canon(r.first); c != r.first) reread.emplace(V, r.first), r.first = c;
    roMemo.emplace(V, r);
    return r;
  };
  // The actuals' own objects by their canonical one: a match whose two
  // sides differ there used the re-read identity (S6), listed.
  std::map<const Value *, std::set<const Value *>> rawRoots;
  auto rawRoot = [&](const Value *V) {
    const Value *c = ro(V).first;
    auto it = reread.find(V);
    return it == reread.end() ? c : it->second;
  };
  auto usedReread = [&](const Value *V) {
    if (!X || reread.empty()) return;
    const Value *c = ro(V).first, *raw = rawRoot(V);
    auto it = rawRoots.find(c);
    if (it == rawRoots.end()) return;
    for (const Value *a : it->second)
      if (a != raw) {
        if (a != c) X->rereads.insert(a);
        if (raw != c) X->rereads.insert(raw);
      }
  };
  // Nodes assumed elements under the link invariant, by object and offset.
  std::set<std::pair<const Value *, int64_t>> linkObj;
  const int64_t elemSize = elemT && !elemT->isOpaque() ? (int64_t)DL.getTypeAllocSize(elemT) : 0;
  for (int outer = 0;; outer++) {
    assert(outer < 64 && "owner-code derivation (link invariant) did not settle");
  std::map<const Value *, uint8_t> cls, assume;
  std::map<const Value *, std::vector<int64_t>> byteRound; // S4 slots: their offsets in the element struct
  std::map<const Value *, std::vector<std::pair<bool, int64_t>>> unionRound; // S5 slots
  const uint8_t TOP = OC_SLOT | OC_VAL | OC_WORD;
  for (const Instruction &I : instructions(F))
    if (isa<PHINode>(I) || isa<SelectInst>(I)) assume[&I] = TOP;
  const std::set<const Value *> ownerSet(owners.begin(), owners.end()), elemSet(grown.begin(), grown.end());
  // Elements by object and offset: a step from the object into an
  // element's declared field is that element's slot.
  std::set<std::pair<const Value *, int64_t>> objAt, ownerAt, elemAt;
  for (const Value *O : owners) ownerAt.insert(ro(O)), rawRoots[ro(O).first].insert(rawRoot(O));
  if (elemSize)
    for (const Value *E : grown) elemAt.insert(ro(E)), rawRoots[ro(E).first].insert(rawRoot(E));
  // Formal objects' nodes at the element actuals' offsets (Q1), assumed.
  std::set<std::pair<const Value *, int64_t>> formalObjAt;
  if (X) {
    ownerAt.insert(X->ownerAt.begin(), X->ownerAt.end());
    if (elemSize) {
      elemAt.insert(X->elemAt.begin(), X->elemAt.end());
      // Where a descent starts at a formal object's node: a LINK slot of it
      // read, or the node merged by a phi or select.
      std::set<std::pair<const Value *, int64_t>> starts;
      if (!X->elemOffs.empty())
        for (const Instruction &I : instructions(F)) {
          if (const auto *L = dyn_cast<LoadInst>(&I)) {
            const auto [r, o] = ro(L->getPointerOperand());
            // The node read is used as a node: merged, or stepped from (not
            // only compared or called, as key_type's vet_description).
            bool asNode = false;
            std::vector<const Value *> us{L};
            for (size_t i = 0; i < us.size() && i < 16 && !asNode; i++)
              for (const User *U : us[i]->users()) {
                if (isa<PHINode>(U) || isa<SelectInst>(U) || isa<GetElementPtrInst>(U)) asNode = true;
                else if (isa<BitCastInst>(U)) us.push_back(U);
              }
            if (isa<Argument>(r) && asNode)
              for (int64_t k : X->elemLinkOffs) starts.insert({r, o - k});
          } else if (isa<PHINode>(I) || isa<SelectInst>(I)) {
            for (const Value *In : I.operands())
              if (In->getType()->isPointerTy())
                if (const auto r = ro(In); isa<Argument>(r.first)) starts.insert(r);
          }
        }
      for (const Argument &A : F.args())
        if (A.getType()->isPointerTy() && !X->actualRoots.count(&A))
          for (int64_t e : X->elemOffs)
            if (starts.count({&A, e}) && !elemAt.count({&A, e}) && !ownerAt.count({&A, e})) {
              formalObjAt.insert({&A, e});
              if (X->unionElemOffs.count(e)) X->unionElemAt.insert({&A, e});
            }
      elemAt.insert(formalObjAt.begin(), formalObjAt.end());
    }
  }
  auto usedFormalObj = [&](const std::pair<const Value *, int64_t> &K) {
    if (formalObjAt.count(K)) X->formalObjUsed.insert(K);
  };
  objAt.insert(ownerAt.begin(), ownerAt.end());
  objAt.insert(elemAt.begin(), elemAt.end());
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
  // Constant addresses (`&L.tree[0]` as a constant GEP): a declared slot of
  // an owner or element by object and offset, known before the fixpoint so
  // a load through one is derived (Fable 2026-10-16 S2: mod_tree's root).
  std::set<const Value *> constSlots;
  for (const Instruction &I : instructions(F))
    for (const Value *Op : I.operands())
      if (const auto *CE = dyn_cast<ConstantExpr>(Op); CE && isa<GEPOperator>(CE))
        if (const int64_t k = slotStart(CE); k >= 0) {
          const auto [r, o] = ro(CE);
          if (objAt.count({r, o - k})) constSlots.insert(CE);
        }
  // An actual inside a union (S5): its declared slots at actual + k, under
  // the premise's own assumption.
  auto unionHits = [&](const Value *V) {
    if (!X || (X->unionOwnerAt.empty() && X->unionElemAt.empty())) return false;
    const auto [r, o] = ro(V);
    std::vector<std::pair<bool, int64_t>> hits;
    for (int64_t k : X->ownerSlots)
      if (X->unionOwnerAt.count({r, o - k})) hits.push_back({true, k});
    for (int64_t k : elemSlots)
      if (X->unionElemAt.count({r, o - k})) hits.push_back({false, k}), usedFormalObj({r, o - k});
    if (hits.empty()) return false;
    unionRound[V] = hits;
    usedReread(V);
    return true;
  };
  OwnerClassFn get = [&](const Value *V) -> uint8_t {
    V = look(V);
    uint8_t m = 0;
    if (ownerSet.count(V)) m |= OC_OWNER;
    if (elemSet.count(V)) m |= OC_VAL;
    if (constSlots.count(V)) m |= OC_SLOT;
    // Owners and elements by object and offset (Fable 2026-10-16 S1: an
    // element at +0 of its object, `&epi->rbn` through a zero GEP).
    if (V->getType()->isPointerTy() && !isa<Constant>(V) &&
        (!linkObj.empty() || !ownerAt.empty() || !elemAt.empty())) {
      const auto r = ro(V);
      if (ownerAt.count(r)) m |= OC_OWNER;
      if (elemAt.count(r) || linkObj.count(r)) m |= OC_VAL, usedFormalObj(r);
      if (m & (OC_OWNER | OC_VAL)) usedReread(V);
      if (unionHits(V)) m |= OC_SLOT;
    }
    if (auto it = assume.find(V); it != assume.end()) return m | it->second;
    if (auto it = cls.find(V); it != cls.end()) m |= it->second;
    if ((m & (OC_OWNER | OC_VAL)) && !(m & OC_SLOT) && isSlot(V)) m |= OC_SLOT;
    // An owner at its own address is its handle at +0 when the owner struct
    // declares one there, by the row's premise (the owner actual is that
    // struct), named or not (Q2: i915's `&engine->barrier_tasks`).
    if ((m & OC_OWNER) && !(m & OC_SLOT) && X && X->ownerSlots.count(0)) m |= OC_SLOT;
    return m;
  };
  // Null, undef and a link word's null plus tag join anything.
  auto isNull = [](const Value *V) {
    if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return true;
    const auto *CI = dyn_cast<ConstantInt>(V);
    return CI && CI->getValue().ult(8);
  };
  // V + k is an element: by its object and offset, or as a derived value's
  // own address, or (a phi or select) every entry's object at that offset
  // is one; a cycle is assumed (the greatest fixpoint's).
  std::set<const Value *> nodeOnPath;
  std::function<bool(const Value *, int64_t, int)> nodeAt = [&](const Value *V, int64_t k, int d) -> bool {
    if (d > 6) return false;
    const auto [r, o0] = ro(V);
    const int64_t o = o0 + k;
    if (elemAt.count({r, o}) || linkObj.count({r, o})) return usedFormalObj({r, o}), true;
    if (o == 0 && (get(r) & OC_VAL)) return true;
    if (!(isa<PHINode>(r) || isa<SelectInst>(r))) return false;
    if (!nodeOnPath.insert(r).second) return true;
    std::vector<const Value *> ins;
    if (const auto *PN = dyn_cast<PHINode>(r)) ins.assign(PN->incoming_values().begin(), PN->incoming_values().end());
    else ins = {cast<SelectInst>(r)->getTrueValue(), cast<SelectInst>(r)->getFalseValue()};
    bool all = true, any = false;
    for (const Value *In : ins) {
      if (In == r || isNull(In)) continue;
      any = true;
      if (!nodeAt(In, o, d + 1)) { all = false; break; }
    }
    nodeOnPath.erase(r);
    return all && any;
  };
  std::map<const CallBase *, AsmModel> asmMemo;
  auto transfer = [&](const Instruction &I) -> uint8_t {
    if (const auto *GEP = dyn_cast<GEPOperator>(&I)) {
      const uint8_t b = get(GEP->getPointerOperand());
      if ((b & (OC_OWNER | OC_VAL)) && slotOf(nullptr, &I)) return OC_SLOT;
      if (const int64_t k = slotStart(&I); k >= 0) {
        const auto [r, o] = ro(&I);
        if (objAt.count({r, o - k})) return usedReread(&I), usedFormalObj({r, o - k}), OC_SLOT;
      }
      if (unionHits(&I)) return OC_SLOT;
      if (GEP->hasAllZeroIndices()) return b & OC_SLOT;
      // Byte arithmetic from a derived value (Fable 2026-10-16 S4): through
      // container_of and word steps, a pointer at the value's own address is
      // the value; at a declared slot offset of the element struct, that
      // slot (each step of a select of constant indices must be one).
      if (elemSize && !elemSlots.empty()) {
        std::vector<int64_t> acc{0};
        const Value *P = &I;
        for (int d = 0; d < 8; d++) {
          const auto *G = dyn_cast<GEPOperator>(P);
          if (!G) break;
          const std::vector<int64_t> st = gepSteps(G, DL);
          if (st.empty() || (st.size() > 1 && acc.size() > 1)) break;
          std::vector<int64_t> next;
          for (int64_t a : acc)
            for (int64_t s : st) next.push_back(a + s);
          acc = next;
          P = look(G->getPointerOperand());
          if (!(get(P) & OC_VAL)) continue;
          bool self = true, slots = true;
          for (int64_t a : acc) self &= a == 0, slots &= elemSlots.count(a) > 0;
          if (self) return OC_VAL | (elemSlots.count(0) ? OC_SLOT : 0);
          if (slots) {
            if (byteSlots) byteRound[&I] = acc;
            return OC_SLOT;
          }
          break;
        }
      }
      // A constant step k over objects each of which has an element at k
      // (the phi meet over objects: insert_after's `&parent->shared.rb` with
      // parent a phi of container_of(node) and the formal `prev`).
      if (elemSize) {
        APInt Off(64, 0);
        if (GEP->accumulateConstantOffset(DL, Off) && nodeAt(GEP->getPointerOperand(), Off.getSExtValue(), 0))
          return OC_VAL | (elemSlots.count(0) ? OC_SLOT : 0);
      }
      return 0;
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
    if (const auto *CB = dyn_cast<CallBase>(&I)) {
      // An asm, by its model (D4, Fable 2026-10-16 Q2): an operand both read
      // and written is a load of the slot into the result (an inlined
      // llist_del_all, `xchg(&head->first, NULL)`: a remove-all lookup).
      if (CB->isInlineAsm()) {
        if (!CB->getType()->isPointerTy() && !CB->getType()->isIntegerTy()) return 0;
        auto ait = asmMemo.find(CB);
        if (ait == asmMemo.end()) ait = asmMemo.emplace(CB, asmModel(*CB, &DL)).first;
        for (const AsmModel::Slot &Sl : ait->second.slots) {
          if (Sl.output || !Sl.load.ok || !Sl.ptr) continue;
          const uint8_t a = get(Sl.ptr);
          if ((a & OC_SLOT) || ((a & (OC_OWNER | OC_VAL)) && slotOf(nullptr, Sl.ptr)))
            return CB->getType()->isPointerTy() ? OC_VAL : OC_WORD;
        }
        return 0;
      }
      return CB->getType()->isPointerTy() && rowRet(CB, get) ? OC_VAL : 0;
    }
    return 0;
  };
  // A formal of F at its own address, not an owner: a node the caller
  // passed, assumed an element where a descent merges it (S7).
  auto formalNode = [&](const Value *V) {
    if (!elemSize || !V->getType()->isPointerTy()) return false;
    const auto r = ro(V);
    return isa<Argument>(r.first) && r.second == 0 && !ownerAt.count(r);
  };
  auto meet = [&](const Instruction *I) -> uint8_t {
    uint8_t m = TOP;
    bool any = false;
    auto in = [&](const Value *V) {
      if (V == I || isNull(V)) return;
      any = true;
      uint8_t g = get(V);
      if (!(g & OC_VAL) && formalNode(V)) g |= OC_VAL;
      m &= g;
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
    cls.clear(), byteRound.clear(), unionRound.clear();
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
  for (const Value *CE : constSlots) cls[CE] |= OC_SLOT;
  // Identity everywhere (Fable 2026-10-16): a value whose object and offset
  // is an owner's, an element's or a union actual's slot carries that class
  // in the result too, for every reader of it (the O1 check strips a zero
  // step to its object: `&root->rb_node` is the re-read root).
  {
    auto addId = [&](const Value *V) {
      if (!V->getType()->isPointerTy()) return;
      if (const uint8_t m = get(V)) {
        auto it = cls.find(V);
        if (it == cls.end()) cls.emplace(V, m);
        else it->second |= m;
      }
    };
    for (const Argument &A : F.args()) addId(&A);
    for (const Instruction &I : instructions(F)) addId(&I);
  }
  if (byteSlots) *byteSlots = byteRound;
  if (X) {
    X->unionSlots = unionRound, X->unionUsed.clear(), X->formalNodes.clear();
    for (auto &[V, hs] : unionRound) {
      const auto [r, o] = ro(V);
      for (auto [own, k] : hs) X->unionUsed.insert({r, o - k});
    }
    // The phis and selects whose element class rests on a formal node.
    for (auto &[V, a] : assume) {
      if (!(a & OC_VAL)) continue;
      std::vector<const Value *> ins;
      if (const auto *PN = dyn_cast<PHINode>(V)) ins.assign(PN->incoming_values().begin(), PN->incoming_values().end());
      else ins = {cast<SelectInst>(V)->getTrueValue(), cast<SelectInst>(V)->getFalseValue()};
      for (const Value *In : ins)
        if (In != V && !isNull(In) && !(get(In) & OC_VAL) && formalNode(In)) {
          X->formalNodes.push_back(cast<Instruction>(V));
          break;
        }
    }
  }
  if (!elemSize) return cls;
  // Backward: what an element was read from. Through phis and selects (each
  // entry, on its path), casts, a link word's decode (inttoptr of tag ops
  // over a LINKWORD load), and a LINK load: the node read from is an element
  // under the link invariant.
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
    auto [r, o] = ro(L->getPointerOperand());
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
