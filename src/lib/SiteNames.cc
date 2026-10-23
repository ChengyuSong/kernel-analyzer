// Site names (B, Fable 2026-10-21): a fresh allocation site whose mint
// label is L is named L for the covers when every write found from the
// site is checked against L's layout ((i)) and its size conforms ((iii)).
// The name is a checked premise, never a filter: an unchecked write leaves
// the site an untyped allocation, with the reason. Writes the site's web
// does not find are judged at the solve ((c), CellSolver.cc); a cover's
// by-origins write on a named site is decided by the object walk's offset
// against L (B6, Containers.cc). GAPS.md "Site names (B)".
#include "AllocExtents.h"
#include "CallGraph.h"
#include "CallGraphInternal.h"

#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"

#include <functional>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using namespace llvm;
using namespace ka;

namespace {
// "function file:line" of an instruction (as CellSolver.cc's instLoc).
std::string instLoc(const Instruction *I) {
  if (!I) return "?";
  std::string s = I->getFunction()->getName().str();
  if (const DILocation *L = I->getDebugLoc())
    s += " " + L->getFilename().str() + ":" + std::to_string(L->getLine());
  return s;
}
std::string valueText(const Value *V) {
  std::string t;
  raw_string_ostream os(t);
  V->printAsOperand(os, false);
  return os.str();
}
// An alloca used only as the address of loads and stores (an -O0 slot):
// what is stored into it is what its loads read.
bool transientSlot(const Value *A) {
  const auto *AI = dyn_cast<AllocaInst>(A);
  if (!AI) return false;
  for (const User *U : AI->users()) {
    if (const auto *L = dyn_cast<LoadInst>(U)) {
      if (L->getPointerOperand() != AI) return false;
    } else if (const auto *S = dyn_cast<StoreInst>(U)) {
      if (S->getPointerOperand() != AI || S->getValueOperand() == AI) return false;
    } else if (!isa<DbgInfoIntrinsic>(U)) {
      return false;
    }
  }
  return true;
}

// Does V's def web carry a pointer's bits: a ptrtoint, through casts,
// phis, selects, insert/extract, and/or/xor, an add, or a sub of a
// non-pointer from one? A difference of two pointers is an offset, not a
// pointer; loads, calls and formals end the web. Past the budget: yes.
bool carriesPtrToInt(const Value *V) {
  std::map<const Value *, bool> memo;
  size_t budget = 512;
  std::function<bool(const Value *)> P = [&](const Value *X) -> bool {
    if (auto it = memo.find(X); it != memo.end()) return it->second;
    if (!budget--) return true;
    memo[X] = false; // a cycle through a phi adds nothing
    bool r = false;
    const auto *U = dyn_cast<User>(X);
    const unsigned op = isa<Instruction>(X)    ? cast<Instruction>(X)->getOpcode()
                        : isa<ConstantExpr>(X) ? cast<ConstantExpr>(X)->getOpcode()
                                               : 0;
    if (op == Instruction::PtrToInt) r = true;
    else if (isa<ConstantAggregate>(X) || isa<PHINode>(X) || isa<SelectInst>(X) || isa<InsertElementInst>(X) ||
             isa<ExtractElementInst>(X) || isa<ShuffleVectorInst>(X) || isa<InsertValueInst>(X) ||
             isa<ExtractValueInst>(X) || op == Instruction::And || op == Instruction::Or || op == Instruction::Xor ||
             op == Instruction::Add || (op && Instruction::isCast(op))) {
      for (unsigned i = isa<SelectInst>(X) ? 1 : 0; U && i < U->getNumOperands(); i++)
        if (P(U->getOperand(i))) r = true;
    } else if (op == Instruction::Sub) {
      r = P(U->getOperand(0)) && !P(U->getOperand(1));
    }
    return memo[X] = r;
  };
  return P(V);
}

} // namespace

// Does the address A reach its object through a struct step (a GEP whose
// indices step through a struct type, any depth through casts and GEPs)?
// Such an access is rule (b)'s at the solve.
bool addressStructStep(const Value *A) {
  for (int d = 0; A && d < 64; d++) {
    if (const auto *G = dyn_cast<GEPOperator>(A)) {
      if (isa<StructType>(G->getSourceElementType())) return true;
      for (auto It = gep_type_begin(G), E = gep_type_end(G); It != E; ++It)
        if (It.getStructTypeOrNull()) return true;
      A = G->getPointerOperand();
    } else if (const auto *C = dyn_cast<CastInst>(A); C && C->getType()->isPointerTy()) {
      A = C->getOperand(0);
    } else {
      return false;
    }
  }
  return false;
}

// The IR leaf at byte `off` of L as the site's extent reads it: an array
// of L (folded), L's trailing array run on (A1 / gap 2), or one L. leaf:
// the scalar there; start: its first byte (absolute); un: the enclosing
// union slot (struct name without "struct.", its offset, its size) when
// off lies in one. past: off is beyond the extent.
namespace {
struct Leaf {
  Type *leaf = nullptr;
  int64_t start = 0;
  bool past = false, padding = false;
  std::tuple<std::string, uint64_t, uint64_t> un;
  bool inUnion = false;
};
Leaf leafIn(Type *T, int64_t off, const DataLayout &DL, int64_t abs0) {
  Leaf R;
  StructType *encl = nullptr;
  int64_t enclAt = 0; // the absolute start of encl
  for (int d = 0; T && d < 64; d++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque() || off < 0 || (uint64_t)off >= DL.getTypeAllocSize(ST)) return R;
      if (ST->hasName() && ST->getName().starts_with("union.") && !R.inUnion) {
        R.inUnion = true;
        if (encl) {
          StringRef n = stripStructNameSuffix(encl->getName());
          n.consume_front("struct.");
          R.un = {n.str(), (uint64_t)(abs0 - enclAt), DL.getTypeAllocSize(ST)};
        }
      }
      if (ST->hasName() && !ST->getName().starts_with("union.")) encl = ST, enclAt = abs0;
      const StructLayout *SL = DL.getStructLayout(ST);
      const unsigned i = SL->getElementContainingOffset(off);
      const int64_t b = SL->getElementOffset(i);
      Type *E = ST->getElementType(i);
      if (off - b >= (int64_t)DL.getTypeAllocSize(E)) { // padding after element i
        R.padding = true;
        R.start = abs0 + off;
        return R;
      }
      T = E, off -= b, abs0 += b;
      continue;
    }
    if (auto *AT = dyn_cast<ArrayType>(T)) {
      const int64_t es = DL.getTypeAllocSize(AT->getElementType());
      if (!es) return R;
      abs0 += off / es * es, off %= es;
      T = AT->getElementType();
      continue;
    }
    if (auto *VT = dyn_cast<FixedVectorType>(T)) {
      const int64_t es = DL.getTypeAllocSize(VT->getElementType());
      if (!es) return R;
      abs0 += off / es * es, off %= es;
      T = VT->getElementType();
      continue;
    }
    if (off != 0 && off >= (int64_t)DL.getTypeStoreSize(T)) return R;
    R.leaf = T;
    R.start = abs0;
    return R;
  }
  return R;
}
} // namespace

// (S: a CallGraphPass::SiteName.)
template <class SiteNameT> static Leaf siteLeaf(const SiteNameT &S, int64_t off, const DataLayout &DL) {
  Leaf R;
  if (off < 0) return R;
  if (S.repeats && S.size) {
    const int64_t base = off / S.size * S.size;
    R = leafIn(S.layout, off - base, DL, base);
    return R;
  }
  if (S.trailing && S.trailElem && off >= S.trailAt) {
    const int64_t e = (int64_t)DL.getTypeAllocSize(S.trailElem);
    const int64_t base = S.trailAt + (off - S.trailAt) / e * e;
    return leafIn(S.trailElem, off - base, DL, base);
  }
  if (off >= S.size) {
    R.past = true;
    return R;
  }
  return leafIn(S.layout, off, DL, 0);
}

std::string CallGraphPass::judgeSiteWrite(const SiteName &S, int64_t off, uint64_t bytes, Type *VT, const Value *V,
                                          const DataLayout &DL, SiteWriteNote *note) {
  if (off < 0) return "runtime offset";
  if (!VT) return "a block write";
  Type *ET = VT->isVectorTy() ? VT->getScalarType() : VT;
  const bool ptrVal = ET->isPointerTy();
  const bool ptrBits = !ptrVal && V && carriesPtrToInt(V);
  const bool constant = V && isa<Constant>(V) && !ptrBits;
  const int64_t es = VT->isVectorTy() ? (int64_t)DL.getTypeStoreSize(ET) : (int64_t)bytes;
  int64_t cur = off;
  const int64_t end = off + (int64_t)bytes;
  bool overPtr = false;
  auto text = [&] {
    std::string t;
    raw_string_ostream os(t);
    VT->print(os);
    return "+" + std::to_string(off) + " " + std::to_string(bytes) + "B " + os.str();
  };
  while (cur < end) {
    const Leaf L = siteLeaf(S, cur, DL);
    if (L.past) return text() + " past " + S.label + "'s extent (" + std::to_string(S.size) + ")";
    if (L.inUnion) {
      // (iv): a union slot is the union census's (keyed: member cells;
      // unkeyed: the slot's confluence cell); never against L.
      if (note) note->unionSlot = L.un;
      if (note) note->inUnion = true;
      cur++;
      continue;
    }
    if (L.padding) {
      if (ptrVal || ptrBits) return text() + ": a pointer over padding of " + S.label;
      cur++;
      continue;
    }
    if (!L.leaf) return text() + " not on " + S.label + "'s fields";
    const int64_t ls = (int64_t)DL.getTypeStoreSize(L.leaf);
    if (ptrVal || ptrBits) {
      // A pointer (or a pointer's bits) only into whole pointer fields.
      if (!L.leaf->isPointerTy()) return text() + ": a pointer into a non-pointer field of " + S.label;
      if (L.start != cur || (VT->isVectorTy() && ls != es) || cur + ls > end)
        return text() + ": a pointer not on " + S.label + "'s pointer fields";
      if (!ptrVal) return text() + ": a ptrtoint value over a pointer field of " + S.label;
      cur += ls;
      continue;
    }
    // A non-pointer value: any bytes (a bitfield's storage, a merged store
    // over several fields); over a pointer field it passes, counted (B5).
    if (L.leaf->isPointerTy()) overPtr = true;
    assert(L.start <= cur && L.start + ls > cur && "a leaf holds the byte it was found for");
    cur = L.start + ls;
  }
  if (overPtr && note) (constant ? note->constOverPtr : note->dataOverPtr) = true;
  return "";
}

// One verdict for a write found from a site, by its web ((i)) or at the
// solve ((c), Fable 2026-10-22: the same function and consequence).
CallGraphPass::WriteVerdict CallGraphPass::judgeFoundWrite(const SiteName &S, const FoundWrite &w,
                                                           const DataLayout &DL) {
  WriteVerdict v;
  auto open = [&](const char *cls, std::string why) {
    v.cls = cls, v.why = std::move(why);
    return v;
  };
  switch (w.kind) {
  case 'm': {
    // A memset writes one byte value, repeated: never a pointer unless the
    // byte is taken from one (Fable 2026-10-22). Its length is the extent's
    // question, counted.
    if (carriesPtrToInt(w.V)) return open("memset", "a memset of a ptrtoint-derived value");
    const auto *Z = dyn_cast<ConstantInt>(w.V);
    v.kinds.push_back(Z && Z->isZero() ? "zero memset" : "memset of a non-pointer byte");
    if (!w.bytes) v.kinds.push_back("memset of runtime length");
    return v;
  }
  case 'c': {
    if (w.srcName.empty()) return open("copy", "a copy from an open source (D1)");
    const int64_t d = w.off >= 0 && S.repeats && S.size ? w.off % S.size : w.off;
    bool same = false;
    StringRef ln = isa<StructType>(S.layout) && cast<StructType>(S.layout)->hasName()
                       ? stripStructNameSuffix(cast<StructType>(S.layout)->getName())
                       : StringRef();
    if (!ln.empty() && d >= 0)
      same = (w.srcName == ln && w.srcOff == d) || (w.srcOff == 0 && structStartsAt(S.layout, d, w.srcName, DL)) ||
             (d == 0 && [&] {
               StructType *SS = StructType::getTypeByName(S.layout->getContext(), w.srcName);
               return SS && structStartsAt(SS, w.srcOff, ln, DL);
             }());
    if (!same) return open("copy", "a copy from " + w.srcName + "+" + std::to_string(w.srcOff));
    v.kinds.push_back("copy K-to-K");
    return v;
  }
  case 'u': break;
  default: llvm_unreachable("judgeFoundWrite: a write of no store, memset or copy kind");
  }
  // A store at a constant offset, or at a stride.
  if (w.off < 0) return open("runtime", "a runtime offset");
  if (w.sd && !(S.repeats && S.size && w.sd % S.size == 0)) {
    // A stride of an array inside L, or of the trailing array.
    const int64_t o2 = S.repeats && S.size ? w.off % S.size : w.off;
    std::function<bool(Type *, int64_t)> inArr = [&](Type *T, int64_t o) -> bool {
      if (auto *ST = dyn_cast<StructType>(T)) {
        if (ST->isOpaque() || o < 0 || (uint64_t)o >= DL.getTypeAllocSize(ST)) return false;
        const StructLayout *SL = DL.getStructLayout(ST);
        const unsigned i = SL->getElementContainingOffset(o);
        return inArr(ST->getElementType(i), o - SL->getElementOffset(i));
      }
      if (auto *AT = dyn_cast<ArrayType>(T)) {
        const int64_t es = DL.getTypeAllocSize(AT->getElementType());
        return (es && w.sd % es == 0 && (w.sd <= (int64_t)DL.getTypeAllocSize(AT) || S.trailing)) ||
               (es && inArr(AT->getElementType(), o % es));
      }
      return false;
    };
    const bool trailStride = S.trailing && S.trailElem && o2 >= S.trailAt &&
                             w.sd % (int64_t)DL.getTypeAllocSize(S.trailElem) == 0;
    if (!trailStride && !inArr(S.layout, o2)) {
      std::string t;
      raw_string_ostream os(t);
      w.VT->print(os);
      return open("runtime", "+" + std::to_string(w.off) + " " + os.str() + " at a stride " + std::to_string(w.sd) +
                                 " of no array of " + S.label);
    }
    v.kinds.push_back("stride of an inner array");
  }
  // A past-the-extent offset of an unknown-size one-then-unknown block
  // lies in its trailing object, not in L.
  if (!S.repeats && !S.trailing && w.off >= S.size && S.pastIsTrailingObject) {
    v.kinds.push_back("in the trailing object");
    return v;
  }
  SiteWriteNote n;
  const std::string why = judgeSiteWrite(S, w.off, w.bytes, w.VT, w.V, DL, &n);
  v.inUnion = n.inUnion, v.unionSlot = n.unionSlot, v.constOverPtr = n.constOverPtr, v.dataOverPtr = n.dataOverPtr;
  if (n.inUnion) v.kinds.push_back("union slot");
  if (!why.empty()) return open("FAIL", why);
  v.kinds.push_back("store on L's fields");
  return v;
}

CallGraphPass::FoundWrite CallGraphPass::solveWrite(const Instruction *I, int64_t off) {
  const DataLayout &DL = I->getModule()->getDataLayout();
  auto store = [&](const Value *SV) {
    return FoundWrite{I, off, DL.getTypeStoreSize(SV->getType()).getFixedValue(), SV->getType(), SV, 'u', 0, "", "", "", 0};
  };
  if (const auto *St = dyn_cast<StoreInst>(I)) return store(St->getValueOperand());
  if (const auto *RMW = dyn_cast<AtomicRMWInst>(I)) return store(RMW->getValOperand());
  if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(I)) return store(CX->getNewValOperand());
  if (const auto *MS = dyn_cast<MemSetInst>(I)) {
    const auto *Len = dyn_cast<ConstantInt>(MS->getLength());
    return FoundWrite{I, off, Len ? Len->getZExtValue() : 0, nullptr, MS->getValue(), 'm', 0, "", "", "", 0};
  }
  const auto *MT = dyn_cast<MemTransferInst>(I);
  assert(MT && "solveWrite: a store, an atomic or a memory intrinsic");
  if (!solvePointees) solvePointees = std::make_shared<PointeeResolver>(Ctx);
  StructType *SS = nullptr;
  int64_t so = 0;
  std::string sn;
  if (namedSlot(MT, MT->getRawSource(), DL, *solvePointees, SS, so) && SS && SS->hasName())
    sn = stripStructNameSuffix(SS->getName()).str();
  const auto *Len = dyn_cast<ConstantInt>(MT->getLength());
  return FoundWrite{I, off, Len ? Len->getZExtValue() : 0, nullptr, nullptr, 'c', 0, "", "", sn, so};
}

bool CallGraphPass::siteWriteHolds(const SiteName &S, int64_t off, int64_t len, StringRef KS, int64_t koff,
                                   int64_t klen, const DataLayout &DL) {
  Type *T = S.layout;
  int64_t lo = off;
  if (S.repeats && S.size) lo = off % S.size;
  else if (S.trailing && S.trailElem && off >= S.trailAt) {
    T = S.trailElem;
    const int64_t e = (int64_t)DL.getTypeAllocSize(T);
    lo = (off - S.trailAt) % e;
  }
  bool hit = false;
  structCover(T, lo, lo + std::max<int64_t>(len, 1), DL, [&](StructType *ST, int64_t a, int64_t b) {
    hit |= ST->hasName() && stripStructNameSuffix(ST->getName()) == KS && a < koff + klen && koff < b;
  });
  return hit;
}

void CallGraphPass::buildSiteNames() {
  siteNames.clear();
  siteNameOrder.clear();
  if (!mintTable) return;
  PointeeResolver pointees(Ctx);
  using W = FoundWrite;
  for (const CallBase *C : mintTable->order) {
    const SizeTerms::HeapMint &H = mintTable->at.at(C);
    if (!H.layout) continue;
    const Function *CF = C->getCalledFunction();
    if (!CF) continue;
    {
      auto sit = Ctx->FuncSummaries.find(CF);
      const bool fresh = (sit != Ctx->FuncSummaries.end() && sit->second && sit->second->fresh) ||
                         Ctx->AllocFuncs.count(const_cast<Function *>(CF));
      if (!fresh) continue;
    }
    const DataLayout &DL = C->getModule()->getDataLayout();
    SiteName S;
    S.layout = H.layout;
    S.label = H.ident.empty() ? H.label : H.ident;
    S.size = H.size;
    S.repeats = H.repeats || H.declArray;
    S.pastIsTrailingObject = H.extentSet && (H.extent.kind == 'u' || H.extent.kind == 'h');
    uint64_t tn = 2;
    if (Type *E = trailingArrayElem(H.layout, DL, &tn); E && E->isSized() && DL.getTypeAllocSize(E))
      S.trailElem = E, S.trailAt = S.size - (int64_t)(tn * DL.getTypeAllocSize(E));
    // (iii) the size, as the mint's extent reads it.
    bool sizeOK = true;
    if (H.declArray) {
      S.sizeKind = "n * sizeof(L) (a declared array)";
    } else if (!H.extentSet) {
      S.sizeKind = "sizeof(L)";
    } else {
      switch (H.extent.kind) {
      case '1': S.sizeKind = "sizeof(L)"; break;
      case 'a': S.sizeKind = "n * sizeof(L)"; break;
      case 'f': S.sizeKind = "sizeof(L) + k trailing elements (gap 2)", S.trailing = true; break;
      case 'u':
        S.sizeKind = "runtime";
        if (S.trailElem) S.sizeKind += " (sizeof(L) + k trailing elements, gap 2)", S.trailing = true;
        break;
      case 'h': {
        std::vector<const Value *> ops;
        int64_t add = 0;
        uint64_t prod = 1;
        bool cst = mintTable->terms->sizeOps(C, ops, add);
        for (const Value *X : ops)
          if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(X))) prod *= K->getZExtValue();
          else cst = false;
        if (S.trailElem) {
          const int64_t e = (int64_t)DL.getTypeAllocSize(S.trailElem);
          const int64_t rest = (int64_t)prod + add - S.size;
          if (!cst || (rest > 0 && rest % e == 0)) {
            S.sizeKind = cst ? "sizeof(L) + " + std::to_string(rest / e) + " trailing elements (A1)"
                             : "sizeof(L) + k trailing elements (A1, runtime k)";
            S.trailing = true;
            break;
          }
        }
        sizeOK = false;
        S.sizeKind = cst ? "header + data, size " + std::to_string((int64_t)prod + add) + " vs " +
                               std::to_string(S.size)
                         : "header + data, runtime size";
        break;
      }
      default: S.sizeKind = "runtime";
      }
    }
    // (i) the writes found from the site: its web (casts, -O0 slots, phis,
    // selects), GEP chains, direct callees' formals (recursively, cycles
    // cut), returns (a direct callee returning its formal: its call; the
    // site's own function and every function it is returned from at the
    // top: every direct caller).
    std::vector<W> WS;
    std::set<std::pair<const Argument *, int64_t>> vis;
    std::set<const Function *> retFollowed;
    std::function<std::vector<int64_t>(std::vector<std::tuple<const Value *, int64_t, bool, int64_t>>, int)> walk =
        [&](std::vector<std::tuple<const Value *, int64_t, bool, int64_t>> aw, int depth) {
          std::vector<int64_t> returned;
          std::set<const Value *> aseen;
          while (!aw.empty() && aseen.size() < 4096) {
            auto [A, off, st, sd] = aw.back();
            aw.pop_back();
            if (!aseen.insert(A).second) continue;
            // A pool carve is an object of its own (Carves.cc), not the block's.
            if (const auto *AI = dyn_cast<Instruction>(A); AI && A != C && poolCarvePool.count(AI)) {
              S.kinds["pool carves (their own objects)"]++;
              continue;
            }
            const DataLayout &ADL = isa<Instruction>(A) ? cast<Instruction>(A)->getModule()->getDataLayout()
                                                         : cast<Argument>(A)->getParent()->getParent()->getDataLayout();
            for (const User *U : A->users()) {
              if (const auto *G2 = dyn_cast<GEPOperator>(U)) {
                if (G2->getPointerOperand() != A) continue;
                // Constant indices add to the offset; one variable index is a
                // stride of the type it indexes; two, or a stride on a
                // stride, is a runtime offset.
                bool ss = st || isa<StructType>(G2->getSourceElementType());
                int64_t c = 0, stride = 0;
                bool ok = off >= 0;
                for (auto It = gep_type_begin(G2), E = gep_type_end(G2); ok && It != E; ++It) {
                  if (StructType *STy = It.getStructTypeOrNull()) {
                    ss = true;
                    c += ADL.getStructLayout(STy)->getElementOffset(cast<ConstantInt>(It.getOperand())->getZExtValue());
                    continue;
                  }
                  const int64_t es = ADL.getTypeAllocSize(It.getIndexedType());
                  if (const auto *CI = dyn_cast<ConstantInt>(It.getOperand())) c += CI->getSExtValue() * es;
                  else if (!stride && !sd) stride = es;
                  else ok = false;
                }
                aw.push_back({G2, ok ? off + c : -1, ss, ok ? (stride ? stride : sd) : 0});
              } else if ((isa<CastInst>(U) && U->getType()->isPointerTy()) || isa<PHINode>(U) || isa<SelectInst>(U)) {
                aw.push_back({U, off, st, sd});
              } else if (const auto *St = dyn_cast<StoreInst>(U)) {
                if (St->getValueOperand() == A) {
                  // Into an -O0 slot: its loads read it. Elsewhere: an escape
                  // by store, which (c) judges at the solve.
                  if (const auto *AI = dyn_cast<AllocaInst>(St->getPointerOperand()->stripPointerCasts());
                      AI && transientSlot(AI))
                    for (const User *SU : AI->users())
                      if (isa<LoadInst>(SU)) aw.push_back({SU, off, st, sd});
                  continue;
                }
                Type *VT = St->getValueOperand()->getType();
                WS.push_back({St, off, ADL.getTypeStoreSize(VT).getFixedValue(), VT, St->getValueOperand(), st ? 's' : 'u',
                              sd, "", "", "", 0});
              } else if (const auto *RMW = dyn_cast<AtomicRMWInst>(U)) {
                if (RMW->getPointerOperand() != A) continue;
                Type *VT = RMW->getValOperand()->getType();
                WS.push_back({RMW, off, ADL.getTypeStoreSize(VT).getFixedValue(), VT, RMW->getValOperand(), st ? 's' : 'u',
                              sd, "", "", "", 0});
              } else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(U)) {
                if (CX->getPointerOperand() != A) continue;
                Type *VT = CX->getNewValOperand()->getType();
                WS.push_back({CX, off, ADL.getTypeStoreSize(VT).getFixedValue(), VT, CX->getNewValOperand(),
                              st ? 's' : 'u', sd, "", "", "", 0});
              } else if (const auto *MS = dyn_cast<MemSetInst>(U)) {
                if (MS->getRawDest() != A) continue;
                const auto *Len = dyn_cast<ConstantInt>(MS->getLength());
                WS.push_back({MS, off, Len ? Len->getZExtValue() : 0, nullptr, MS->getValue(), 'm', sd, "", "", "", 0});
              } else if (const auto *MT = dyn_cast<MemTransferInst>(U)) {
                if (MT->getRawDest() != A) continue;
                StructType *SS = nullptr;
                int64_t so = 0;
                std::string sn;
                if (namedSlot(MT, MT->getRawSource(), ADL, pointees, SS, so) && SS && SS->hasName())
                  sn = stripStructNameSuffix(SS->getName()).str();
                const auto *Len = dyn_cast<ConstantInt>(MT->getLength());
                WS.push_back({MT, off, Len ? Len->getZExtValue() : 0, nullptr, nullptr, 'c', sd, "", "", sn, so});
              } else if (isa<ReturnInst>(U)) {
                if (depth > 0) {
                  returned.push_back(off);
                  continue;
                }
                const Function *F = cast<Instruction>(U)->getFunction();
                if (!retFollowed.insert(F).second) continue;
                for (const User *FU : F->users()) {
                  const auto *CB2 = dyn_cast<CallBase>(FU);
                  if (CB2 && CB2->getCalledOperand() == F) {
                    aw.push_back({CB2, off, st, sd});
                    continue;
                  }
                  WS.push_back({cast<Instruction>(U), off, 0, nullptr, nullptr, 'o', sd, "return",
                                "returned by " + F->getName().str() + ", which has an indirect or unknown caller", "", 0});
                  break;
                }
              } else if (const auto *C2 = dyn_cast<CallBase>(U)) {
                if (isa<IntrinsicInst>(C2) || C2->getCalledOperand() == A) continue;
                const Function *F = dyn_cast<Function>(C2->getCalledOperand()->stripPointerCasts());
                for (unsigned i = 0; i < C2->arg_size(); i++) {
                  if (C2->getArgOperand(i) != A) continue;
                  if (!F) {
                    // B1: an indirect call is OPEN (R5 follows its slot: C).
                    std::string slot = valueText(C2->getCalledOperand());
                    if (const auto *Ld = dyn_cast<LoadInst>(C2->getCalledOperand()->stripPointerCasts())) {
                      StructType *SS = nullptr;
                      int64_t so = 0;
                      if (namedSlot(Ld, Ld->getPointerOperand(), ADL, pointees, SS, so) && SS && SS->hasName())
                        slot = stripStructNameSuffix(SS->getName()).str() + "+" + std::to_string(so);
                    }
                    WS.push_back({C2, off, 0, nullptr, nullptr, 'o', sd, "call", "passed to an indirect call through " + slot,
                                  "", 0});
                    continue;
                  }
                  auto sit = Ctx->FuncSummaries.find(F);
                  auto FS = sit != Ctx->FuncSummaries.end() ? sit->second : nullptr;
                  if (FS && FS->externOnly && !F->isDeclaration()) FS = nullptr;
                  if (FS && !FS->body && !FS->none) {
                    // B4: a summarized callee by its atoms only.
                    if (FS->noop) {
                      WS.push_back({C2, off, 0, nullptr, nullptr, 'n', sd, "", "", "", 0});
                      continue;
                    }
                    if (FS->freeArg == (int)i) continue; // the object is dead after the call
                    for (const auto &At : FS->atoms) {
                      using K = std::decay_t<decltype(At)>;
                      if (At.kind == K::Alias && At.src == (int)i && At.dst == -1) {
                        aw.push_back({C2, off, st, sd}); // the result is the object
                        continue;
                      }
                      if (At.dst != (int)i || At.gdst) continue;
                      if (At.kind == K::Store || At.kind == K::FreshSub) {
                        // The stored value: the actual at src (a global's
                        // address, or a fresh sub-object: a pointer).
                        const Value *SV = At.kind == K::Store && !At.gsrc && At.src >= 0 &&
                                                  (unsigned)At.src < C2->arg_size()
                                              ? C2->getArgOperand(At.src)
                                              : nullptr;
                        Type *SVT = SV ? SV->getType() : PointerType::get(F->getContext(), 0);
                        WS.push_back({C2, off >= 0 ? off + At.dstByteOff : -1, ADL.getTypeStoreSize(SVT).getFixedValue(),
                                      SVT, SV, 'u', sd, "", "summary of " + F->getName().str(), "", 0});
                      }
                      else if (At.kind == K::Cpy || At.kind == K::Move || At.kind == K::MoveX || At.kind == K::Move2 ||
                               At.kind == K::Store2)
                        WS.push_back({C2, off, 0, nullptr, nullptr, 'b', sd, "bodiless write",
                                      "bytes written by " + F->getName().str() + "'s summary", "", 0});
                    }
                    continue;
                  }
                  if (F->isDeclaration()) {
                    WS.push_back({C2, off, 0, nullptr, nullptr, 'o', sd, "call",
                                  "passed to bodiless " + F->getName().str() + (FS ? " (NONE)" : " (no summary)"), "", 0});
                    continue;
                  }
                  if (i >= F->arg_size()) {
                    WS.push_back({C2, off, 0, nullptr, nullptr, 'o', sd, "vararg",
                                  "passed as a vararg to " + F->getName().str(), "", 0});
                    continue;
                  }
                  const Argument *FA = F->getArg(i);
                  if (!vis.insert({FA, off}).second) {
                    S.cycles++;
                    continue;
                  }
                  if (depth >= 8) {
                    WS.push_back({C2, off, 0, nullptr, nullptr, 'o', sd, "call",
                                  "callee depth 8 reached at " + F->getName().str(), "", 0});
                    continue;
                  }
                  for (int64_t r : walk({{FA, off, st, sd}}, depth + 1)) aw.push_back({C2, r, st, sd});
                }
              }
            }
          }
          return returned;
        };
    walk({{C, 0, false, 0}}, 0);
    // Judge each write against L.
    std::map<std::string, std::string> firstOf; // category -> its first write
    auto note1 = [&](const std::string &cat, const std::string &x, const Instruction *I) {
      S.kinds[cat]++;
      if (!firstOf.count(cat)) firstOf[cat] = x + " " + instLoc(I);
    };
    for (const W &w : WS) {
      S.found.insert(w.I);
      switch (w.kind) {
      case 's': S.kinds["struct step"]++; continue;
      case 'n': S.kinds["NOOP call"]++; continue;
      case 'o': note1(w.cat, w.why, w.I); continue;
      case 'b': {
        // Amendment 3: bytes over no pointer field of L pass.
        // The size of such an atom's write is not known: judged against the
        // whole extent (L, and its trailing array's element).
        std::function<bool(Type *)> holdsPtr = [&](Type *T) -> bool {
          if (T->isPointerTy()) return true;
          if (auto *ST = dyn_cast<StructType>(T))
            return llvm::any_of(ST->elements(), [&](Type *E) { return holdsPtr(E); });
          if (auto *AT = dyn_cast<ArrayType>(T)) return holdsPtr(AT->getElementType());
          if (auto *VT = dyn_cast<VectorType>(T)) return holdsPtr(VT->getElementType());
          return false;
        };
        if (holdsPtr(S.layout) || (S.trailing && S.trailElem && holdsPtr(S.trailElem)))
          note1("bodiless write", w.why, w.I);
        else S.kinds["bodiless bytes over no pointer field"]++;
        continue;
      }
      default: break;
      }
      const WriteVerdict v = judgeFoundWrite(S, w, DL);
      if (v.inUnion) {
        if (cellUnionSlots.count(v.unionSlot)) S.keyedUnion++;
        else S.unkeyedUnion++;
      }
      if (v.constOverPtr) S.constOverPtr++;
      if (v.dataOverPtr) S.dataOverPtr++;
      if (v.cls.empty()) {
        for (const std::string &k : v.kinds) S.kinds[k]++;
      } else note1(v.cls, v.why, w.I);
    }
    static const char *const order[] = {"FAIL",    "call",           "copy",   "memset",
                                        "runtime", "bodiless write", "vararg", "return"};
    for (const char *k : order)
      if (firstOf.count(k)) {
        S.verdict = std::string(k) == "FAIL" ? 'f' : 'o';
        S.why = k;
        S.first = firstOf[k];
        break;
      }
    if (!S.verdict) S.verdict = sizeOK ? 'n' : 's';
    if (S.verdict == 's') S.why = S.sizeKind;
    // (c): a write found at an earlier solve that does not check.
    if (auto b = siteBrokenAtSolve.find(C); S.verdict == 'n' && b != siteBrokenAtSolve.end())
      S.verdict = 'c', S.why = "(c)", S.first = b->second;
    siteNameOrder.push_back(C);
    siteNames.emplace(C, std::move(S));
  }
  siteNamesReport(true);
}

void CallGraphPass::siteNamesReport(bool logRows) {
  // The log line and the rule report's rows, in IR order.
  std::map<std::string, size_t> openBy;
  size_t named = 0, fail = 0, bySize = 0, atSolve = 0, cycles = 0, cOver = 0, dOver = 0, unk = 0, keyed = 0, noop = 0, bodilessOK = 0;
  siteNameRows.clear();
  for (const CallBase *C : siteNameOrder) {
    const SiteName &S = siteNames.at(C);
    cycles += S.cycles, cOver += S.constOverPtr, dOver += S.dataOverPtr;
    if (auto it = S.kinds.find("NOOP call"); it != S.kinds.end()) noop += it->second;
    if (auto it = S.kinds.find("bodiless bytes over no pointer field"); it != S.kinds.end()) bodilessOK += it->second;
    if (S.verdict == 'n') {
      named++;
      unk += S.unkeyedUnion > 0, keyed += S.keyedUnion > 0;
    } else if (S.verdict == 'f') fail++;
    else if (S.verdict == 's') bySize++;
    else if (S.verdict == 'c') atSolve++;
    else openBy[S.why]++;
    std::string ks;
    for (auto &[k, n] : S.kinds) ks += (ks.empty() ? "" : ", ") + k + " " + std::to_string(n);
    const std::string head = instLoc(C) + " " + C->getCalledFunction()->getName().str() + ": " + S.label + ": ";
    const std::string row = head +
                            (S.verdict == 'n'   ? std::string("named")
                             : S.verdict == 's' ? "untyped by size (" + S.why + ")"
                             : S.verdict == 'f' ? "FAIL: " + S.first
                             : S.verdict == 'c' ? "untyped at the solve: " + S.first
                                                : "open (" + S.why + "): " + S.first) +
                            "; (iii) " + S.sizeKind + "; writes: " + ks + "; cycles cut " + std::to_string(S.cycles);
    if (logRows) CG_LOG("Cells: site names (B): " << row << "\n");
    if (S.verdict != 'n') siteNameRows.push_back(row);
  }
  auto ob = [&](const char *k) { auto it = openBy.find(k); return it == openBy.end() ? (size_t)0 : it->second; };
  size_t open = 0;
  for (auto &[k, n] : openBy) open += n;
  siteNameSummary = std::to_string(named) + " named of " + std::to_string(siteNameOrder.size()) +
                    " mint-labeled fresh sites; open " + std::to_string(open) + " (call " + std::to_string(ob("call")) +
                    ", copy " + std::to_string(ob("copy")) + ", memset " + std::to_string(ob("memset")) + ", runtime " +
                    std::to_string(ob("runtime")) + ", bodiless write " + std::to_string(ob("bodiless write")) +
                    ", vararg " + std::to_string(ob("vararg")) + ", return " + std::to_string(ob("return")) + "); FAIL " +
                    std::to_string(fail) + "; untyped by size " + std::to_string(bySize) + "; untyped at the solve ((c)) " +
                    std::to_string(atSolve) + "; cycles cut " +
                    std::to_string(cycles) + "; non-pointer values over pointer fields: " + std::to_string(cOver) +
                    " constant, " + std::to_string(dOver) + " with no ptrtoint; named sites with a union-slot write: " +
                    std::to_string(unk) + " unkeyed, " + std::to_string(keyed) + " keyed; NOOP calls " +
                    std::to_string(noop) + ", bodiless byte writes over no pointer field " + std::to_string(bodilessOK);
  if (logRows) CG_LOG("Cells: site names (B): " << siteNameSummary << "\n");
}
