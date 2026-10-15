//===-- LinkWords.cc - tagged-pointer link words (plan 3.55 R1) ----------===//
//
// A link word is an integer field that holds a pointer whose low bits carry
// data (rb_node.__rb_parent_color = parent | color). The flow already keeps
// p's facts through `ptrtoint | k`, masks, compares and inttoptr
// (ptrToIntTagRoundTripOnly, GraphBuild.cc); this pass adds the checked
// classification, report only (Fable 2026-10-15, R1 step 1):
// - candidates: integer fields of pointer width (named by the innermost
//   struct holding them) with a load whose value reaches inttoptr;
// - a tag value is a constant < 8, `and x, c` with c < 8, or casts, or/xor,
//   phi/select of tag values;
// - a tagged word is ptrtoint(p); a constant < 8 (null plus tag); a load of
//   a candidate field (a copy); or/xor of a tagged word and a tag value;
//   add of a tag value onto a word whose low bits are known zero
//   (ptrtoint(p) or a clear: rb_set_parent's `p + color`); `and w, c` with
//   ~c < 8 (a clear); phi/select of tagged words;
// - a field passes when every store's value is a tagged word and every
//   load's uses (through phi/select, or-tag and clears) end in inttoptr, a
//   compare, a tag extraction, or a store into a candidate field. A field
//   that fails is dropped and the rest re-checked (a copy's status is its
//   source's), to a fixpoint;
// - an inttoptr with no clear on the way is admitted as an ASSUMPTION
//   (the program relies on tag 0 at that read: rb_red_parent); counted:
//   self-link stores (an element's own address into its own word, R2) and
//   self-derived stores (over a load of the same cell, R4).
// Pointer-typed fields that receive inttoptr-encoded words (XArray slots:
// node | 2, values, internal constants) are reported by shape, no verdict
// (R1 addendum (b) is measured, not built).
// An access names its field by its struct GEP, its struct-path TBAA tag, an
// array member's GEP at a variable index, or, at offset 0 with neither (the
// kernel: -fno-strict-aliasing, no debug info), the address's declared
// pointee (PointeeResolver: debug info, sibling GEPs, formal provenance).
// A copy through an access none of these name fails its field "on naming".
// The classification reads SSA: a value through a local slot (-O0) is a
// copy from an unnamed access and fails its field.
//
//===----------------------------------------------------------------------===//

#include "CallGraph.h"
#include "CallGraphInternal.h"
#include "NamedCells.h"
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Operator.h>

using namespace llvm;

namespace {
using FieldKey = std::pair<std::string, int64_t>; // (struct name, byte offset)


static const Value *stripIntCasts(const Value *V) {
  for (int i = 0; i < 16; i++) {
    if (const auto *C = dyn_cast<CastInst>(V);
        C && (isa<ZExtInst>(C) || isa<TruncInst>(C) || isa<BitCastInst>(C) || isa<SExtInst>(C)))
      V = C->getOperand(0);
    else if (const auto *F = dyn_cast<FreezeInst>(V))
      V = F->getOperand(0);
    else
      break;
  }
  return V;
}

static std::string siteOf(const Instruction *I) {
  std::string s;
  raw_string_ostream os(s);
  os << I->getFunction()->getName() << ":";
  if (const DebugLoc &DLc = I->getDebugLoc()) os << DLc.getLine() << ":";
  os << " ";
  I->print(os);
  return s.substr(0, 240);
}
} // namespace

// A pointer stored into a pointer field, by the R1 addendum (b) clauses: a
// node | k, a value (odd), an internal constant or encoding ((v << 2) | 2),
// a decoded pointer (a mask or subtraction back to an address), null, or an
// untagged pointer.
static std::string encodedClass(const Value *V) {
  if (isa<ConstantPointerNull>(V)) return "null";
  const Value *IV = nullptr;
  if (const auto *IP = dyn_cast<IntToPtrInst>(V)) IV = IP->getOperand(0);
  else if (const auto *CE = dyn_cast<ConstantExpr>(V); CE && CE->getOpcode() == Instruction::IntToPtr)
    IV = CE->getOperand(0);
  if (!IV) return "untagged pointer";
  IV = stripIntCasts(IV);
  if (const auto *C = dyn_cast<ConstantInt>(IV)) {
    const uint64_t v = C->getZExtValue();
    return v == 0 ? "null" : (v & 1) ? "value encoding" : (v & 3) == 2 ? "internal constant" : "constant other";
  }
  const auto *BO = dyn_cast<Operator>(IV);
  if (!BO || !Instruction::isBinaryOp(BO->getOpcode())) return "decoded pointer";
  const auto *C = dyn_cast<ConstantInt>(BO->getOperand(1));
  const Value *A = stripIntCasts(BO->getOperand(0));
  if (BO->getOpcode() == Instruction::Or && C) {
    if (isa<PtrToIntOperator>(A) && C->getValue().ult(8)) return "node link (tag " + std::to_string(C->getZExtValue()) + ")";
    if (C->getZExtValue() & 1) return "value encoding";
    if ((C->getZExtValue() & 3) == 2) return "internal encoding";
  }
  if ((BO->getOpcode() == Instruction::And && C && (~C->getValue()).ult(8)) ||
      ((BO->getOpcode() == Instruction::Add || BO->getOpcode() == Instruction::Sub) && C))
    return "decoded pointer";
  return "encoded other";
}

void CallGraphPass::computeLinkWords() {
  linkWordReport.clear();
  linkWordFields.clear();
  linkWordVerdicts.clear();
  struct Field {
    std::vector<const StoreInst *> stores;
    std::vector<const LoadInst *> loads;
    bool isInt = false, isPtr = false, reads = false, encoded = false;
  };
  std::map<FieldKey, Field> fields;
  std::map<const Instruction *, FieldKey> fieldOf;
  PointeeResolver pointees(Ctx);
  std::map<const Function *, size_t> unnamedIn; // unnamed offset-0 accesses that would feed a link word
  auto reachesI2P = [](const Value *L) {
    std::vector<const Value *> wl{L};
    std::set<const Value *> seen{L};
    while (!wl.empty()) {
      const Value *X = wl.back();
      wl.pop_back();
      for (const User *U : X->users()) {
        if (isa<IntToPtrInst>(U)) return true;
        if ((isa<CastInst>(U) || isa<BinaryOperator>(U) || isa<PHINode>(U) || isa<SelectInst>(U) ||
             isa<FreezeInst>(U)) && seen.insert(U).second)
          wl.push_back(U);
      }
    }
    return false;
  };
  auto hasPtrToInt = [](const Value *V) {
    std::vector<const Value *> wl{V};
    std::set<const Value *> seen{V};
    for (int steps = 0; !wl.empty() && steps < 64; steps++) {
      const Value *X = wl.back();
      wl.pop_back();
      if (isa<PtrToIntOperator>(X)) return true;
      if (const auto *O = dyn_cast<Operator>(X))
        if (isa<CastInst>(O) || Instruction::isBinaryOp(O->getOpcode()) || isa<PHINode>(O) || isa<SelectInst>(O))
          for (const Value *Op : O->operands())
            if (seen.insert(Op).second) wl.push_back(Op);
    }
    return false;
  };
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    const unsigned pw = DL.getPointerSizeInBits();
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        const Value *Addr = nullptr;
        Type *AT = nullptr;
        if (const auto *L = dyn_cast<LoadInst>(&I)) Addr = L->getPointerOperand(), AT = L->getType();
        else if (const auto *S = dyn_cast<StoreInst>(&I))
          Addr = S->getPointerOperand(), AT = S->getValueOperand()->getType();
        else continue;
        StructType *ST = nullptr;
        int64_t off = 0;
        if ((!accessSlot(&I, Addr, DL, ST, off) || !ST || !ST->hasName()) && !arraySlot(Addr, DL, ST, off)) {
          pointees.viaFormal = pointees.viaSibling = pointees.viaDecl = false;
          ST = pointees.get(Addr, I.getContext()), off = 0;
          if (ST)
            (pointees.viaFormal    ? pointees.byFormal
             : pointees.viaSibling ? pointees.bySibling
             : pointees.viaDecl    ? pointees.byDecl
                                   : pointees.byDI)++;
          if (!ST) {
            // Would it have fed a link word? A pointer-width integer access
            // that reads into inttoptr or stores a ptrtoint-derived word.
            if (AT->isIntegerTy(pw) && (isa<StoreInst>(&I) || reachesI2P(&I)) &&
                (isa<LoadInst>(&I) || hasPtrToInt(cast<StoreInst>(&I)->getValueOperand())))
              unnamedIn[&F]++;
            continue;
          }
        }
        FieldKey K;
        Type *leaf = nullptr;
        int64_t inLeaf = 0;
        if (!innermostField(ST, off, DL, K, leaf, inLeaf) || inLeaf != 0) continue;
        const bool lInt = leaf->isIntegerTy(pw), lPtr = leaf->isPointerTy();
        if (!lInt && !lPtr) continue;
        if (DL.getTypeStoreSize(AT) != DL.getTypeStoreSize(leaf)) continue; // a partial or wide access
        Field &Fd = fields[K];
        Fd.isInt = lInt, Fd.isPtr = lPtr;
        fieldOf[&I] = K;
        if (const auto *L = dyn_cast<LoadInst>(&I)) {
          Fd.loads.push_back(L);
          if (lInt && AT->isPointerTy()) Fd.reads = true;
          if (lInt && AT->isIntegerTy() && !Fd.reads) Fd.reads = reachesI2P(L); // the word reaches inttoptr
        } else {
          const auto *S = cast<StoreInst>(&I);
          Fd.stores.push_back(S);
          if (lPtr) {
            const std::string c = encodedClass(S->getValueOperand());
            if (c.rfind("node link", 0) == 0 || c == "value encoding" || c == "internal constant" ||
                c == "internal encoding")
              Fd.encoded = true;
          }
        }
      }
  }

  std::set<FieldKey> cand;
  for (auto &[K, Fd] : fields)
    if (Fd.isInt && Fd.reads) cand.insert(K);
  const std::set<FieldKey> candidates = cand;

  auto keyName = [](const FieldKey &K) { return K.first + "+" + std::to_string(K.second); };
  auto isTag = [&](const Value *V) {
    std::function<bool(const Value *, int)> rec = [&](const Value *X, int d) -> bool {
      X = stripIntCasts(X);
      if (d > 8) return false;
      if (const auto *C = dyn_cast<ConstantInt>(X)) return C->getValue().ult(8);
      if (const auto *BO = dyn_cast<BinaryOperator>(X)) {
        if (BO->getOpcode() == Instruction::And)
          for (unsigned i = 0; i < 2; i++)
            if (const auto *C = dyn_cast<ConstantInt>(BO->getOperand(i)); C && C->getValue().ult(8)) return true;
        if (BO->getOpcode() == Instruction::Or || BO->getOpcode() == Instruction::Xor)
          return rec(BO->getOperand(0), d + 1) && rec(BO->getOperand(1), d + 1);
        return false;
      }
      if (const auto *SI = dyn_cast<SelectInst>(X)) return rec(SI->getTrueValue(), d + 1) && rec(SI->getFalseValue(), d + 1);
      if (const auto *PN = dyn_cast<PHINode>(X)) {
        for (const Value *In : PN->incoming_values())
          if (In != PN && !rec(In, d + 1)) return false;
        return true;
      }
      return false;
    };
    return rec(V, 0);
  };

  // One store's value: is it a tagged word? `top` names its shape; the
  // flags mark a self-link (R2) and a self-derived value (R4).
  struct StoreEval {
    bool ok = true;
    std::string top, why;
    bool selfLink = false, selfDerived = false, copy = false, naming = false;
  };
  auto evalStore = [&](const StoreInst *S, const FieldKey &K) {
    StoreEval E;
    const Value *Addr = S->getPointerOperand();
    const DataLayout &DL = S->getModule()->getDataLayout();
    APInt offA(DL.getIndexTypeSizeInBits(Addr->getType()), 0);
    const Value *baseA = Addr->stripAndAccumulateConstantOffsets(DL, offA, true);
    std::set<const Value *> onPath;
    // lowZero: the word's low bits are known zero (ptrtoint(p), a clear).
    std::function<bool(const Value *, bool &)> tw = [&](const Value *V, bool &lowZero) -> bool {
      V = stripIntCasts(V);
      lowZero = false;
      if (!onPath.insert(V).second) return true; // a loop through phis: the other entries decide
      struct Pop { std::set<const Value *> &s; const Value *v; ~Pop() { s.erase(v); } } pop{onPath, V};
      if (const auto *C = dyn_cast<ConstantInt>(V)) {
        if (!C->getValue().ult(8)) return E.why = "constant >= 8", false;
        lowZero = C->isZero();
        return true;
      }
      if (isa<ConstantPointerNull>(V)) return lowZero = true, true;
      const Value *P = nullptr;
      if (const auto *PI = dyn_cast<PtrToIntInst>(V)) P = PI->getOperand(0);
      else if (const auto *CE = dyn_cast<ConstantExpr>(V); CE && CE->getOpcode() == Instruction::PtrToInt)
        P = CE->getOperand(0);
      if (P) {
        APInt offP(DL.getIndexTypeSizeInBits(P->getType()), 0);
        const Value *baseP = P->stripAndAccumulateConstantOffsets(DL, offP, true);
        if (baseP == baseA && (offA - offP).getSExtValue() == K.second) E.selfLink = true;
        lowZero = true;
        return true;
      }
      if (V->getType()->isPointerTy()) return lowZero = true, true; // a pointer stored as the word
      if (isTag(V)) return true;                                    // tag bits over a null word
      if (const auto *L = dyn_cast<LoadInst>(V)) {
        if (L->getPointerOperand() == Addr) E.selfDerived = true;
        auto it = fieldOf.find(L);
        if (it == fieldOf.end()) return E.why = "copy from an unnamed access", E.naming = true, false;
        if (!cand.count(it->second)) return E.why = "copy from " + keyName(it->second) + " (not a link word)", false;
        E.copy = true;
        return true;
      }
      const auto *BO = dyn_cast<Operator>(V);
      if (BO && Instruction::isBinaryOp(BO->getOpcode())) {
        const Value *A = BO->getOperand(0), *B = BO->getOperand(1);
        const std::string opName = Instruction::getOpcodeName(BO->getOpcode());
        switch (BO->getOpcode()) {
        case Instruction::Or:
        case Instruction::Xor:
        case Instruction::Add: {
          if (isTag(A)) std::swap(A, B);
          if (!isTag(B))
            return E.why = opName +
                           (isa<ConstantInt>(B) || isa<ConstantInt>(A) ? " of a constant >= 8" : " of two non-tag values"),
                   false;
          bool lz = false;
          if (!tw(A, lz)) return false;
          if (BO->getOpcode() == Instruction::Add && !lz) return E.why = "add to tagged word", false;
          return true;
        }
        case Instruction::And: {
          const auto *C = dyn_cast<ConstantInt>(B);
          if (!C) C = dyn_cast<ConstantInt>(A), A = B;
          if (!C || !(~C->getValue()).ult(8)) return E.why = "mask beyond tag bits", false;
          bool lz = false;
          if (!tw(A, lz)) return false;
          lowZero = true;
          return true;
        }
        default:
          return E.why = "arithmetic: " + opName, false;
        }
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        bool all = true;
        for (const Value *In : PN->incoming_values()) {
          bool lz = false;
          if (!tw(In, lz)) return false;
          all &= lz;
        }
        lowZero = all;
        return true;
      }
      if (const auto *SI = dyn_cast<SelectInst>(V)) {
        bool l1 = false, l2 = false;
        if (!tw(SI->getTrueValue(), l1) || !tw(SI->getFalseValue(), l2)) return false;
        lowZero = l1 && l2;
        return true;
      }
      if (isa<Argument>(V)) return E.why = "argument", false;
      if (isa<CallBase>(V)) return E.why = "call result", false;
      if (const auto *I = dyn_cast<Instruction>(V)) return E.why = I->getOpcodeName(), false;
      return E.why = "constant expression", false;
    };
    const Value *V = stripIntCasts(S->getValueOperand());
    bool lz = false;
    E.ok = tw(V, lz);
    if (V->getType()->isPointerTy()) E.top = "pointer";
    else if (isa<ConstantInt>(V) || (isTag(V) && !isa<LoadInst>(V))) E.top = "null+tag";
    else if (const auto *PO = dyn_cast<PtrToIntOperator>(V); PO) E.top = E.selfLink ? "self-link" : "ptrtoint";
    else if (isa<LoadInst>(V)) E.top = "copy";
    else if (isa<PHINode>(V) || isa<SelectInst>(V)) E.top = "phi";
    else if (const auto *BO = dyn_cast<Operator>(V); BO && Instruction::isBinaryOp(BO->getOpcode()))
      E.top = BO->getOpcode() == Instruction::And ? "clear tag"
              : BO->getOpcode() == Instruction::Add ? "add tag" : "or tag";
    else E.top = "other";
    if (E.top != "self-link" && E.selfLink && E.top != "phi") E.top += " (self-link)";
    return E;
  };

  // One load's uses: the classes they end in, assumption sites (inttoptr
  // with no clear on the way), or the first failing use.
  struct LoadEval {
    bool ok = true;
    std::string why;
    bool naming = false;
    const Instruction *at = nullptr;
    std::set<std::string> classes;
    std::vector<const Instruction *> unmasked;
  };
  auto evalLoad = [&](const LoadInst *L) {
    LoadEval E;
    if (L->getType()->isPointerTy()) {
      E.classes.insert("unmasked");
      E.unmasked.push_back(L);
      return E;
    }
    std::vector<std::pair<const Value *, bool>> wl{{L, false}}; // (value, cleared on the way)
    std::set<std::pair<const Value *, bool>> seen{{L, false}};
    auto push = [&](const Value *V, bool m) {
      if (seen.insert({V, m}).second) wl.push_back({V, m});
    };
    while (!wl.empty() && E.ok) {
      auto [X, masked] = wl.back();
      wl.pop_back();
      for (const User *U : X->users()) {
        const auto *UI = dyn_cast<Instruction>(U);
        if (!UI) continue;
        auto fail = [&](const std::string &w) {
          if (E.ok) E.ok = false, E.why = w, E.at = UI;
        };
        if (isa<IntToPtrInst>(UI)) {
          if (masked) E.classes.insert("masked");
          else E.classes.insert("unmasked"), E.unmasked.push_back(cast<Instruction>(UI));
        } else if (isa<ICmpInst>(UI) || isa<SwitchInst>(UI)) {
          E.classes.insert("compared");
        } else if (isa<PHINode>(UI) || isa<SelectInst>(UI) || isa<FreezeInst>(UI) || isa<ZExtInst>(UI) ||
                   isa<TruncInst>(UI) || isa<BitCastInst>(UI)) {
          push(UI, masked);
        } else if (const auto *BO = dyn_cast<BinaryOperator>(UI)) {
          const Value *O = BO->getOperand(BO->getOperand(0) == X ? 1 : 0);
          const auto *C = dyn_cast<ConstantInt>(O);
          if (BO->getOpcode() == Instruction::And && C && C->getValue().ult(8)) E.classes.insert("tag extract");
          else if (BO->getOpcode() == Instruction::And && C && (~C->getValue()).ult(8)) push(UI, true);
          else if ((BO->getOpcode() == Instruction::Or || BO->getOpcode() == Instruction::Xor) && isTag(O))
            E.classes.insert("set tag"), push(UI, false);
          else if (BO->getOpcode() == Instruction::Add && isTag(O)) fail("add to tagged word");
          else fail(std::string("arithmetic: ") + BO->getOpcodeName());
        } else if (const auto *S = dyn_cast<StoreInst>(UI)) {
          if (S->getValueOperand() != X) { fail("used as an address"); continue; }
          auto it = fieldOf.find(S);
          if (it != fieldOf.end() && cand.count(it->second)) E.classes.insert("copy");
          else if (it == fieldOf.end()) fail("copied into an unnamed access"), E.naming = true;
          else fail("stored into " + keyName(it->second) + " (not a link word)");
        } else if (isa<CallBase>(UI)) {
          fail("call argument");
        } else if (isa<ReturnInst>(UI)) {
          fail("returned");
        } else {
          fail(UI->getOpcodeName());
        }
      }
    }
    return E;
  };

  // The fixpoint: drop a field on a failing site, re-check the rest.
  for (bool changed = true; changed;) {
    changed = false;
    for (const FieldKey &K : std::set<FieldKey>(cand)) {
      const Field &Fd = fields[K];
      bool ok = true;
      for (const StoreInst *S : Fd.stores)
        if (!evalStore(S, K).ok) { ok = false; break; }
      for (size_t i = 0; ok && i < Fd.loads.size(); i++)
        if (!evalLoad(Fd.loads[i]).ok) ok = false;
      if (!ok) cand.erase(K), changed = true;
    }
  }

  // The report: every candidate with its verdict, shapes and sites.
  size_t nPass = 0, nAssume = 0, nFail = 0, nSelfLink = 0, nSelfDerived = 0, nCopies = 0, nUnmasked = 0;
  auto line = [&](const std::string &l) {
    CG_LOG("LinkWord: " << l << "\n");
    linkWordReport.push_back(l);
  };
  auto counts = [](const std::map<std::string, size_t> &m) {
    std::string s;
    for (auto &[k, n] : m) s += (s.empty() ? "" : ", ") + k + " " + std::to_string(n);
    return s;
  };
  for (const FieldKey &K : candidates) {
    const Field &Fd = fields[K];
    const bool pass = cand.count(K);
    cand.insert(K); // a failed field's own copies: show the shape that failed it
    std::map<std::string, size_t> st, ld;
    std::vector<std::string> fails, assumes;
    size_t namingFails = 0;
    size_t selfLink = 0, selfDerived = 0, copies = 0;
    for (const StoreInst *S : Fd.stores) {
      StoreEval E = evalStore(S, K);
      st[E.top]++;
      selfLink += E.selfLink, selfDerived += E.selfDerived, copies += E.copy;
      if (!E.ok) fails.push_back("store: " + E.why + " at " + siteOf(S)), namingFails += E.naming;
    }
    for (const LoadInst *L : Fd.loads) {
      LoadEval E = evalLoad(L);
      for (const std::string &c : E.classes) ld[c]++;
      for (const Instruction *U : E.unmasked) assumes.push_back(siteOf(U));
      if (!E.ok) fails.push_back("load: " + E.why + " at " + siteOf(E.at)), namingFails += E.naming;
    }
    if (!pass) cand.erase(K);
    std::string verdict = !pass ? "FAIL (" + std::to_string(fails.size()) + " sites)"
                          : assumes.empty() ? "PASS"
                                            : "PASS with " + std::to_string(assumes.size()) + " assumptions";
    if (!pass && fails.empty()) verdict = "FAIL (a copy or copy target failed)";
    else if (!pass && namingFails == fails.size())
      verdict = "FAIL on naming (" + std::to_string(fails.size()) + " sites through unnamed accesses)";
    line(keyName(K) + ": " + verdict + "; stores " + std::to_string(Fd.stores.size()) + " {" + counts(st) +
         "}; self-link " + std::to_string(selfLink) + ", self-derived " + std::to_string(selfDerived) + ", copies " +
         std::to_string(copies) + "; loads " + std::to_string(Fd.loads.size()) + " {" + counts(ld) + "}");
    linkWordVerdicts[keyName(K)] = {verdict, assumes};
    for (const std::string &a : assumes)
      line("  ASSUMPTION " + keyName(K) + ": the program relies on tag 0 at this read: " + a);
    for (const std::string &f : fails) line("  FAIL " + keyName(K) + ": " + f);
    if (pass) {
      linkWordFields.insert(K);
      (assumes.empty() ? nPass : nAssume)++;
      nSelfLink += selfLink, nSelfDerived += selfDerived, nCopies += copies, nUnmasked += assumes.size();
    } else {
      nFail++;
    }
  }

  // Pointer-typed fields that receive encoded words (XArray / radix tree
  // slots): shapes only, by the R1 addendum (b) clauses.
  size_t nEncoded = 0;
  for (auto &[K, Fd] : fields) {
    if (!Fd.isPtr || !Fd.encoded) continue;
    nEncoded++;
    std::map<std::string, size_t> st, ld;
    for (const StoreInst *S : Fd.stores) {
      const Value *V = S->getValueOperand();
      std::string c = encodedClass(V);
      if (const auto *L = dyn_cast<LoadInst>(V))
        if (auto it = fieldOf.find(L); it != fieldOf.end() && fields[it->second].encoded) c = "copy";
      st[c]++;
    }
    for (const LoadInst *L : Fd.loads) {
      std::set<std::string> cls;
      std::vector<const Value *> wl{L};
      std::set<const Value *> seen{L};
      while (!wl.empty()) {
        const Value *X = wl.back();
        wl.pop_back();
        for (const User *U : X->users()) {
          if (isa<PHINode>(U) || isa<SelectInst>(U) || isa<FreezeInst>(U)) {
            if (seen.insert(U).second) wl.push_back(U);
          } else if (isa<ICmpInst>(U)) {
            cls.insert("compare");
          } else if (const auto *G = dyn_cast<GetElementPtrInst>(U); G && G->getSourceElementType()->isIntegerTy(8) &&
                                                                      G->getNumIndices() == 1) {
            const auto *C = dyn_cast<ConstantInt>(G->idx_begin()->get());
            cls.insert(C && C->getSExtValue() < 0 && C->getSExtValue() > -8 ? "subtract-decode" : "untagged use");
          } else if (isa<PtrToIntInst>(U)) {
            std::vector<const Value *> iw{U};
            std::set<const Value *> iseen{U};
            while (!iw.empty()) {
              const Value *Y = iw.back();
              iw.pop_back();
              for (const User *V : Y->users()) {
                const auto *BO = dyn_cast<BinaryOperator>(V);
                const auto *C = BO ? dyn_cast<ConstantInt>(BO->getOperand(1)) : nullptr;
                if (isa<PHINode>(V) || isa<SelectInst>(V) || isa<ZExtInst>(V) || isa<TruncInst>(V)) {
                  if (iseen.insert(V).second) iw.push_back(V);
                } else if (BO && C && (BO->getOpcode() == Instruction::Add || BO->getOpcode() == Instruction::Sub))
                  cls.insert("subtract-decode");
                else if (BO && C && BO->getOpcode() == Instruction::And && (~C->getValue()).ult(8))
                  cls.insert("mask-decode");
                else if (BO && C && BO->getOpcode() == Instruction::And && C->getValue().ult(8))
                  cls.insert("low-bit test");
                else if (isa<ICmpInst>(V))
                  cls.insert("compare");
                else
                  cls.insert("integer use");
              }
            }
          } else {
            cls.insert("untagged use");
          }
        }
      }
      for (const std::string &c : cls) ld[c]++;
    }
    line(keyName(K) + ": encoded pointer field (shapes only); stores " + std::to_string(Fd.stores.size()) + " {" +
         counts(st) + "}; loads " + std::to_string(Fd.loads.size()) + " {" + counts(ld) + "}");
  }
  CG_LOG("LinkWord: " << candidates.size() << " integer fields read as pointers: " << nPass << " pass, " << nAssume
                      << " pass with assumptions (" << nUnmasked << " reads), " << nFail << " fail; " << nSelfLink
                      << " self-link stores, " << nSelfDerived << " self-derived, " << nCopies << " copies; "
                      << nEncoded << " pointer fields receive encoded words\n");
  size_t nUnnamed = 0;
  std::vector<std::pair<size_t, std::string>> top;
  for (auto &[F, n] : unnamedIn) nUnnamed += n, top.push_back({n, F->getName().str()});
  std::sort(top.rbegin(), top.rend());
  std::string tops;
  for (size_t i = 0; i < top.size() && i < 10; i++) tops += (i ? ", " : "") + top[i].second + " " + std::to_string(top[i].first);
  for (auto &[n, fn] : top) linkWordReport.push_back("  UNNAMED " + fn + " " + std::to_string(n)); // the full list: rule report only
  line("naming of offset-0 accesses with no struct GEP or TBAA: " + std::to_string(pointees.byDI) +
       " accesses by declared type, " + std::to_string(pointees.byDecl) + " by the object's IR type, " +
       std::to_string(pointees.bySibling) + " by sibling GEPs, " +
       std::to_string(pointees.byFormal) + " by formal provenance; " + std::to_string(nUnnamed) +
       " unnamed that would feed a link word, in " + std::to_string(unnamedIn.size()) + " functions" +
       (tops.empty() ? "" : " (" + tops + ")"));
  // The rule report carries the section only when the program has a link
  // word or an encoded pointer field (a rule the call graph then rests on);
  // the naming counts stay in the log.
  if (candidates.empty() && !nEncoded) linkWordReport.clear();
}
