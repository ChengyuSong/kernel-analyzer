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
// The object an access belongs to: the struct GEP's base (O0 reloads of one
// local slot are one object).
const Value *objKey(const Value *Addr) {
  const Value *B = Addr->stripPointerCasts();
  if (const GEPOperator *G = structGEP(Addr)) B = G->getPointerOperand()->stripPointerCasts();
  if (const auto *L = dyn_cast<LoadInst>(B))
    if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) return A;
  return B;
}
// The constants a value may be (casts, phis, selects, non-escaping O0
// slots), or false.
bool constSet(const Value *V, std::set<int64_t> &out, int depth = 0) {
  if (depth > 8) return false;
  while (const auto *C = dyn_cast<CastInst>(V)) V = C->getOperand(0);
  if (const auto *K = dyn_cast<ConstantInt>(V)) { out.insert(K->getSExtValue()); return true; }
  if (const auto *PN = dyn_cast<PHINode>(V)) {
    for (const Value *In : PN->incoming_values())
      if (!constSet(In, out, depth + 1)) return false;
    return true;
  }
  if (const auto *SI = dyn_cast<SelectInst>(V))
    return constSet(SI->getTrueValue(), out, depth + 1) && constSet(SI->getFalseValue(), out, depth + 1);
  if (const auto *L = dyn_cast<LoadInst>(V))
    if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
      bool any = false;
      for (const User *U : A->users()) {
        if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == A) {
          if (!constSet(S->getValueOperand(), out, depth + 1)) return false;
          any = true;
          continue;
        }
        if (const auto *L2 = dyn_cast<LoadInst>(U); L2 && L2->getPointerOperand() == A) continue;
        if (isa<DbgInfoIntrinsic>(U)) continue;
        return false; // the slot escapes
      }
      return any;
    }
  return false;
}
std::string locOf(const Instruction *I) {
  if (!I) return "?";
  std::string s = I->getFunction()->getName().str();
  if (const DILocation *L = I->getDebugLoc()) s += ":" + std::to_string(L->getLine());
  return s;
}
} // namespace

void CallGraphPass::computeTaggedFields() {
  taggedReport.clear();
  taggedPairs.clear();
  const auto t0 = std::chrono::steady_clock::now();
  if (!CFLCells || CFLUnionKeys != "tag") return;
  // A tag store: constants it sets, or a transform v -> (v & a) | o of the
  // tag it loaded from the same object, or unknown.
  struct TagStore {
    const StoreInst *I;
    const Value *obj;
    bool unknown = false, transform = false;
    std::set<int64_t> consts;
    int64_t a = -1, o = 0;
  };
  struct FAccess { const Instruction *I; const Value *obj; };
  using Field = std::pair<std::string, int64_t>; // (struct, offset)
  std::map<Field, std::vector<FAccess>> fStores, fLoads;
  std::map<Field, std::vector<TagStore>> dStores;
  auto analyzeTag = [&](const StoreInst *S, const Value *obj, const Field &D, TagStore &T) {
    const Value *V = S->getValueOperand();
    if (constSet(V, T.consts)) return;
    T.consts.clear();
    int64_t a = -1, o = 0;
    for (int d = 0; d < 8; d++) {
      while (const auto *C = dyn_cast<CastInst>(V)) V = C->getOperand(0);
      if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
        const auto *K = dyn_cast<ConstantInt>(BO->getOperand(1));
        if (!K) K = dyn_cast<ConstantInt>(BO->getOperand(0));
        const Value *X = K == BO->getOperand(1) ? BO->getOperand(0) : BO->getOperand(1);
        if (K && BO->getOpcode() == Instruction::Or) { o |= K->getSExtValue(); V = X; continue; }
        if (K && BO->getOpcode() == Instruction::And) {
          a &= K->getSExtValue();
          o &= K->getSExtValue();
          V = X;
          continue;
        }
      }
      if (const auto *L = dyn_cast<LoadInst>(V)) {
        StructType *S2 = nullptr;
        int64_t off2 = 0;
        if (accessSlot(L, L->getPointerOperand(), L->getModule()->getDataLayout(), S2, off2) && S2 &&
            S2->hasName() && stripStructNameSuffix(S2->getName()) == D.first && off2 == D.second &&
            objKey(L->getPointerOperand()) == obj) {
          T.transform = true;
          T.a = a;
          T.o = o;
          return;
        }
      }
      break;
    }
    T.unknown = true;
  };
  // ---- scan ----
  // The certificate a tag needs: every write to it named. Unnamed integer
  // stores (no struct or TBAA name, not a local slot) by width, and memset
  // fill bytes (a constant fill is a constant retag: the byte pattern).
  std::set<unsigned> unnamedWidths;
  using Field0 = std::pair<std::string, int64_t>;
  std::map<Field0, std::string> escapedAt; // fields whose address escapes
  std::map<unsigned, std::string> unnamedAt;
  std::set<int64_t> memsetFills;
  bool memsetUnknown = false;
  std::string memsetUnknownAt;
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        if (const auto *MS = dyn_cast<MemSetInst>(&I)) {
          if (const auto *K = dyn_cast<ConstantInt>(MS->getValue())) memsetFills.insert(K->getZExtValue() & 0xff);
          else if (!memsetUnknown) { memsetUnknown = true; memsetUnknownAt = locOf(&I); }
          continue;
        }
        // An integer store through byte-offset arithmetic with no struct
        // or TBAA name (the -O3 field idiom) may write any field.
        if (const auto *SI = dyn_cast<StoreInst>(&I); SI && SI->getValueOperand()->getType()->isIntegerTy()) {
          StructType *S0 = nullptr;
          int64_t o0 = 0;
          const auto *BG = dyn_cast<GEPOperator>(SI->getPointerOperand()->stripPointerCasts());
          if (BG && BG->getSourceElementType()->isIntegerTy(8) &&
              !(accessSlot(SI, SI->getPointerOperand(), DL, S0, o0) && S0 && S0->hasName())) {
            const unsigned w = SI->getValueOperand()->getType()->getIntegerBitWidth();
            if (unnamedWidths.insert(w).second) unnamedAt[w] = locOf(SI);
          }
        }
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
        const Value *obj = objKey(Addr);
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
      it->second.push_back({Br, dl, stripStructNameSuffix(S2->getName()).str(), o2, objKey(dl->getPointerOperand())});
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
      struct Writer { const Instruction *I; std::set<int64_t> tags; bool unknown = false; };
      std::vector<Writer> writers;
      std::vector<const TagStore *> retags;
      bool nonConstRetag = false;
      for (const TagStore &t : ds)
        if (!coWriting.count({t.I->getFunction(), t.obj})) {
          retags.push_back(&t);
          nonConstRetag |= t.unknown;
        }
      for (const FAccess &w : fs) {
        Writer W{w.I};
        bool co = false;
        for (const TagStore &t : ds)
          if (t.I->getFunction() == w.I->getFunction() && t.obj == w.obj) {
            co = true;
            if (t.unknown || t.transform) W.unknown = true;
            W.tags.insert(t.consts.begin(), t.consts.end());
          }
        if (!co) W.unknown = true;
        writers.push_back(std::move(W));
      }
      // The tag must be certified: no unnamed store of its width anywhere.
      unsigned dWidth = 0;
      for (const TagStore &t : ds) dWidth = t.I->getValueOperand()->getType()->getIntegerBitWidth();
      if (unnamedWidths.count(dWidth) || escapedAt.count(Df)) {
        pairsUncertified++;
        if (fs.size() >= 10)
          taggedReport.push_back("UNKEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                                 std::to_string(dOff) + ": tag not certified (" +
                                 (escapedAt.count(Df) ? "its address escapes at " + escapedAt[Df]
                                                      : "a byte-offset i" + std::to_string(dWidth) +
                                                            " store, e.g. " + unnamedAt[dWidth]) + ")");
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
      // Tags reachable from each writer through the retags.
      std::set<int64_t> sets;
      std::vector<std::pair<int64_t, int64_t>> xforms;
      for (const TagStore *t : retags) {
        if (t->transform) xforms.push_back({t->a, t->o});
        else sets.insert(t->consts.begin(), t->consts.end());
      }
      for (int64_t b : memsetFills) { // the fill byte repeated over the tag
        int64_t v = 0;
        for (unsigned k = 0; k < dWidth / 8; k++) v = (v << 8) | b;
        sets.insert(v);
      }
      auto reach = [&](const std::set<int64_t> &from, bool &all) {
        std::set<int64_t> R = from;
        R.insert(sets.begin(), sets.end());
        std::vector<int64_t> work(R.begin(), R.end());
        while (!work.empty() && !all) {
          const int64_t v = work.back();
          work.pop_back();
          for (auto [a, o] : xforms) {
            const int64_t w = (v & a) | o;
            if (R.insert(w).second) work.push_back(w);
            if (R.size() > 4096) all = true;
          }
        }
        return R;
      };
      std::vector<std::set<int64_t>> wTags(writers.size());
      std::vector<bool> wAll(writers.size(), false);
      for (size_t i = 0; i < writers.size(); i++) {
        if (writers[i].unknown) { wAll[i] = true; continue; }
        bool all = false;
        wTags[i] = reach(writers[i].tags, all);
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
            const unsigned bw = C->getType()->getIntegerBitWidth();
            if (isa<TruncInst>(C) && bw < 64) return *a & ((int64_t(1) << bw) - 1);
            return a;
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
      if (keyed.empty()) continue;
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
      taggedReport.push_back("KEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                               std::to_string(dOff) + ": " + std::to_string(writers.size()) + " writers, " +
                               std::to_string(pairReadsKeyed) + " reads keyed, " +
                               std::to_string(retags.size()) + " retags");
    }
  }
  CG_LOG("TaggedFields: " << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count()
         << " s; " << pairsKeyed << " pairs keyed (" << writersTagged << " tagged writers, "
         << writersUntagged << " untagged: no co-written tag in the writer's function); reads: "
         << readsKeyed << " keyed, " << readsNoTest << " with no dominating test, " << readsAll
         << " admitting every writer; " << pairsNonConst << " pairs unkeyed by a non-constant retag, "
         << pairsUncertified << " by an uncertified tag (unnamed store of its width)\n");
  if (VerboseLevel >= 2)
    for (const std::string &l : taggedReport) CG_LOG("TaggedFields:   " << l << "\n");
  taggedCounts = {pairsKeyed, writersTagged, writersUntagged, readsKeyed, readsNoTest, readsAll, pairsNonConst};
}
