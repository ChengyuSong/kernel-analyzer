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
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Support/KnownBits.h>
#include <chrono>
#include <deque>
#include <unordered_map>

using namespace llvm;

namespace {
// The struct GEP an embedded struct's address is: a constant GEP from
// element 0 whose result is the inner access's struct (plan 3.54 (a)).
static const GEPOperator *embeddingGEP(const Value *A, const Type *Inner) {
  const GEPOperator *O = structGEP(A);
  if (!O || !O->hasAllConstantIndices() || O->getResultElementType() != Inner) return nullptr;
  const auto *I0 = O->getNumIndices() ? dyn_cast<ConstantInt>(*O->idx_begin()) : nullptr;
  const auto *OS = dyn_cast<StructType>(O->getSourceElementType());
  return I0 && I0->isZero() && OS && OS->hasName() ? O : nullptr;
}
// The structs whose fields are only ever accessed inside one embedding
// (struct name -> outer struct name, its offset there): computed per run
// (computeTaggedFields). A struct also used on its own (z_stream_s, a
// standalone png_unknown_chunk_t) keeps its own field names, so one field
// never has two names.
static std::map<std::string, std::pair<std::string, int64_t>> g_embedOnly;
static const DataLayout &dataLayoutOf(const Value *V) {
  V = V->stripPointerCasts();
  if (const auto *I = dyn_cast<Instruction>(V)) return I->getModule()->getDataLayout();
  if (const auto *A = dyn_cast<Argument>(V)) return A->getParent()->getParent()->getDataLayout();
  if (const auto *GV = dyn_cast<GlobalValue>(V)) return GV->getParent()->getDataLayout();
  if (const auto *CE = dyn_cast<GEPOperator>(V)) return dataLayoutOf(CE->getPointerOperand());
  llvm_unreachable("an access address with no module");
}
// One composition step: the embedding of the inner struct S at A, when S
// is only ever accessed there.
static const GEPOperator *composeStep(const Value *A, const Type *S, const DataLayout &DL, int64_t &by) {
  const GEPOperator *O = embeddingGEP(A, S);
  if (!O) return nullptr;
  const auto *ST = dyn_cast<StructType>(S);
  if (!ST || !ST->hasName()) return nullptr;
  auto it = g_embedOnly.find(stripStructNameSuffix(ST->getName()).str());
  APInt Ap(64, 0);
  if (it == g_embedOnly.end() || !O->accumulateConstantOffset(DL, Ap) ||
      it->second != std::make_pair(stripStructNameSuffix(O->getSourceElementType()->getStructName()).str(),
                                   Ap.getSExtValue()))
    return nullptr;
  by = Ap.getSExtValue();
  return O;
}
// accessSlot, composed outward (plan 3.54 (a)): a field of a struct
// embedded at a constant offset in another (tif->tif_tagmethods.vsetfield,
// two GEPs at -O0) is named by its offset in the outermost struct, as one
// GEP or the struct-path TBAA tag (-O3) names it; only through structs
// accessed in no other way (g_embedOnly).
static bool composedSlot(const Instruction *I, const Value *Addr, const DataLayout &DL, StructType *&S,
                         int64_t &off) {
  if (!accessSlot(I, Addr, DL, S, off)) return false;
  const GEPOperator *G = structGEP(Addr);
  if (!G || G->getSourceElementType() != S) return true; // named by its TBAA tag
  int64_t by = 0;
  for (const GEPOperator *O = composeStep(G->getPointerOperand(), S, DL, by); O;
       O = composeStep(O->getPointerOperand(), S, DL, by)) {
    S = cast<StructType>(O->getSourceElementType());
    off += by;
  }
  return true;
}
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
  // A store into a named field of a struct (a struct GEP or struct-path
  // TBAA naming it), with A a pointer-typed slot: by rule (b) the store's
  // object is labeled as the struct and the slot as a pointer, so it
  // cannot write the slot (a label disagreement there is a (b) row).
  static bool fieldStoreOnly(const Instruction *I, const AllocaInst *A) {
    const auto *St = dyn_cast<StoreInst>(I);
    if (!St || St->isVolatile() || !A->getAllocatedType()->isPointerTy()) return false;
    StructType *S = nullptr;
    int64_t off = 0;
    return composedSlot(St, St->getPointerOperand(), St->getModule()->getDataLayout(), S, off) && S && S->hasName() &&
           St->getPointerOperand()->stripPointerCasts() != A;
  }
  // objSize: the accessed struct's size (a -O3 byte offset inside it is a
  // field of the base; past it, another element).
  // Accesses whose struct GEP is an anonymous struct's: their object is
  // the enclosing named struct's base (counted, by address).
  std::set<const Value *> viaAnon;
  const Value *of(const Value *Addr, int64_t objSize = 0, int depth = 0) {
    const Value *B = Addr->stripPointerCasts();
    // A field of an anonymous struct is named by the enclosing named struct
    // (accessSlot), so its object is that struct's (the same walk,
    // enclosingNamed); then outward as below.
    bool anonDone = false;
    if (const GEPOperator *G = structGEP(Addr); G && isAnonStruct(dyn_cast<StructType>(G->getSourceElementType()))) {
      StructType *NS = nullptr;
      int64_t noff = 0;
      const Value *NB = nullptr;
      if (enclosingNamed(Addr, dataLayoutOf(Addr), NS, noff, &NB) && NB) {
        viaAnon.insert(Addr);
        anonDone = true;
        B = NB->stripPointerCasts();
        int64_t by = 0;
        const DataLayout &DL = dataLayoutOf(Addr);
        for (const Type *In = NS; const GEPOperator *O = composeStep(B, In, DL, by);) {
          In = O->getSourceElementType();
          B = O->getPointerOperand()->stripPointerCasts();
        }
      }
    }
    // A field of the object (constant indices from element 0); another
    // element of an array is another object.
    if (const GEPOperator *G = anonDone ? nullptr : structGEP(Addr)) {
      const auto *I0 = G->getNumIndices() ? dyn_cast<ConstantInt>(*G->idx_begin()) : nullptr;
      if (G->hasAllConstantIndices() && I0) {
        const bool bytes = G->getSourceElementType()->isIntegerTy(8) && G->getNumIndices() == 1;
        if (bytes ? (I0->getSExtValue() >= 0 && I0->getSExtValue() < objSize) : I0->isZero()) {
          B = G->getPointerOperand()->stripPointerCasts();
          // A field of an embedded struct: the object is the outermost
          // struct's (plan 3.54 (a)).
          if (!bytes) {
            int64_t by = 0;
            const DataLayout &DL = dataLayoutOf(Addr);
            for (const Type *In = G->getSourceElementType(); const GEPOperator *O = composeStep(B, In, DL, by);) {
              In = O->getSourceElementType();
              B = O->getPointerOperand()->stripPointerCasts();
            }
          }
        }
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
            else if (fieldStoreOnly(I, A))
              continue; // a store into a named struct field does not write a pointer slot (rule (b))
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
  widenedTagsOf.clear();
  size_t stepPosByTag = 0, stepPosUnnamed = 0, stepAddrUnnamed = 0, stepPosConst = 0, stepPosPast = 0;
  size_t knownBitsTerms = 0; // values evaluated by their known bits alone
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
  taggedOutsideEntries.clear();
  taggedOutsidePre.clear();
  taggedUntested.clear();
  taggedInPlace.clear();
  taggedAdmitVia.clear();
  taggedDisagreeRows.clear();
  p3Excluded.clear();
  p3Reads = 0;
  taggedParamChannels.clear();
  taggedParamValueChannels.clear();
  taggedAccessSets.clear();
  taggedWatches.clear();
  taggedEntryFormals.clear();
  taggedEntryReads.clear();
  taggedEntryTermKeys.clear();
  // Plan 3.54 (a): the structs only ever accessed inside one embedding
  // (every field GEP of the struct steps from the same outer struct's
  // constant GEP at the same offset; no struct-path TBAA access names it
  // as the base). Only their fields are named by the outer struct.
  g_embedOnly.clear();
  {
    std::map<std::string, std::set<std::pair<std::string, int64_t>>> targets;
    std::set<std::string> standalone;
    auto classify = [&](const GEPOperator *G, const DataLayout &DL) {
      const auto *T = dyn_cast<StructType>(G->getSourceElementType());
      // An anonymous struct's fields are named by its encloser already
      // (accessSlot); a struct inside one keeps its own name.
      if (!T || !T->hasName() || isAnonStruct(T)) return;
      const std::string tn = stripStructNameSuffix(T->getName()).str();
      const GEPOperator *O = embeddingGEP(G->getPointerOperand(), T);
      APInt Ap(64, 0);
      if (O && !isAnonStruct(dyn_cast<StructType>(O->getSourceElementType())) &&
          O->accumulateConstantOffset(DL, Ap))
        targets[tn].insert({stripStructNameSuffix(O->getSourceElementType()->getStructName()).str(), Ap.getSExtValue()});
      else
        standalone.insert(tn);
    };
    for (auto &[M, _] : Ctx->Modules) {
      const DataLayout &DL = M->getDataLayout();
      for (Function &F : *M)
        for (Instruction &I : instructions(F)) {
          if (const auto *G = dyn_cast<GetElementPtrInst>(&I)) {
            classify(cast<GEPOperator>(G), DL);
            continue;
          }
          const Value *Addr = nullptr;
          if (const auto *L = dyn_cast<LoadInst>(&I)) Addr = L->getPointerOperand();
          else if (const auto *St = dyn_cast<StoreInst>(&I)) Addr = St->getPointerOperand();
          if (!Addr) continue;
          if (const GEPOperator *G = structGEP(Addr)) {
            if (!isa<Instruction>(G)) classify(G, DL); // a constant GEP of a global
            continue;
          }
          StructType *S = nullptr;
          int64_t off = 0;
          if (accessSlot(&I, Addr, DL, S, off) && S && S->hasName()) // named by its TBAA tag alone
            standalone.insert(stripStructNameSuffix(S->getName()).str());
        }
    }
    for (auto &[tn, ts] : targets)
      if (ts.size() == 1 && !standalone.count(tn)) g_embedOnly[tn] = *ts.begin();
  }
  taggedEntryReadList.clear();
  taggedEntryReadIdx.clear();
  taggedEntryChannels.clear();
  taggedEntrySites.clear();
  taggedEntryRows.clear();
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
    // The load the symbolic tag was read at (rule iii: it is the tag that
    // held there, the current one only if nothing writes it in between);
    // ldMany: read at several loads.
    const Instruction *ld = nullptr;
    bool ldMany = false;
    // Bits taken from another object's tag of the same field: they are the
    // projection of some value the field holds (U), not free (x-mask).
    int64_t xm = 0;
    // An image of a tag value taken at a load, on the paths through a test
    // of that value: only source tags the test admits (index into the
    // filter table; -1: none).
    int flt = -1;
  };
  // Function-pointer tags (plan 3.51 ruling a): a pointer-valued tag holds
  // NULL (0), the special constant -1 (sqlite's SQLITE_TRANSIENT), a small
  // integer cast to a pointer, or a function, each a distinct constant.
  std::map<const Function *, int64_t> fnId;
  std::vector<const Function *> fnById;
  constexpr int64_t kFnBase = int64_t(1) << 20, kAllOnes = (int64_t(1) << 31) - 1; // all below 2^31
  auto ptrConst = [&](const Value *V) -> std::optional<int64_t> {
    V = V->stripPointerCasts();
    if (const auto *GA = dyn_cast<GlobalAlias>(V)) V = GA->getAliasee()->stripPointerCasts();
    if (isa<ConstantPointerNull>(V)) return 0;
    if (const auto *F = dyn_cast<Function>(V)) {
      auto [it, ins] = fnId.try_emplace(F, kFnBase + (int64_t)fnById.size());
      if (ins) fnById.push_back(F);
      assert(it->second < kAllOnes - 2 && "function-pointer tag encoding exhausted");
      return it->second;
    }
    if (const auto *CE = dyn_cast<ConstantExpr>(V); CE && CE->getOpcode() == Instruction::IntToPtr)
      if (const auto *K = dyn_cast<ConstantInt>(CE->getOperand(0)); K && K->getBitWidth() <= 64) {
        const int64_t c = K->getSExtValue();
        if (c == -1) return kAllOnes;
        if (c >= 0 && c < kFnBase) return c;
      }
    return std::nullopt;
  };
  auto constOf = [&](const Value *V) -> std::optional<int64_t> {
    if (const auto *K = dyn_cast<ConstantInt>(V)) {
      if (K->getBitWidth() > 64) return std::nullopt; // not a term (u128)
      return K->getSExtValue();
    }
    if (V->getType()->isPointerTy() && isa<Constant>(V)) return ptrConst(V);
    return std::nullopt;
  };
  auto widthOf = [](Type *T) -> unsigned {
    if (const auto *VT = dyn_cast<FixedVectorType>(T)) T = VT->getElementType(); // a lane (plan 3.54)
    return T->isPointerTy() ? 64u : T->getIntegerBitWidth();
  };
  // The outside domain of a function pointer (ruling a.2 and Q1, the 3.48
  // exposure question applied to function values): code outside the
  // corpus can name only NULL, -1, its own functions (one value,
  // kOutsideFn, and the corpus's bodiless ones), exported functions in a
  // partial corpus, and functions whose address reaches it. Pre-solve, an
  // address reaches the outside unless every use of it is a direct call, a
  // comparison, or a store into a struct field (the outside performs no
  // field access on what it is handed: the printed premise); through
  // casts, phis and selects. The solver computes the exact set and reports
  // a function in it that this set excluded.
  const int64_t kOutsideFn = kAllOnes - 2;
  auto addrMayReachOutside = [&](const Function &G) {
    std::vector<const Value *> work{&G};
    std::set<const Value *> seen;
    while (!work.empty()) {
      const Value *V = work.back();
      work.pop_back();
      if (!seen.insert(V).second) continue;
      for (const User *U : V->users()) {
        if (const auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand() == V) continue;
        if (isa<ICmpInst>(U)) continue;
        if (const auto *St = dyn_cast<StoreInst>(U); St && St->getValueOperand() == V) {
          StructType *S2 = nullptr;
          int64_t o2 = 0;
          if (composedSlot(St, St->getPointerOperand(), St->getModule()->getDataLayout(), S2, o2) && S2 &&
              S2->hasName())
            continue;
          return true;
        }
        if (isa<PHINode>(U) || isa<SelectInst>(U) || isa<CastInst>(U) ||
            (isa<ConstantExpr>(U) && cast<ConstantExpr>(U)->isCast())) {
          work.push_back(U);
          continue;
        }
        if (isa<BlockAddress>(U) || isa<DSOLocalEquivalent>(U)) continue;
        return true; // an initializer, an argument, a store elsewhere, ...
      }
    }
    return false;
  };
  for (auto &[M, _] : Ctx->Modules)
    for (Function &G : *M)
      if (!G.isDeclaration() && addrMayReachOutside(G)) taggedOutsidePre.insert(&G);
  std::vector<int64_t> outsideDomain;
  auto outsideDom = [&]() -> const std::vector<int64_t> & {
    if (!outsideDomain.empty()) return outsideDomain;
    outsideDomain = {0, kAllOnes, kOutsideFn};
    for (auto &[M, _] : Ctx->Modules)
      for (Function &G : *M)
        if (G.isDeclaration() ? !G.isIntrinsic() && G.hasAddressTaken()
                              : taggedOutsidePre.count(&G) || (!CFLWholeProgram && !G.hasLocalLinkage()))
          outsideDomain.push_back(*ptrConst(&G));
    return outsideDomain;
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
  std::map<Field, std::vector<FAccess>> vecLanes; // vector-of-pointer stores, per lane's field
  std::map<Field, std::vector<TagStore>> dStores;
  std::set<Field> fnFields;
  std::map<Field, std::vector<FAccess>> uStores, uLoads; // union members' non-pointer accesses
  size_t unionFields = 0;
  // Is the member at byte off of ST (nested at that offset) a union?
  auto unionAt = [](StructType *ST, int64_t off, const DataLayout &DL) {
    Type *T = ST;
    for (int depth = 0; depth < 16; depth++) {
      auto *S2 = dyn_cast<StructType>(T);
      if (!S2 || S2->isOpaque()) return false;
      if (depth && S2->hasName() && S2->getName().starts_with("union.")) return true;
      const StructLayout *SL = DL.getStructLayout(S2);
      if (off < 0 || (uint64_t)off >= SL->getSizeInBytes()) return false;
      const unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      if (off) return false; // inside a member, not at its start
      T = S2->getElementType(i);
    }
    return false;
  };
  // Every value a term set may take (a symbolic tag's bits free).
  auto concretize = [](const std::vector<Term> &ts, std::set<int64_t> &out) {
    for (const Term &t : ts) {
      const uint64_t fr = (uint64_t)((t.src == 'c' ? 0 : t.a) | t.m | t.xm) & ~(uint64_t)t.f;
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
  // The side of a combination that cannot be paired: another object's tag
  // ('x') keeps its bits as an x-mask (a value of the field, U); this
  // object's tag ('s') becomes free.
  auto freeOf = [](const Term &t) {
    Term r{'c', 0, t.f, 0};
    if (t.src == 'x') {
      r.xm = (t.a | t.xm) & ~t.f;
      r.m = t.m & ~t.f & ~r.xm;
    } else
      r.m = ((t.src == 'c' ? 0 : t.a) | t.m | t.xm) & ~t.f;
    return r;
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
      if (!ev1(V, depth, mine)) {
        // Not evaluable by its operands: its bits LLVM knows (plan 3.51 (3),
        // Fable 2026-10-16), the known ones fixed and the rest free, when
        // that is any knowledge at all. elflink.c:5250's
        // `h->root.non_ir_ref_dynamic = x` inserts `(x & 1) << 9`: bit 9
        // free, the others zero, so the store keeps the old load's bits
        // over type:8 (a write changing other bits only).
        const auto *IT = dyn_cast<IntegerType>(V->getType());
        const auto *VI = dyn_cast<Instruction>(V);
        if (!IT || IT->getBitWidth() > 64 || !VI) return false; // memo stays empty: failed
        const KnownBits K = computeKnownBits(V, VI->getModule()->getDataLayout());
        if (K.Zero.isZero() && K.One.isZero()) return false;
        const unsigned w = IT->getBitWidth();
        const int64_t wm = w >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << w) - 1);
        const int64_t one = (int64_t)K.One.getZExtValue(), zero = (int64_t)K.Zero.getZExtValue();
        mine.push_back({'c', 0, one, wm & ~(one | zero)});
        knownBitsTerms++;
      }
      memo[V] = mine;
      out.insert(out.end(), mine.begin(), mine.end());
      return out.size() <= kMaxTerms;
    };
    ev1 = [&](const Value *V, int depth, std::vector<Term> &out) -> bool {
      if (depth > 24 || out.size() > kMaxTerms) return false;
      // An integer wider than 64 bits (kernel u128 arithmetic) is not a
      // term: the store is not evaluable, its pair refused or unkeyed and
      // counted, as for any such store.
      if (V->getType()->isIntegerTy() && V->getType()->getIntegerBitWidth() > 64) return false;
      if (auto c = constOf(V)) {
        out.push_back({'c', 0, *c, 0});
        return true;
      }
      if (isa<Constant>(V) && V->getType()->isPointerTy()) return false; // another pointer constant
      auto mask = [](unsigned bits) { return bits >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << bits) - 1); };
      if (const auto *C = dyn_cast<CastInst>(V)) {
        if (isa<PtrToIntInst>(C) || isa<IntToPtrInst>(C) ||
            (C->getType()->isPointerTy() && C->getOperand(0)->getType()->isPointerTy()))
          return ev(C->getOperand(0), depth + 1, out); // 64-bit values, unchanged
        if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) return false;
        std::vector<Term> in;
        if (!ev(C->getOperand(0), depth + 1, in)) return false;
        const unsigned sb = C->getOperand(0)->getType()->getIntegerBitWidth(), db = C->getType()->getIntegerBitWidth();
        if (isa<TruncInst>(C) || isa<ZExtInst>(C)) {
          const int64_t m = mask(isa<TruncInst>(C) ? db : sb);
          for (Term t : in) out.push_back({t.src, t.a & m, t.f & m, t.m & m, t.who, t.ld, t.ldMany, t.xm & m});
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
          for (const Term &t : ts) if ((t.src != 'c' && t.a != 0) || t.m != 0 || t.xm != 0) return false;
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
            // Per bit: known zero, one (f), the tag (a), U's projection
            // (xm), or free (m). Tag against U, or U against U (two
            // objects), is free.
            const int64_t Zp = ~(p.a | p.f | p.m | p.xm), Zq = ~(q.a | q.f | q.m | q.xm);
            int64_t Z;
            if (op == Instruction::Or) {
              r.f = p.f | q.f;
              Z = Zp & Zq;
              r.a = ((p.a & (Zq | q.a)) | (q.a & Zp)) & ~r.f;
              r.xm = ((p.xm & Zq) | (q.xm & Zp)) & ~r.f;
            } else {
              r.f = p.f & q.f;
              Z = Zp | Zq;
              r.a = (p.a & (q.f | q.a)) | (q.a & p.f);
              r.xm = (p.xm & q.f) | (q.xm & p.f);
            }
            r.m = ~Z & ~r.f & ~r.a & ~r.xm;
            r.src = r.a ? src : 'c';
            r.who = p.a ? p.who : q.who;
            r.ld = p.a ? p.ld : q.ld;
            r.ldMany = p.ldMany || q.ldMany || (p.a && q.a && p.ld != q.ld);
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
        // An element of a constant integer table (sqlite3's
        // `flags = aFlag[p1 & 1]`): one of its elements.
        if (const auto *G = dyn_cast<GEPOperator>(L->getPointerOperand()); G && L->getType()->isIntegerTy())
          if (const auto *GV = dyn_cast<GlobalVariable>(G->getPointerOperand());
              GV && GV->isConstant() && GV->hasDefinitiveInitializer() && G->getNumIndices() == 2 &&
              G->getSourceElementType() == GV->getValueType())
            if (const auto *CD = dyn_cast<ConstantDataSequential>(GV->getInitializer());
                CD && CD->getElementType() == L->getType() && CD->getNumElements() <= 256) {
              for (unsigned k = 0; k < CD->getNumElements(); k++)
                out.push_back({'c', 0, (int64_t)CD->getElementAsInteger(k), 0});
              return true;
            }
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
        if ((L->getType()->isIntegerTy() || L->getType()->isPointerTy()) &&
            composedSlot(L, L->getPointerOperand(), L->getModule()->getDataLayout(), S2, off2) && S2 &&
            S2->hasName() && stripStructNameSuffix(S2->getName()) == D.first && off2 == D.second) {
          const Value *who = objKey(L, L->getPointerOperand(), S2);
          out.push_back({sameObj(who, obj, L) ? 's' : 'x', -1, 0, 0, who, L});
          return true;
        }
        return false;
      }
      if (const auto *Ar = dyn_cast<Argument>(V)) {
        const Function *F = Ar->getParent();
        // A function the outside may call (its address may reach the
        // outside, or exported in a partial corpus): a pointer parameter
        // holds its call sites' arguments or the outside domain; the
        // solver checks that no indirect call in the corpus reaches it.
        const bool fromOutside = (taggedOutsidePre.count(F) || (!CFLWholeProgram && !F->hasLocalLinkage())) &&
                                 Ar->getType()->isPointerTy();
        if (!fromOutside && (!CFLWholeProgram || F->hasAddressTaken())) return false;
        size_t sites = 0;
        const bool ok = fixpoint(Ar, [&](std::vector<Term> &acc) {
          sites = 0;
          for (const User *U : F->users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (!CB || CB->getCalledOperand() != F) {
              if (fromOutside) continue; // the address taken: the outside's calls
              return false;
            }
            sites++;
            if (!ev(CB->getArgOperand(Ar->getArgNo()), depth + 1, acc)) return false;
          }
          if (fromOutside)
            for (int64_t v : outsideDom()) acc.push_back({'c', 0, v, 0});
          return true;
        }, out);
        if (ok && fromOutside) taggedOutsideEntries[F].insert(Ar->getArgNo());
        if (ok && (sites || fromOutside))
          T.via.push_back(F->getName().str() + " arg" + std::to_string(Ar->getArgNo()) + " from " +
                          std::to_string(sites) + " call sites" + (fromOutside ? " and the outside domain" : ""));
        return ok;
      }
      return false;
    };
    std::vector<Term> ts;
    if (!ev(S->getValueOperand(), 0, ts)) { T.unknown = true; return; }
    // The store keeps the tag's width.
    const unsigned w = widthOf(S->getValueOperand()->getType());
    const int64_t m = w >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << w) - 1);
    std::set<std::tuple<char, int64_t, int64_t, int64_t, int64_t>> seen;
    for (const Term &t : ts) {
      const bool c = t.src == 'c' || (t.a & m) == 0;
      const int64_t f = t.f & m;
      const Term n{c ? 'c' : t.src, c ? 0 : t.a & m & ~f, f, t.m & m & ~f, t.who, t.ld, t.ldMany, t.xm & m & ~f};
      if (seen.insert({n.src, n.a, n.f, n.m, n.xm}).second) T.terms.push_back(n);
      else if (n.src == 's') // the same map read at another load: both must hold
        for (Term &e : T.terms)
          if (e.src == 's' && e.a == n.a && e.f == n.f && e.m == n.m && e.ld != n.ld) e.ldMany = true;
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
  struct EscRange { int64_t lo, hi; std::string at; };
  std::map<std::string, std::vector<EscRange>> escapedAt; // byte ranges whose address escapes, by struct
  auto escapedOver = [&](const std::string &S, int64_t lo, int64_t hi) -> const std::string * {
    if (auto it = escapedAt.find(S); it != escapedAt.end())
      for (const EscRange &e : it->second)
        if (e.lo < hi && lo < e.hi) return &e.at;
    return nullptr;
  };
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
    if (composedSlot(I, Addr, DL, S0, o0) && S0 && S0->hasName()) {
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
        // An embedded struct's address used only as the base of its own
        // fields' constant GEPs is not an escape: those GEPs are checked
        // themselves, under their composed names (plan 3.54 (a)). Any other
        // use escapes every byte of it, by the test a field's own address
        // gets: a byte is certified or not whatever GEP spells its address.
        if (const GEPOperator *FG = dyn_cast<GEPOperator>(&I); FG && structGEP(&I) == FG) {
          StructType *S0 = nullptr;
          int64_t o0 = 0;
          const bool named0 = composedSlot(&I, &I, DL, S0, o0) && S0 && S0->hasName();
          if (!named0 && isa<StructType>(FG->getSourceElementType()) && FG->getNumIndices() &&
              !(isa<ConstantInt>(*FG->idx_begin()) && cast<ConstantInt>(*FG->idx_begin())->isZero()))
            stepAddrUnnamed++; // a byte step's address: no field of a name escapes by it
          if (named0) {
            // Through pointer-to-pointer casts (the typed-pointer upgrade
            // leaves `bitcast ptr %f to ptr` before a store at -O0): the
            // address is still used only as a load or store address.
            std::vector<const Value *> work{&I};
            bool esc = false;
            while (!work.empty() && !esc) {
              const Value *A = work.back();
              work.pop_back();
              for (const User *U : A->users()) {
                if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == A) continue;
                if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand() == A) continue;
                if (isa<DbgInfoIntrinsic>(U)) continue;
                if (const auto *C = dyn_cast<BitCastInst>(U); C && C->getType()->isPointerTy()) {
                  work.push_back(C);
                  continue;
                }
                if (const auto *IG = dyn_cast<GetElementPtrInst>(U);
                    IG && IG->getPointerOperand() == A && IG->hasAllConstantIndices() &&
                    IG->getSourceElementType() == FG->getResultElementType() &&
                    FG->getResultElementType()->isStructTy())
                  if (const auto *I0 = dyn_cast<ConstantInt>(*IG->idx_begin()); I0 && I0->isZero())
                    continue; // a field of the embedded struct: checked as its own GEP
                esc = true;
                break;
              }
            }
            if (esc) { // every byte of it: an embedded struct's escape is its fields' (plan 3.54 (a))
              Type *RT = FG->getResultElementType();
              const int64_t sz = RT->isSized() ? (int64_t)DL.getTypeAllocSize(RT) : 1;
              escapedAt[stripStructNameSuffix(S0->getName()).str()].push_back(
                  {o0, o0 + std::max<int64_t>(sz, 1), locOf(&I)});
            }
          }
        }
        const Value *Addr = nullptr;
        Type *T = nullptr;
        if (const auto *L = dyn_cast<LoadInst>(&I)) Addr = L->getPointerOperand(), T = L->getType();
        else if (const auto *S = dyn_cast<StoreInst>(&I)) Addr = S->getPointerOperand(), T = S->getValueOperand()->getType();
        else continue;
        StructType *ST = nullptr;
        int64_t off = 0;
        // A struct GEP whose leading index is not 0 is a byte step: named
        // only by its TBAA tag (accessSlot), else unnamed; counted.
        const GEPOperator *SG = structGEP(Addr);
        const bool step = SG && isa<StructType>(SG->getSourceElementType()) && SG->getNumIndices() &&
                          !(isa<ConstantInt>(*SG->idx_begin()) && cast<ConstantInt>(*SG->idx_begin())->isZero());
        const bool named = composedSlot(&I, Addr, DL, ST, off) && ST && ST->hasName();
        if (step) {
          (named ? stepPosByTag : stepPosUnnamed)++;
          // Past the layout of the struct the step is written in (what the
          // GEP alone used to name, S+off with off outside S).
          APInt Ap(64, 0);
          auto *GS = cast<StructType>(SG->getSourceElementType());
          if (SG->accumulateConstantOffset(DL, Ap)) {
            stepPosConst++;
            if (!GS->isSized() || Ap.isNegative() || Ap.getSExtValue() >= (int64_t)DL.getTypeAllocSize(GS))
              stepPosPast++;
          }
        }
        if (!named) continue;
        const Field fld{stripStructNameSuffix(ST->getName()).str(), off};
        const Value *obj = objKey(&I, Addr, ST);
        // A union member (plan 3.51, Mem.u): every access of any width
        // accesses the one field; kept aside until the scan shows a
        // pointer store there.
        if (!T->isPointerTy() && unionAt(ST, off, DL)) {
          if (isa<StoreInst>(&I)) uStores[fld].push_back({&I, obj});
          else if (T->isIntegerTy(DL.getPointerSizeInBits())) uLoads[fld].push_back({&I, obj});
        }
        if (T->isPointerTy()) {
          (isa<StoreInst>(&I) ? fStores : fLoads)[fld].push_back({&I, obj});
          if (const auto *St = dyn_cast<StoreInst>(&I); St && isa<Function>(St->getValueOperand()->stripPointerCasts()))
            fnFields.insert(fld); // a function-pointer field: also a tag candidate
        }
        else if (T->isIntegerTy() && isa<StoreInst>(&I)) {
          TagStore TS{cast<StoreInst>(&I), obj};
          analyzeTag(cast<StoreInst>(&I), obj, fld, TS);
          dStores[fld].push_back(std::move(TS));
        }
        else if (const auto *VT = dyn_cast<FixedVectorType>(T);
                 VT && VT->getElementType()->isPointerTy() && isa<StoreInst>(&I)) {
          // A store of a vector of pointers (-O3 restores two saved
          // methods with one <2 x ptr> store): a write of each lane's field.
          const int64_t es = (int64_t)DL.getTypeStoreSize(VT->getElementType());
          for (unsigned i = 0; i < VT->getNumElements(); i++)
            vecLanes[{fld.first, off + (int64_t)i * es}].push_back({&I, obj});
        }
      }
  }
  // A function-pointer field written as a vector lane: a tag store whose
  // value is not evaluated (unknown); like any tag store, it retags nothing
  // when its tag is never read under.
  for (auto &[fld, ws] : vecLanes)
    if (fnFields.count(fld))
      for (const FAccess &w : ws) {
        TagStore TS{cast<StoreInst>(w.I), w.obj};
        TS.unknown = true;
        dStores[fld].push_back(std::move(TS));
      }
  // A union member with pointer stores is a pointer field whose writers
  // are all its stores (an integer or float write holds no pointer) and
  // whose reads are its pointer and pointer-width integer loads; its
  // stores are not tags.
  for (auto &[fld, us] : uStores) {
    auto fit = fStores.find(fld);
    if (fit == fStores.end()) continue;
    fit->second.insert(fit->second.end(), us.begin(), us.end());
    auto &ls = fLoads[fld];
    ls.insert(ls.end(), uLoads[fld].begin(), uLoads[fld].end());
    dStores.erase(fld);
    unionFields++;
  }
  // A function-pointer field's stores are tag stores too (its values are
  // functions and the special constants).
  for (const Field &fld : fnFields)
    for (const FAccess &w : fStores[fld]) {
      TagStore TS{cast<StoreInst>(w.I), w.obj};
      analyzeTag(cast<StoreInst>(w.I), w.obj, fld, TS);
      dStores[fld].push_back(std::move(TS));
    }
  // Method-installed state (plan 3.54). Where each function is installed:
  // the function-pointer fields its address is stored into as a constant.
  // The dispatch sites that are tests of such a field D: the callee is a
  // load of D on the receiver (dispatchReceiver, one level), and nothing
  // is written between the load and the call (no store, no call), so the
  // content F of the receiver at the call is its content at the test.
  std::map<const Function *, std::set<Field>> fnInstalled;
  std::map<Field, std::set<const Function *>> installedIn; // the methods of D (plan 3.54 (b))
  std::set<Field> entrySiteFields;
  for (const Field &fld : fnFields) {
    for (const FAccess &w : fStores[fld])
      if (const auto *G = dyn_cast<Function>(cast<StoreInst>(w.I)->getValueOperand()->stripPointerCasts()))
        fnInstalled[G].insert(fld), installedIn[fld].insert(G);
    for (const FAccess &r : fLoads[fld]) {
      const auto *L = cast<LoadInst>(r.I);
      for (const User *U : L->users()) {
        const auto *CS = dyn_cast<CallBase>(U);
        if (!CS || CS->getCalledOperand()->stripPointerCasts() != L || CS->getParent() != L->getParent()) continue;
        std::vector<std::pair<const Value *, const Value *>> path;
        if (dispatchReceiver(CS, &path) < 0 || path.size() != 1 || path[0].second != L->getPointerOperand()) continue;
        bool quiet = L->comesBefore(CS);
        for (const Instruction *I = L->getNextNode(); quiet && I && I != CS; I = I->getNextNode())
          if (I->mayWriteToMemory() && !isa<DbgInfoIntrinsic>(I)) quiet = false;
        if (!quiet) continue;
        taggedEntrySites[CS] = {fld.first, fld.second};
        entrySiteFields.insert(fld);
      }
    }
  }
  size_t entryTestsMade = 0;
  std::map<std::string, size_t> entryRefusals; // why a method's reads take no entry test
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
  // dl: the field load the test reads, or a predicate call (a pure
  // function of its parameter's tag fields, evaluated by interpretation).
  struct FnTest { const BranchInst *Br; const Instruction *dl; std::string S; int64_t off; const Value *obj; };
  std::map<const Function *, std::vector<FnTest>> fnTests;
  // Predicates (plan 3.51 ruling a.3): a function returning an integer that
  // is a pure function of one pointer parameter's fields of one struct and
  // constants, with no write but to its own locals and no call.
  // readsField: it reads a field of its parameter (a failed one is an open
  // predicate test, not merely a call).
  struct Pred { bool ok = false, readsField = false; unsigned k = 0; std::string S; std::set<int64_t> offs; std::string why; };
  std::map<const Function *, Pred> predMemo;
  size_t predClosed = 0, predOpen = 0;
  std::map<std::string, std::pair<size_t, std::string>> predOpenWhy; // reason -> (tests, an example)
  auto predicateOf = [&](const Function *P) -> const Pred & {
    auto [it, ins] = predMemo.try_emplace(P);
    Pred &R = it->second;
    if (!ins) return R;
    if (P->isDeclaration() || !P->getReturnType()->isIntegerTy()) { R.why = "no body or not an integer"; return R; }
    int kArg = -1;
    for (const Instruction &I : instructions(*P)) {
      if (isa<DbgInfoIntrinsic>(I) || isa<AllocaInst>(I) || isa<GetElementPtrInst>(I) || isa<CastInst>(I) ||
          isa<BinaryOperator>(I) || isa<ICmpInst>(I) || isa<SelectInst>(I) || isa<PHINode>(I) ||
          isa<BranchInst>(I) || isa<ReturnInst>(I))
        continue;
      if (const auto *St = dyn_cast<StoreInst>(&I)) {
        if (isa<AllocaInst>(St->getPointerOperand()->stripPointerCasts())) continue;
        R.why = "a store at " + locOf(&I);
        return R;
      }
      if (const auto *L = dyn_cast<LoadInst>(&I)) {
        if (isa<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) continue;
        StructType *S2 = nullptr;
        int64_t o2 = 0;
        if (!composedSlot(L, L->getPointerOperand(), L->getModule()->getDataLayout(), S2, o2) || !S2 || !S2->hasName()) {
          R.why = "an unnamed load at " + locOf(&I);
          return R;
        }
        const auto *A = dyn_cast<Argument>(objKey(L, L->getPointerOperand(), S2));
        const std::string SN = stripStructNameSuffix(S2->getName()).str();
        if (!A || (kArg >= 0 && (int)A->getArgNo() != kArg) || (!R.S.empty() && R.S != SN)) {
          R.why = "a load not of the parameter at " + locOf(&I);
          return R;
        }
        kArg = (int)A->getArgNo();
        R.S = SN;
        R.offs.insert(o2);
        R.readsField = true;
        continue;
      }
      R.why = std::string("an instruction it cannot evaluate (") + I.getOpcodeName() + ") at " + locOf(&I);
      return R;
    }
    if (kArg < 0) { R.why = "reads no field"; return R; }
    R.ok = true;
    R.k = (unsigned)kArg;
    return R;
  };
  // Interpret predicate P with the tested fields at the given values.
  std::map<std::pair<const Function *, std::vector<std::pair<int64_t, int64_t>>>, std::optional<int64_t>> predCache;
  auto predEval = [&](const Function *P, const std::map<int64_t, int64_t> &vals) -> std::optional<int64_t> {
    std::vector<std::pair<int64_t, int64_t>> key(vals.begin(), vals.end());
    auto [cit, cins] = predCache.try_emplace({P, key});
    if (!cins) return cit->second;
    const Pred &PR = predicateOf(P);
    std::map<const Value *, int64_t> env;
    std::map<const AllocaInst *, int64_t> slots;
    auto val = [&](const Value *V) -> std::optional<int64_t> {
      if (auto c = constOf(V)) return c;
      if (auto it = env.find(V); it != env.end()) return it->second;
      return std::nullopt;
    };
    const BasicBlock *B = &P->getEntryBlock(), *prev = nullptr;
    std::optional<int64_t> result;
    for (int steps = 0; B && steps < 2000;) {
      const BasicBlock *next = nullptr;
      bool done = false, fail = false;
      for (const Instruction &I : *B) {
        if (++steps > 2000) { fail = true; break; }
        if (isa<DbgInfoIntrinsic>(I) || isa<AllocaInst>(I) || isa<GetElementPtrInst>(I)) continue;
        if (const auto *PN = dyn_cast<PHINode>(&I)) {
          auto v = prev ? val(PN->getIncomingValueForBlock(prev)) : std::nullopt;
          if (!v) { fail = true; break; }
          env[&I] = *v;
          continue;
        }
        if (const auto *St = dyn_cast<StoreInst>(&I)) {
          if (auto v = val(St->getValueOperand()))
            slots[cast<AllocaInst>(St->getPointerOperand()->stripPointerCasts())] = *v;
          continue; // a pointer stored to a slot: not tracked
        }
        if (const auto *L = dyn_cast<LoadInst>(&I)) {
          if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
            if (auto it = slots.find(A); it != slots.end()) env[&I] = it->second;
            continue; // an untracked (pointer) slot: its loads only address fields
          }
          StructType *S2 = nullptr;
          int64_t o2 = 0;
          composedSlot(L, L->getPointerOperand(), L->getModule()->getDataLayout(), S2, o2);
          auto it = vals.find(o2);
          if (it == vals.end()) { fail = true; break; }
          env[&I] = it->second;
          continue;
        }
        if (const auto *C = dyn_cast<CastInst>(&I)) {
          auto v = val(C->getOperand(0));
          if (!v) continue; // a pointer cast
          const unsigned sb = widthOf(C->getOperand(0)->getType()), db = widthOf(C->getType());
          int64_t r = *v;
          if (isa<TruncInst>(C)) r = db < 64 ? r & ((int64_t(1) << db) - 1) : r;
          else if (isa<ZExtInst>(C)) r = sb < 64 ? r & ((int64_t(1) << sb) - 1) : r;
          else if (isa<SExtInst>(C)) r = APInt(sb, (uint64_t)r).sext(64).getSExtValue();
          env[&I] = r;
          continue;
        }
        if (const auto *BO = dyn_cast<BinaryOperator>(&I)) {
          auto a = val(BO->getOperand(0)), b = val(BO->getOperand(1));
          if (!a || !b) { fail = true; break; }
          int64_t r;
          switch (BO->getOpcode()) {
          case Instruction::And: r = *a & *b; break;
          case Instruction::Or: r = *a | *b; break;
          case Instruction::Xor: r = *a ^ *b; break;
          case Instruction::Add: r = (int64_t)((uint64_t)*a + (uint64_t)*b); break;
          case Instruction::Sub: r = (int64_t)((uint64_t)*a - (uint64_t)*b); break;
          default: fail = true; r = 0; break;
          }
          if (fail) break;
          env[&I] = r;
          continue;
        }
        if (const auto *IC = dyn_cast<ICmpInst>(&I)) {
          auto a = val(IC->getOperand(0)), b = val(IC->getOperand(1));
          if (!a || !b) { fail = true; break; }
          const unsigned bw = widthOf(IC->getOperand(0)->getType());
          env[&I] = ICmpInst::compare(APInt(bw, (uint64_t)*a, true), APInt(bw, (uint64_t)*b, true), IC->getPredicate());
          continue;
        }
        if (const auto *SI = dyn_cast<SelectInst>(&I)) {
          auto c = val(SI->getCondition());
          if (!c) { fail = true; break; }
          auto v = val(*c ? SI->getTrueValue() : SI->getFalseValue());
          if (!v) { fail = true; break; }
          env[&I] = *v;
          continue;
        }
        if (const auto *Br = dyn_cast<BranchInst>(&I)) {
          if (Br->isUnconditional()) next = Br->getSuccessor(0);
          else {
            auto c = val(Br->getCondition());
            if (!c) { fail = true; break; }
            next = Br->getSuccessor(*c ? 0 : 1);
          }
          break;
        }
        if (const auto *Ret = dyn_cast<ReturnInst>(&I)) {
          result = Ret->getReturnValue() ? val(Ret->getReturnValue()) : std::nullopt;
          done = true;
          break;
        }
        fail = true;
        break;
      }
      if (fail || done) break;
      prev = B;
      B = next;
    }
    (void)PR;
    return cit->second = result;
  };
  auto fnTestsOf = [&](const Function *Fn) -> const std::vector<FnTest> & {
    auto [it, ins] = fnTests.try_emplace(Fn);
    if (!ins) return it->second;
    for (const BasicBlock &BB : *Fn) {
      const auto *Br = dyn_cast<BranchInst>(BB.getTerminator());
      if (!Br || !Br->isConditional()) continue;
      const Instruction *dl = nullptr;
      bool clean = true;
      std::vector<const Value *> work{Br->getCondition()};
      std::set<const Value *> seen;
      while (!work.empty() && clean) {
        const Value *X = work.back();
        work.pop_back();
        if (!seen.insert(X).second) continue;
        if (isa<ConstantInt>(X) || constOf(X)) continue;
        if (const auto *L = dyn_cast<LoadInst>(X)) {
          if (dl && dl != L) clean = false;
          dl = L;
          continue;
        }
        if (const auto *CB = dyn_cast<CallBase>(X); CB && CB->getCalledFunction() &&
                                                       !CB->getCalledFunction()->isDeclaration() &&
                                                       CB->getType()->isIntegerTy()) {
          if (dl && dl != CB) clean = false;
          dl = CB;
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
      if (const auto *CB = dyn_cast<CallBase>(dl)) { // a predicate call
        const Pred &PR = predicateOf(CB->getCalledFunction());
        if (!PR.ok) {
          if (PR.readsField) {
            predOpen++;
            const std::string kind = PR.why.substr(0, PR.why.find(" at "));
            auto &[n, ex] = predOpenWhy[kind];
            if (!n++) ex = CB->getCalledFunction()->getName().str() + " (" + PR.why + ")";
          }
          continue;
        }
        predClosed++;
        if (PR.k >= CB->arg_size()) continue;
        // One tested field: that field; several: off -1, matched by a product.
        const int64_t off = PR.offs.size() == 1 ? *PR.offs.begin() : -1;
        it->second.push_back({Br, dl, PR.S, off, ids.of(CB->getArgOperand(PR.k)->stripPointerCasts(), 0)});
        continue;
      }
      const auto *DL0 = cast<LoadInst>(dl);
      StructType *S2 = nullptr;
      int64_t o2 = 0;
      if (!composedSlot(DL0, DL0->getPointerOperand(), DL0->getModule()->getDataLayout(), S2, o2) || !S2 ||
          !S2->hasName())
        continue;
      it->second.push_back({Br, dl, stripStructNameSuffix(S2->getName()).str(), o2, objKey(DL0, DL0->getPointerOperand(), S2)});
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
  std::map<const Instruction *, const TagStore *> tagStoreAt;
  for (auto &[X, ts] : dStores)
    for (const TagStore &t : ts) dObjOf[t.I] = t.obj, tagStoreAt[t.I] = &t;
  // A tag write whose value may be a function of the tag it overwrites
  // (an 's' term, or not evaluable): it maps the tag found.
  auto mapsOld = [&](const Instruction *I) {
    auto it = tagStoreAt.find(I);
    if (it == tagStoreAt.end() || it->second->unknown) return true;
    for (const Term &tm : it->second->terms) if (tm.src == 's') return true;
    return false;
  };
  struct FieldCtx {
    Field X;
    bool isD = false;
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
      P->isD = isD;
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
    r.flt = p.flt;
    const int64_t pa = p.src == 'c' ? 0 : p.a;
    r.f = (p.f & q.a) | q.f;
    r.m = ((p.m & q.a) | q.m) & ~r.f;
    r.a = pa & q.a & ~r.f & ~r.m;
    if (!r.a) r.src = 'c';
    return r;
  };
  auto dedupT = [](std::vector<Term> &ts) {
    std::sort(ts.begin(), ts.end(), [](const Term &a, const Term &b) {
      return std::tie(a.src, a.a, a.f, a.m, a.flt) < std::tie(b.src, b.a, b.f, b.m, b.flt);
    });
    ts.erase(std::unique(ts.begin(), ts.end(), [](const Term &a, const Term &b) {
      return a.src == b.src && a.a == b.a && a.f == b.f && a.m == b.m && a.flt == b.flt;
    }), ts.end());
  };
  using EffKey = std::tuple<std::string, int64_t, const Function *, unsigned>;
  std::map<EffKey, Eff> effs;
  std::map<EffKey, std::set<EffKey>> effReaders;
  // A key's IR order: the function's module and place in it, the argument,
  // the field. Readers are re-queued in this order, so the worklist's
  // history (and every tuple a round makes) does not follow addresses.
  std::map<const Function *, std::pair<unsigned, unsigned>> fnPos;
  {
    unsigned mi = 0;
    for (auto &[M, _] : Ctx->Modules) {
      unsigned fi = 0;
      for (const Function &F : *M) fnPos[&F] = {mi, fi++};
      mi++;
    }
  }
  auto effIROrder = [&](const EffKey &a, const EffKey &b) {
    return std::make_tuple(fnPos[std::get<2>(a)], std::get<3>(a), std::get<0>(a), std::get<1>(a)) <
           std::make_tuple(fnPos[std::get<2>(b)], std::get<3>(b), std::get<0>(b), std::get<1>(b));
  };
  // before()'s loops cut at 8 rounds (open, listed): the one step of the
  // effect computation not shown monotone.
  std::vector<std::string> loopLimitAt;
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
        if (round == 7) {
          E.open = true;
          E.why = "a loop that does not settle at " + locOf(I);
          loopLimitAt.push_back(Dc.X.first + "+" + std::to_string(Dc.X.second) + " in " + Fn->getName().str() + " at " +
                                locOf(I));
        }
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
        std::vector<EffKey> rs(effReaders[q].begin(), effReaders[q].end());
        std::sort(rs.begin(), rs.end(), effIROrder);
        for (const EffKey &r : rs)
          if (effInWl.insert(r).second) effWl.push_back(r);
      }
      effSolving = false;
    }
    return effs[key];
  };
  size_t effClosed = 0, effOpen = 0, ceRounds = 0, ceUnsettled = 0;
  double ceSecs = 0, tagsSecs = 0;
  size_t tagsComputes = 0;
  std::vector<std::pair<const Instruction *, std::string>> effOpenAt; // every open site; the first 8 in IR order are printed
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
  // Br null: from the function's entry (Succ its entry block; an entry
  // test, plan 3.54, reads only).
  std::string unstableWhy; // why the last test was dropped (reports)
  // TBs: more test blocks left out of the region (a set test's); crossBlock:
  // the test's load may be in another block than its branch (a dispatch).
  auto stableBetween = [&](const Instruction *dl, const Instruction *Br, const BasicBlock *Succ, const Instruction *at,
                           const Field &X, bool isD, const Value *obj, std::set<uint32_t> &as,
                           std::vector<Term> *E, const std::set<const BasicBlock *> *TBs = nullptr,
                           bool crossBlock = false) {
    assert((Br || !isD) && "an entry test is a read's");
    if (Br && dl->getParent() != Br->getParent() && !crossBlock) {
      unstableWhy = "the test's load is in another block";
      return false;
    }
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
    if (Br && dl->getParent() == Br->getParent())
      for (const Instruction *I = dl->getNextNode(); I && I != Br; I = I->getNextNode())
        if (writes(*I)) { unstableWhy = "a write at " + locOf(I) + " between the test's load and its branch"; return false; }
    if (Br && dl->getParent() != Br->getParent()) {
      // The load in another block (a dispatch's table index): the stretch
      // from it to the branch, not back through either block, writes
      // nothing and redefines no pointer of the object.
      const BasicBlock *LB = dl->getParent(), *BB = Br->getParent();
      std::set<const BasicBlock *> f2, mid;
      std::vector<const BasicBlock *> w{LB};
      while (!w.empty()) {
        const BasicBlock *B = w.back();
        w.pop_back();
        for (const BasicBlock *N : successors(B))
          if (N != LB && N != BB && f2.insert(N).second) w.push_back(N);
      }
      w = {BB};
      std::set<const BasicBlock *> seen{BB};
      while (!w.empty()) {
        const BasicBlock *B = w.back();
        w.pop_back();
        for (const BasicBlock *P : predecessors(B))
          if (f2.count(P) && seen.insert(P).second) mid.insert(P), w.push_back(P);
      }
      const Defs &d2 = defsOf(obj);
      auto bad = [&](const Instruction &I) {
        if (writes(I)) { unstableWhy = "a write at " + locOf(&I) + " between the test's load and its branch"; return true; }
        if (d2.insts.count(&I)) { unstableWhy = "the object's pointer is defined between the test's load and its branch"; return true; }
        return false;
      };
      for (const Instruction *I = dl->getNextNode(); I; I = I->getNextNode())
        if (bad(*I)) return false;
      // In function order (as below): the scan stops at the first write, and
      // writes() makes the alias assumptions it passes, so which tuples
      // exist must not follow block addresses.
      for (const BasicBlock &MB : *BB->getParent()) {
        const BasicBlock *B = &MB;
        if (!mid.count(B)) continue;
        if (d2.blocks.count(B)) { unstableWhy = "the object's pointer merges between the test's load and its branch"; return false; }
        for (const Instruction &I : *B)
          if (bad(I)) return false;
      }
      if (d2.blocks.count(BB)) { unstableWhy = "the object's pointer merges at the test's branch"; return false; }
      for (const Instruction *I = &BB->front(); I && I != Br; I = I->getNextNode())
        if (bad(*I)) return false;
    }
    if (isD) {
      EffMemo memo;
      std::set<const Instruction *> cyc;
      Eff e = effectBefore(C, at->getFunction(), obj, at, Succ, memo, cyc);
      as.insert(e.assumes.begin(), e.assumes.end());
      if (e.open) { unstableWhy = "an open D effect: " + e.why; return false; }
      if (E) *E = std::move(e.maps);
      return true;
    }
    const BasicBlock *TB = Br ? Br->getParent() : nullptr;
    auto isTB = [&](const BasicBlock *B) { return B == TB || (TBs && TBs->count(B)); };
    std::set<const BasicBlock *> fwd, bwd;
    std::vector<const BasicBlock *> work{Succ};
    fwd.insert(Succ);
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      for (const BasicBlock *N : successors(B))
        if (!isTB(N) && fwd.insert(N).second) work.push_back(N);
    }
    work = {at->getParent()};
    bwd.insert(at->getParent());
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (B == Succ) continue;
      for (const BasicBlock *P : predecessors(B))
        if (!isTB(P) && fwd.count(P) && bwd.insert(P).second) work.push_back(P);
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
        if (isTB(B) || !sn.insert(B).second) continue;
        if (B == at->getParent()) atCycle = true;
        for (const BasicBlock *N : successors(B)) w2.push_back(N);
      }
    }
    // In function order: the first write met ends the scan, and writes()
    // makes the alias assumptions it passes on the way.
    for (const BasicBlock &BBr : *at->getFunction()) {
      const BasicBlock *B = &BBr;
      if (bwd.count(B) && fwd.count(B)) {
        if (idDefs.blocks.count(B) && (B != at->getParent() || atCycle)) { unstableWhy = "the object's pointer merges between"; return false; }
        for (const Instruction &I : *B) {
          if (idDefs.insts.count(&I) && !(B == at->getParent() && at->comesBefore(&I) && !atCycle)) {
            unstableWhy = "the object's pointer is defined between";
            return false;
          }
          if (writes(I)) { unstableWhy = "a write at " + locOf(&I); return false; }
        }
      }
    }
    return true;
  };
  // A test of D on the access's object dominating it, stable up to it.
  // A tag value packs field o1 (its low w1 bits) and, for a product,
  // field o2 above them; off: the field the test's load reads.
  struct Test {
    const Value *cond;
    const Instruction *d;
    bool onTrue;
    int64_t off, o1, o2 = INT64_MIN;
    unsigned w1 = 64;
    // A test in a callee on a parameter the call passes the tag in
    // (parameter-pair tests): the tag's value there is argExpr's, with
    // argLeaf (the caller's load of D) the tag.
    const Value *argExpr = nullptr;
    const Instruction *argLeaf = nullptr;
    // A switch edge: cond is the switch value; the edge holds iff it is
    // one of caseVals (or, for the default edge, none of them).
    bool sw = false, swDefault = false;
    std::vector<int64_t> caseVals;
    // An entry test (plan 3.54): D == entryFn on entry to entryFn through
    // a dispatch o->D(o, ...), o its formal entryK (a switch edge on the
    // read itself standing for the tag: cond == d).
    const Function *entryFn = nullptr;
    unsigned entryK = 0;
    // A set test (Fable 2026-10-17, (T)): the test holds iff one of these
    // does (each an edge's own test); the fields above are the first's.
    std::vector<Test> anyOf;
  };
  std::vector<std::vector<Test>> termFilters; // Term::flt
  // Products (plan 3.51 ruling a): a predicate reading an integer tag and
  // a function-pointer tag of one object is judged on both at once; the
  // virtual field (S, -1 - index) stands for the pair.
  struct Prod { int64_t d1, d2; unsigned w1; };
  std::vector<Prod> prods;
  std::map<std::tuple<std::string, int64_t, int64_t>, int64_t> prodIdx;
  size_t testsUnstable = 0, setTestsMade = 0, dispatchTestsMade = 0, dispatchTestsDropped = 0;
  size_t writersUnderTest = 0; // untagged writers a stable test of their tag dominates (measured, reporting only)
  // Reads (Ef null): stable against F writes. Retags (Ef set): each
  // test's composed D effect up to the access, parallel to tests.
  std::string lastTestsWhy; // the last testsAt's reason for dropping tests
  auto testsAt = [&](const Instruction *at, const Value *obj, const Field &Df, const Field &Ff,
                     std::vector<Test> &tests, std::set<uint32_t> &as,
                     std::vector<std::vector<Term>> *Ef = nullptr) {
    lastTestsWhy = "no dominating test of the tag on this object";
    const Function *Fn = at->getFunction();
    DominatorTree &DT = domOf(Fn);
    const Prod *pp = Df.second < 0 ? &prods[-1 - Df.second] : nullptr;
    for (const FnTest &ft : fnTestsOf(Fn)) {
      if (ft.S != Df.first || ft.obj != obj) continue;
      if (const auto *CB = dyn_cast<CallBase>(ft.dl)) {
        // A predicate: of this field (other fields unknown), or, for a
        // product, of both (one-field tests are the components' own).
        const Pred &PR = predicateOf(CB->getCalledFunction());
        if (pp ? !PR.offs.count(pp->d1) || !PR.offs.count(pp->d2) : !PR.offs.count(Df.second)) continue;
      } else if (pp || ft.off != Df.second) continue;
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
        tests.push_back({ft.Br->getCondition(), ft.dl, si == 0, ft.off, pp ? pp->d1 : Df.second,
                         pp ? pp->d2 : INT64_MIN, pp ? pp->w1 : 64u});
        if (Ef) Ef->push_back(std::move(E));
      }
    }
    // A set test (Fable 2026-10-17, (T)): a block dominating the read,
    // entered only on edges of tests of D on this object (`t == a || t ==
    // b`: each equality's true edge, the second test reached on the first's
    // false edge): there D satisfies one of them. Each is stable from its
    // edge up to the read, every test block of the set left out of the
    // region. Reads only (a retag keeps its own tests).
    if (tests.empty() && !Ef && !pp) {
      const std::vector<FnTest> &fts = fnTestsOf(Fn);
      for (const DomTreeNode *N = DT.getNode(at->getParent()); N && tests.empty(); N = N->getIDom()) {
        const BasicBlock *J = N->getBlock();
        if (J->hasNPredecessors(0) || J->getSinglePredecessor()) continue;
        std::vector<std::pair<const FnTest *, bool>> alts; // test, its edge into J the true one
        std::set<const BasicBlock *> TBs;
        bool all = true;
        for (const BasicBlock *P : predecessors(J)) {
          const FnTest *hit = nullptr;
          for (const FnTest &ft : fts)
            if (ft.Br->getParent() == P && ft.S == Df.first && ft.obj == obj && ft.off == Df.second &&
                !isa<CallBase>(ft.dl))
              hit = &ft;
          if (!hit || hit->Br->getSuccessor(0) == hit->Br->getSuccessor(1)) { all = false; break; }
          if (TBs.insert(P).second) alts.push_back({hit, hit->Br->getSuccessor(0) == J});
        }
        if (!all || alts.size() < 2) continue;
        std::set<uint32_t> a2;
        bool stable = true;
        for (const auto &[ft, onT] : alts)
          if (!stableBetween(ft->dl, ft->Br, J, at, Ff, false, obj, a2, nullptr, &TBs)) {
            testsUnstable++;
            lastTestsWhy = "set test at " + locOf(ft->Br) + " dropped: " + unstableWhy;
            stable = false;
            break;
          }
        if (!stable) continue;
        as.insert(a2.begin(), a2.end());
        Test st{alts[0].first->Br->getCondition(), alts[0].first->dl, alts[0].second, Df.second, Df.second};
        for (const auto &[ft, onT] : alts)
          st.anyOf.push_back(Test{ft->Br->getCondition(), ft->dl, onT, Df.second, Df.second});
        tests.push_back(std::move(st));
        setTestsMade++;
      }
    }
    // The same set test as -O0 emits it: a branch on a phi of conditions
    // (`t == a || t == b` is `br (phi i1 [true, P1], [c2, P2])`). On the
    // edge whose value is b, the read was reached through an entry whose
    // value is b: a constant b entry through its block's own test of D
    // (its edge into the phi's block), a condition entry through that
    // condition on one load of D on this object; an entry whose constant
    // is not b never takes the edge.
    auto dLoadOf = [&](const Value *C) -> const LoadInst * {
      const LoadInst *leaf = nullptr;
      std::vector<const Value *> work{C};
      std::set<const Value *> seen;
      while (!work.empty()) {
        const Value *X = work.back();
        work.pop_back();
        if (!seen.insert(X).second || isa<Constant>(X)) continue;
        if (const auto *L = dyn_cast<LoadInst>(X)) {
          if (leaf && leaf != L) return nullptr;
          leaf = L;
          continue;
        }
        if (isa<ICmpInst>(X) || isa<CastInst>(X) ||
            (isa<BinaryOperator>(X) && (cast<BinaryOperator>(X)->getOpcode() == Instruction::And ||
                                        cast<BinaryOperator>(X)->getOpcode() == Instruction::Or ||
                                        cast<BinaryOperator>(X)->getOpcode() == Instruction::Xor))) {
          for (const Value *Op : cast<User>(X)->operands()) work.push_back(Op);
          continue;
        }
        return nullptr;
      }
      StructType *S2 = nullptr;
      int64_t o2 = 0;
      if (!leaf || !composedSlot(leaf, leaf->getPointerOperand(), leaf->getModule()->getDataLayout(), S2, o2) || !S2 ||
          !S2->hasName() || stripStructNameSuffix(S2->getName()) != Df.first || o2 != Df.second ||
          objKey(leaf, leaf->getPointerOperand(), S2) != obj)
        return nullptr;
      return leaf;
    };
    if (tests.empty() && !Ef && !pp) {
      const std::vector<FnTest> &fts = fnTestsOf(Fn);
      for (const DomTreeNode *N = DT.getNode(at->getParent()); N && tests.empty(); N = N->getIDom()) {
        const BasicBlock *J = N->getBlock(), *B = J->getSinglePredecessor();
        const auto *Br = B ? dyn_cast<BranchInst>(B->getTerminator()) : nullptr;
        if (!Br || !Br->isConditional() || Br->getSuccessor(0) == Br->getSuccessor(1)) continue;
        const auto *PN = dyn_cast<PHINode>(Br->getCondition());
        if (!PN || PN->getParent() != B) continue;
        const bool want = Br->getSuccessor(0) == J;
        std::vector<Test> alts;
        bool ok = true;
        for (unsigned q = 0; q < PN->getNumIncomingValues() && ok; q++) {
          const Value *V = PN->getIncomingValue(q);
          const BasicBlock *P = PN->getIncomingBlock(q);
          if (const auto *K = dyn_cast<ConstantInt>(V)) {
            if (K->isOne() != want) continue; // this entry never takes the edge
            const FnTest *hit = nullptr;
            for (const FnTest &ft : fts)
              if (ft.Br->getParent() == P && ft.S == Df.first && ft.obj == obj && ft.off == Df.second &&
                  !isa<CallBase>(ft.dl) && ft.Br->getSuccessor(0) != ft.Br->getSuccessor(1))
                hit = &ft;
            if (!hit || (hit->Br->getSuccessor(0) != B && hit->Br->getSuccessor(1) != B)) { ok = false; break; }
            alts.push_back(Test{hit->Br->getCondition(), hit->dl, hit->Br->getSuccessor(0) == B, Df.second, Df.second});
            continue;
          }
          const LoadInst *dl = dLoadOf(V);
          if (!dl) { ok = false; break; }
          alts.push_back(Test{V, dl, want, Df.second, Df.second});
        }
        if (!ok || alts.empty()) continue;
        std::set<uint32_t> a2;
        bool stable = true;
        for (const Test &x : alts)
          if (!stableBetween(x.d, Br, J, at, Ff, false, obj, a2, nullptr, nullptr, true)) {
            testsUnstable++;
            lastTestsWhy = "set test at " + locOf(Br) + " dropped: " + unstableWhy;
            stable = false;
            break;
          }
        if (!stable) continue;
        as.insert(a2.begin(), a2.end());
        Test st = alts[0];
        if (alts.size() > 1) st.anyOf = alts;
        tests.push_back(std::move(st));
        setTestsMade++;
      }
    }
    // A dispatch (Fable 2026-10-17, (T)): a switch dominating the read on D
    // itself or on a value read from a constant 2-D integer table, one index
    // of which is D (binutils' `switch (link_action[row][prev])`, prev =
    // h->type or a constant): on the switch's edges that reach the read
    // (not back through the switch), D is one of the values whose table
    // entries, in any row, take such an edge. A constant the index may also
    // hold that takes such an edge leaves D untested. Each reaching edge
    // stable up to the read, the stretch from D's load to the switch too.
    if (tests.empty() && !Ef && !pp)
      for (const DomTreeNode *N = DT.getNode(at->getParent()); N && tests.empty(); N = N->getIDom()) {
        const auto *SW = dyn_cast<SwitchInst>(N->getBlock()->getTerminator());
        if (!SW || N->getBlock() == at->getParent() || SW->getCondition()->getType()->getIntegerBitWidth() > 64) continue;
        const BasicBlock *SB = SW->getParent();
        // The value switched on: through an -O0 local with one store.
        auto through = [&](const Value *V) -> const Value * {
          for (int d = 0; d < 8; d++) {
            V = V->stripPointerCasts();
            if (const auto *L = dyn_cast<LoadInst>(V))
              if (const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
                const StoreInst *one = nullptr;
                for (const User *U : AI->users())
                  if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand()->stripPointerCasts() == AI) {
                    if (one) return nullptr;
                    one = St;
                  }
                if (!one) return nullptr;
                V = one->getValueOperand();
                continue;
              }
            return V;
          }
          return nullptr;
        };
        // The terms an index or the switched value may be: D's expressions
        // (each with its load of D) and constants.
        struct DTerm { const Value *expr; const Instruction *dl; };
        std::function<bool(const Value *, int, std::vector<DTerm> &, std::vector<int64_t> &)> terms =
            [&](const Value *V, int d, std::vector<DTerm> &dts, std::vector<int64_t> &cs) -> bool {
          if (d > 6) return false;
          const Value *W = V;
          while (const auto *C = dyn_cast<CastInst>(W)) {
            if (!C->getType()->isIntegerTy() || !C->getOperand(0)->getType()->isIntegerTy()) break;
            W = C->getOperand(0);
          }
          if (const auto *K = dyn_cast<ConstantInt>(W)) {
            if (K->getBitWidth() > 64) return false;
            cs.push_back(K->getSExtValue());
            return true;
          }
          if (const auto *L = dyn_cast<LoadInst>(W))
            if (const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
              bool any = false;
              for (const User *U : AI->users())
                if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand()->stripPointerCasts() == AI) {
                  if (!terms(St->getValueOperand(), d + 1, dts, cs)) return false;
                  any = true;
                } else if (!isa<LoadInst>(U) && !isa<DbgInfoIntrinsic>(U)) return false; // the local escapes
              return any;
            }
          if (const auto *PN = dyn_cast<PHINode>(W)) {
            for (const Value *In : PN->incoming_values())
              if (!terms(In, d + 1, dts, cs)) return false;
            return true;
          }
          // An expression of one load of D on this object (casts and bit
          // operations with constants).
          const Instruction *leaf = nullptr;
          std::vector<const Value *> work{W};
          std::set<const Value *> seen;
          while (!work.empty()) {
            const Value *X = work.back();
            work.pop_back();
            if (!seen.insert(X).second || isa<Constant>(X)) continue;
            if (const auto *L = dyn_cast<LoadInst>(X)) {
              if (leaf && leaf != L) return false;
              leaf = L;
              continue;
            }
            if (isa<CastInst>(X) || (isa<BinaryOperator>(X) && (cast<BinaryOperator>(X)->getOpcode() == Instruction::And ||
                                                                 cast<BinaryOperator>(X)->getOpcode() == Instruction::Or ||
                                                                 cast<BinaryOperator>(X)->getOpcode() == Instruction::Xor))) {
              for (const Value *Op : cast<User>(X)->operands()) work.push_back(Op);
              continue;
            }
            return false;
          }
          const auto *DL0 = dyn_cast_or_null<LoadInst>(leaf);
          StructType *S2 = nullptr;
          int64_t o2 = 0;
          if (!DL0 || !composedSlot(DL0, DL0->getPointerOperand(), DL0->getModule()->getDataLayout(), S2, o2) || !S2 ||
              !S2->hasName() || stripStructNameSuffix(S2->getName()) != Df.first || o2 != Df.second ||
              objKey(DL0, DL0->getPointerOperand(), S2) != obj)
            return false;
          dts.push_back({W, DL0});
          return true;
        };
        // The switch's edges that reach the read without passing the switch.
        std::map<const BasicBlock *, bool> reachMemo;
        auto reaches = [&](const BasicBlock *S) {
          auto [it, ins] = reachMemo.try_emplace(S, false);
          if (!ins) return it->second;
          std::set<const BasicBlock *> sn{S};
          std::vector<const BasicBlock *> w{S};
          while (!w.empty() && !it->second) {
            const BasicBlock *B = w.back();
            w.pop_back();
            if (B == at->getParent()) it->second = true;
            for (const BasicBlock *M : successors(B))
              if (M != SB && sn.insert(M).second) w.push_back(M);
          }
          return it->second;
        };
        auto takes = [&](int64_t v) { // the switch on v takes an edge that reaches the read
          for (auto C : SW->cases())
            if (C.getCaseValue()->getSExtValue() == v) return reaches(C.getCaseSuccessor());
          return reaches(SW->getDefaultDest());
        };
        const Value *SV = through(SW->getCondition());
        if (!SV) continue;
        std::vector<DTerm> dts;
        std::vector<int64_t> cs, admitted; // admitted: D's index values (or D's values) that take a reaching edge
        bool ok = false;
        const auto *TL = dyn_cast<LoadInst>(SV);
        const GlobalVariable *GV = nullptr;
        std::vector<const Value *> idx;
        if (TL && TL->getType()->isIntegerTy()) {
          // The table read: GEPs from a constant [nr x [nc x iK]] global, indices (0, i1, i2).
          const Value *P = TL->getPointerOperand();
          std::vector<const Value *> rev;
          for (int d = 0; d < 3; d++) {
            const auto *G = dyn_cast<GEPOperator>(P);
            if (!G) break;
            std::vector<const Value *> ix(G->idx_begin(), G->idx_end());
            if (ix.empty() || !isa<ConstantInt>(ix[0]) || !cast<ConstantInt>(ix[0])->isZero()) { rev.clear(); P = nullptr; break; }
            for (size_t q = ix.size(); q-- > 1;) rev.push_back(ix[q]);
            P = G->getPointerOperand();
          }
          GV = P ? dyn_cast<GlobalVariable>(P->stripPointerCasts()) : nullptr;
          idx.assign(rev.rbegin(), rev.rend());
        }
        if (GV && GV->isConstant() && GV->hasDefinitiveInitializer() && idx.size() == 2) {
          const auto *AT = dyn_cast<ArrayType>(GV->getValueType());
          const auto *RT = AT ? dyn_cast<ArrayType>(AT->getElementType()) : nullptr;
          if (RT && RT->getElementType()->isIntegerTy() && AT->getNumElements() * RT->getNumElements() <= 4096) {
            const int64_t nr = (int64_t)AT->getNumElements(), nc = (int64_t)RT->getNumElements();
            auto entry = [&](int64_t r, int64_t c) -> std::optional<int64_t> {
              const Constant *Row = GV->getInitializer()->getAggregateElement((unsigned)r);
              const Constant *E = Row ? Row->getAggregateElement((unsigned)c) : nullptr;
              if (const auto *K = dyn_cast_or_null<ConstantInt>(E)) return K->getSExtValue();
              return std::nullopt;
            };
            std::vector<DTerm> d0, d1;
            std::vector<int64_t> c0, c1;
            const bool t0 = terms(idx[0], 0, d0, c0), t1 = terms(idx[1], 0, d1, c1);
            // D in exactly one index; the other any value.
            const bool dRow = t0 && !d0.empty() && !(t1 && !d1.empty());
            const bool dCol = t1 && !d1.empty() && !(t0 && !d0.empty());
            if (dRow || dCol) {
              dts = dRow ? d0 : d1;
              cs = dRow ? c0 : c1;
              const int64_t nD = dRow ? nr : nc, nO = dRow ? nc : nr;
              ok = true;
              for (int64_t k = 0; k < nD && ok; k++)
                for (int64_t o = 0; o < nO; o++) {
                  auto e = dRow ? entry(k, o) : entry(o, k);
                  if (!e) { ok = false; break; }
                  if (takes(*e)) { admitted.push_back(k); break; }
                }
            }
          }
        } else if (terms(SV, 0, dts, cs) && !dts.empty()) {
          // A switch on D itself: its case values that take a reaching edge
          // (the default's: D any value the cases do not name).
          ok = !reaches(SW->getDefaultDest());
          for (auto C : SW->cases())
            if (reaches(C.getCaseSuccessor())) admitted.push_back(C.getCaseValue()->getSExtValue());
        }
        if (!ok || dts.empty()) continue;
        bool untested = false;
        for (int64_t c : cs) untested |= std::find(admitted.begin(), admitted.end(), c) != admitted.end();
        if (untested) { dispatchTestsDropped++; lastTestsWhy = "dispatch at " + locOf(SW) + ": a constant the index may hold takes the edge"; continue; }
        std::set<const BasicBlock *> succs;
        for (const BasicBlock *S : successors(SB))
          if (reaches(S)) succs.insert(S);
        std::set<uint32_t> a2;
        bool stable = true;
        for (const DTerm &dt : dts) {
          for (const BasicBlock *S : succs)
            if (!stableBetween(dt.dl, SW, S, at, Ff, false, obj, a2, nullptr, nullptr, true)) { stable = false; break; }
          if (!stable) break;
        }
        if (!stable) {
          testsUnstable++;
          lastTestsWhy = "dispatch at " + locOf(SW) + " dropped: " + unstableWhy;
          continue;
        }
        as.insert(a2.begin(), a2.end());
        std::vector<Test> alts;
        for (const DTerm &dt : dts) {
          Test x{dt.expr, dt.dl, true, Df.second, Df.second};
          x.sw = true;
          x.caseVals = admitted;
          alts.push_back(std::move(x));
        }
        Test st = alts[0];
        if (alts.size() > 1) st.anyOf = alts;
        tests.push_back(std::move(st));
        dispatchTestsMade++;
      }
    // Plan 3.54: no test in the function, but the function is a method
    // installed in D and the object is its receiver formal. On entry
    // through a dispatch o->D(o, ...) (a test site), D == M held at the
    // dispatch's load of D, and F has not been written since (the site's
    // check, then this function's up to the read). The test stands for
    // those entries only: the solver gives every other entry of the formal
    // the unkeyed read. Reads only (a retag keeps its own tests).
    if (!tests.empty() || Ef || pp || !entrySiteFields.count(Df)) return;
    const Function *M = Fn;
    int k = -1;
    for (unsigned i = 0; i < M->arg_size() && k < 0; i++)
      if (M->getArg(i)->getType()->isPointerTy() && argId(M->getArg(i)) == obj) k = (int)i;
    if (k < 0) return; // not the receiver formal
    auto iit = fnInstalled.find(M);
    if (iit == fnInstalled.end() || !iit->second.count(Df)) return; // not a method of D
    auto refuse = [&](const std::string &why) {
      entryRefusals[why]++;
      lastTestsWhy = "no entry test: " + why;
    };
    if (taggedOutsidePre.count(M)) return refuse("the method's address may reach the outside (entries the solve does not see)");
    std::set<uint32_t> a2;
    if (!stableBetween(nullptr, nullptr, &M->getEntryBlock(), at, Ff, false, obj, a2, nullptr))
      return refuse("F may be written between the entry and the read: " + unstableWhy);
    as.insert(a2.begin(), a2.end());
    Test t{at, at, true, Df.second, Df.second};
    t.sw = true;
    t.caseVals = {*ptrConst(M)};
    t.entryFn = M;
    t.entryK = (unsigned)k;
    tests.push_back(std::move(t));
    entryTestsMade++;
  };
  // The test being evaluated (its packing of the tag), and field o's
  // value in tag v.
  const Test *curT = nullptr;
  auto partOf = [&](int64_t v, int64_t o) -> int64_t {
    if (curT->o2 == INT64_MIN) return v;
    if (o == curT->o1) return v & (int64_t)((uint64_t(1) << curT->w1) - 1);
    return (int64_t)((uint64_t)v >> curT->w1);
  };
  // Evaluate a test with the tag = v.
  std::function<std::optional<int64_t>(const Value *, const Instruction *, int64_t)> eval =
      [&](const Value *X, const Instruction *dl, int64_t v) -> std::optional<int64_t> {
    if (X == dl) {
      if (const auto *CB = dyn_cast<CallBase>(dl)) {
        // The tag's fields; a field it does not hold stays unknown (the
        // interpretation fails if the predicate reads it).
        const Pred &PR = predicateOf(CB->getCalledFunction());
        std::map<int64_t, int64_t> vals;
        for (int64_t o : PR.offs)
          if (o == curT->o1 || o == curT->o2) vals[o] = partOf(v, o);
        return predEval(CB->getCalledFunction(), vals);
      }
      return partOf(v, curT->off);
    }
    if (auto c = constOf(X)) return c;
    if (const auto *C = dyn_cast<CastInst>(X)) {
      auto a = eval(C->getOperand(0), dl, v);
      if (!a) return std::nullopt;
      if (isa<PtrToIntInst>(C) || isa<IntToPtrInst>(C) ||
          (C->getType()->isPointerTy() && C->getOperand(0)->getType()->isPointerTy()))
        return a;
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
      const unsigned bw = widthOf(IC->getOperand(0)->getType());
      const APInt A(bw, (uint64_t)*a, true), B(bw, (uint64_t)*b, true);
      return (int64_t)ICmpInst::compare(A, B, IC->getPredicate());
    }
    return std::nullopt;
  };
  // The same tests over a widened tag (plan 3.51, ruling gamma): bits
  // known or free; a test that may hold does not exclude.
  std::function<std::optional<KnownBits>(const Value *, const Instruction *, const KnownBits &)> evalKB =
      [&](const Value *X, const Instruction *dl, const KnownBits &kb) -> std::optional<KnownBits> {
    if (X == dl && isa<CallBase>(dl)) return std::nullopt; // a predicate over unknown bits: may hold
    if (X == dl) {
      const unsigned w = widthOf(dl->getType());
      KnownBits k = kb;
      if (curT->o2 != INT64_MIN)
        k = curT->off == curT->o1 ? kb.trunc(curT->w1).zext(64) : kb.extractBits(64 - curT->w1, curT->w1).zext(64);
      return w == 64 ? k : k.trunc(w);
    }
    if (const auto *K = dyn_cast<ConstantInt>(X)) return KnownBits::makeConstant(K->getValue());
    if (auto c = constOf(X)) return KnownBits::makeConstant(APInt(64, (uint64_t)*c));
    if (const auto *C = dyn_cast<CastInst>(X)) {
      if (isa<PtrToIntInst>(C) || isa<IntToPtrInst>(C) ||
          (C->getType()->isPointerTy() && C->getOperand(0)->getType()->isPointerTy())) {
        auto a = evalKB(C->getOperand(0), dl, kb);
        if (!a || a->getBitWidth() != 64) return std::nullopt;
        return a;
      }
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
  std::function<bool(const Value *, const Instruction *, uint64_t, uint64_t &)> demand =
      [&](const Value *X, const Instruction *dl, uint64_t want, uint64_t &acc) -> bool {
    if (X == dl && isa<CallBase>(dl)) return false; // a predicate observes its fields whole
    if (X == dl) { acc |= want; return true; }
    if (isa<ConstantInt>(X) || constOf(X)) return true;
    if (const auto *C = dyn_cast<CastInst>(X);
        C && (isa<PtrToIntInst>(C) || isa<IntToPtrInst>(C) ||
              (C->getType()->isPointerTy() && C->getOperand(0)->getType()->isPointerTy())))
      return demand(C->getOperand(0), dl, want, acc);
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
      const uint64_t all = maskOf(widthOf(IC->getOperand(0)->getType()));
      return demand(IC->getOperand(0), dl, all, acc) && demand(IC->getOperand(1), dl, all, acc);
    }
    return false;
  };
  // A switch edge on value x (width bw).
  auto swHolds = [](const Test &t, int64_t x, unsigned bw) {
    const uint64_t m = bw >= 64 ? ~uint64_t(0) : ((uint64_t(1) << bw) - 1);
    bool in = false;
    for (int64_t c : t.caseVals) in |= ((uint64_t)c & m) == ((uint64_t)x & m);
    return t.swDefault ? !in : in;
  };
  auto mayHold1 = [&](const Test &t, const KnownBits &kb) {
    do { // one test: `continue` is "no constraint"
      curT = &t;
      std::optional<KnownBits> in = kb;
      if (t.argExpr) {
        in = evalKB(t.argExpr, t.argLeaf, kb);
        if (!in) continue;
        if (in->getBitWidth() != 64) in = in->sext(64);
      }
      auto r = evalKB(t.cond, t.d, *in);
      if (!r || !r->isConstant()) continue; // may hold
      if (t.sw) {
        if (!swHolds(t, (int64_t)r->getConstant().getZExtValue(), r->getBitWidth())) return false;
        continue;
      }
      if ((!r->getConstant().isZero()) != t.onTrue) return false;
    } while (false);
    return true;
  };
  auto mayHold = [&](const std::vector<Test> &tests, const KnownBits &kb) {
    for (const Test &t : tests) {
      if (t.anyOf.empty()) {
        if (!mayHold1(t, kb)) return false;
        continue;
      }
      bool any = false;
      for (const Test &a : t.anyOf) any = any || mayHold1(a, kb);
      if (!any) return false;
    }
    return true;
  };
  auto holds1 = [&](const Test &t, int64_t v) {
    do { // one test: `continue` is "no constraint"
      curT = &t;
      int64_t in = v;
      if (t.argExpr) {
        auto a = eval(t.argExpr, t.argLeaf, v);
        if (!a) continue;
        in = *a;
      }
      auto r2 = eval(t.cond, t.d, in);
      if (!r2) continue; // not evaluable: no constraint
      if (t.sw) {
        if (!swHolds(t, *r2, widthOf(t.cond->getType()))) return false;
        continue;
      }
      if ((*r2 != 0) != t.onTrue) return false;
    } while (false);
    return true;
  };
  auto holds = [&](const std::vector<Test> &tests, int64_t v) {
    for (const Test &t : tests) {
      if (t.anyOf.empty()) {
        if (!holds1(t, v)) return false;
        continue;
      }
      bool any = false;
      for (const Test &a : t.anyOf) any = any || holds1(a, v);
      if (!any) return false;
    }
    return true;
  };
  // ---- Parameter-pair tests (plan 3.51) ----
  // A callee G receiving an object's tag in parameter k and its F content
  // in parameter j: per use of j, the tests on k whose edges dominate it
  // (parameters are values: nothing in G changes them). A parameter's
  // values: the argument, or the reloads of the -O0 slot it is stored to
  // (nullopt if that slot has any other use).
  auto paramVals = [&](const Function *G, unsigned k) -> std::optional<std::set<const Value *>> {
    std::set<const Value *> vals;
    const Argument *A = G->getArg(k);
    vals.insert(A);
    for (const User *U : A->users()) {
      const auto *St = dyn_cast<StoreInst>(U);
      const auto *AI = St ? dyn_cast<AllocaInst>(St->getPointerOperand()) : nullptr;
      if (!AI || St->getValueOperand() != A) continue;
      for (const User *V : AI->users()) {
        if (V == St || isa<DbgInfoIntrinsic>(V)) continue;
        const auto *L = dyn_cast<LoadInst>(V);
        if (!L || L->getPointerOperand() != AI) return std::nullopt; // the slot is written or escapes
        vals.insert(L);
      }
    }
    return vals;
  };
  struct PPUse { const Instruction *use; std::vector<Test> tests; bool channel; }; // channel: a slot reload
  std::map<std::tuple<const Function *, unsigned, unsigned, int64_t>, std::optional<std::vector<PPUse>>> ppMemo;
  auto ppSummary = [&](const Function *G, unsigned k, unsigned j, int64_t dOff) -> const std::optional<std::vector<PPUse>> & {
    auto [it, ins] = ppMemo.try_emplace({G, k, j, dOff});
    if (!ins) return it->second;
    const auto kv = paramVals(G, k), jv = paramVals(G, j);
    if (!kv || !jv) return it->second;
    // The leaf of a condition: one value of parameter k, through casts and
    // bit operations with constants.
    auto leafOf = [&](const Value *C) -> const Instruction * {
      const Value *leaf = nullptr;
      std::vector<const Value *> work{C};
      std::set<const Value *> seen;
      while (!work.empty()) {
        const Value *X = work.back();
        work.pop_back();
        if (!seen.insert(X).second || isa<Constant>(X)) continue;
        if (kv->count(X)) { if (leaf && leaf != X) return nullptr; leaf = X; continue; }
        if (isa<ICmpInst>(X) || isa<CastInst>(X) ||
            (isa<BinaryOperator>(X) && (cast<BinaryOperator>(X)->getOpcode() == Instruction::And ||
                                        cast<BinaryOperator>(X)->getOpcode() == Instruction::Or ||
                                        cast<BinaryOperator>(X)->getOpcode() == Instruction::Xor))) {
          for (const Value *Op : cast<User>(X)->operands()) work.push_back(Op);
          continue;
        }
        return nullptr;
      }
      return dyn_cast_or_null<Instruction>(leaf); // the argument itself (-O3) is not an Instruction: unsupported
    };
    struct Edge { const BasicBlock *succ; Test t; };
    std::vector<Edge> edges;
    for (const BasicBlock &B : *G) {
      const Instruction *Term = B.getTerminator();
      if (const auto *Br = dyn_cast<BranchInst>(Term); Br && Br->isConditional()) {
        const Instruction *leaf = leafOf(Br->getCondition());
        if (!leaf || Br->getSuccessor(0) == Br->getSuccessor(1)) continue;
        for (unsigned si = 0; si < 2; si++)
          if (Br->getSuccessor(si)->getUniquePredecessor() == &B)
            edges.push_back({Br->getSuccessor(si), {Br->getCondition(), leaf, si == 0, dOff, dOff}});
      } else if (const auto *SW = dyn_cast<SwitchInst>(Term)) {
        const Instruction *leaf = leafOf(SW->getCondition());
        if (!leaf || SW->getCondition()->getType()->getIntegerBitWidth() > 64) continue; // u128: no tag test
        std::map<const BasicBlock *, std::vector<int64_t>> labels;
        std::vector<int64_t> all;
        for (auto C : SW->cases()) {
          labels[C.getCaseSuccessor()].push_back(C.getCaseValue()->getSExtValue());
          all.push_back(C.getCaseValue()->getSExtValue());
        }
        for (auto &[Succ, vs] : labels) {
          if (Succ == SW->getDefaultDest() || Succ->getUniquePredecessor() != &B) continue;
          Test t{SW->getCondition(), leaf, true, dOff, dOff};
          t.sw = true;
          t.caseVals = vs;
          edges.push_back({Succ, t});
        }
        const BasicBlock *Dflt = SW->getDefaultDest();
        if (!labels.count(Dflt) && Dflt->getUniquePredecessor() == &B) {
          Test t{SW->getCondition(), leaf, true, dOff, dOff};
          t.sw = t.swDefault = true;
          t.caseVals = all;
          edges.push_back({Dflt, t});
        }
      }
    }
    DominatorTree &DT = domOf(G);
    std::vector<PPUse> uses;
    // The uses: each reload of j's -O0 slot (its tests hold at all its
    // users), and each direct user of the argument (then no channel).
    auto testsAtBlock = [&](const Instruction *UI) {
      std::vector<Test> ts;
      for (const Edge &e : edges)
        if (DT.dominates(e.succ, UI->getParent())) ts.push_back(e.t);
      return ts;
    };
    for (const Value *V : *jv) {
      if (const auto *L = dyn_cast<LoadInst>(V)) { uses.push_back({L, testsAtBlock(L), true}); continue; }
      for (const User *U : V->users()) {
        const auto *UI = dyn_cast<Instruction>(U);
        if (!UI || isa<DbgInfoIntrinsic>(UI)) continue;
        if (const auto *St = dyn_cast<StoreInst>(UI); St && St->getValueOperand() == G->getArg(j) &&
                                                         isa<AllocaInst>(St->getPointerOperand()))
          continue; // the -O0 spill into its slot
        uses.push_back({UI, testsAtBlock(UI), false});
      }
    }
    return it->second = std::move(uses);
  };
  // At a read of F: its value passed as parameter j of a direct call, with
  // the same identity's D (through casts) as parameter k, both loads and
  // the call in one block with no write between: one test set per use of
  // j in the callee (an empty set: an untested use).
  std::map<std::pair<const Instruction *, int64_t>, std::optional<std::vector<std::vector<Test>>>> ppReadMemo;
  struct PPUseInfo { const CallBase *CB = nullptr; const Function *G = nullptr; unsigned j = 0, k = 0; int64_t dOff = 0;
                     std::vector<const Instruction *> uses; bool channelable = true; };
  std::map<std::pair<const Instruction *, int64_t>, PPUseInfo> ppUseInfo; // per pp read: its call and the callee's uses
  size_t ppKeyedReads = 0, ppUntestedReads = 0, ppChannelCallees = 0;
  auto ppTestsFor = [&](const Instruction *R, const Value *robj, const Field &Df)
      -> const std::optional<std::vector<std::vector<Test>>> & {
    auto [it, ins] = ppReadMemo.try_emplace({R, Df.second});
    if (!ins) return it->second;
    const Value *v = R;
    const CallBase *CB = nullptr;
    for (int d = 0; d < 4 && !CB; d++) {
      if (!v->hasOneUse()) return it->second;
      const User *U = *v->user_begin();
      if (const auto *C = dyn_cast<CallBase>(U)) CB = C;
      else if (isa<CastInst>(U)) v = U;
      else return it->second;
    }
    const Function *G = CB ? CB->getCalledFunction() : nullptr;
    if (!G || G->isDeclaration() || CB->getParent() != R->getParent()) return it->second;
    unsigned j = ~0u;
    for (unsigned a = 0; a < CB->arg_size(); a++) if (CB->getArgOperand(a) == v) j = a;
    if (j == ~0u || j >= G->arg_size()) return it->second;
    for (unsigned k = 0; k < CB->arg_size() && k < G->arg_size(); k++) {
      if (k == j || !CB->getArgOperand(k)->getType()->isIntegerTy()) continue;
      const Value *x = CB->getArgOperand(k);
      while (const auto *C = dyn_cast<CastInst>(x)) x = C->getOperand(0);
      const auto *LD = dyn_cast<LoadInst>(x);
      StructType *S2 = nullptr;
      int64_t o2 = 0;
      if (!LD || LD->getParent() != CB->getParent() ||
          !composedSlot(LD, LD->getPointerOperand(), LD->getModule()->getDataLayout(), S2, o2) || !S2 ||
          !S2->hasName() || stripStructNameSuffix(S2->getName()) != Df.first || o2 != Df.second ||
          !sameObj(objKey(LD, LD->getPointerOperand(), S2), robj, CB))
        continue;
      // No write between the earlier load and the call.
      const Instruction *first = LD->comesBefore(R) ? LD : R;
      bool clean = true;
      for (const Instruction *I = first->getNextNode(); I && I != CB; I = I->getNextNode())
        if (!isa<DbgInfoIntrinsic>(I) && I->mayWriteToMemory()) clean = false;
      if (!clean) continue;
      const auto &sum = ppSummary(G, k, j, Df.second);
      if (!sum) continue;
      std::vector<std::vector<Test>> sets;
      auto &ui = ppUseInfo[{R, Df.second}];
      ui.CB = CB;
      ui.G = G;
      ui.j = j;
      ui.k = k;
      ui.dOff = Df.second;
      for (const PPUse &u : *sum) ui.uses.push_back(u.use), ui.channelable &= u.channel;
      for (const PPUse &u : *sum) {
        std::vector<Test> ts = u.tests;
        for (Test &t : ts) t.argExpr = CB->getArgOperand(k), t.argLeaf = LD;
        sets.push_back(std::move(ts));
      }
      return it->second = std::move(sets);
    }
    return it->second;
  };
  // Can a callee use's tests (on its tag parameter) hold at a call whose
  // tag argument is E? E constant: evaluate. Otherwise, when the tests
  // name finite values (switch cases), each such value is checked against
  // the caller's tests on E's value that dominate the call (by integer
  // identity); any other shape may hold.
  auto mayHoldAtCall = [&](const CallBase *CB, const Value *E, const std::vector<Test> &T) -> bool {
    if (T.empty()) return true;
    const Value *e = E;
    while (const auto *C = dyn_cast<CastInst>(e)) e = C->getOperand(0);
    if (const auto *K = dyn_cast<ConstantInt>(E->stripPointerCasts()); K && K->getBitWidth() <= 64)
      return holds(T, K->getSExtValue());
    if (const auto *K = dyn_cast<ConstantInt>(e); K && K->getBitWidth() <= 64) return holds(T, K->getSExtValue());
    std::vector<int64_t> cands;
    for (const Test &t : T)
      if (t.sw && !t.swDefault) { cands = t.caseVals; break; }
    if (cands.empty()) return true;
    const Value *eid = ids.intId(e, 0);
    const Function *Fn = CB->getFunction();
    DominatorTree &DT = domOf(Fn);
    std::vector<Test> callerTests;
    for (const BasicBlock &BB : *Fn) {
      const auto *Br = dyn_cast<BranchInst>(BB.getTerminator());
      if (!Br || !Br->isConditional() || Br->getSuccessor(0) == Br->getSuccessor(1)) continue;
      // The condition's one leaf: E's value (same integer identity).
      const Instruction *leaf = nullptr;
      bool clean = true;
      std::vector<const Value *> work{Br->getCondition()};
      std::set<const Value *> seen;
      while (!work.empty() && clean) {
        const Value *X = work.back();
        work.pop_back();
        if (!seen.insert(X).second || isa<Constant>(X)) continue;
        if (const auto *XI = dyn_cast<Instruction>(X); XI && !isa<ICmpInst>(XI) && !isa<CastInst>(XI) &&
                                                       !isa<BinaryOperator>(XI)) {
          if (ids.intId(XI, 0) != eid) { clean = false; break; }
          if (leaf && leaf != XI) { clean = false; break; }
          leaf = XI;
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
      if (!clean || !leaf) continue;
      for (unsigned si = 0; si < 2; si++) {
        const BasicBlock *Succ = Br->getSuccessor(si);
        if (Succ->getUniquePredecessor() == &BB && DT.dominates(Succ, CB->getParent()))
          callerTests.push_back({Br->getCondition(), leaf, si == 0, 0, 0});
      }
    }
    for (int64_t v : cands)
      if (holds(T, v) && holds(callerTests, v)) return true;
    return false;
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
  // Return identity (plan 3.51, ruling Q2): the last writers of C.X of the
  // object a call returns, before the return, per return path; a path that
  // reaches the callee's entry with an argument as the returned pointer
  // continues before the call on that argument (retArgs). Recursion
  // through a return in progress is open.
  struct RetSum { Walk w; std::set<unsigned> retArgs; };
  std::function<const RetSum &(const FieldCtx &, const Function *)> retSumOf;
  std::function<Walk(const FieldCtx &, const Function *, const Value *, const Instruction *)> walkBackF;
  size_t retDefsClosed = 0, retDefsOpen = 0;
  // Out-parameter writes (plan 3.51, Mem.u): does H write through its
  // pointer parameter k on every return path (a store through it, or a
  // call handing it to a callee that does)? Recursion in progress: no.
  std::map<std::pair<const Function *, unsigned>, int> outMemo; // 0 busy, 1 yes, 2 no
  std::function<bool(const Function *, unsigned)> outMustWrite = [&](const Function *H, unsigned k) -> bool {
    auto [it, ins] = outMemo.try_emplace({H, k}, 0);
    if (!ins) return it->second == 1;
    if (H->isDeclaration() || k >= H->arg_size() || !H->getArg(k)->getType()->isPointerTy()) return (it->second = 2) == 1;
    const Value *P = H->getArg(k);
    bool all = true;
    for (const BasicBlock &RB : *H) {
      const auto *Ret = dyn_cast<ReturnInst>(RB.getTerminator());
      if (!Ret || !all) continue;
      std::set<const BasicBlock *> seen;
      std::vector<std::pair<const BasicBlock *, const Instruction *>> work{{&RB, Ret}};
      while (!work.empty() && all) {
        auto [B, I] = work.back();
        work.pop_back();
        bool done = false;
        for (; I && !done; I = I->getPrevNode()) {
          if (const auto *St = dyn_cast<StoreInst>(I); St && argId(St->getPointerOperand()) == P) done = true;
          else if (const auto *CB = dyn_cast<CallBase>(I); CB && CB->getCalledFunction())
            for (unsigned j = 0; j < CB->arg_size() && !done; j++)
              if (CB->getArgOperand(j)->getType()->isPointerTy() && argId(CB->getArgOperand(j)) == P &&
                  outMustWrite(CB->getCalledFunction(), j))
                done = true;
        }
        if (done) continue;
        if (B == &H->getEntryBlock() || seen.size() > 4000) { all = false; break; }
        for (const BasicBlock *Pb : predecessors(B))
          if (seen.insert(Pb).second) work.push_back({Pb, &Pb->back()});
      }
    }
    outMemo[{H, k}] = all ? 1 : 2;
    return all;
  };
  size_t outParamWrites = 0;
  // The last writers of field C.X of object `id` before `at` in Fn.
  size_t walksBack = 0, walksFwd = 0, walkBlocks = 0;
  std::map<const Function *, size_t> walkBlocksBy;
  // Per-path guards (plan 3.51, ruling i): edges (pred, succ) the
  // outermost walk does not cross (nested walks, in callees or summaries,
  // never see them).
  const std::set<std::pair<const BasicBlock *, const BasicBlock *>> *walkCuts = nullptr;
  std::set<std::pair<const BasicBlock *, const BasicBlock *>> walkCutsHit; // the cut edges an open path reached
  int walkDepth = 0;
  auto walkBack = [&](const FieldCtx &C, const Function *Fn, const Value *id, const Instruction *at) {
    walksBack++;
    struct Depth { int &d; Depth(int &x) : d(x) { d++; } ~Depth() { d--; } } depthGuard{walkDepth};
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
          stopped = true;
          // The object a direct call returns: the callee's return summary.
          const auto *RC = dyn_cast<CallBase>(I);
          const Function *RH = RC && I == id ? RC->getCalledFunction() : nullptr;
          if (!RH || RH->isDeclaration() || !RH->getReturnType()->isPointerTy()) {
            openWhy("the object's pointer is defined at " + locOf(I));
            continue;
          }
          const RetSum &RS = retSumOf(C, RH);
          R.W.insert(RS.w.W.begin(), RS.w.W.end());
          R.assumes.insert(RS.w.assumes.begin(), RS.w.assumes.end());
          if (RS.w.open) openWhy(RS.w.why);
          for (unsigned k : RS.retArgs) {
            if (k >= RC->arg_size()) { openWhy("a returned argument past the call's at " + locOf(I)); continue; }
            const Walk w2 = walkBackF(C, Fn, argId(RC->getArgOperand(k)), RC);
            R.W.insert(w2.W.begin(), w2.W.end());
            R.assumes.insert(w2.assumes.begin(), w2.assumes.end());
            if (w2.open) openWhy(w2.why);
            R.entry |= w2.entry;
          }
          (RS.w.open ? retDefsOpen : retDefsClosed)++;
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
        // F's own address handed to a callee that writes through it on
        // every path (sqlite3AtoF(z, &pMem->u.r, ..)): an F writer here.
        if (!C.isD)
          for (unsigned k = 0; k < CB->arg_size() && k < H->arg_size() && !must; k++) {
            const Value *A = CB->getArgOperand(k);
            StructType *S2 = nullptr;
            int64_t o2 = 0;
            if (!A->getType()->isPointerTy() || !structGEP(A) ||
                !composedSlot(CB, A, CB->getModule()->getDataLayout(), S2, o2) || !S2 || !S2->hasName() ||
                stripStructNameSuffix(S2->getName()) != C.X.first || o2 != C.X.second ||
                !sameObj(objKey(CB, A, S2), id, CB) || !outMustWrite(H, k))
              continue;
            outParamWrites++;
            must = true;
          }
        if (must) { stopped = true; continue; }
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
        if (walkCuts && walkDepth == 1 && walkCuts->count({P, B})) { walkCutsHit.insert({P, B}); continue; } // a guarded path
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
  walkBackF = walkBack;
  // Settled results are memoized; one computed while summaries are being
  // solved (they may still grow) is recomputed on each read.
  std::map<std::tuple<std::string, int64_t, const Function *>, RetSum> retMemo;
  std::set<std::tuple<std::string, int64_t, const Function *>> retBusy;
  std::deque<RetSum> retScratch; // unsettled results (stable addresses)
  retSumOf = [&](const FieldCtx &C, const Function *H) -> const RetSum & {
    const auto key = std::make_tuple(C.X.first, C.X.second, H);
    if (auto it = retMemo.find(key); it != retMemo.end()) return it->second;
    RetSum out;
    if (!retBusy.insert(key).second) {
      out.w.open = true;
      out.w.why = "recursion through the return of " + H->getName().str();
      retScratch.push_back(std::move(out));
      return retScratch.back();
    }
    const bool settled = !sumSolving;
    // The return paths: each return, or (-O0's one return of a %retval
    // slot) each store into the slot followed only by the branch to the
    // return block, which holds only the reload and the return.
    std::vector<std::pair<const Value *, const Instruction *>> paths; // (returned value, from)
    for (const BasicBlock &B : *H)
      if (const auto *Ret = dyn_cast<ReturnInst>(B.getTerminator())) {
        const Value *rv = Ret->getReturnValue();
        const auto *RL = rv ? dyn_cast<LoadInst>(rv) : nullptr;
        const auto *RA = RL ? dyn_cast<AllocaInst>(RL->getPointerOperand()) : nullptr;
        bool split = RA && RL->getParent() == &B;
        for (const Instruction &X : B)
          if (&X != RL && &X != Ret && !isa<DbgInfoIntrinsic>(X)) split = false;
        std::vector<const StoreInst *> sts;
        if (split)
          for (const User *U : RA->users()) {
            if (U == RL) continue;
            const auto *St = dyn_cast<StoreInst>(U);
            const auto *Br = St ? dyn_cast<BranchInst>(St->getNextNode()) : nullptr;
            if (!St || St->getPointerOperand() != RA || !Br || Br->isConditional() || Br->getSuccessor(0) != &B) {
              split = false;
              break;
            }
            sts.push_back(St);
          }
        if (split && !sts.empty())
          for (const StoreInst *St : sts) paths.push_back({St->getValueOperand(), St});
        else
          paths.push_back({rv, Ret});
      }
    for (auto [rv, from] : paths) {
      if (!rv || isa<ConstantPointerNull>(rv->stripPointerCasts())) continue; // no object
      const Value *rid = argId(rv);
      const Walk w = walkBack(C, H, rid, from);
      out.w.W.insert(w.W.begin(), w.W.end());
      out.w.assumes.insert(w.assumes.begin(), w.assumes.end());
      if (w.open && !out.w.open) out.w.why = w.why;
      out.w.open |= w.open;
      if (w.entry) {
        if (const auto *A = dyn_cast<Argument>(rid)) out.retArgs.insert(A->getArgNo());
        else if (!out.w.open) { out.w.open = true; out.w.why = "the object " + H->getName().str() + " returns, at its entry"; }
      }
    }
    retBusy.erase(key);
    if (settled) return retMemo[key] = std::move(out);
    retScratch.push_back(std::move(out));
    return retScratch.back();
  };
  // Can W's content be read before its object's D or F is rewritten?
  // 1: W's content can be read under the tag it found; 2: only mapped
  // from it (every path reaching a use of the found tag reaches a tag
  // write computed from it first; those writes in mapAt); 0: neither.
  auto observed = [&](const FieldCtx &Fc, const FieldCtx &Dc, const MayWrite &mrF,
                      const std::map<const Instruction *, const Value *> &reads, const Value *id,
                      const Instruction *W, std::set<uint32_t> &as, std::vector<const Instruction *> &mapAt) -> int {
    walksFwd++;
    std::set<const BasicBlock *> seen;
    std::vector<std::pair<const BasicBlock *, const Instruction *>> work{{W->getParent(), W->getNextNode()}};
    size_t blocks = 0;
    const Defs &idDefs = defsOf(id);
    while (!work.empty()) {
      auto [B, I] = work.back();
      work.pop_back();
      if (idDefs.blocks.count(B) && I == &B->front()) return 1; // the name becomes another object
      bool stopped = false;
      for (; I && !stopped; I = I->getNextNode()) {
        if (isa<ReturnInst>(I) || idDefs.insts.count(I)) return 1;
        if (auto rit = reads.find(I); rit != reads.end()) {
          if (sameObj(rit->second, id, I)) return 1;
          as.insert(assume(id, Fc.X, accessSet(Fc.X, '1', I), I)); // a read of another identity
          continue;
        }
        if (isa<UnreachableInst>(I)) { stopped = true; break; }
        if (auto dit = Dc.stores.find(I); dit != Dc.stores.end() && sameObj(dit->second, id, I)) {
          if (mapsOld(I)) mapAt.push_back(I); // the new tag is computed from the found one
          stopped = true;
          break;
        }
        if (auto fit = Fc.stores.find(I); fit != Fc.stores.end() && sameObj(fit->second, id, I)) { stopped = true; break; }
        const auto *CB = dyn_cast<CallBase>(I);
        if (!CB || isa<IntrinsicInst>(CB) || CB->isInlineAsm()) continue;
        const Function *H = CB->getCalledFunction();
        if (!H) {
          if (mrF.viaIndirect) as.insert(assume(id, Fc.X, accessSet(Fc.X, 'r', nullptr), I));
          continue;
        }
        if (H->isDeclaration()) {
          if (outsideRoots) return 1;
          continue;
        }
        bool mapped = false;
        for (unsigned k = 0; k < CB->arg_size() && k < H->arg_size(); k++)
          if (CB->getArgOperand(k)->getType()->isPointerTy() && argId(CB->getArgOperand(k)) == id) {
            mapped = true;
            if (mrF.fns.count(H)) return 1; // it may read it through the parameter
            const Walk &Sm = sumOf(Dc, H, k);
            if (!Sm.entry) {
              for (const Instruction *d : Sm.W)
                if (mapsOld(d)) mapAt.push_back(d); // its last write may compute from the found tag
              stopped = true; // the callee must-write D of it
              as.insert(Sm.assumes.begin(), Sm.assumes.end());
            }
          }
        if (!mapped && mrF.fns.count(H)) as.insert(assume(id, Fc.X, accessSet(Fc.X, 'r', H), I));
      }
      if (stopped) continue;
      for (const BasicBlock *N : successors(B)) {
        if (!seen.insert(N).second) continue;
        if (++blocks > kWalkBlocks) return 1;
        work.push_back({N, &N->front()});
      }
    }
    return mapAt.empty() ? 0 : 2;
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
  // Per-path guards (plan 3.51, ruling i). For a retag t of D with no
  // dominating test: the tests on its identity's own D in its function
  // whose successor edge is stable up to t (no D write of the object, no
  // call that may write D, no redefinition of the identity in the region
  // between the edge and t). Cutting all of them, if the F walk from t
  // closes, every open path crosses one: that path's guard is its edge's
  // test. Empty if not.
  size_t pathGuarded = 0, coFills = 0, censusSubsumed = 0;
  // Census member keys dropped for accesses over F's bytes: F's own, and
  // others that lose a member key without gaining a tag key.
  size_t censusDropF = 0, censusDropNotF = 0, censusReadsKept = 0;
  std::map<const Instruction *, std::string> tagPrefixOf; // tag-keyed accesses: their pair's key prefix
  std::map<const Instruction *, std::vector<std::string>> memberOf; // a tag-keyed read's census member key (P3)
  std::set<const Instruction *> uncheckedReplaced; // the census's UNCHECKED reads a tag pair keys
  std::map<const Instruction *, std::string> tagWriteOf; // writes of F keyed in both schemes: their pair's prefix
  auto pathGuards = [&](const TagStore &t, const Field &Df, const FieldCtx &Fc,
                        const FieldCtx &Dc) -> std::vector<Test> {
    const Function *Fn = t.I->getFunction();
    const Defs &idDefs = defsOf(t.obj);
    std::vector<Test> tests;
    std::vector<std::pair<const BasicBlock *, const BasicBlock *>> edgeOf; // per test
    std::set<std::pair<const BasicBlock *, const BasicBlock *>> cuts;
    auto writesD = [&](const Instruction &I) {
      if (&I == t.I) return false;
      if (idDefs.insts.count(&I)) return true;
      if (auto sit = Dc.stores.find(&I); sit != Dc.stores.end() && sameObj(sit->second, t.obj, &I)) return true;
      if (const auto *CB = dyn_cast<CallBase>(&I); CB && !isa<IntrinsicInst>(CB) && !CB->isInlineAsm()) {
        const Function *H = CB->getCalledFunction();
        return H ? (H->isDeclaration() ? outsideRoots : Dc.mw.fns.count(H) != 0) : Dc.mw.viaIndirect;
      }
      return false;
    };
    for (const FnTest &ft : fnTestsOf(Fn)) {
      if (isa<CallBase>(ft.dl) || ft.S != Df.first || ft.off != Df.second || !sameObj(ft.obj, t.obj, ft.Br))
        continue;
      for (unsigned si = 0; si < 2; si++) {
        const BasicBlock *TB = ft.Br->getParent(), *Succ = ft.Br->getSuccessor(si);
        if (ft.Br->getSuccessor(0) == ft.Br->getSuccessor(1)) continue;
        // The region from Succ to t (not back through the test block); an
        // edge into a join is cut as an edge, so Succ may have other
        // predecessors.
        std::set<const BasicBlock *> fwd{Succ}, reg;
        std::vector<const BasicBlock *> work{Succ};
        while (!work.empty()) {
          const BasicBlock *B = work.back();
          work.pop_back();
          if (B == t.I->getParent()) continue;
          for (const BasicBlock *N : successors(B))
            if (N != TB && fwd.insert(N).second) work.push_back(N);
        }
        if (!fwd.count(t.I->getParent())) continue;
        { // t's block on a cycle not through the test: t's own write comes between
          std::set<const BasicBlock *> cyc;
          std::vector<const BasicBlock *> w2(succ_begin(t.I->getParent()), succ_end(t.I->getParent()));
          bool loops = false;
          while (!w2.empty() && !loops) {
            const BasicBlock *B = w2.back();
            w2.pop_back();
            if (B == TB || !cyc.insert(B).second) continue;
            if (B == t.I->getParent()) loops = true;
            for (const BasicBlock *N : successors(B)) w2.push_back(N);
          }
          if (loops) continue;
        }
        work = {t.I->getParent()};
        reg.insert(t.I->getParent());
        while (!work.empty()) {
          const BasicBlock *B = work.back();
          work.pop_back();
          if (B == Succ) continue;
          for (const BasicBlock *P : predecessors(B))
            if (fwd.count(P) && reg.insert(P).second) work.push_back(P);
        }
        bool stable = true;
        for (const Instruction *I = ft.dl->getNextNode(); I && I != ft.Br && stable; I = I->getNextNode())
          stable = !writesD(*I);
        for (const BasicBlock *B : reg) {
          if (!stable) break;
          if (idDefs.blocks.count(B)) { stable = false; break; }
          for (const Instruction &I : *B) {
            if (B == t.I->getParent() && &I == t.I) break; // after t: t's block is not re-entered (fwd stops there)
            if (writesD(I)) { stable = false; break; }
          }
        }
        if (!stable) continue;
        cuts.insert({TB, Succ});
        edgeOf.push_back({TB, Succ});
        tests.push_back({ft.Br->getCondition(), ft.dl, si == 0, ft.off, Df.second});
      }
    }
    if (tests.empty()) return {};
    walkCuts = &cuts;
    walkCutsHit.clear();
    const Walk L = walkBack(Fc, Fn, t.obj, t.I);
    walkCuts = nullptr;
    if (L.open || L.entry) return {};
    // Only the edges open paths reach guard them (a closed path stops
    // before its edge and is a co-write).
    std::vector<Test> used;
    for (size_t q = 0; q < tests.size(); q++)
      if (walkCutsHit.count(edgeOf[q])) used.push_back(tests[q]);
    return used;
  };
  // Rule (iii): an 's' term is the tag that held at its load L. It is the
  // current tag at the store only when the load is in the store's function
  // and no write of D to the object, no call that may write D, and no
  // redefinition of the identity can come between them. Otherwise it is
  // the set that held at L: the last D writes before L when those are
  // closed and constant, else any tag of the field (an 'x' image).
  size_t sTermsKept = 0, sTermsAtLoad = 0, valueTests = 0;
  for (auto &[Dx, ts] : dStores) {
    const FieldCtx &Dc = ctxOf(Dx, true);
    for (TagStore &t : ts) {
      std::vector<Term> nt;
      bool changed = false;
      for (const Term &tm : t.terms) {
        if (tm.src != 's' || !tm.ld) { nt.push_back(tm); continue; }
        bool cur = !tm.ldMany && tm.ld->getFunction() == t.I->getFunction();
        if (cur) { // backward from the store to the load on every path
          const Defs &idDefs = defsOf(t.obj);
          std::set<const BasicBlock *> seen;
          std::vector<std::pair<const BasicBlock *, const Instruction *>> work{{t.I->getParent(), t.I->getPrevNode()}};
          while (!work.empty() && cur) {
            auto [B, I] = work.back();
            work.pop_back();
            bool reached = false;
            for (; I && cur; I = I->getPrevNode()) {
              if (I == tm.ld) { reached = true; break; }
              if (idDefs.insts.count(I)) cur = false;
              else if (auto sit = Dc.stores.find(I); sit != Dc.stores.end() && sameObj(sit->second, t.obj, I)) cur = false;
              else if (const auto *CB = dyn_cast<CallBase>(I); CB && !isa<IntrinsicInst>(CB) && !CB->isInlineAsm()) {
                const Function *H = CB->getCalledFunction();
                if (H ? (H->isDeclaration() ? outsideRoots : Dc.mw.fns.count(H) != 0) : Dc.mw.viaIndirect) cur = false;
              }
            }
            if (reached || !cur) continue;
            if (idDefs.blocks.count(B) || B == &B->getParent()->getEntryBlock()) { cur = false; break; }
            for (const BasicBlock *P : predecessors(B))
              if (seen.insert(P).second) work.push_back({P, &P->back()});
          }
        }
        if (cur) { nt.push_back(tm); sTermsKept++; continue; }
        changed = true;
        sTermsAtLoad++;
        // The set at L: the last D writes of the identity read at L.
        const Walk LD = walkBack(Dc, tm.ld->getFunction(), tm.who, tm.ld);
        bool constant = !LD.open && !LD.entry && !LD.W.empty();
        std::vector<int64_t> vals;
        for (const Instruction *d : LD.W) {
          auto it = tagStoreAt.find(d);
          if (it == tagStoreAt.end() || it->second->unknown) { constant = false; break; }
          std::set<int64_t> cs;
          for (const Term &u : it->second->terms)
            if (u.src != 'c' || !concretize({u}, cs)) { constant = false; break; }
          if (!constant) break;
          vals.insert(vals.end(), cs.begin(), cs.end());
        }
        // Value tests (ruling, round 3): a test on the value loaded at L (a
        // reload of the slot it was stored to, or the load itself) is a
        // fact about that value, whatever D does after. Per path from L to
        // the store: the tests of the edges it crosses (cut and walked as
        // for per-path guards); a path crossing none keeps the whole set.
        std::vector<int> filters; // -1: unfiltered
        {
          const Function *Fn = t.I->getFunction();
          std::vector<std::pair<std::pair<const BasicBlock *, const BasicBlock *>, Test>> edges;
          if (tm.ld->getFunction() == Fn && !tm.ldMany)
            for (const BasicBlock &BB : *Fn) {
              const auto *Br = dyn_cast<BranchInst>(BB.getTerminator());
              if (!Br || !Br->isConditional() || Br->getSuccessor(0) == Br->getSuccessor(1)) continue;
              // The condition's one leaf: the loaded value, or its reload.
              const Instruction *leaf = nullptr;
              bool clean = true;
              std::vector<const Value *> work{Br->getCondition()};
              std::set<const Value *> seen;
              while (!work.empty() && clean) {
                const Value *X = work.back();
                work.pop_back();
                if (!seen.insert(X).second || isa<Constant>(X)) continue;
                const Instruction *XI = dyn_cast<Instruction>(X);
                bool isVal = XI == tm.ld;
                if (const auto *R = dyn_cast<LoadInst>(X); R && !isVal)
                  if (const auto *A = dyn_cast<AllocaInst>(R->getPointerOperand()->stripPointerCasts());
                      A && ids.storedInto(A)) {
                    const ObjIds::SlotInfo &SI = ids.slot(A);
                    if (auto dit = SI.def.find(R); dit != SI.def.end()) {
                      const Value *sv = dit->second->getValueOperand();
                      while (const auto *C = dyn_cast<CastInst>(sv)) sv = C->getOperand(0);
                      isVal = sv == tm.ld;
                    }
                  }
                if (isVal) { if (leaf && leaf != XI) clean = false; leaf = XI; continue; }
                if (isa<ICmpInst>(X) || isa<CastInst>(X) ||
                    (isa<BinaryOperator>(X) && (cast<BinaryOperator>(X)->getOpcode() == Instruction::And ||
                                                cast<BinaryOperator>(X)->getOpcode() == Instruction::Or ||
                                                cast<BinaryOperator>(X)->getOpcode() == Instruction::Xor))) {
                  for (const Value *Op : cast<User>(X)->operands()) work.push_back(Op);
                  continue;
                }
                clean = false;
              }
              if (!clean || !leaf) continue;
              for (unsigned si = 0; si < 2; si++)
                edges.push_back({{&BB, Br->getSuccessor(si)},
                                 Test{Br->getCondition(), leaf, si == 0, Dx.second, Dx.second}});
            }
          // Walk back from the store to L with the test edges cut.
          std::set<std::pair<const BasicBlock *, const BasicBlock *>> cut, hit;
          for (auto &e : edges) cut.insert(e.first);
          bool plain = false;
          if (tm.ld->getFunction() != Fn) plain = true;
          else if (tm.ld->getParent() == t.I->getParent() && tm.ld->comesBefore(t.I)) plain = true;
          else {
            std::set<const BasicBlock *> seenB{t.I->getParent()};
            std::vector<const BasicBlock *> work{t.I->getParent()};
            while (!work.empty() && !plain) {
              const BasicBlock *B = work.back();
              work.pop_back();
              for (const BasicBlock *P : predecessors(B)) {
                if (cut.count({P, B})) { hit.insert({P, B}); continue; }
                if (P == tm.ld->getParent()) { plain = true; break; }
                if (seenB.insert(P).second) work.push_back(P);
              }
            }
          }
          if (plain || edges.empty()) filters.push_back(-1);
          // A path whose stretches from L to its test and from the edge to
          // the store hold no D write of the object (nor a call that may
          // write D, nor a redefinition) keeps the current tag there: the
          // own-tag map, unchanged.
          const Defs &idDefs = defsOf(t.obj);
          auto writesD = [&](const Instruction &I) {
            if (&I == t.I) return false;
            if (idDefs.insts.count(&I)) return true;
            if (auto sit = Dc.stores.find(&I); sit != Dc.stores.end() && sameObj(sit->second, t.obj, &I)) return true;
            if (const auto *CB = dyn_cast<CallBase>(&I); CB && !isa<IntrinsicInst>(CB) && !CB->isInlineAsm()) {
              const Function *H = CB->getCalledFunction();
              return H ? (H->isDeclaration() ? outsideRoots : Dc.mw.fns.count(H) != 0) : Dc.mw.viaIndirect;
            }
            return false;
          };
          auto currentOn = [&](const BasicBlock *TB, const BasicBlock *Succ) {
            if (tm.ld->getParent() != TB) return false;
            for (const Instruction *I = tm.ld->getNextNode(); I; I = I->getNextNode())
              if (writesD(*I)) return false;
            std::set<const BasicBlock *> fwd{Succ}, reg;
            std::vector<const BasicBlock *> w{Succ};
            while (!w.empty()) {
              const BasicBlock *B = w.back();
              w.pop_back();
              if (B == t.I->getParent()) continue;
              for (const BasicBlock *N : successors(B))
                if (N != TB && fwd.insert(N).second) w.push_back(N);
            }
            if (!fwd.count(t.I->getParent())) return false;
            w = {t.I->getParent()};
            reg.insert(t.I->getParent());
            while (!w.empty()) {
              const BasicBlock *B = w.back();
              w.pop_back();
              if (B == Succ) continue;
              for (const BasicBlock *P : predecessors(B))
                if (fwd.count(P) && reg.insert(P).second) w.push_back(P);
            }
            for (const BasicBlock *B : reg) {
              if (idDefs.blocks.count(B)) return false;
              for (const Instruction &I : *B) {
                if (B == t.I->getParent() && &I == t.I) break;
                if (writesD(I)) return false;
              }
            }
            return true;
          };
          for (auto &e : edges)
            if (hit.count(e.first)) {
              if (currentOn(e.first.first, e.first.second)) { filters.push_back(-2); continue; } // current here
              filters.push_back((int)termFilters.size());
              termFilters.push_back({e.second});
              valueTests++;
            }
          if (filters.empty()) filters.push_back(-1);
        }
        bool keptCurrent = false;
        for (int fi : filters) {
          if (fi == -2) { // the own-tag map holds on this path
            if (!keptCurrent) nt.push_back(tm), keptCurrent = true;
            continue;
          }
          if (constant)
            for (int64_t v : vals) {
              if (fi >= 0 && !holds(termFilters[fi], v)) continue; // the value test rejects it on this path
              const int64_t f = (v & tm.a) | tm.f;
              Term c{'c', 0, f, tm.m & ~f};
              c.xm = tm.xm & ~f;
              nt.push_back(c);
            }
          else {
            Term x{'x', tm.a, tm.f, tm.m};
            x.xm = tm.xm;
            x.flt = fi;
            nt.push_back(x);
          }
        }
      }
      if (changed) t.terms = std::move(nt);
    }
  }
  // x-masks (plan 3.51): a term's bits taken from another object's tag of
  // the field are the projection of U, every value the field holds in the
  // program: the least fixpoint of its constants (0, memset fills, 'c'
  // terms) under every tag write's maps, guards ignored (a superset). Each
  // x-masked term becomes one term per projected value; if U widens (past
  // 4096 values or a map with too many free bits), the bits are free.
  size_t xmTerms = 0, xmFieldsWide = 0;
  std::vector<std::string> xmFieldSizes;
  for (auto &[Dx, ts] : dStores) {
    bool any = false;
    for (const TagStore &t : ts) for (const Term &tm : t.terms) any |= tm.xm != 0;
    if (!any) continue;
    unsigned w = 0;
    for (const TagStore &t : ts) w = widthOf(t.I->getValueOperand()->getType());
    const int64_t wm = w >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << w) - 1);
    // Maps are bitwise, so U's projection onto a mask X is the fixpoint of
    // the projected constants under the projected maps: computed per mask,
    // at most 2^|X| values.
    std::string whyWide;
    std::set<int64_t> fills{0};
    if (auto fit = fillsOf.find(Dx.first); fit != fillsOf.end())
      for (const Fill &f : fit->second)
        if (f.lo < Dx.second + (int64_t)(w / 8) && Dx.second < f.hi) {
          if (f.fill < 0) { whyWide = "a non-constant memset"; break; }
          int64_t v = 0;
          for (unsigned k = 0; k < w / 8; k++) v = (v << 8) | f.fill;
          fills.insert(v & wm);
        }
    for (const TagStore &t : ts)
      if (t.unknown && whyWide.empty()) whyWide = "an unevaluable tag write at " + locOf(t.I);
    std::map<int64_t, std::optional<std::set<int64_t>>> projOf; // mask -> U & mask (none: widened)
    auto projection = [&](int64_t X) -> const std::optional<std::set<int64_t>> & {
      auto [it, ins] = projOf.try_emplace(X);
      if (!ins) return it->second;
      if (!whyWide.empty() || llvm::popcount((uint64_t)X) > 12) return it->second;
      std::set<int64_t> P;
      for (int64_t v : fills) P.insert(v & X);
      for (bool grew = true; grew;) {
        grew = false;
        const std::set<int64_t> cur = P;
        for (const TagStore &t : ts)
          for (const Term &tm : t.terms) {
            const int64_t a = tm.a & X, f = tm.f & X, m = tm.m & X, xm = tm.xm & X;
            if (llvm::popcount((uint64_t)(m | xm)) > 12) return it->second; // too free to enumerate
            std::vector<int64_t> ins;
            if (tm.src == 'c') ins.push_back(0);
            else ins.assign(cur.begin(), cur.end());
            const uint64_t fr = (uint64_t)m;
            const std::set<int64_t> none{0};
            for (int64_t v : ins)
              for (int64_t x : xm ? cur : none) // another object's bits: some value of the field
                for (uint64_t sub = fr;; sub = (sub - 1) & fr) {
                  if (P.insert(((tm.src == 'c' ? 0 : v & a) | f | (int64_t)sub | (x & xm)) & X).second) grew = true;
                  if (!sub) break;
                }
          }
      }
      return it->second = std::move(P);
    };
    bool wide = false;
    std::string sizes;
    std::set<int64_t> masks;
    for (const TagStore &t : ts) for (const Term &tm : t.terms) if (tm.xm) masks.insert(tm.xm);
    for (int64_t X : masks) {
      const auto &P = projection(X);
      if (!P) wide = true;
      sizes += " mask 0x" + utohexstr((uint64_t)X) + ": " + (P ? std::to_string(P->size()) : std::string("widened"));
    }
    if (wide && whyWide.empty()) whyWide = "a projection too free to enumerate";
    xmFieldsWide += wide;
    xmFieldSizes.push_back(Dx.first + "+" + std::to_string(Dx.second) + ":" + sizes +
                           (whyWide.empty() ? "" : " (" + whyWide + ")"));
    if (wide)
      widenedTagsOf[Dx.first].push_back("tag " + Dx.first + "+" + std::to_string(Dx.second) + " widened" +
                                        (whyWide.empty() ? "" : " (" + whyWide + ")"));
    for (TagStore &t : ts) {
      std::vector<Term> nt;
      for (const Term &tm : t.terms) {
        if (!tm.xm) { nt.push_back(tm); continue; }
        xmTerms++;
        const auto &P = projection(tm.xm);
        if (!P || P->size() > 64) {
          Term r = tm;
          r.m |= r.xm;
          r.xm = 0;
          nt.push_back(r);
          continue;
        }
        for (int64_t x : *P) {
          Term r = tm;
          r.f |= x;
          r.m &= ~x;
          r.xm = 0;
          nt.push_back(r);
        }
      }
      t.terms = std::move(nt);
    }
  }
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
    // Products: an integer tag (at most 32 bits, so a function-pointer
    // tag's values, below 2^31, fit above it) with a function-pointer tag, where a read
    // is tested by a predicate of both.
    struct ProdReads { int64_t virt; std::vector<std::pair<const Instruction *, std::vector<Test>>> reads; std::set<uint32_t> as; };
    std::vector<ProdReads> fProds;
    std::set<int64_t> prodNeed;
    std::set<const Instruction *> prodRead;
    for (int64_t d1 : dOffs) {
      const auto &s1 = dStores[{S, d1}];
      if (fnFields.count({S, d1}) || s1.empty() || widthOf(s1.front().I->getValueOperand()->getType()) > 32) continue;
      for (int64_t d2 : dOffs) {
        if (!fnFields.count({S, d2})) continue;
        auto [pit, pins] = prodIdx.try_emplace({S, d1, d2}, -1 - (int64_t)prods.size());
        if (pins) prods.push_back({d1, d2, widthOf(s1.front().I->getValueOperand()->getType())});
        ProdReads PRs{pit->second, {}, {}};
        for (const FAccess &r : fLoads[Ff]) {
          std::vector<Test> tt;
          testsAtM(r.I, r.obj, {S, pit->second}, Ff, tt, PRs.as);
          if (!tt.empty()) PRs.reads.push_back({r.I, std::move(tt)}), prodRead.insert(r.I);
        }
        if (PRs.reads.empty()) continue;
        prodNeed.insert(d1);
        prodNeed.insert(d2);
        fProds.push_back(std::move(PRs));
      }
    }
    // Per tag field (or product) that keys reads: the writers it names
    // (a known tag) and each read's admitted writers; a read keyed by
    // several admits their intersection (each a sound superset). Writer
    // keys do not name the tag, so every read's list refers to the same
    // cells.
    struct CompRes { std::vector<bool> any; std::vector<std::set<int64_t>> vals; std::vector<std::optional<KnownBits>> kb; std::set<uint32_t> as; };
    std::map<int64_t, CompRes> comps; // the components of products
    std::map<const Instruction *, std::vector<size_t>> readAdm;
    // Plan 3.54: a read's entry-test admissions, per field its method is
    // entered by: their union (an entry through D's site has D == M); a
    // field admitting every writer makes the union every writer (entryAll).
    // byTerm (plan 3.54 (b)): per field, per method X of it, the writers
    // a test D == X admits (absent: every writer).
    struct EntryAdm {
      std::pair<const Function *, unsigned> fn;
      std::set<int64_t> fields;
      std::set<size_t> adm;
      std::map<int64_t, std::map<const Function *, std::vector<size_t>>> byTerm;
    };
    std::map<const Instruction *, EntryAdm> entryAdm;
    std::set<const Instruction *> entryAll;
    std::vector<bool> namedW(fs.size(), false);
    std::vector<std::string> unknownWhy(fs.size()); // an untagged writer: why its tag is unknown (reports)
    std::vector<TaggedPair> fPairs;
    std::vector<std::set<uint32_t>> fPairAs;
    std::vector<std::string> fDims;
    // pp read -> (per use: admitted writers; its call and the callee's uses)
    std::map<const Instruction *, std::pair<std::vector<std::vector<size_t>>, const PPUseInfo *>> ppPerUse;
    auto keyRead = [&](const Instruction *I, std::vector<size_t> adm) {
      auto [it, ins] = readAdm.try_emplace(I, std::move(adm));
      if (ins) return;
      std::vector<size_t> both;
      std::set_intersection(it->second.begin(), it->second.end(), adm.begin(), adm.end(), std::back_inserter(both));
      it->second = std::move(both);
    };
    std::set<const Instruction *> anyTest(prodRead.begin(), prodRead.end()); // reads some tag test guards
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
        std::vector<Term> topMaps;  // maps of an unknown found tag (mapped, never read, from an open tag)
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
        // A read whose value goes to a callee testing its tag parameter.
        bool pp = false;
        if (tt.empty())
          if (const auto &ps = ppTestsFor(r.I, r.obj, Df); ps) {
            pp = !ps->empty();
            for (const auto &u : *ps) pp &= !u.empty();
          }
        if (!tt.empty() || pp || (prodNeed.count(dOff) && prodRead.count(r.I))) tested[r.I] = r.obj, testedV.push_back(r.I);
        if (!tt.empty() || pp) anyTest.insert(r.I);
      }
      if (tested.empty()) { // no read with a stable test: no read can be keyed
        readsNoTest += fLoads[Ff].size();
        continue;
      }
      MayWrite mrF;
      closureOf(testedV, mrF);
      struct Obs { int r = 0; std::set<uint32_t> as; std::vector<const Instruction *> mapAt; };
      std::map<std::pair<const Instruction *, const Value *>, Obs> obsMemo;
      auto obsFull = [&](const Value *id, const Instruction *W, std::set<uint32_t> &as) -> const Obs & {
        auto [it, ins] = obsMemo.try_emplace({W, id});
        if (ins) it->second.r = observed(Fc, Dc, mrF, tested, id, W, it->second.as, it->second.mapAt);
        as.insert(it->second.as.begin(), it->second.as.end());
        return it->second;
      };
      auto obsM = [&](const Value *id, const Instruction *W, std::set<uint32_t> &as) { return obsFull(id, W, as).r != 0; };
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
      size_t closedStores = 0, openStores = 0, observedWriters = 0, openPrior = 0, mappedFromOpen = 0;
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
          openWhyOf[&t] = (L.open ? L.why : std::string("the function entry (F from before it)")) +
                          "; F writers on other paths: " + std::to_string(L.W.size());
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
          else if (const std::vector<Test> pg = pathGuards(t, Df, Fc, Dc); !pg.empty()) {
            // Guarded per path: each open path's map under its edge's test
            // (a constant under a guard is a map with no input bits).
            pathGuarded++;
            for (const Term &q : t.terms)
              for (const Test &T : pg) {
                R.maps.push_back(q.src == 'c' ? Term{'s', 0, q.f, q.m} : q);
                R.guards.push_back(q.src == 'x' ? std::vector<Test>{} : std::vector<Test>{T});
              }
            continue;
          }
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
      size_t effSites = 0, effAbsorbed = 0, effUnseen = 0;
      std::string effOpenSite; // the first open effect that retags (the row's site)
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
          loopLimitAt.push_back("content effects of " + Df.first + "+" + std::to_string(Df.second) + " (12 rounds)");
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
            // As for a tag store: a callee that can execute no tested read
            // of F, after which the content is never read under the tag it
            // leaves (D or F rewritten first on every path), meets no
            // content: its effect gives nothing and retags nothing (a
            // cleanup restoring a saved method, then freeing the state).
            {
              std::set<uint32_t> a2;
              // Mapped only (2): every path meets a tag write computed from
              // the left tag first; when each of those writes is itself
              // never read under, the chain meets no content either.
              auto unseen = [&](const Obs &ob) {
                if (ob.r == 0) return true;
                if (ob.r != 2) return false;
                for (const Instruction *d : ob.mapAt) {
                  auto tit = tagStoreAt.find(d);
                  if (tit == tagStoreAt.end() || obsFull(tit->second->obj, d, a2).r != 0) return false;
                }
                return true;
              };
              if (!mrF.fns.count(G) && unseen(obsFull(argId(CB->getArgOperand(k)), CB, a2))) {
                effUnseen++;
                pas.insert(a2.begin(), a2.end());
                continue;
              }
            }
            effSites++;
            (E.open ? effOpen : effClosed)++;
            if (E.open) effOpenAt.push_back({CB, locOf(CB) + " -> " + G->getName().str()});
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
            if (E.open && effOpenSite.empty()) effOpenSite = locOf(CB) + " -> " + G->getName().str();
            effMaps.insert(effMaps.end(), E.maps.begin(), E.maps.end());
            effGuards.insert(effGuards.end(), E.guards.begin(), E.guards.end());
            for (size_t q = 0; q < E.maps.size(); q++) effLab.push_back("call " + locOf(CB) + " -> " + G->getName().str());
          }
        }
      }
      nonConstRetag |= effUnknownRetag;
      for (size_t i = 0; i < writers.size(); i++) {
        const FAccess &w = fs[i];
        const Obs &ob = obsFull(w.obj, w.I, pas);
        if (!ob.r) continue;
        observedWriters++;
        const Walk LD = walkBackM(Dc, w.I->getFunction(), w.obj, w.I);
        pas.insert(LD.assumes.begin(), LD.assumes.end());
        if ((LD.open || LD.entry) && ob.r == 2) {
          // Only mapped from an open tag: the content is read under the
          // mapping writes' images of an unknown tag.
          const Instruction *firstOpen = nullptr; // in IR order: mapAt follows a pointer set
          for (const Instruction *d : ob.mapAt)
            if (tagStoreAt.at(d)->unknown && (!firstOpen || irOrderLess(d, firstOpen))) firstOpen = d;
          if (firstOpen && !writers[i].unknown) writers[i].why = "mapped by an unevaluable tag write at " + locOf(firstOpen);
          for (const Instruction *d : ob.mapAt) {
            const TagStore *t = tagStoreAt.at(d);
            if (t->unknown) writers[i].unknown = true;
            for (const Term &tm : t->terms)
              if (tm.src == 'c') { if (!concretize({tm}, writers[i].tags)) writers[i].unknown = true; }
              else if (tm.src == 's') writers[i].topMaps.push_back(tm);
              else writers[i].fromAny.push_back(tm);
          }
          mappedFromOpen++;
          continue;
        }
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
      for (const TagStore &t : ds) dWidth = widthOf(t.I->getValueOperand()->getType());
      const int64_t dBytes = dWidth / 8;
      std::set<const Instruction *> own;
      for (const TagStore &t : ds) own.insert(t.I);
      const Instruction *coveredBy = nullptr;
      auto coveredIn = [&](const std::string &SN, int64_t lo, int64_t hi) {
        if (auto cit = covers.find(SN); cit != covers.end())
          for (const Cover &c : cit->second)
            // An own write: exactly D, or a vector store with D as a lane.
            if (c.lo < hi && lo < c.hi &&
                !(own.count(c.I) && c.lo <= lo && hi <= c.hi && ((c.lo == lo && c.hi == hi) ||
                                                               (lo - c.lo) % (hi - lo) == 0))) {
              coveredBy = c.I;
              return;
            }
      };
      coveredIn(S, dOff, dOff + dBytes);
      // D in an embedded struct (plan 3.54 (a)): a store named by the
      // embedded struct alone covers it too.
      if (!coveredBy && !ds.empty()) {
        const auto *TI = cast<StoreInst>(ds.front().I);
        const DataLayout &TDL = TI->getModule()->getDataLayout();
        StructType *STy = nullptr;
        int64_t o = 0;
        if (composedSlot(TI, TI->getPointerOperand(), TDL, STy, o) && STy)
          structCover(STy, dOff, dOff + dBytes, TDL, [&](StructType *ST2, int64_t l, int64_t h) {
            const std::string N2 = stripStructNameSuffix(ST2->getName()).str();
            if (N2 != S && !coveredBy) coveredIn(N2, l, h);
          });
      }
      const std::string *escAt = escapedOver(S, dOff, dOff + std::max<int64_t>(dBytes, 1));
      if (coveredBy || storesUnwatchable || escAt) {
        pairsUncertified++;
        if (fs.size() >= 10)
          taggedReport.push_back("UNKEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                                 std::to_string(dOff) + ": tag not certified (" +
                                 (escAt ? "its address escapes at " + *escAt
                                  : coveredBy ? "an unnamed or wider store covers it at " + locOf(coveredBy)
                                              : "a store with no watchable pointer, e.g. " + unwatchableAt) + ")");
        continue;
      }
      // memset fills that may cover the tag: constant retags, or (a
      // non-constant fill) an unevaluable one.
      std::set<int64_t> pairFills;
      std::vector<std::string> fillAt; // reports: fills retagging the field
      const Instruction *fillUnknownAt = nullptr;
      if (auto fit = fillsOf.find(S); fit != fillsOf.end())
        for (const Fill &f : fit->second)
          if (f.lo < dOff + dBytes && dOff < f.hi) {
            // A fill covering all of F and D is a co-write: F's content
            // becomes bytes (no pointer), so no writer's content is read
            // under the filled tag through this object.
            if (f.lo <= Ff.second && Ff.second + 8 <= f.hi && f.lo <= dOff && dOff + dBytes <= f.hi) {
              coFills++;
              continue;
            }
            if (f.fill < 0) { if (!fillUnknownAt) fillUnknownAt = f.I; }
            else {
              pairFills.insert(f.fill);
              if (fillAt.size() < 8)
                fillAt.push_back(locOf(f.I) + " [" + std::to_string(f.lo) + "," + std::to_string(f.hi) + ") byte " +
                                 std::to_string(f.fill));
            }
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
                                 " writes): non-constant retag at " +
                                 (at ? locOf(at) : "the call " + effOpenSite + " (an open effect)") + " (" +
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
      std::vector<std::pair<const Instruction *, std::string>> inPlaceHere; // unguarded open retags (rule row)
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
        // Per-path guards: when no test dominates the retag, the tests on
        // its own D whose edges every open path crosses (cutting them
        // closes the F walk); each path's guard is the test on its edge.
        std::vector<Test> pg;
        {
          std::vector<Test> dom;
          std::vector<std::vector<Term>> E2;
          std::set<uint32_t> a2;
          testsAtM(t->I, t->obj, Df, Ff, dom, a2, &E2);
          if (dom.empty()) pg = pathGuards(*t, Df, Fc, Dc);
        }
        if (!pg.empty()) {
          pathGuarded++;
          for (const Term &tm : t->terms) {
            if (tm.src == 'x') { anyImgs.push_back(tm); continue; }
            const Term mp = tm.src == 's' ? tm : Term{'s', 0, tm.f, tm.m};
            for (const Test &T : pg)
              xforms.push_back(mp), xformGuard.push_back({T}),
                  xformLab.push_back(locOf(t->I) + " guarded per path (" + locOf(T.d) + ")");
          }
          if (VerboseLevel >= 2) {
            std::string d = locOf(t->I) + " {";
            for (const Term &tm : t->terms) d += std::string(d.back() == '{' ? "" : ", ") + termStr(tm);
            allRetagAt.push_back(d + "} [guarded per path by " + std::to_string(pg.size()) + " tests]");
          }
          continue;
        }
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
          if (g.empty()) {
            std::string mp = "{";
            for (const Term &tm : t->terms) mp += std::string(mp.size() > 1 ? ", " : "") + termStr(tm);
            inPlaceHere.push_back({t->I, mp + "}"});
          }
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
          allRetagAt.push_back(d + "} [" + openWhyOf[t] + "]");
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
        // A function-pointer tag: NULL, -1, or a pointer equal to no
        // function and no small constant.
        if (fnFields.count(Df)) v = b == 0 ? 0 : b == 0xff ? kAllOnes : kAllOnes - 1;
        sets.insert(v);
      }
      // Projection (precision only): tag sets may be computed on the bits a
      // read's tests observe, R; tests and guards are then judged with the
      // other bits unknown (may hold), which is sound for any R, and every
      // map is bitwise, so it commutes with the projection. Used when the
      // full-width sets widen: each read gets the sets for its own R.
      std::vector<std::string> wideTests, witnessLines;
      const int64_t wmask = dWidth >= 64 ? (int64_t)-1 : (int64_t)((uint64_t(1) << dWidth) - 1);
      auto observedBits = [&](const std::vector<Test> &g0) -> int64_t {
        int64_t r = 0;
        std::vector<Test> g; // a set test's alternatives each
        for (const Test &t : g0)
          if (t.anyOf.empty()) g.push_back(t);
          else g.insert(g.end(), t.anyOf.begin(), t.anyOf.end());
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
              if (auto c = constOf(X)) r |= *c;
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
      auto addImages = [&](TagSet &T, const TagSet &FromAll, const Term &t) {
        // A filtered image: only source tags its test admits.
        TagSet filtered;
        const TagSet *fp = &FromAll;
        if (t.flt >= 0) {
          const std::vector<Test> &g = termFilters[t.flt];
          if (FromAll.wide) {
            if (FromAll.kb.hasConflict() || !mayHold(g, FromAll.kb)) return;
          } else {
            for (int64_t v : FromAll.vals) if (holdsP(g, v)) filtered.vals.insert(v);
            fp = &filtered;
          }
        }
        const TagSet &From = *fp;
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
      // Guard results, cached by (guard content, tag, projection): the same
      // guards meet the same tags in every closure.
      struct PairHash {
        size_t operator()(const std::tuple<uint64_t, int64_t, int64_t> &k) const {
          return std::hash<uint64_t>()(std::get<0>(k) * 1000003u ^ (uint64_t)std::get<1>(k) * 7919u ^
                                       (uint64_t)std::get<2>(k));
        }
      };
      std::unordered_map<std::tuple<uint64_t, int64_t, int64_t>, bool, PairHash> guardCache;
      auto guardSig = [](const std::vector<Test> &g) {
        uint64_t h = 1469598103934665603ull;
        for (const Test &t : g) h = (h ^ (uint64_t)(uintptr_t)t.cond ^ (t.onTrue ? 0x9e3779b97f4a7c15ull : 0)) * 1099511628211ull;
        return h;
      };
      auto closure = [&](TagSet &T, const std::vector<Term> &maps, const std::vector<std::vector<Test>> *guards) {
        auto guarded = [&](size_t mi) { return guards && mi < guards->size() && !(*guards)[mi].empty(); };
        std::vector<uint64_t> gsig(maps.size(), 0);
        for (size_t mi = 0; mi < maps.size(); mi++) if (guarded(mi)) gsig[mi] = guardSig((*guards)[mi]);
        auto admits = [&](size_t mi, int64_t v) {
          auto [it, ins] = guardCache.try_emplace({gsig[mi], v, curR}, false);
          if (ins) it->second = holdsP((*guards)[mi], v);
          return it->second;
        };
        if (!T.wide) {
          std::vector<int64_t> work(T.vals.begin(), T.vals.end());
          while (!work.empty() && !T.wide) {
            const int64_t v = work.back();
            work.pop_back();
            for (size_t mi = 0; mi < maps.size() && !T.wide; mi++) {
              const Term &t = maps[mi];
              if (guarded(mi) && !admits(mi, v)) continue;
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
      const bool provOn = (VerboseLevel >= 2 && fs.size() >= 20) || !CFLRuleReport.empty();
      std::map<int64_t, Tags> tagsByR;
      std::vector<bool> wAll(writers.size(), false);
      for (size_t i = 0; i < writers.size(); i++) wAll[i] = writers[i].unknown;
      auto computeTags = [&](int64_t R) -> const Tags & {
        auto [it, ins] = tagsByR.try_emplace(R);
        if (!ins) return it->second;
        tagsComputes++;
        const auto t0c = std::chrono::steady_clock::now();
        struct Timer { double &acc; std::chrono::steady_clock::time_point t; ~Timer() { acc += std::chrono::duration<double>(std::chrono::steady_clock::now() - t).count(); } } tm{tagsSecs, t0c};
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
        for (size_t q = 0; q < ai.size(); q++) // a filtered image applies to admitted tags only
          if (ai[q].flt >= 0) allGuards[allGuards.size() - ai.size() + q] = termFilters[ai[q].flt];
        for (const Writer &W : writers) {
          for (int64_t v : W.tags) add(U, pv(v));
          for (const Term &t : W.fromAny) allMaps.push_back(pt(t));
          allGuards.resize(allMaps.size());
          for (const Term &t : W.ownMaps) allMaps.push_back(pt(t));
          allGuards.insert(allGuards.end(), W.ownGuards.begin(), W.ownGuards.end());
        }
        closure(U, allMaps, &allGuards);
        TagSet base = sets2; // what retags may set on any object
        TagSet top;          // every tag
        top.wide = true;
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
          for (const Term &t : writers[i].topMaps) addImages(from, top, pt(t));
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
      if (prodNeed.count(dOff)) {
        CompRes &C = comps[dOff];
        C.as = pas;
        for (size_t i = 0; i < writers.size(); i++) {
          C.any.push_back(wAll[i]);
          C.vals.push_back(full.w[i].wide ? std::set<int64_t>() : full.w[i].vals);
          C.kb.push_back(full.w[i].wide ? std::optional<KnownBits>(full.w[i].kb) : std::nullopt);
        }
      }
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
      std::map<const Instruction *, std::pair<const Function *, unsigned>> entryHere; // plan 3.54
      std::map<const Instruction *, std::map<const Function *, std::vector<size_t>>> termAdm; // plan 3.54 (b)
      size_t pairReadsKeyed = 0;
      for (const FAccess &r : fLoads[Ff]) {
        std::vector<Test> tests;
        testsAtM(r.I, r.obj, Df, Ff, tests, pas);
        if (tests.size() == 1 && tests[0].entryFn) entryHere[r.I] = {tests[0].entryFn, tests[0].entryK};
        if (tests.empty()) {
          // Parameter-pair tests: the union over the callee's uses of what
          // each use's tests admit; an untested use admits every writer.
          const auto &ps = ppTestsFor(r.I, r.obj, Df);
          bool untested = !ps;
          if (ps) for (const auto &u : *ps) untested |= u.empty();
          if (untested) {
            if (ps) ppUntestedReads++;
            readsNoTest++;
            continue;
          }
          std::vector<size_t> adm;
          std::vector<std::vector<size_t>> perUse(ps->size());
          for (size_t i = 0; i < writers.size(); i++) {
            bool any = false;
            for (size_t q = 0; q < ps->size(); q++) {
              bool ok = wAll[i];
              const TagSet &ws = full.w[i];
              if (!ok && ws.wide) ok = !ws.kb.hasConflict() && mayHold((*ps)[q], ws.kb);
              else if (!ok) for (int64_t v : ws.vals) if (holds((*ps)[q], v)) { ok = true; break; }
              if (ok) perUse[q].push_back(i), any = true;
            }
            if (any) adm.push_back(i);
          }
          ppPerUse[r.I] = {std::move(perUse), &ppUseInfo[{r.I, Df.second}]};
          if (adm.size() == writers.size()) { readsAll++; continue; }
          keyed.push_back({r.I, adm});
          pairReadsKeyed++;
          ppKeyedReads++;
          continue;
        }
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
          if (provOn && i < TT->prov.size())
            for (int64_t v : ws.vals) {
              if (!holdsP(tests, v)) continue;
              std::set<std::string> &via = taggedAdmitVia[{r.I, writers[i].I}];
              int64_t cur = v;
              bool mapped = false;
              for (int d = 0; d < 12; d++) {
                auto pit = TT->prov[i].find(cur);
                if (pit == TT->prov[i].end()) break;
                via.insert(pit->second.second + ": 0x" + utohexstr((uint64_t)pit->second.first) + " -> 0x" +
                           utohexstr((uint64_t)cur));
                mapped = true;
                cur = pit->second.first;
              }
              if (!mapped) via.insert("");
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
        if (adm.size() == writers.size()) {
          readsAll++;
          if (entryHere.count(r.I)) entryAll.insert(r.I);
          continue;
        }
        // Plan 3.54 (b): what the entry test would admit for each method
        // of D, for objects entering with that method's term.
        if (entryHere.count(r.I))
          for (const Function *X : installedIn[Df]) {
            if (!ptrConst(X)) continue;
            std::vector<Test> tx = tests;
            tx[0].caseVals = {*ptrConst(X)};
            const auto [TX, RX] = tagsFor(tx);
            curR = RX;
            std::vector<size_t> ax;
            for (size_t i = 0; i < writers.size(); i++) {
              if (wAll[i]) { ax.push_back(i); continue; }
              const TagSet &ws = TX->w[i];
              if (ws.wide) {
                if (!ws.kb.hasConflict() && mayHold(tx, ws.kb)) ax.push_back(i);
                continue;
              }
              for (int64_t v : ws.vals)
                if (holdsP(tx, v)) { ax.push_back(i); break; }
            }
            curR = wmask;
            if (ax.size() < writers.size()) termAdm[r.I][X] = std::move(ax);
          }
        keyed.push_back({r.I, adm});
        pairReadsKeyed++;
      }
      for (auto &[I, mp] : inPlaceHere)
        taggedInPlace.push_back({S + "+" + std::to_string(Ff.second) + " by +" + std::to_string(dOff), I, mp});
      if (keyed.empty()) {
        if (fs.size() >= 10) {
          size_t nAll = std::count(wAll.begin(), wAll.end(), true);
          std::string d = "PLAIN " + S + "+" + std::to_string(Ff.second) + " by +" + std::to_string(dOff) + " (" +
                          std::to_string(fs.size()) + " writes): every tested read admits every writer; " +
                          (uAll ? std::string("widened") : std::to_string(full.uSize)) + " tags, " +
                          std::to_string(nAll) + " writers with any tag; bits observed " +
                          std::to_string(llvm::popcount((uint64_t)projR)) + "; call-site effects " + std::to_string(effSites) +
                          " (" + std::to_string(effAbsorbed) + " absorbed by callers, " + std::to_string(effUnseen) +
                          " never read under); tag stores " +
                          std::to_string(absorbedStores) + " accounted at call sites, " + std::to_string(unseenStores) +
                          " never read under, " + std::to_string(closedStores) +
                          " closed, " + std::to_string(openStores) + " open (retags" +
                          (openAt.empty() ? std::string() : ", e.g. " + openAt) + "); " +
                          std::to_string(observedWriters) + " writers read under their prior tag (" + std::to_string(mappedFromOpen) +
                          " only mapped from an open one; " +
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
              for (const std::string &fa : fillAt) d += "; fill " + fa;
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
      // Record: the writers with a known tag are named; each keyed read
      // its admitted writers (the unknown ones among them: every tag).
      bool any = false;
      for (size_t i = 0; i < writers.size(); i++) any |= !writers[i].unknown;
      if (!any) continue;
      for (size_t i = 0; i < writers.size(); i++) if (!writers[i].unknown) namedW[i] = true;
      for (size_t i = 0; i < writers.size(); i++)
        if (writers[i].unknown && unknownWhy[i].empty())
          unknownWhy[i] = "by +" + std::to_string(dOff) + ": " + (writers[i].why.empty() ? std::string("?") : writers[i].why);
      // Entry-keyed reads (plan 3.54) collect a union over D fields
      // (installed below); the others intersect over Ds (keyRead).
      size_t entryKeyed = 0;
      for (auto &[I, adm] : keyed) {
        auto eit = entryHere.find(I);
        if (eit == entryHere.end()) {
          keyRead(I, adm);
          continue;
        }
        EntryAdm &ea = entryAdm[I];
        ea.fn = eit->second;
        ea.fields.insert(dOff);
        ea.adm.insert(adm.begin(), adm.end());
        ea.byTerm[dOff] = termAdm[I];
        entryKeyed++;
      }
      fPairs.push_back({S, Ff.second, dOff, (int64_t)(dWidth / 8)});
      fPairAs.push_back(pas);
      fDims.push_back("+" + std::to_string(dOff));
      std::string extra;
      for (const std::string &d : xformAt) extra += "; retag " + d;
      for (const std::string &v : via) extra += "; bound " + v;
      taggedReport.push_back("KEYED " + S + "+" + std::to_string(Ff.second) + " by +" +
                               std::to_string(dOff) + ": " + std::to_string(writers.size()) + " writers, " +
                               std::to_string(pairReadsKeyed) + " reads keyed (" + std::to_string(entryKeyed) +
                               " by a method's entry test), " +
                               std::to_string(retags.size()) + " retags, bits observed " + std::to_string(llvm::popcount((uint64_t)projR)) + " (" + std::to_string(closedStores) +
                               " tag stores closed; " + std::to_string(observedWriters) + " writers read under their prior tag; " +
                               std::to_string(guarded) +
                               " guarded, " + std::to_string(unguarded) + " unguarded transforms), " +
                               (uAll ? std::string("widened") : std::to_string(full.uSize)) + " tags" + extra);
    }
    if (!dOffs.empty())
      for (const FAccess &r : fLoads[Ff])
        if (!anyTest.count(r.I)) taggedUntested.push_back({S + "+" + std::to_string(Ff.second), r.I});
    // Products: writer i admitted iff some (v1, v2) of its component tag
    // sets satisfies the tests (the cartesian product of the components'
    // sets: a sound superset of the pairs it can hold; a component any
    // tag or widened is its known bits).
    for (const ProdReads &PRs : fProds) {
      const Prod &P = prods[-1 - PRs.virt];
      auto c1 = comps.find(P.d1), c2 = comps.find(P.d2);
      if (c1 == comps.end() || c2 == comps.end()) continue; // a component not certified or not computed
      auto cands = [](const CompRes &C, size_t i, unsigned w) {
        std::vector<KnownBits> r;
        if (C.any[i]) r.push_back(KnownBits(64));
        else if (C.kb[i]) r.push_back(*C.kb[i]);
        else for (int64_t v : C.vals[i]) r.push_back(KnownBits::makeConstant(APInt(64, (uint64_t)v)));
        if (w < 64) for (KnownBits &k : r) k = k.trunc(w).zext(64);
        return r;
      };
      auto joinAll = [](std::vector<KnownBits> &v) {
        if (v.size() < 2) return;
        KnownBits j = v[0];
        for (const KnownBits &k : v) j = j.intersectWith(k);
        v = {j};
      };
      auto pack = [&](const KnownBits &a, const KnownBits &b) {
        KnownBits r(64);
        const APInt lo = APInt::getLowBitsSet(64, P.w1);
        r.One = (a.One & lo) | b.One.shl(P.w1);
        r.Zero = (a.Zero & lo) | b.Zero.shl(P.w1);
        return r;
      };
      size_t prodKeyed = 0;
      for (const auto &[I, tt] : PRs.reads) {
        std::vector<size_t> adm;
        for (size_t i = 0; i < fs.size(); i++) {
          std::vector<KnownBits> A = cands(c1->second, i, P.w1), B = cands(c2->second, i, 64);
          if (A.size() * B.size() > 65536) joinAll(A), joinAll(B);
          bool ok = false;
          for (const KnownBits &a : A)
            for (const KnownBits &b : B) {
              if (ok) break;
              const KnownBits k = pack(a, b);
              ok = k.isConstant() ? holds(tt, (int64_t)k.getConstant().getZExtValue()) : mayHold(tt, k);
            }
          if (ok) adm.push_back(i);
        }
        if (adm.size() == fs.size()) continue;
        keyRead(I, adm);
        prodKeyed++;
      }
      if (!prodKeyed) continue;
      for (size_t i = 0; i < fs.size(); i++) namedW[i] = namedW[i] || !c1->second.any[i] || !c2->second.any[i];
      std::set<uint32_t> as = PRs.as;
      for (const auto *C : {&c1->second, &c2->second}) as.insert(C->as.begin(), C->as.end());
      for (int64_t d : {P.d1, P.d2}) {
        fPairs.push_back({S, Ff.second, d, d == P.d1 ? (int64_t)(P.w1 / 8) : 8});
        fPairAs.push_back(as);
      }
      fDims.push_back("+" + std::to_string(P.d1) + " x +" + std::to_string(P.d2));
      taggedReport.push_back("KEYED " + S + "+" + std::to_string(Ff.second) + " by +" + std::to_string(P.d1) +
                             " x +" + std::to_string(P.d2) + ": " + std::to_string(prodKeyed) +
                             " reads keyed by predicates of both");
    }
    // Plan 3.54: an entry-keyed read admits the union of its fields'
    // admissions, intersected with what a test of every entry admits. In IR
    // order: it orders taggedEntryFormals, so the T entry rows.
    std::map<const Instruction *, const EntryAdm *, IROrder> entryKeyedF;
    for (auto &[I, ea] : entryAdm) {
      if (entryAll.count(I)) continue;
      const std::vector<size_t> u(ea.adm.begin(), ea.adm.end());
      auto [it, ins] = readAdm.try_emplace(I, u);
      if (!ins) {
        std::vector<size_t> both;
        std::set_intersection(it->second.begin(), it->second.end(), u.begin(), u.end(), std::back_inserter(both));
        it->second = std::move(both);
      }
      entryKeyedF[I] = &ea;
    }
    // Install, once per F. Another mechanism's keys on a writer or a read
    // of F would not meet these: F stays unkeyed then.
    if (readAdm.empty()) continue;
    // Union keys of the union slot holding F (plan 3.17's census, keyed by
    // the union field's own offset: unionFieldNotes) are subsumed for a
    // union next to a certified tag: they are dropped for every access
    // whose bytes overlap F's (an access left unkeyed reads every write),
    // then the tag keys go in; accesses to other bytes of the slot keep
    // their member keys (Fable 2026-10-16). Any other mechanism's keys
    // refuse the field.
    const std::string slotPrefix = S + "+" + std::to_string(Ff.second) + "#";
    int64_t uoff = Ff.second;
    if (auto nit = unionFieldNotes.find(S); nit != unionFieldNotes.end()) {
      auto uit = nit->second.upper_bound(Ff.second);
      if (uit != nit->second.begin()) {
        --uit;
        if (Ff.second < uit->first + std::max<int64_t>(uit->second.size, 1)) uoff = uit->first;
      }
    }
    const std::string censusPrefix = S + "+" + std::to_string(uoff) + "#";
    auto isCensus = [&](const Instruction *I) {
      auto it = unionKeyNames.find(I);
      if (it == unionKeyNames.end() || it->second.empty()) return false;
      for (const std::string &k : it->second)
        if (k.rfind(censusPrefix, 0) != 0 || k.rfind(slotPrefix + "!t", 0) == 0) return false;
      return true;
    };
    // Another mechanism's keys on an access of F refuse the field, before
    // anything is dropped (a refused pair leaves the census keys as they
    // are).
    const Instruction *other = nullptr;
    for (const FAccess &w : fs) if (!other && unionKeyNames.count(w.I) && !isCensus(w.I)) other = w.I;
    for (const FAccess &r : fLoads[Ff]) if (!other && unionKeyNames.count(r.I) && !isCensus(r.I)) other = r.I;
    if (other) {
      std::string ok;
      for (const std::string &k : unionKeyNames[other]) ok += (ok.empty() ? "" : " ") + k;
      taggedReport.push_back("UNKEYED " + S + "+" + std::to_string(Ff.second) + ": an access already keyed otherwise at " +
                             locOf(other) + " {" + ok + "}");
      continue;
    }
    // Two partitions of one set of writes (Fable 2026-10-16): the tag keys
    // and the union census's member keys of the slot holding F, each with a
    // catch-all ("every member": the census prefix + "?"; "every tag": the
    // tag prefix + "?"). Every write over F's bytes carries a key of each
    // scheme (its member key or the census catch-all; its tag key or the
    // tag catch-all); every read carries one scheme's keys and that
    // scheme's catch-all: the tag keys where a stable dominating test keys
    // it (a checked read), else its census member key (the user's
    // 2026-10-07 assumption, unchanged), else none (it reads the whole slot:
    // every key, both catch-alls and the unkeyed cell). The unkeyed cell
    // (what neither scheme types) is read by every read of the slot. A read
    // in either scheme meets every write of that scheme, and every write is
    // in both. "#!t": no member or function name (the census's keys) starts
    // with '!' (bfd.tdata's member tekhex_data did start with "t").
    const std::string prefix = S + "+" + std::to_string(Ff.second) + "#!t";
    const std::string tagAll = prefix + "?", censusAll = censusPrefix + "?";
    std::vector<std::string> everyTag; // the writes keyed every tag (tagAll), each with its cause (reports)
    const int64_t fsz = (int64_t)fs.front().I->getModule()->getDataLayout().getPointerSize();
    std::set<const Instruction *> mine;
    for (const FAccess &w : fs) mine.insert(w.I);
    for (const FAccess &r : fLoads[Ff]) mine.insert(r.I);
    auto overF = [&](const Instruction *I) { // the access's bytes, by the one naming route (accessSlot)
      const Value *Addr = getLoadStorePointerOperand(I);
      const Type *AT = Addr ? getLoadStoreType(const_cast<Instruction *>(I)) : nullptr;
      StructType *S2 = nullptr;
      int64_t o2 = 0;
      const DataLayout &DL2 = I->getModule()->getDataLayout();
      const bool named = Addr && AT && AT->isSized() && accessSlot(I, Addr, DL2, S2, o2) && S2 && S2->hasName() &&
                         stripStructNameSuffix(S2->getName()) == S;
      if (!named) return true; // bytes unknown: over F's, as far as one can tell
      const int64_t hi2 = o2 + (int64_t)DL2.getTypeStoreSize(const_cast<Type *>(AT));
      return hi2 > Ff.second && o2 < Ff.second + fsz;
    };
    // Two schemes only where the census keys the slot: an access of F, or
    // another over F's bytes, carries census keys. Elsewhere (F in no
    // union, or one the census did not key) the tag keys alone, as before:
    // a tagged write its key, an untagged one the unkeyed cell, a read its
    // writers' keys.
    bool censusHere = false;
    for (const FAccess &w : fs) censusHere |= isCensus(w.I);
    for (const FAccess &r : fLoads[Ff]) censusHere |= isCensus(r.I);
    for (auto &[I, ks] : unionKeyNames)
      if (!censusHere && !mine.count(I) && isCensus(I) && overF(I)) censusHere = true;
    if (!censusHere) {
      for (size_t i = 0; i < fs.size(); i++) {
        if (!namedW[i]) { writersUntagged++; continue; }
        unionKeyNames[fs[i].I] = {prefix + "w" + std::to_string(i)};
        writersTagged++;
      }
      for (auto &[I, adm] : readAdm) {
        std::vector<std::string> ks;
        for (size_t i : adm)
          if (namedW[i]) ks.push_back(prefix + "w" + std::to_string(i));
        if (ks.empty()) ks.push_back(prefix + "none");
        if (uncheckedReads.count(I)) uncheckedReplaced.insert(I);
        unionKeyNames[I] = ks;
        tagPrefixOf[I] = prefix;
        readsKeyed++;
      }
    }
    if (censusHere) {
      // The census-keyed accesses over F's bytes that are not F's: a write
      // gains the tag catch-all (every tag); a read keeps its member key and
      // reads the census catch-all too.
      bool tookCensus = false;
      for (auto &[I, ks] : unionKeyNames) {
        if (mine.count(I) || !isCensus(I) || !overF(I)) continue;
        if (isa<StoreInst>(I)) {
          std::string k;
          for (const std::string &x : ks) k += (k.empty() ? "" : " ") + x;
          everyTag.push_back(locOf(I) + ": a write of another member over F's bytes {" + k +
                             "} (the pair evaluates only F's own writers' tags)");
        }
        ks.push_back(isa<StoreInst>(I) ? tagAll : censusAll);
        tookCensus = true;
        (isa<StoreInst>(I) ? censusDropNotF : censusReadsKept)++;
      }
      for (size_t i = 0; i < fs.size(); i++) {
        std::vector<std::string> ks;
        if (isCensus(fs[i].I)) ks = unionKeyNames[fs[i].I], tookCensus = true, censusDropF++;
        else ks.push_back(censusAll); // untyped by member: every member
        if (namedW[i]) ks.push_back(prefix + "w" + std::to_string(i)), writersTagged++;
        else {
          ks.push_back(tagAll), writersUntagged++; // untagged: every tag
          // Measured (reporting only): whether a stable test of the tag on
          // its object dominates the writer, as one keys a read.
          std::string under;
          for (const TaggedPair &P : fPairs) {
            std::vector<Test> tests;
            std::set<uint32_t> as;
            const size_t c1 = testsUnstable, c2 = setTestsMade, c3 = dispatchTestsMade, c4 = dispatchTestsDropped;
            testsAt(fs[i].I, fs[i].obj, Field{S, P.D}, Ff, tests, as);
            testsUnstable = c1, setTestsMade = c2, dispatchTestsMade = c3, dispatchTestsDropped = c4; // not a read's
            under += (under.empty() ? "" : "; ") + std::string("+") + std::to_string(P.D) + ": " +
                     (tests.empty() ? lastTestsWhy : std::to_string(tests.size()) + " stable dominating tests");
            writersUnderTest += !tests.empty();
          }
          everyTag.push_back(locOf(fs[i].I) + ": F's writer, its tag unknown " +
                             (unknownWhy[i].empty() ? std::string("(no tag store evaluated)") : "(" + unknownWhy[i] + ")") +
                             " [" + under + "]");
        }
        unionKeyNames[fs[i].I] = ks;
        tagWriteOf[fs[i].I] = prefix;
      }
      if (tookCensus) censusSubsumed++;
      for (auto &[I, adm] : readAdm) {
        std::vector<std::string> ks;
        for (size_t i : adm)
          if (namedW[i]) ks.push_back(prefix + "w" + std::to_string(i));
        if (ks.empty()) ks.push_back(prefix + "none");
        ks.push_back(tagAll);
        if (uncheckedReads.count(I)) uncheckedReplaced.insert(I);
        if (isCensus(I)) memberOf[I] = unionKeyNames[I]; // its census member key (P3)
        unionKeyNames[I] = ks;
        tagPrefixOf[I] = prefix;
        // Its callee's tested uses read it through their own tests' keys,
        // when every call of the callee is such a read (below).
        readsKeyed++;
      }
      // F's reads the pair does not key: their census member key and the
      // census catch-all (a census-keyed read of F), else the whole slot.
      for (const FAccess &r : fLoads[Ff]) {
        if (readAdm.count(r.I) || !isCensus(r.I)) continue;
        unionKeyNames[r.I].push_back(censusAll);
        censusReadsKept++;
      }
      // Product keys (P3, Fable 2026-10-17): every write over F's bytes is
      // filed under (tag key, member key) for each key of each scheme it
      // carries, so a read can take one scheme or both. A read in one
      // scheme reads every product with its scheme's component (as
      // before: the same writes); a tag-keyed read that has a census member
      // key m reads the intersection, the products (t, c) with t in its tag
      // keys or the tag catch-all and c in {m, the census catch-all}: a
      // write the census types as another member is excluded by its member
      // name, the user's name-compatible-stores principle on the write
      // side, a per-read ASSUMPTION listing those writes (an untagged
      // write; or a tagged one, a tag/member disagreement, reported).
      std::map<std::pair<std::string, std::string>, std::vector<const Instruction *>> prodWrites;
      auto splitKeys = [&](const std::vector<std::string> &ks, std::vector<std::string> &tg, std::vector<std::string> &mm) {
        for (const std::string &k : ks)
          if (k.rfind(prefix, 0) == 0) tg.push_back(k);
          else if (k.rfind(censusPrefix, 0) == 0) mm.push_back(k);
      };
      for (auto &[I, ks] : unionKeyNames) {
        if (isa<LoadInst>(I) || !overF(I)) continue;
        std::vector<std::string> tg, mm;
        splitKeys(ks, tg, mm);
        if (tg.empty() || mm.empty()) continue; // no write of this slot's two schemes
        std::vector<std::string> ps;
        for (const std::string &tk : tg)
          for (const std::string &mk : mm) {
            ps.push_back(tk + "&" + mk);
            prodWrites[{tk, mk}].push_back(I);
          }
        ks = ps;
      }
      for (auto &[I, ks] : unionKeyNames) {
        if (!isa<LoadInst>(I) || !overF(I)) continue;
        std::vector<std::string> tg, mm;
        splitKeys(ks, tg, mm);
        if (tg.empty() && mm.empty()) continue;
        auto mit = memberOf.find(I);
        const bool both = !tg.empty() && mit != memberOf.end();
        std::set<std::string> T(tg.begin(), tg.end()), M(mm.begin(), mm.end());
        if (both) {
          M.insert(mit->second.begin(), mit->second.end());
          M.insert(censusAll);
        }
        std::vector<std::string> ps;
        for (const auto &[pr, ws] : prodWrites) {
          const bool tOk = tg.empty() || T.count(pr.first),
                     mOk = (tg.empty() || both) ? M.count(pr.second) != 0 : true;
          if (tOk && mOk) ps.push_back(pr.first + "&" + pr.second);
          else if (both && tOk && !mOk)
            for (const Instruction *W : ws) p3Excluded[I].push_back({W, pr.first != tagAll});
        }
        if (both) p3Reads++;
        if (ps.empty()) ps.push_back(prefix + "none");
        ks = ps;
      }
    }
    // Plan 3.54: the installed entry-keyed reads and their formals; a
    // formal's test fields are those every one of its reads was tested on.
    for (auto &[I, ea] : entryKeyedF) {
      auto [M, k] = ea->fn;
      uint32_t fi = 0;
      while (fi < taggedEntryFormals.size() && (taggedEntryFormals[fi].M != M || taggedEntryFormals[fi].k != k)) fi++;
      if (fi == taggedEntryFormals.size()) taggedEntryFormals.push_back({M, k, S, ea->fields});
      TaggedEntryFormal &E = taggedEntryFormals[fi];
      assert(E.S == S && "a formal's reads are of one struct");
      std::set<int64_t> both;
      std::set_intersection(E.Ds.begin(), E.Ds.end(), ea->fields.begin(), ea->fields.end(), std::inserter(both, both.end()));
      E.Ds = std::move(both);
      E.Fs.insert(Ff.second);
      taggedEntryReads[I] = fi;
      auto &tk = taggedEntryTermKeys[I];
      for (auto &[d, byX] : ea->byTerm) {
        auto &dk = tk[d];
        for (auto &[X, ax] : byX) {
          std::vector<std::string> ks;
          for (size_t i : ax)
            if (namedW[i]) ks.push_back(prefix + "w" + std::to_string(i));
          if (ks.empty()) ks.push_back(prefix + "none");
          dk[X] = std::move(ks);
        }
      }
    }
    // Per-use channels: for a callee G and content parameter j whose every
    // call (G's address not taken) is a keyed pp read of this field, each
    // use of j reads, per call, the keys its own test admits.
    {
      std::map<std::pair<const Function *, unsigned>, std::vector<const Instruction *>> byCallee;
      for (auto &[R, pu] : ppPerUse)
        if (readAdm.count(R) && pu.second && pu.second->G) byCallee[{pu.second->G, pu.second->j}].push_back(R);
      for (auto &[gj, Rs] : byCallee) {
        const Function *G = gj.first;
        if (G->hasAddressTaken()) continue;
        size_t calls = 0;
        for (const User *U : G->users()) {
          const auto *CB = dyn_cast<CallBase>(U);
          if (!CB || CB->getCalledOperand() != G) { calls = SIZE_MAX; break; }
          calls++;
        }
        std::set<const CallBase *> seenCalls;
        bool chan = calls != SIZE_MAX;
        for (const Instruction *R : Rs) seenCalls.insert(ppPerUse[R].second->CB), chan &= ppPerUse[R].second->channelable;
        if (!chan || seenCalls.size() != Rs.size()) continue;
        // The other calls: per use, the call's content argument when the
        // use's tests can hold for the call's tag argument.
        const PPUseInfo &ui0 = *ppPerUse[Rs.front()].second;
        const auto &sum = ppSummary(G, ui0.k, ui0.j, ui0.dOff);
        if (!sum) continue;
        std::vector<std::pair<const Instruction *, const Value *>> valueEdges; // (use, content arg)
        bool ok = true;
        for (const User *U : G->users()) {
          const auto *CB = cast<CallBase>(U);
          if (seenCalls.count(CB)) continue;
          if (ui0.k >= CB->arg_size() || ui0.j >= CB->arg_size()) { ok = false; break; }
          for (const PPUse &u : *sum) {
            if (!u.channel) { ok = false; break; }
            if (mayHoldAtCall(CB, CB->getArgOperand(ui0.k), u.tests))
              valueEdges.push_back({u.use, CB->getArgOperand(ui0.j)});
          }
          if (!ok) break;
        }
        if (!ok) continue;
        for (auto &[u, X] : valueEdges) taggedParamValueChannels[u].push_back(X);
        for (const Instruction *R : Rs) {
          const auto &[perUse, ui] = ppPerUse[R];
          for (size_t q = 0; q < ui->uses.size() && q < perUse.size(); q++) {
            std::vector<std::string> ks;
            for (size_t i : perUse[q]) if (namedW[i]) ks.push_back(prefix + "w" + std::to_string(i));
            if (ks.empty()) ks.push_back(prefix + "none");
            taggedParamChannels[ui->uses[q]].push_back({R, ks});
          }
        }
        ppChannelCallees++;
      }
    }
    pairsKeyed++;
    cellUnionSlots.insert({S.substr(S.rfind('.') + 1), Ff.second, 8});
    for (size_t q = 0; q < fPairs.size(); q++) {
      taggedPairs.push_back(fPairs[q]);
      taggedPairAssumes.push_back(std::vector<uint32_t>(fPairAs[q].begin(), fPairAs[q].end()));
    }
    std::string dims;
    for (const std::string &d : fDims) dims += (dims.empty() ? "" : ", ") + d;
    taggedReport.push_back("KEYS " + S + "+" + std::to_string(Ff.second) + " by " + dims + ": " +
                           std::to_string(readAdm.size()) + " reads keyed" +
                           (everyTag.empty() ? std::string()
                                             : "; " + std::to_string(everyTag.size()) + " writes keyed every tag (" +
                                                   tagAll + "), which every keyed read admits:"));
    std::sort(everyTag.begin(), everyTag.end()); // filled from pointer-keyed maps: by text (fn, file:line first)
    for (const std::string &e : everyTag) taggedReport.push_back("    every tag: " + e);
  }
  for (auto &[M, _] : Ctx->Modules) // the entry reads in IR order (their hub keys)
    for (Function &F : *M)
      for (Instruction &I : instructions(F))
        if (taggedEntryReads.count(&I)) {
          taggedEntryReadIdx[&I] = taggedEntryReadList.size();
          taggedEntryReadList.push_back(&I);
        }
  // Plan 3.54 (b): the channels. A call in a method X that passes X's
  // receiver identity on as an argument carries X's terms for the object
  // when the F fields read under them are unwritten from X's entry to the
  // call; the alias assumptions that rests on go to those fields' pairs.
  size_t channelsMade = 0;
  {
    std::map<std::string, std::set<int64_t>> fsOf;
    for (const TaggedEntryFormal &E : taggedEntryFormals) fsOf[E.S].insert(E.Fs.begin(), E.Fs.end());
    for (uint32_t fi = 0; fi < taggedEntryFormals.size(); fi++) {
      const TaggedEntryFormal &E = taggedEntryFormals[fi];
      const Value *id = argId(E.M->getArg(E.k));
      for (const Instruction &I : instructions(*E.M)) {
        const auto *CS = dyn_cast<CallBase>(&I);
        if (!CS || isa<IntrinsicInst>(CS) || CS->isInlineAsm()) continue;
        for (unsigned k = 0; k < CS->arg_size(); k++) {
          if (!CS->getArgOperand(k)->getType()->isPointerTy() || argId(CS->getArgOperand(k)) != id) continue;
          TaggedChannel ch{k, fi, {}};
          std::set<uint32_t> as;
          for (int64_t F : fsOf[E.S]) {
            std::set<uint32_t> a2;
            if (stableBetween(nullptr, nullptr, &E.M->getEntryBlock(), CS, Field{E.S, F}, false, id, a2, nullptr)) {
              ch.Fs.insert(F);
              as.insert(a2.begin(), a2.end());
            }
          }
          if (ch.Fs.empty()) continue;
          for (size_t q = 0; q < taggedPairs.size(); q++)
            if (taggedPairs[q].S == E.S && ch.Fs.count(taggedPairs[q].F))
              taggedPairAssumes[q].insert(taggedPairAssumes[q].end(), as.begin(), as.end());
          taggedEntryChannels[CS].push_back(std::move(ch));
          channelsMade++;
        }
      }
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
    for (auto &[F, n] : walkBlocksBy) // a tie: the first by name (the map's order follows the heap)
      if (!top || n > walkBlocksBy[top] || (n == walkBlocksBy[top] && F->getName() < top->getName())) top = F;
    {
      std::string sites;
      std::vector<const Instruction *> es(eqMergeSites.begin(), eqMergeSites.end());
      std::sort(es.begin(), es.end(), irOrderLess); // the cut keeps the first in IR order, not by pointer
      for (const Instruction *I : es) if (sites.size() < 300) sites += " " + locOf(I);
      CG_LOG("TaggedFields: pointer-equality identity merges: " << eqMergeSites.size() << " (" << sites << " )\n");
    }
    CG_LOG("TaggedFields: time: tag sets " << tagsSecs << " s (" << tagsComputes << " computations), content effects "
           << ceSecs << " s\n");
    CG_LOG("TaggedFields: callee D-effects composed: " << effClosed << " closed, " << effOpen << " open ("
           << effComputes << " effect computations; content effects " << ceRounds << " rounds, " << ceUnsettled
           << " pairs unsettled, " << ceSecs << " s)\n");
    if (VerboseLevel >= 2) {
      std::stable_sort(effOpenAt.begin(), effOpenAt.end(),
                       [](const auto &a, const auto &b) { return irOrderLess(a.first, b.first); });
      for (size_t i = 0; i < effOpenAt.size() && i < 8; ++i)
        CG_LOG("TaggedFields:   open D-effect at " << effOpenAt[i].second << "\n");
    }
    CG_LOG("TaggedFields: walks " << walksBack << " backward, " << walksFwd << " forward, " << walkBlocks
           << " blocks (most in " << (top ? top->getName().str() : std::string("-")) << ": "
           << (top ? walkBlocksBy[top] : 0) << "); " << sumComputes << " summary computations, "
           << walkBounds << " walks at the bound; " << loopLimitAt.size()
           << " loops that do not settle (a walk's loop in 8 rounds, a pair's content effects in 12; open, listed)\n");
    for (const std::string &l : loopLimitAt) CG_LOG("TaggedFields:   loop that does not settle: " << l << "\n");
    // The alias assumptions reported are the ones an answer rests on: the
    // tagged pairs' (the solver checks them). A tuple a walk made whose
    // result no pair took is no assumption of anything.
    std::set<uint32_t> held;
    for (const auto &v : taggedPairAssumes) held.insert(v.begin(), v.end());
    CG_LOG("TaggedFields: alias assumptions the tagged pairs rest on (the solver checks them): " << held.size() << "; "
           << taggedAssumes.size() - held.size() << " tuples made by walks no answer rests on, not reported\n");
  }
  CG_LOG("TaggedFields: " << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count()
         << " s; " << pairsKeyed << " pairs keyed (" << writersTagged << " tagged writers, "
         << writersUntagged << " untagged: no co-written tag in the writer's function); reads: "
         << readsKeyed << " keyed, " << readsNoTest << " with no stable dominating test (" << testsUnstable
         << " tests dropped: D may be written before the access), " << setTestsMade
         << " set tests (t == a || t == b), " << dispatchTestsMade << " dispatch tests (a switch on D or on a constant table of it; "
         << dispatchTestsDropped << " left untested: a constant the index may hold takes the edge), " << readsAll
         << " admitting every writer; " << pairsNonConst << " pairs unkeyed by a non-constant retag, "
         << pairsUncertified << " by an uncertified tag; " << unionFields
         << " union members read as one pointer field; " << outParamWrites << " out-parameter F writes; "
         << sTermsKept << " own-tag terms current at their store, " << sTermsAtLoad << " taken at their load (rule iii); "
         << xmTerms << " terms with x-masks over " << xmFieldSizes.size() << " fields (" << xmFieldsWide << " U widened); "
         << pathGuarded << " retags guarded per path; " << coFills << " fills that write F and D together; "
         << "parameter-pair tests: " << ppKeyedReads << " keyed reads, " << ppUntestedReads << " untested; "
         << censusSubsumed << " union slots keyed in both schemes, tag and union census (writes of F with a member key "
         << censusDropF << ", other writes over F's bytes made every tag " << censusDropNotF
         << ", reads over F's bytes keeping their member key " << censusReadsKept << "); " << ppChannelCallees
         << " callees with per-use parameter channels; " << valueTests
         << " value tests narrowing a tag taken at its load; " << writersUnderTest
         << " untagged writers under a stable dominating test of their tag (measured)\n");
  // The census's UNCHECKED reads a tag pair keys by a stable dominating
  // test: checked now, so no longer listed assumptions; the final count is
  // net of them (a read the pair does not key keeps its member key).
  CG_LOG("UnionKeys: " << uncheckedReplaced.size()
         << " UNCHECKED reads replaced by tag keys (keyed by a stable test of the tag); net UNCHECKED reads: "
         << uncheckedReads.size() - uncheckedReplaced.size() << " of " << uncheckedReads.size() << "\n");
  // The two schemes (asserted): a tag-keyed read carries only its pair's
  // keys (with its catch-all); a write of F a key of each scheme (a
  // catch-all counts).
  for (const auto &[I, pre] : tagPrefixOf) {
    auto it = unionKeyNames.find(I);
    if (it == unionKeyNames.end()) continue;
    for (const std::string &k : it->second) {
      assert(k.rfind(pre, 0) == 0 && "a tag-keyed read with another kind of key");
      (void)k;
    }
  }
  for (const auto &[I, pre] : tagWriteOf) {
    auto it = unionKeyNames.find(I);
    assert(it != unionKeyNames.end() && "a write of a doubly keyed slot with no key");
    for (const std::string &k : it->second) {
      const size_t amp = k.find('&');
      assert(k.rfind(pre, 0) == 0 && amp != std::string::npos && amp + 1 < k.size() &&
             "a write of a doubly keyed slot whose key is not a (tag, member) product");
      (void)amp;
    }
  }
  // (C'') A one-field union copy's own tag keys: the tag components of its
  // product keys (on a slot keyed in both schemes; on a census-only slot it
  // has none, and each key goes to the same key).
  for (auto &[S, L] : unionCopyOf) {
    (void)L;
    auto it = unionKeyNames.find(S);
    if (it == unionKeyNames.end()) continue;
    std::set<std::string> tags;
    for (const std::string &k : it->second)
      if (const size_t amp = k.find('&'); amp != std::string::npos) tags.insert(k.substr(0, amp));
    if (!tags.empty()) unionCopyTags[S].assign(tags.begin(), tags.end());
  }
  // P3: the reads of both schemes and the writes they exclude by member
  // name (untagged; tagged: a tag/member disagreement).
  {
    size_t untagged = 0, tagged = 0;
    for (auto &[R, ws] : p3Excluded)
      for (auto &[W, tg] : ws) (tg ? tagged : untagged)++;
    CG_LOG("UnionKeys: " << p3Reads << " tag-keyed reads with a census member key read both schemes; "
           << untagged << " untagged and " << tagged
           << " tagged stores of other members excluded by their member name (the tagged ones a tag/member disagreement)\n");
    std::set<std::pair<const Instruction *, const Instruction *>> shown;
    // Per tagged write excluded: the reads, and the maps by which their
    // tests admit its tag (rule report).
    std::map<const Instruction *, std::pair<std::set<const Instruction *>, std::set<std::string>>, IROrder> byW; // rows in IR order
    for (auto &[R, wsHeap] : p3Excluded) {
      // The writes were filed from unionKeyNames (pointer order): logged
      // in IR order.
      auto ws = wsHeap;
      std::stable_sort(ws.begin(), ws.end(), [](const auto &a, const auto &b) { return irOrderLess(a.first, b.first); });
      for (auto &[W, tg] : ws) {
        if (!tg) continue;
        auto &bw = byW[W];
        bw.first.insert(R);
        auto vit = taggedAdmitVia.find({R, W});
        if (vit == taggedAdmitVia.end()) bw.second.insert("?");
        else bw.second.insert(vit->second.begin(), vit->second.end());
        if (shown.insert({R, W}).second)
          CG_LOG("UnionKeys:   tag/member disagreement: " << locOf(W) << " admitted by its tag at " << locOf(R)
                 << ", another member by the census\n");
      }
    }
    for (auto &[W, bw] : byW) {
      // Grouped by map: "<map>: 0xA -> 0xB, ...".
      std::map<std::string, std::vector<std::string>> byMap;
      for (const std::string &l : bw.second) {
        const size_t c = l.rfind(": 0x");
        if (c == std::string::npos) byMap[l];
        else byMap[l.substr(0, c)].push_back(l.substr(c + 2));
      }
      std::string via;
      for (auto &[m, ts] : byMap) {
        via += " [" + (m.empty() ? std::string("its own tag") : m == "?" ? std::string("no provenance recorded") : m);
        for (size_t k = 0; k < ts.size(); k++) via += (k ? ", " : ": ") + ts[k];
        via += "]";
      }
      taggedDisagreeRows.push_back(std::to_string(bw.first.size()) + " reads, 1 write (" + locOf(W) +
                                   "), admitted by its tag through:" + via + "; another member by the census");
    }
  }
  // Plan 3.54 rows: per method formal, its D field, its installers and
  // its keyed reads; the refusals by reason.
  {
    std::map<uint32_t, size_t> readsOf;
    for (auto &[I, fi] : taggedEntryReads) readsOf[fi]++;
    for (uint32_t fi = 0; fi < taggedEntryFormals.size(); fi++) {
      const TaggedEntryFormal &E = taggedEntryFormals[fi];
      std::set<std::string> inst;
      std::string dl;
      for (int64_t D : E.Ds) {
        dl += (dl.empty() ? "+" : ", +") + std::to_string(D);
        for (const FAccess &w : fStores[Field{E.S, D}])
          if (cast<StoreInst>(w.I)->getValueOperand()->stripPointerCasts() == E.M)
            inst.insert(w.I->getFunction()->getName().str());
      }
      std::string il;
      for (const std::string &n : inst) il += (il.empty() ? "" : ", ") + n;
      size_t sites = 0;
      for (auto &[CS, f] : taggedEntrySites) sites += f.first == E.S && E.Ds.count(f.second);
      taggedEntryRows.push_back("method " + E.M->getName().str() + " arg " + std::to_string(E.k) + ": " + E.S +
                                " by " + (dl.empty() ? std::string("no field (every entry unkeyed)") : dl) + ", " +
                                std::to_string(readsOf[fi]) +
                                " reads keyed by its entry test; installed by " + il + "; " +
                                std::to_string(sites) + " dispatch sites of the fields are tests");
    }
    for (auto &[why, n] : entryRefusals)
      taggedEntryRows.push_back("refused " + std::to_string(n) + " reads: " + why);
  }
  CG_LOG("TaggedFields: method entry tests (plan 3.54): " << taggedEntrySites.size() << " dispatch sites are tests ("
         << entrySiteFields.size() << " fields); " << entryTestsMade << " entry tests made; "
         << taggedEntryReads.size() << " reads keyed by them, through " << taggedEntryFormals.size()
         << " method formals; " << channelsMade << " calls pass a formal's object on with its terms (3.54 (b))\n");
  if (VerboseLevel >= 2)
    for (const std::string &r : taggedEntryRows) CG_LOG("TaggedFields:   ENTRY " << r << "\n");
  if (VerboseLevel >= 2)
    for (const std::string &u : xmFieldSizes) CG_LOG("TaggedFields:   U of " << u << "\n");
    CG_LOG("TaggedFields: addresses through an anonymous struct whose object is the enclosing named struct's: "
           << ids.viaAnon.size() << "\n");
    CG_LOG("TaggedFields: tag-write values evaluated by their known bits alone (LLVM computeKnownBits): "
           << knownBitsTerms << "\n");
    CG_LOG("TaggedFields: accesses through a struct GEP whose leading index is not 0 (a byte step): "
           << stepPosByTag << " named by their TBAA tag, " << stepPosUnnamed << " unnamed; " << stepPosConst
           << " of them at constant indices (the GEP alone used to name them), " << stepPosPast
           << " of those past the layout of the struct the step is written in; " << stepAddrUnnamed
           << " such addresses taken (unnamed)\n");
  if (VerboseLevel >= 2) {
    for (const std::string &l : taggedReport) CG_LOG("TaggedFields:   " << l << "\n");
    CG_LOG("TaggedFields: predicate tests " << predClosed << " closed, " << predOpen << " open\n");
    for (auto &[k, ne] : predOpenWhy)
      CG_LOG("TaggedFields:   open predicate tests: " << ne.first << " by " << k << ", e.g. " << ne.second << "\n");
  }
  taggedCounts = {pairsKeyed, writersTagged, writersUntagged, readsKeyed, readsNoTest, readsAll, pairsNonConst,
                  predClosed, predOpen, ppKeyedReads, ppUntestedReads};
}
