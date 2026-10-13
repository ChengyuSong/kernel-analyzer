/*
 * Call graph construction
 *
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// TypeLabels.cc: type labels of memory objects, recovered from their
// initialization (--cfl-census-type-labels; measurement only).
//
// Most heap allocation sites carry no type: malloc returns bytes, and a
// wrapper (_TIFFmalloc, xmalloc) returns the same bytes to every caller.
// The type appears when the caller initializes the object: the first
// typed writes through the call's result (a struct GEP, a struct-path
// TBAA tag) name the struct the object is. That struct is the object's
// LABEL; the flows-to solution carries it from the allocation to every
// use. With labels:
//   - an untyped write (no struct position of its own) is typed by the
//     labels of the objects its pointer reaches, or is harmless when
//     those objects hold no struct at all;
//   - a named access is checked against the labels of the objects it
//     reaches: consistent ("the type shortcut is legit here") or not
//     (a pun, or a merge of the analysis).
// Globals and stack slots are labeled by their declared types.

#include "CallGraphInternal.h"

#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/InstIterator.h>
#include <set>

namespace {

std::string structKey(const llvm::StructType *ST) {
  return stripStructNameSuffix(ST->getName()).str();
}

bool namedStruct(const llvm::StructType *ST) {
  return ST && !ST->isLiteral() && ST->hasName() &&
         !ST->getName().starts_with("union");
}

} // namespace

// Allocation calls (allocators and their wrappers) labeled by the typed
// writes through their results. IR only: usable before the solve.
void CallGraphPass::labelAllocationSites(
    std::unordered_map<const CallBase *, AllocSiteLabel> &siteLabel,
    size_t &allocCalls, size_t &wrapperCalls) {
  // ---- 1. Allocation calls: direct allocators and their wrappers ----
  // A wrapper returns only allocation results (through casts, phis of
  // them, or null).
  std::unordered_map<const Function *, int> wrapState; // 0 visiting, 1 yes, 2 no
  std::function<bool(const Function *)> isAllocWrapper =
      [&](const Function *F) -> bool {
    if (!F || F->isDeclaration())
      return false;
    if (Ctx->AllocFuncs.count(const_cast<Function *>(F)))
      return true;
    auto [it, ins] = wrapState.try_emplace(F, 0);
    if (!ins)
      return it->second == 1;
    bool any = false, all = true;
    std::function<bool(const Value *, int)> allocResult =
        [&](const Value *V, int depth) -> bool {
      V = V->stripPointerCasts();
      if (isa<ConstantPointerNull>(V))
        return true;
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        if (depth > 8)
          return false;
        for (const Value *In : PN->incoming_values())
          if (!allocResult(In, depth + 1))
            return false;
        return true;
      }
      if (const auto *CB = dyn_cast<CallBase>(V)) {
        if (Ctx->AllocSites.count(const_cast<CallBase *>(CB)))
          return true;
        return isAllocWrapper(CB->getCalledFunction());
      }
      return false;
    };
    for (const BasicBlock &BB : *F)
      if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
        if (const Value *RV = RI->getReturnValue()) {
          any = true;
          if (!allocResult(RV, 0))
            all = false;
        }
    const bool yes = any && all;
    wrapState[F] = yes ? 1 : 2;
    return yes;
  };

  // ---- 2. Labels of each allocation call from its typed writes ----
  // Aliases of the result in the calling function: casts, constant GEPs
  // (with their byte offset), and at -O0 the stack slot it is stored to
  // when that slot is stored exactly once.
  // Address expressions within a function: the same base value (a
  // stack slot stored once reads as what was stored) and the same
  // constant GEP path denote the same memory. A slot stored once in a
  // function and reloaded there reads the stored value back
  // (store->load forwarding; the -O0 idiom `tif->tif_data = malloc(..);
  // sp = (JPEGState *)tif->tif_data;`).
  std::function<std::string(const Value *, int)> addrKey =
      [&](const Value *P, int depth) -> std::string {
    P = P->stripPointerCasts();
    if (depth < 8) {
      if (const auto *G = dyn_cast<GEPOperator>(P)) {
        std::string k = addrKey(G->getPointerOperand(), depth + 1) + "/";
        raw_string_ostream os(k);
        G->getSourceElementType()->print(os);
        for (const Use &Ix : G->indices()) {
          const auto *CI = dyn_cast<ConstantInt>(Ix.get());
          if (!CI)
            return "v:" + std::to_string((uintptr_t)P);
          os << ":" << CI->getSExtValue();
        }
        return os.str();
      }
      if (const auto *LI = dyn_cast<LoadInst>(P))
        if (const auto *AI =
                dyn_cast<AllocaInst>(LI->getPointerOperand()->stripPointerCasts())) {
          const StoreInst *only = nullptr;
          size_t n = 0;
          for (const User *U : AI->users())
            if (const auto *SI = dyn_cast<StoreInst>(U))
              if (SI->getPointerOperand()->stripPointerCasts() == AI) {
                n++;
                only = SI;
              }
          if (n == 1)
            return addrKey(only->getValueOperand(), depth + 1);
        }
    }
    return "v:" + std::to_string((uintptr_t)P);
  };
  struct FnAddrs {
    std::map<std::string, std::vector<const StoreInst *>> stores;
    std::map<std::string, std::vector<const LoadInst *>> loads;
  };
  std::unordered_map<const Function *, FnAddrs> fnAddrs;
  auto addrsOf = [&](const Function *F) -> const FnAddrs & {
    auto [it, ins] = fnAddrs.try_emplace(F);
    if (ins)
      for (const Instruction &I : instructions(*F)) {
        if (const auto *SI = dyn_cast<StoreInst>(&I))
          it->second.stores[addrKey(SI->getPointerOperand(), 0)].push_back(SI);
        else if (const auto *LI = dyn_cast<LoadInst>(&I))
          if (LI->getType()->isPointerTy())
            it->second.loads[addrKey(LI->getPointerOperand(), 0)].push_back(LI);
      }
    return it->second;
  };
  // The struct a variable of debug type T points to, by its IR name ("" if
  // T is not a pointer to a struct the IR still has).
  auto diPointee = [&](const DIType *T, const Module *M) -> std::string {
    if (!T) return "";
    const StringRef N = ka::diStructName(T, true);
    if (N.empty()) return "";
    llvm::StructType *S = llvm::StructType::getTypeByName(M->getContext(), "struct." + N.str());
    return S && namedStruct(S) ? structKey(S) : "";
  };
  // A variable of debug type T** (void **, char **): an array of pointer
  // slots; the declared pointee's name for the reports ("" otherwise).
  auto diPtrArray = [](const DIType *T) -> std::string {
    auto strip = [](const DIType *X) {
      for (int i = 0; i < 16 && X; i++) {
        const auto *D = dyn_cast<DIDerivedType>(X);
        if (!D) break;
        const auto tag = D->getTag();
        if (tag != dwarf::DW_TAG_typedef && tag != dwarf::DW_TAG_const_type &&
            tag != dwarf::DW_TAG_volatile_type && tag != dwarf::DW_TAG_restrict_type)
          break;
        X = D->getBaseType();
      }
      return X;
    };
    const auto *P = dyn_cast_or_null<DIDerivedType>(strip(T));
    if (!P || P->getTag() != dwarf::DW_TAG_pointer_type) return "";
    const auto *Q = dyn_cast_or_null<DIDerivedType>(strip(P->getBaseType()));
    if (!Q || Q->getTag() != dwarf::DW_TAG_pointer_type) return "";
    const DIType *E = strip(Q->getBaseType());
    return (E && !E->getName().empty() ? E->getName().str() : std::string("void")) + " *";
  };
  auto labelSite = [&](const CallBase *C) {
    AllocSiteLabel L;
    const DataLayout &DL = C->getModule()->getDataLayout();
    // The variable that receives the result, by its declared type (plan
    // 3.53 1b: the site's own declaration comes first): a dbg.value on the
    // result, or the slot the result is stored to (dbg.declare).
    {
      SmallVector<DbgValueInst *, 2> DVs;
      findDbgValues(DVs, const_cast<CallBase *>(C));
      for (DbgValueInst *DV : DVs) {
        if (L.siteDeclared.empty())
          L.siteDeclared = diPointee(DV->getVariable()->getType(), C->getModule());
        if (L.sitePtrArray.empty())
          L.sitePtrArray = diPtrArray(DV->getVariable()->getType());
      }
      SmallVector<const Value *, 4> vs{C};
      for (size_t i = 0; i < vs.size() && L.siteDeclared.empty() && L.sitePtrArray.empty() && i < 8; i++)
        for (const User *U : vs[i]->users()) {
          if (isa<CastInst>(U)) { vs.push_back(U); continue; }
          const auto *SI = dyn_cast<StoreInst>(U);
          if (!SI || SI->getValueOperand() != vs[i]) continue;
          if (const auto *AI = dyn_cast<AllocaInst>(SI->getPointerOperand()->stripPointerCasts()))
            for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(AI))) {
              if (L.siteDeclared.empty())
                L.siteDeclared = diPointee(DDI->getVariable()->getType(), C->getModule());
              if (L.sitePtrArray.empty())
                L.sitePtrArray = diPtrArray(DDI->getVariable()->getType());
            }
        }
    }
    std::vector<std::pair<const Value *, int64_t>> work{{C, 0}};
    std::set<const Value *> seen{C};
    auto push = [&](const Value *V, int64_t off) {
      if (seen.insert(V).second)
        work.emplace_back(V, off);
    };
    auto segment = [&](int64_t off, const std::string &B) {
      if (off <= 0 || B.empty()) return;
      auto [it, ins] = L.segments.try_emplace(off, B);
      if (!ins && it->second != B) it->second.clear(); // two declarations: none
    };
    // The segments' own walk (records only segments): from result + c, the
    // variable receiving it (its declared pointee), its reloads when that
    // slot is stored once, constant GEPs, and struct GEPs written there
    // (`pCsr = (Fts3MultiSegReader *)&pFilter[1]` after `pFilter = ...`).
    std::set<std::pair<const Value *, int64_t>> segSeen;
    std::function<void(const Value *, int64_t, int)> segWalk = [&](const Value *V, int64_t off, int depth) {
      if (off <= 0 || depth > 8 || !segSeen.insert({V, off}).second) return;
      SmallVector<DbgValueInst *, 2> DVs;
      findDbgValues(DVs, const_cast<Value *>(V));
      for (DbgValueInst *DV : DVs) segment(off, diPointee(DV->getVariable()->getType(), C->getModule()));
      for (const User *U : V->users()) {
        if (const auto *CI = dyn_cast<CastInst>(U)) {
          if (CI->getType()->isPointerTy()) segWalk(CI, off, depth + 1);
        } else if (const auto *SI = dyn_cast<StoreInst>(U); SI && SI->getValueOperand() == V) {
          const auto *AI = dyn_cast<AllocaInst>(SI->getPointerOperand()->stripPointerCasts());
          if (!AI) continue;
          for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(AI)))
            segment(off, diPointee(DDI->getVariable()->getType(), C->getModule()));
          const FnAddrs &FA = addrsOf(SI->getFunction());
          const std::string K = addrKey(SI->getPointerOperand(), 0);
          auto st = FA.stores.find(K);
          if (st != FA.stores.end() && st->second.size() == 1)
            if (auto ld = FA.loads.find(K); ld != FA.loads.end())
              for (const LoadInst *LI : ld->second) segWalk(LI, off, depth + 1);
        } else if (const auto *G = dyn_cast<GEPOperator>(U); G && G->getPointerOperand() == V) {
          auto *ST = dyn_cast<llvm::StructType>(G->getSourceElementType());
          const auto *I0 = G->getNumIndices() ? dyn_cast<ConstantInt>(*G->idx_begin()) : nullptr;
          if (namedStruct(ST) && I0 && I0->isZero()) {
            bool written = false;
            for (const User *GU : G->users())
              if (const auto *S2 = dyn_cast<StoreInst>(GU)) written |= S2->getPointerOperand() == G;
            if (written) segment(off, structKey(ST));
          }
          APInt A(64, 0);
          if (G->accumulateConstantOffset(DL, A)) segWalk(G, off + A.getSExtValue(), depth + 1);
        }
      }
    };
    for (size_t i = 0; i < work.size(); i++) {
      const auto [V, off] = work[i];
      if (off > 0) segWalk(V, off, 0);
      // A variable's declared struct names the object only at its start
      // (`Fts3Table *t = (Fts3Table *)&p[1]` is not p's type).
      if (L.declared.empty() && off == 0)
        if (llvm::StructType *S = accessNames->baseStruct(V).S)
          L.declared = structKey(S);
      for (const User *U : V->users()) {
        if (const auto *CI = dyn_cast<CastInst>(U)) {
          if (CI->getType()->isPointerTy())
            push(CI, off);
        } else if (const auto *LI = dyn_cast<LoadInst>(U)) {
          if (!LI->getType()->isPointerTy() && !LI->getType()->isAggregateType())
            L.scalarUse = true;
        } else if (const auto *G = dyn_cast<GEPOperator>(U)) {
          if (G->getPointerOperand() != V)
            continue;
          if (!isa<llvm::StructType>(G->getSourceElementType()))
            for (const User *GU : G->users())
              if ((isa<LoadInst>(GU) && !GU->getType()->isPointerTy()) ||
                  (isa<StoreInst>(GU) &&
                   !cast<StoreInst>(GU)->getValueOperand()->getType()->isPointerTy()))
                L.scalarUse = true;
          // A struct GEP at the object's start names its type.
          auto *ST = dyn_cast<llvm::StructType>(G->getSourceElementType());
          if (namedStruct(ST)) {
            bool written = false;
            for (const User *GU : G->users())
              if (const auto *SI = dyn_cast<StoreInst>(GU))
                written |= SI->getPointerOperand() == G;
              else
                written |= isa<GEPOperator>(GU) || isa<CastInst>(GU);
            const auto *I0 = G->getNumIndices() ? dyn_cast<ConstantInt>(*G->idx_begin()) : nullptr;
            (void)I0;
            if (written && off == 0)
              L.types.insert(structKey(ST));
          }
          APInt A(64, 0);
          if (G->accumulateConstantOffset(DL, A))
            push(G, off + A.getSExtValue());
        } else if (const auto *SI = dyn_cast<StoreInst>(U)) {
          if (SI->getPointerOperand() == V) {
            if (!SI->getValueOperand()->getType()->isPointerTy() &&
                !SI->getValueOperand()->getType()->isAggregateType())
              L.scalarUse = true;
            // A store at the object through a struct-path TBAA tag: the
            // tag's struct starts where the access offset is the tag's own
            // offset in it (an access at 24 + offsetof(Fts3Table, db) is a
            // Fts3Table at 24, not this object's type).
            if (const MDNode *Tag = SI->getMetadata(LLVMContext::MD_tbaa))
              if (Tag->getNumOperands() >= 3 &&
                  Tag->getOperand(0) != Tag->getOperand(1))
                if (const auto *B = dyn_cast<MDNode>(Tag->getOperand(0)))
                  if (B->getNumOperands() >= 3)
                    if (const auto *N = dyn_cast<MDString>(B->getOperand(0)))
                      if (const auto *TO = mdconst::dyn_extract<ConstantInt>(Tag->getOperand(2)))
                        if (off == TO->getSExtValue())
                          if (llvm::StructType *S = accessNames->structByTag(
                                  SI->getModule(), N->getString()))
                            L.types.insert(structKey(S));
          } else if (SI->getValueOperand() == V && off == 0) {
            // The result stored to an address the function writes only
            // here: its reloads in the function are the object.
            const FnAddrs &FA = addrsOf(SI->getFunction());
            const std::string K = addrKey(SI->getPointerOperand(), 0);
            auto st = FA.stores.find(K);
            if (st != FA.stores.end() && st->second.size() == 1) {
              auto ld = FA.loads.find(K);
              if (ld != FA.loads.end())
                for (const LoadInst *LI : ld->second)
                  push(LI, 0);
            }
          }
        }
      }
    }
    siteLabel[C] = std::move(L);
  };
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F))
        if (const auto *CB = dyn_cast<CallBase>(&I)) {
          if (Ctx->AllocSites.count(const_cast<CallBase *>(CB))) {
            allocCalls++;
            labelSite(CB);
          } else if (isAllocWrapper(CB->getCalledFunction())) {
            wrapperCalls++;
            labelSite(CB);
          }
        }

}

// The allocations a labeling call creates: itself when it is an
// allocation, else the allocations its wrapper returns (shared by all
// callers: such an object collects every caller's type).
void CallGraphPass::allocationsOfCall(const CallBase *C,
                                      std::set<const CallBase *> &out) {
  std::function<void(const Function *, int)> inner = [&](const Function *F,
                                                         int depth) {
    if (!F || F->isDeclaration() || depth > 8)
      return;
    for (const BasicBlock &BB : *F)
      if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
        if (const Value *RV = RI->getReturnValue()) {
          SmallVector<const Value *, 4> vs{RV->stripPointerCasts()};
          while (!vs.empty()) {
            const Value *V = vs.pop_back_val();
            if (const auto *PN = dyn_cast<PHINode>(V)) {
              for (const Value *In : PN->incoming_values())
                vs.push_back(In->stripPointerCasts());
            } else if (const auto *CB = dyn_cast<CallBase>(V)) {
              if (Ctx->AllocSites.count(const_cast<CallBase *>(CB)))
                out.insert(CB);
              else
                inner(CB->getCalledFunction(), depth + 1);
            }
          }
        }
  };
  if (Ctx->AllocSites.count(const_cast<CallBase *>(C)))
    out.insert(C);
  else
    inner(C->getCalledFunction(), 0);
}

// Labels by value, before any solve: a global or stack slot by its
// declared struct, a heap allocation by the typed writes of every call
// that creates it (--cfl-weld-watch).
void CallGraphPass::staticLabels(
    std::unordered_map<const Value *, std::set<std::string>> &out) {
  std::unordered_map<const CallBase *, AllocSiteLabel> siteLabel;
  size_t allocCalls = 0, wrapperCalls = 0;
  labelAllocationSites(siteLabel, allocCalls, wrapperCalls);
  allocSegments.clear();
  std::set<const Value *> segSeen;
  for (auto &[C, SL] : siteLabel) {
    std::set<const CallBase *> allocs;
    allocationsOfCall(C, allocs);
    for (const CallBase *A : allocs) {
      // Segments: the creating sites must agree (a wrapper's allocation is
      // created by every caller).
      std::map<int64_t, std::string> seg;
      for (auto &[c, B] : SL.segments)
        if (!B.empty()) seg[c] = B;
      if (segSeen.insert(A).second) allocSegments[A] = std::move(seg);
      else if (allocSegments[A] != seg) allocSegments[A].clear();
      auto &L = out[A];
      // The receiving variable's declared struct first (1b), then the
      // typed writes, then a declared struct found along the result.
      if (!SL.siteDeclared.empty()) {
        L.insert(SL.siteDeclared);
        continue;
      }
      // An array of pointer slots, its declared pointee named after the
      // marker (the cell solver lays it out as ptr elements).
      if (!SL.sitePtrArray.empty()) {
        L.insert("ptr[]:" + SL.sitePtrArray);
        continue;
      }
      L.insert(SL.types.begin(), SL.types.end());
      if (SL.types.empty() && !SL.declared.empty())
        L.insert(SL.declared);
    }
  }
  // A declared object by its debug-info type: linking unifies structurally
  // identical IR types under one name (an fts3 local reads as
  // struct.WindowUpdate), the variable's declared type does not. The IR
  // type only when there is no debug info.
  auto diLabel = [&](const DIType *T) -> std::string {
    for (int i = 0; i < 8 && T; i++) {
      if (const auto *C = dyn_cast<DICompositeType>(T))
        if (C->getTag() == dwarf::DW_TAG_array_type) {
          T = C->getBaseType();
          continue;
        }
      if (const auto *D = dyn_cast<DIDerivedType>(T))
        if (D->getTag() == dwarf::DW_TAG_typedef ||
            D->getTag() == dwarf::DW_TAG_const_type ||
            D->getTag() == dwarf::DW_TAG_volatile_type) {
          T = D->getBaseType();
          continue;
        }
      break;
    }
    const StringRef N = ka::diStructName(T, false);
    return N.empty() ? std::string() : "struct." + N.str();
  };
  for (auto &[M, _] : Ctx->Modules) {
    auto decl = [&](const Value *V, Type *T, const DIType *DT) {
      if (DT) {
        const std::string L = diLabel(DT);
        if (!L.empty()) out[V].insert(L);
        return;
      }
      while (T->isArrayTy())
        T = T->getArrayElementType();
      if (auto *ST = dyn_cast<llvm::StructType>(T))
        if (namedStruct(ST))
          out[V].insert(structKey(ST));
    };
    for (GlobalVariable &GV : M->globals()) {
      SmallVector<DIGlobalVariableExpression *, 1> GVEs;
      GV.getDebugInfo(GVEs);
      decl(&GV, GV.getValueType(), GVEs.empty() ? nullptr : GVEs[0]->getVariable()->getType());
    }
    for (Function &F : *M)
      for (Instruction &I : instructions(F))
        if (auto *AI = dyn_cast<AllocaInst>(&I)) {
          const DIType *DT = nullptr;
          for (auto *DDI : findDbgDeclares(AI))
            if (auto *Var = DDI->getVariable()) { DT = Var->getType(); break; }
          decl(AI, AI->getAllocatedType(), DT);
        }
  }
}

void CallGraphPass::runTypeLabelCensus(
    const std::function<void(NodeIndex, std::vector<uint32_t> &)> &originsOf,
    const std::function<void(uint32_t, std::vector<const Value *> &)>
        &originValues,
    const std::function<bool(NodeIndex)> &anyFact,
    const std::function<std::string(NodeIndex, uint32_t, std::string &)>
        &explain,
    const std::string &emptyReadLine) {
  const bool report = !CFLRuleReport.empty();
  std::unordered_map<const CallBase *, AllocSiteLabel> siteLabel;
  size_t allocCalls = 0, wrapperCalls = 0;
  labelAllocationSites(siteLabel, allocCalls, wrapperCalls);

  // ---- 3. Labels of each origin ----
  // An origin's label set: for a heap origin, the labels of every
  // allocation call whose result reaches it (a wrapper's single malloc
  // collects all its callers' types); for a global or stack slot, its
  // declared struct, or "nonstruct" when it holds no struct.
  enum Kind { Heap, Declared, NonStruct, Unknown };
  struct OriginLabel {
    Kind kind = Unknown;
    std::set<std::string> types;
    bool buffer = false;
  };
  std::unordered_map<uint32_t, OriginLabel> originLabel;
  auto declOf = [&](const Value *V, OriginLabel &L) {
    Type *T = nullptr;
    if (const auto *GV = dyn_cast<GlobalVariable>(V))
      T = GV->getValueType();
    else if (const auto *AI = dyn_cast<AllocaInst>(V))
      T = AI->getAllocatedType();
    if (!T)
      return false;
    while (T->isArrayTy())
      T = T->getArrayElementType();
    if (auto *ST = dyn_cast<llvm::StructType>(T)) {
      if (namedStruct(ST)) {
        L.kind = Declared;
        L.types.insert(structKey(ST));
      } else if (const auto *GV = dyn_cast<GlobalVariable>(V)) {
        if (llvm::StructType *U = initUseTypeOf(GV)) {
          L.kind = Declared;
          L.types.insert(structKey(U));
        }
      }
      return true;
    }
    if (L.kind == Unknown)
      L.kind = NonStruct;
    return true;
  };
  std::vector<uint32_t> rids;
  std::vector<const Value *> vals;
  std::unordered_map<const CallBase *, std::vector<uint32_t>> ridsOfAlloc;
  auto originsCreatedBy = [&](const CallBase *A) -> const std::vector<uint32_t> & {
    auto [it, ins] = ridsOfAlloc.try_emplace(A);
    if (!ins)
      return it->second;
    NodeIndex n = getRepNodeForValue(A);
    if (n == AndersNodeFactory::InvalidIndex)
      return it->second;
    std::vector<uint32_t> cand;
    originsOf(getCanonicalNode(n), cand);
    for (uint32_t r : cand) {
      originValues(r, vals);
      if (std::find(vals.begin(), vals.end(), A) != vals.end())
        it->second.push_back(r);
    }
    return it->second;
  };
  for (auto &[C, SL] : siteLabel) {
    std::set<const CallBase *> allocs;
    allocationsOfCall(C, allocs);
    for (const CallBase *A : allocs)
      for (uint32_t r : originsCreatedBy(A)) {
        OriginLabel &L = originLabel[r];
        L.kind = Heap;
        if (!SL.siteDeclared.empty()) {
          L.types.insert(SL.siteDeclared); // the receiving variable's declaration
          continue;
        }
        L.types.insert(SL.types.begin(), SL.types.end());
        if (SL.types.empty() && !SL.declared.empty())
          L.types.insert(SL.declared); // typed only by its variable
        if (SL.types.empty() && SL.declared.empty() && SL.scalarUse)
          L.buffer = true;
      }
  }
  // A heap object every creating call uses only as scalars is a buffer.
  for (auto &[r, L] : originLabel)
    if (L.kind == Heap && L.types.empty() && L.buffer)
      L.kind = NonStruct;
  auto labelOf = [&](uint32_t r) -> OriginLabel & {
    auto [it, ins] = originLabel.try_emplace(r);
    if (ins) {
      originValues(r, vals);
      for (const Value *V : vals)
        declOf(V, it->second);
    }
    return it->second;
  };

  // Embedding: the struct names laid out inside a struct (itself included).
  std::unordered_map<std::string, std::set<std::string>> emb;
  std::unordered_map<std::string, llvm::StructType *> byName;
  for (auto &[M, _] : Ctx->Modules)
    for (llvm::StructType *ST : M->getIdentifiedStructTypes())
      if (namedStruct(ST))
        byName.try_emplace(structKey(ST), ST);
  std::function<const std::set<std::string> &(const std::string &)> embOf =
      [&](const std::string &K) -> const std::set<std::string> & {
    auto [it, ins] = emb.try_emplace(K);
    if (!ins)
      return it->second;
    std::set<std::string> out{K};
    auto bit = byName.find(K);
    if (bit != byName.end()) {
      std::function<void(Type *)> walk = [&](Type *T) {
        while (T->isArrayTy())
          T = T->getArrayElementType();
        if (auto *ST = dyn_cast<llvm::StructType>(T)) {
          if (namedStruct(ST) && structKey(ST) != K) {
            const auto &inner = embOf(structKey(ST));
            out.insert(inner.begin(), inner.end());
            return;
          }
          if (!ST->isOpaque())
            for (Type *E : ST->elements())
              walk(E);
        }
      };
      if (!bit->second->isOpaque())
        for (Type *E : bit->second->elements())
          walk(E);
    }
    emb[K] = out;
    return emb[K];
  };
  auto nameStruct = [&](uint32_t name) {
    const std::string &s = accessNames->str(name);
    return s.substr(0, s.rfind('+'));
  };
  // Labels one struct embeds at offset 0 of another are one type (the
  // outer, e.g. LZWCodecState begins with an LZWBaseState).
  auto atZero = [&](const std::string &U) {
    std::set<std::string> out;
    auto it = byName.find(U);
    llvm::StructType *ST = it == byName.end() ? nullptr : it->second;
    while (ST && !ST->isOpaque() && ST->getNumElements()) {
      Type *E = ST->getElementType(0);
      while (E->isArrayTy())
        E = E->getArrayElementType();
      ST = dyn_cast<llvm::StructType>(E);
      if (ST && namedStruct(ST))
        out.insert(structKey(ST));
    }
    return out;
  };
  for (auto &[r, L] : originLabel) {
    if (L.types.size() < 2)
      continue;
    std::set<std::string> inner;
    for (const std::string &U : L.types)
      for (const std::string &T : atZero(U))
        inner.insert(T);
    for (const std::string &T : inner)
      L.types.erase(T);
  }

  // ---- 4. Untyped writes, retyped by the labels they reach ----
  size_t uHarmless = 0, uTyped = 0, uUnknown = 0, uNoFacts = 0;
  std::map<std::string, size_t> uUnknownBy;
  // Rule (c) candidates: an untyped write that reaches a struct object.
  struct UntypedHit { std::string where, labels; };
  std::vector<UntypedHit> ruleC;
  for (auto &[cell, where] : blindWriteLog) {
    NodeIndex p = cellParent(cell);
    if (p == AndersNodeFactory::InvalidIndex) {
      uNoFacts++;
      continue;
    }
    originsOf(getCanonicalNode(p), rids);
    if (rids.empty()) {
      uNoFacts++;
      continue;
    }
    bool unknown = false, typed = false;
    std::string labels;
    for (uint32_t r : rids) {
      const OriginLabel &L = labelOf(r);
      if (L.kind == Unknown || (L.kind == Heap && L.types.empty()))
        unknown = true;
      else if (!L.types.empty()) {
        typed = true;
        for (const std::string &T : L.types)
          if (labels.size() < 200 && labels.find(T) == std::string::npos)
            labels += (labels.empty() ? "" : "|") + T;
      }
    }
    if (typed && report && ruleC.size() < 5000)
      ruleC.push_back({where, labels});
    if (unknown) {
      uUnknown++;
      uUnknownBy[where]++;
    } else if (typed) {
      uTyped++;
    } else {
      uHarmless++;
    }
  }

  // ---- 5. Named accesses against the labels they reach ----
  struct Tally {
    size_t legit = 0, mismatch = 0, unknown = 0;
    size_t allBad = 0; // every labeled object reached is incompatible
    // what the incompatible objects are
    size_t byHeap = 0, byDecl = 0, byBuffer = 0;
  };
  Tally all, icall;
  struct Mis {
    const Instruction *I;
    std::string name, label;
  };
  std::vector<Mis> mismatches;
  std::vector<std::pair<const Instruction *, std::string>> onlyBad;
  // Rule (b) violations: (access, name, the pointer, the origin, its
  // label, whether the pointer reaches no compatible object at all).
  struct TypeHit {
    const Instruction *I;
    uint32_t name;
    NodeIndex ptr;
    uint32_t rid;
    std::string label;
    bool only;
  };
  std::vector<TypeHit> ruleB;
  for (auto &[cell, name, I] : namedAccessLog) {
    NodeIndex p = cellParent(cell);
    if (p == AndersNodeFactory::InvalidIndex)
      continue;
    originsOf(getCanonicalNode(p), rids);
    const std::string S = nameStruct(name);
    bool mis = false, unk = rids.empty();
    bool misHeap = false, misDecl = false, misBuf = false;
    size_t good = 0;
    std::string badLabel;
    for (uint32_t r : rids) {
      const OriginLabel &L = labelOf(r);
      if (L.kind == Unknown || (L.kind == Heap && L.types.empty())) {
        unk = true;
        continue;
      }
      if (L.kind == NonStruct) {
        mis = misBuf = true;
        if (badLabel.empty())
          badLabel = "<nonstruct>";
        continue;
      }
      // Some type the object is initialized as must hold S.
      bool fits = false;
      for (const std::string &T : L.types)
        if (embOf(T).count(S)) {
          fits = true;
          break;
        }
      if (fits)
        good++;
      if (!fits) {
        mis = true;
        (L.kind == Heap ? misHeap : misDecl) = true;
        if (report && ruleB.size() < 20000) {
          std::string lb;
          for (const std::string &T : L.types)
            lb += (lb.empty() ? "" : "|") + T;
          ruleB.push_back({I, name, getCanonicalNode(p), r, lb, false});
        }
        if (badLabel.empty())
          for (const std::string &T : L.types)
            badLabel += (badLabel.empty() ? "" : "|") + T;
      }
    }
    bool isIcall = false;
    if (isa<LoadInst>(I))
      for (const User *U : I->users())
        if (const auto *CB = dyn_cast<CallBase>(U))
          isIcall |= CB->getCalledOperand() == I;
    Tally &T2 = isIcall ? icall : all;
    if (mis) {
      T2.mismatch++;
      if (!good && report)
        for (auto it = ruleB.rbegin(); it != ruleB.rend() && it->I == I; ++it)
          it->only = true;
      if (!good) {
        T2.allBad++;
        std::string why = accessNames->str(name) + " reaches only:";
        for (uint32_t r : rids) {
          const OriginLabel &L = labelOf(r);
          originValues(r, vals);
          std::string ov = "?";
          for (const Value *V : vals) {
            if (const auto *I3 = dyn_cast<Instruction>(V))
              ov = (I3->getFunction()->getName() + "::" + I3->getOpcodeName()).str();
            else if (V->hasName())
              ov = V->getName().str();
            break;
          }
          why += " [" + ov + " = ";
          if (L.kind == NonStruct)
            why += "non-struct";
          else
            for (const std::string &T : L.types)
              why += T + " ";
          why += "]";
          if (why.size() > 400)
            break;
        }
        onlyBad.emplace_back(I, why);
      }
      T2.byHeap += misHeap;
      T2.byDecl += misDecl;
      T2.byBuffer += misBuf;
      if (mismatches.size() < 4000)
        mismatches.push_back({I, accessNames->str(name), badLabel});
    } else if (unk) {
      T2.unknown++;
    } else {
      T2.legit++;
    }
  }

  // ---- Report ----
  size_t heap = 0, heapOne = 0, heapMany = 0, heapNone = 0;
  for (auto &[r, L] : originLabel)
    if (L.kind == Heap) {
      heap++;
      if (L.types.empty())
        heapNone++;
      else if (L.types.size() == 1)
        heapOne++;
      else
        heapMany++;
    }
  errs() << "TypeLabels: " << allocCalls << " allocator calls, "
         << wrapperCalls << " wrapper calls labeled from their typed writes\n";
  errs() << "TypeLabels: heap origins " << heap << ": " << heapOne
         << " one type, " << heapMany << " several types (a shared wrapper "
         << "or reuse), " << heapNone << " no typed write\n";
  size_t shown = 0;
  for (auto &[r, L] : originLabel)
    if (L.kind == Heap && L.types.size() > 1 && shown++ < 12) {
      originValues(r, vals);
      std::string where = "?";
      for (const Value *V : vals)
        if (const auto *I2 = dyn_cast<Instruction>(V))
          where = I2->getFunction()->getName().str();
      errs() << "TypeLabels:   heap @" << where << " typed as " << L.types.size()
             << " structs:";
      size_t k = 0;
      for (const std::string &T : L.types)
        if (k++ < 8)
          errs() << " " << T;
      errs() << "\n";
    }
  errs() << "TypeLabels: untyped writes " << blindWriteLog.size() << ": "
         << uHarmless << " reach only non-struct objects (harmless), " << uTyped
         << " reach only labeled objects (typed by label), " << uUnknown
         << " reach an unlabeled object, " << uNoFacts << " reach nothing\n";
  {
    std::vector<std::pair<size_t, std::string>> top;
    for (auto &[w, c] : uUnknownBy)
      top.emplace_back(c, w);
    std::sort(top.rbegin(), top.rend());
    for (size_t i = 0; i < top.size() && i < 10; i++)
      errs() << "TypeLabels:   still untyped " << top[i].first << " "
             << top[i].second << "\n";
  }
  auto line = [&](const char *what, const Tally &T) {
    errs() << "TypeLabels: " << what << " " << T.legit + T.mismatch + T.unknown
           << ": " << T.legit << " consistent with every label they reach, "
           << T.mismatch << " reach an object labeled otherwise (" << T.allBad
           << " only such objects; incompatible: heap-initialized "
           << T.byHeap << ", declared " << T.byDecl << ", non-struct "
           << T.byBuffer << "), " << T.unknown
           << " reach an unlabeled object\n";
  };
  line("named accesses", all);
  for (auto &[I3, why] : onlyBad) {
    std::string loc = I3->getFunction()->getName().str();
    if (const DILocation *DL3 = I3->getDebugLoc())
      loc += " " + DL3->getFilename().str() + ":" + std::to_string(DL3->getLine());
    errs() << "TypeLabels:   only-incompatible " << loc << ": " << why << "\n";
  }
  line("named icall-callee loads", icall);
  std::map<std::pair<std::string, std::string>, std::pair<size_t, const Instruction *>> mk;
  for (auto &m : mismatches) {
    auto &e = mk[{m.name, m.label}];
    if (!e.first++)
      e.second = m.I;
  }
  std::vector<std::tuple<size_t, std::string, std::string, const Instruction *>> mtop;
  for (auto &[k, v] : mk)
    mtop.emplace_back(v.first, k.first, k.second, v.second);
  std::sort(mtop.begin(), mtop.end(),
            [](auto &a, auto &b) { return std::get<0>(a) > std::get<0>(b); });
  for (size_t i = 0; i < mtop.size() && i < 15; i++) {
    const Instruction *I2 = std::get<3>(mtop[i]);
    std::string loc = I2->getFunction()->getName().str();
    if (const DILocation *L = I2->getDebugLoc())
      loc += " " + L->getFilename().str() + ":" + std::to_string(L->getLine());
    errs() << "TypeLabels:   mismatch x" << std::get<0>(mtop[i]) << " "
           << std::get<1>(mtop[i]) << " on " << std::get<2>(mtop[i]) << " ("
           << loc << ")\n";
  }

  if (!report)
    return;
  // ---- The rule report (plan 3.11 item 1) ----
  std::error_code EC;
  raw_fd_ostream RO(CFLRuleReport, EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "FATAL: cannot write " << CFLRuleReport << ": " << EC.message()
           << "\n";
    exit(1);
  }
  auto locOf = [&](const Instruction *I2) {
    std::string loc = I2->getFunction()->getName().str();
    if (const DILocation *DL2 = I2->getDebugLoc())
      loc += " " + DL2->getFilename().str() + ":" + std::to_string(DL2->getLine());
    return loc;
  };
  auto originName = [&](uint32_t r) {
    originValues(r, vals);
    for (const Value *V : vals) {
      if (const auto *I3 = dyn_cast<Instruction>(V)) {
        std::string n3 = (I3->getFunction()->getName() + "::" +
                          I3->getOpcodeName()).str();
        if (const DILocation *DL3 = I3->getDebugLoc())
          n3 += "@" + std::to_string(DL3->getLine());
        return n3;
      }
      if (V->hasName())
        return V->getName().str();
    }
    return std::string("?");
  };

  // Rule (a): an inttoptr used as a pointer whose integer carries no
  // origin. Its integer sources say what the bytes were: data (a
  // violation), a constant address, or a pointer lost before the cast
  // (an unknown: the pointer that was cast carried nothing).
  struct ForgeHit { const Instruction *I; std::string kind, sources; };
  std::vector<ForgeHit> ruleA;
  size_t aData = 0, aConst = 0, aLost = 0;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        auto *IP = dyn_cast<IntToPtrInst>(&I);
        if (!IP)
          continue;
        bool usedAsPtr = false;
        for (const User *U : IP->users()) {
          if (const auto *LI = dyn_cast<LoadInst>(U))
            usedAsPtr |= LI->getPointerOperand() == IP;
          else if (const auto *SI = dyn_cast<StoreInst>(U))
            usedAsPtr |= SI->getPointerOperand() == IP;
          else if (const auto *CB = dyn_cast<CallBase>(U))
            usedAsPtr |= CB->getCalledOperand() == IP;
          else if (const auto *G = dyn_cast<GetElementPtrInst>(U))
            usedAsPtr |= G->getPointerOperand() == IP;
        }
        if (!usedAsPtr)
          continue;
        const NodeIndex n = getRepNodeForValue(IP->getOperand(0));
        if (n != AndersNodeFactory::InvalidIndex &&
            anyFact(getCanonicalNode(n)))
          continue;
        SmallVector<const Value *, 16> work{IP->getOperand(0)};
        SmallPtrSet<const Value *, 16> seen;
        std::string srcs;
        bool lost = false, allConst = true;
        while (!work.empty() && seen.size() < 24) {
          const Value *V = work.pop_back_val();
          if (!seen.insert(V).second)
            continue;
          std::string leaf;
          if (const auto *CI = dyn_cast<ConstantInt>(V)) {
            leaf = "const";
            (void)CI;
          } else if (isa<PtrToIntInst>(V) ||
                     (isa<ConstantExpr>(V) &&
                      cast<ConstantExpr>(V)->getOpcode() == Instruction::PtrToInt)) {
            leaf = "ptrtoint";
            lost = true;
          } else if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
            work.push_back(BO->getOperand(0));
            work.push_back(BO->getOperand(1));
            continue;
          } else if (const auto *CA = dyn_cast<CastInst>(V)) {
            work.push_back(CA->getOperand(0));
            continue;
          } else if (const auto *PN = dyn_cast<PHINode>(V)) {
            for (const Value *In : PN->incoming_values())
              work.push_back(In);
            continue;
          } else if (const auto *SE = dyn_cast<SelectInst>(V)) {
            work.push_back(SE->getTrueValue());
            work.push_back(SE->getFalseValue());
            continue;
          } else if (const auto *LI = dyn_cast<LoadInst>(V)) {
            leaf = "load " + locOf(LI);
          } else if (const auto *A = dyn_cast<Argument>(V)) {
            leaf = "arg " + A->getParent()->getName().str() + "#" +
                   std::to_string(A->getArgNo());
          } else if (const auto *CB = dyn_cast<CallBase>(V)) {
            const Function *CF = CB->getCalledFunction();
            leaf = "call " + (CF ? CF->getName().str() : std::string("<icall>"));
          } else if (const auto *I4 = dyn_cast<Instruction>(V)) {
            leaf = I4->getOpcodeName();
          } else {
            leaf = "other";
          }
          if (leaf != "const")
            allConst = false;
          if (srcs.size() < 300)
            srcs += (srcs.empty() ? "" : "; ") + leaf;
        }
        const char *kind = lost ? "unknown" : allConst ? "constant" : "data";
        (lost ? aLost : allConst ? aConst : aData)++;
        if (ruleA.size() < 5000)
          ruleA.push_back({&I, kind, srcs});
      }

  // Rule (b): grouped by access; derivations for the first entries.
  std::stable_sort(ruleB.begin(), ruleB.end(),
                   [](const TypeHit &a, const TypeHit &b) {
                     return a.only > b.only;
                   });
  std::set<const Instruction *> bAcc, bOnly;
  for (auto &h : ruleB) {
    bAcc.insert(h.I);
    if (h.only)
      bOnly.insert(h.I);
  }
  std::map<std::pair<std::string, std::string>, size_t> cAgg;
  for (auto &h : ruleC)
    cAgg[{h.where, h.labels}]++;
  size_t heapAll = 0, heapUnl = 0;
  for (auto &[r, L] : originLabel)
    if (L.kind == Heap) {
      heapAll++;
      heapUnl += L.types.empty();
    }
  const std::string prog = Ctx->Modules.empty()
                               ? std::string("?")
                               : Ctx->Modules.front().first->getName().str();

  RO << "# Rule report (plan 3.11). Input: " << prog << "\n"
     << "# The call graph holds for executions that obey three rules:\n"
     << "#  (a) no pointer is made from bytes that never were a pointer;\n"
     << "#  (b) an object initialized as T is accessed only as T or as a "
        "struct embedded in T;\n"
     << "#  (c) a certified field receives no untyped write.\n"
     << "# Each violation below is a place the program (or the model) "
        "breaks one.\n";
  RO << "SUMMARY a " << aData << " pointers from data, " << aConst
     << " constant addresses; unknown " << aLost
     << " (a pointer lost before the cast)\n";
  RO << "SUMMARY b " << bAcc.size() << " named accesses reach an object "
     << "initialized as an incompatible struct (" << bOnly.size()
     << " reach only such objects), of "
     << all.legit + all.mismatch + all.unknown + icall.legit +
            icall.mismatch + icall.unknown
     << " named accesses\n";
  RO << "SUMMARY c " << ruleC.size() << " untyped writes reach a struct "
     << "object, of " << blindWriteLog.size() << " untyped writes\n";
  RO << "UNKNOWN named accesses reaching an unlabeled object: "
     << all.unknown + icall.unknown << "\n";
  RO << "UNKNOWN untyped writes reaching an unlabeled object: " << uUnknown
     << "\n";
  RO << "UNKNOWN heap objects with no typed write: " << heapUnl << " of "
     << heapAll << "\n";
  if (!emptyReadLine.empty())
    RO << "UNKNOWN " << emptyReadLine << "\n";

  RO << "\n== (a) pointers made from bytes that never were a pointer\n";
  for (auto &h : ruleA)
    RO << "A " << h.kind << " " << locOf(h.I) << " from: " << h.sources
       << "\n";

  RO << "\n== (b) accesses reaching an object initialized as an "
        "incompatible struct\n";
  size_t explained = 0;
  std::map<const Instruction *, unsigned> explainedAt;
  for (auto &h : ruleB) {
    bool isIcall = false;
    if (isa<LoadInst>(h.I))
      for (const User *U : h.I->users())
        if (const auto *CB = dyn_cast<CallBase>(U))
          isIcall |= CB->getCalledOperand() == h.I;
    RO << "B " << (h.only ? "only " : "mixed ") << locOf(h.I)
       << " access=" << accessNames->str(h.name) << (isIcall ? " icall" : "")
       << " origin=" << originName(h.rid) << " label=" << h.label << "\n";
    // Up to three origins per access, 3000 in all: every access gets a
    // derivation before any gets many.
    if (explained < 3000 && explainedAt[h.I]++ < 3) {
      explained++;
      std::string merge;
      const std::string der = explain(h.ptr, h.rid, merge);
      RO << "   derivation: " << der << "\n";
      RO << "   first merge: " << (merge.empty() ? "none (value flow only)" : merge)
         << "\n";
    }
  }

  RO << "\n== (c) untyped writes reaching a struct object\n";
  std::vector<std::tuple<size_t, std::string, std::string>> ctop;
  for (auto &[k, c] : cAgg)
    ctop.emplace_back(c, k.first, k.second);
  std::sort(ctop.begin(), ctop.end(),
            [](auto &a, auto &b) { return std::get<0>(a) > std::get<0>(b); });
  for (auto &[c, w, l] : ctop)
    RO << "C x" << c << " " << w << " reaches: " << l << "\n";
  errs() << "RuleReport: a " << aData << "+" << aConst << " const (+" << aLost
         << " unknown), b " << bAcc.size() << " accesses (" << bOnly.size()
         << " only-incompatible), c " << ruleC.size() << " -> "
         << CFLRuleReport << "\n";
}
