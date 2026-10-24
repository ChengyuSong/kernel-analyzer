/*
 * Call graph construction
 *
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// Carves.cc: pool carves (plan 3.53 rule 3, spec in 3.52). A pool hands
// out pieces of a chunk by bumping a pointer field; every piece is the one
// chunk object unless each carve is its own origin. Recognized forms:
//   before-bump   p = load H; store H, p + n; result p
//   minus-len     store H, (load H) + n; result (load H) - n
//   counter       store C, (load C) - n; result (load M) + (load C)
//   header        c = malloc(HDR + n); c stored in a chunk field; result c + HDR
// The hypothesis is that a chunk's carved contents are reached only
// through carve results. Two checks establish it statically:
//   handle fields: every value loaded from a field holding chunk pointers
//     (H, M, and the fields such values are stored into) is used only by
//     the forms, by stores into handle fields, compares, pointer
//     differences, free and memset; a store into H of another value is a
//     rewind (FREE semantics: the pieces after it are dead);
//   chunk bases: an allocation stored into a handle field is accessed
//     only below its header (the header's own fields), and the only GEP
//     at or past the header is the header carve.
// A pool has one cursor (bump or counter field) and it only moves forward:
// a cursor that moves back is a stack, two cursors through one chunk are a
// queue, and both read back what they handed out. A handle field whose
// address is taken is written where the checks do not look. A use outside
// these refuses the pool, printed with its site. Reported
// at --verbose=2. With --cfl-pool-carves the carves of certified pools
// become allocation sites (GraphBuild) and fresh sources for the wrapper
// confirmer, whose R2/R3 exempt the pools' bookkeeping (GAPS.md, "Pool
// carves").

#include "CallGraphInternal.h"
#include <llvm/Analysis/CFG.h>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DebugInfo.h>
#include <chrono>
#include "NamedCells.h"

#include <llvm/IR/Dominators.h>

namespace {

std::string instLocStr(const Instruction *I) {
  std::string s = I->getFunction()->getName().str();
  if (const DILocation *L = I->getDebugLoc())
    s += " " + L->getFilename().str() + ":" + std::to_string(L->getLine());
  return s;
}

std::string instText(const Value *I) {
  std::string s;
  raw_string_ostream os(s);
  if (isa<Instruction>(I)) I->print(os);
  else I->printAsOperand(os, true);
  s = os.str();
  if (size_t p = s.find(", !dbg"); p != std::string::npos) s.resize(p);
  size_t b = s.find_first_not_of(' ');
  return b == std::string::npos ? s : s.substr(b);
}

const Value *peelInt(const Value *V) {
  while (const auto *C = dyn_cast<CastInst>(V))
    if (C->getSrcTy()->isIntegerTy() && C->getDestTy()->isIntegerTy()) V = C->getOperand(0);
    else break;
  return V;
}

// A local slot: an alloca used only as the address of loads and stores.
bool localSlot(const Value *A) {
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

// A handle value: B = derived from a load of a bump or counter-base field
// (a pointer into a chunk's free space), C = a chunk base (an allocation
// stored into a handle field, or a load of a list field).
struct HV {
  char flavor = 'C';               // C chunk base, B free-space pointer, L link pointer (P1 G1)
  std::string field;               // the field it was loaded from ("" for an allocation)
  const CallBase *alloc = nullptr; // the allocation it is (C), in this function
  std::string pool;                // a field of its pool
  std::set<std::string> links;     // L: the link fields it addresses
  const Instruction *src = nullptr; // B: the cursor load it comes from
  const StoreInst *saved = nullptr; // B: the saved-cursor slot store it was reloaded from
  const LoadInst *savedLoad = nullptr; // B: and the slot load
};

} // namespace

void CallGraphPass::checkPoolCarves() {
  poolVerdicts.clear();
  poolInteriorRefillRows.clear();
  poolInteriorHeader = poolInteriorBump = poolInteriorNot = 0;
  // A field access's key: the debug-info struct of the base pointer (the
  // IR merges isomorphic structs: objalloc and demangler_engine are one IR
  // type), else the IR struct; "" if the access names no struct field.
  std::set<std::string> irFallback;
  // Array fields keyed by their element accesses: key -> the array's bytes.
  std::map<std::string, int64_t> arrayBytes;
  std::function<std::string(const Instruction *, const Value *)> fieldKey = [&](const Instruction *I,
                                                                                const Value *Addr) -> std::string {
    if (isa<AllocaInst>(Addr->stripPointerCasts())) return "";
    StructType *S = nullptr;
    int64_t off = 0;
    if (!accessSlot(I, Addr, I->getModule()->getDataLayout(), S, off)) {
      // An element of an array field (`allocator->free[i]`, P1 G1): the
      // array field's key, every element one field.
      const Value *A = Addr; // casts only: free[0] is an all-zero GEP
      while (const auto *BC = dyn_cast<BitCastOperator>(A)) A = BC->getOperand(0);
      const auto *G = dyn_cast<GEPOperator>(A);
      if (!G || !isa<ArrayType>(G->getSourceElementType()) || G->getNumIndices() != 2) return "";
      const auto *Z = dyn_cast<ConstantInt>(G->idx_begin()->get());
      const GEPOperator *B = structGEP(G->getPointerOperand());
      if (!Z || !Z->isZero() || !B || !isa<StructType>(B->getSourceElementType()) || B->hasAllZeroIndices()) return "";
      const std::string k = fieldKey(I, G->getPointerOperand());
      if (!k.empty())
        arrayBytes[k] = (int64_t)I->getModule()->getDataLayout().getTypeAllocSize(G->getSourceElementType());
      return k;
    }
    // An element of an array of S (`(cp + 1)->m`) is the same field.
    if (const int64_t sz = (int64_t)I->getModule()->getDataLayout().getTypeAllocSize(S); sz > 0)
      off = ((off % sz) + sz) % sz;
    const std::string ir = stripStructNameSuffix(S->getName()).str();
    std::string name;
    if (const GEPOperator *G = structGEP(Addr)) {
      if (G->getSourceElementType() == S) {
        const Value *B = G->getPointerOperand()->stripPointerCasts();
        name = diDeclaredStruct(B, true);
        // -O3: an SSA pointer's variable, from its dbg.value.
        if (name.empty()) {
          SmallVector<DbgValueInst *, 2> DVs;
          findDbgValues(DVs, const_cast<Value *>(B));
          for (DbgValueInst *DV : DVs)
            if (name.empty())
              if (const StringRef N = ka::diStructName(DV->getVariable()->getType(), true); !N.empty())
                name = "struct." + N.str();
        }
        // A declared struct the IR still has under its own name is
        // another view of the bytes (a cast): the access's type names it.
        if (!name.empty() && name != ir && StructType::getTypeByName(I->getContext(), name))
          name.clear();
      }
    } else {
      name = ir; // struct-path TBAA: the source's own struct
    }
    const bool fb = name.empty();
    if (fb) name = ir;
    std::string k = name.substr(name.find('.') + 1) + "+" + std::to_string(off);
    if (fb) irFallback.insert(k);
    return k;
  };
  auto isAllocCall = [&](const CallBase *CB) {
    const Function *C = CB ? CB->getCalledFunction() : nullptr;
    if (!C) return false;
    if (Ctx->AllocFuncs.count(C)) return true;
    auto it = Ctx->FuncSummaries.find(C);
    return it != Ctx->FuncSummaries.end() && it->second->fresh;
  };
  auto freesArg = [&](const CallBase *CB, unsigned ai) {
    const Function *C = CB->getCalledFunction();
    if (!C) return false;
    if (isa<MemSetInst>(CB)) return ai == 0;
    if (C->getName() == "free" || C->getName() == "cfree") return ai == 0;
    auto it = Ctx->FuncSummaries.find(C);
    return it != Ctx->FuncSummaries.end() && it->second->freeArg == (int)ai;
  };

  // A body GraphBuild does not build (a summary replaces it, or it is
  // skipped) is not judged (G4, Fable 2026-10-23, P1): the carve premise
  // ranges over the accesses in the model; a body replaced by its summary
  // is not in the model, and the summary's audit stands for it.
  // Casts only: stripPointerCasts would also strip an all-zero GEP, which
  // is &node->next (a link address), not the node (P1 G1).
  auto castsOnly = [](const Value *V) {
    for (;;) {
      if (const auto *BC = dyn_cast<BitCastOperator>(V)) V = BC->getOperand(0);
      else if (const auto *AC = dyn_cast<AddrSpaceCastOperator>(V)) V = AC->getOperand(0);
      else return V;
    }
  };
  // (d) Is the field "S+off" a char pointer by debug info (the leaf member
  // at that byte offset, through nested structs and typedefs)?
  std::map<std::string, const DICompositeType *> diStructs;
  for (auto &[M, _] : Ctx->Modules) {
    DebugInfoFinder DF;
    DF.processModule(*M);
    for (const DIType *T : DF.types())
      if (const auto *CT = dyn_cast<DICompositeType>(T);
          CT && CT->getTag() == dwarf::DW_TAG_structure_type && !CT->getName().empty() && !CT->getElements().empty())
        diStructs.emplace(CT->getName().str(), CT);
  }
  auto charPtrField = [&](const std::string &key) {
    const size_t plus = key.rfind('+');
    if (plus == std::string::npos) return false;
    auto it = diStructs.find(key.substr(0, plus));
    if (it == diStructs.end()) return false;
    uint64_t off = std::stoull(key.substr(plus + 1)) * 8;
    const DIType *T = it->second;
    for (int d = 0; d < 8 && T; d++) {
      while (const auto *DT = dyn_cast<DIDerivedType>(T)) {
        if (DT->getTag() == dwarf::DW_TAG_pointer_type) {
          const DIType *B = DT->getBaseType();
          for (const auto *BD = dyn_cast_or_null<DIDerivedType>(B); BD && BD->getTag() != dwarf::DW_TAG_pointer_type;
               BD = dyn_cast_or_null<DIDerivedType>(B))
            B = BD->getBaseType();
          const auto *BT = dyn_cast_or_null<DIBasicType>(B);
          return off == 0 && BT && (BT->getEncoding() == dwarf::DW_ATE_signed_char || BT->getEncoding() == dwarf::DW_ATE_unsigned_char);
        }
        T = DT->getBaseType();
        if (!T) return false;
      }
      const auto *CT = dyn_cast<DICompositeType>(T);
      if (!CT) return false;
      const DIType *next = nullptr;
      for (const DINode *E : CT->getElements())
        if (const auto *Mb = dyn_cast<DIDerivedType>(E); Mb && Mb->getTag() == dwarf::DW_TAG_member &&
                                                           Mb->getOffsetInBits() <= off &&
                                                           off < Mb->getOffsetInBits() + std::max<uint64_t>(Mb->getSizeInBits(), 1)) {
          off -= Mb->getOffsetInBits();
          next = Mb->getBaseType();
          break;
        }
      T = next;
    }
    return false;
  };
  auto unjudged = [&](const Function &F) {
    return F.isDeclaration() || F.empty() || (Ctx->AllocFuncs.count(&F) && !summaryKeepsBody(Ctx, &F)) ||
           Ctx->ContainerFuncs.count(&F) || shouldSkipFunction(&F);
  };
  // Does V come from an allocation (through casts, GEPs, local slots)?
  // The slot walks below go 8 hops deep; at -O0 a slot has many loads and
  // stores, so each query remembers the (value, depth) pairs it has seen:
  // the same answer, without the exponential re-walks (cjpeg -O0 hung).
  std::set<std::pair<const Value *, int>> seenAlloc;
  std::function<bool(const Value *, int)> fromAlloc = [&](const Value *V, int d) -> bool {
    if (d > 8) return false;
    if (d == 0) seenAlloc.clear();
    if (!seenAlloc.insert({V, d}).second) return false; // walked from here at this depth
    V = V->stripPointerCasts();
    if (const auto *G = dyn_cast<GEPOperator>(V)) return fromAlloc(G->getPointerOperand(), d + 1);
    if (const auto *CB = dyn_cast<CallBase>(V)) return isAllocCall(CB);
    if (const auto *L = dyn_cast<LoadInst>(V))
      if (localSlot(L->getPointerOperand()))
        for (const User *U : L->getPointerOperand()->users())
          if (const auto *S = dyn_cast<StoreInst>(U))
            if (fromAlloc(S->getValueOperand(), d + 1)) return true;
    return false;
  };
  // The allocation V comes from (fromAlloc's walk), and whether V is at a
  // nonzero offset of it (a GEP with a nonzero index on the way); a slot
  // with several writes prefers one at offset 0.
  std::set<std::pair<const Value *, int>> seenAt;
  std::function<const CallBase *(const Value *, int, bool &)> allocAt = [&](const Value *V, int d,
                                                                            bool &inner) -> const CallBase * {
    if (d > 8) return nullptr;
    if (d == 0) seenAt.clear();
    if (!seenAt.insert({V, d}).second) return nullptr;
    V = V->stripPointerCasts();
    if (const auto *G = dyn_cast<GEPOperator>(V)) {
      bool in = inner || !G->hasAllZeroIndices();
      const CallBase *CB = allocAt(G->getPointerOperand(), d + 1, in);
      if (CB) inner = in;
      return CB;
    }
    if (const auto *CB = dyn_cast<CallBase>(V)) return isAllocCall(CB) ? CB : nullptr;
    const CallBase *first = nullptr;
    bool firstIn = false;
    if (const auto *L = dyn_cast<LoadInst>(V))
      if (localSlot(L->getPointerOperand()))
        for (const User *U : L->getPointerOperand()->users())
          if (const auto *S = dyn_cast<StoreInst>(U)) {
            bool in = inner;
            const CallBase *CB = allocAt(S->getValueOperand(), d + 1, in);
            if (CB && !in) return CB;
            if (CB && !first) first = CB, firstIn = in;
          }
    if (first) inner = firstIn;
    return first;
  };
  // The fields an allocation's result is stored into, at any offset of it
  // (through casts, GEPs and slots), except the store `except`.
  auto holdersOf = [&](const CallBase *CB, const StoreInst *except) {
    std::set<std::string> hs;
    std::vector<const Value *> w{CB};
    std::set<const Value *> seen;
    while (!w.empty()) {
      const Value *V = w.back();
      w.pop_back();
      if (!seen.insert(V).second || seen.size() > 256) continue;
      for (const User *U : V->users()) {
        if (isa<CastInst>(U) || isa<GetElementPtrInst>(U)) {
          w.push_back(U);
        } else if (const auto *S = dyn_cast<StoreInst>(U); S && S != except && S->getValueOperand() == V) {
          if (localSlot(S->getPointerOperand())) {
            for (const User *LU : S->getPointerOperand()->users())
              if (isa<LoadInst>(LU)) w.push_back(LU);
          } else if (std::string k = fieldKey(S, S->getPointerOperand()); !k.empty()) {
            hs.insert(k);
          }
        }
      }
    }
    return hs;
  };
  // Is V a formal of its function (through casts, local slots)?
  std::function<bool(const Value *, int)> fromFormal = [&](const Value *V, int d) -> bool {
    V = V->stripPointerCasts();
    if (isa<Argument>(V)) return true;
    const auto *L = dyn_cast<LoadInst>(V);
    if (d > 4 || !L || !localSlot(L->getPointerOperand())) return false;
    bool all = true, any = false;
    for (const User *U : L->getPointerOperand()->users())
      if (const auto *S = dyn_cast<StoreInst>(U)) {
        any = true;
        all &= fromFormal(S->getValueOperand(), d + 1);
      }
    return any && all;
  };
  // Is V a load of field k (through casts and joins: -O3 merges the
  // reload with a refill's value)?
  std::function<bool(const Value *, const std::string &, int)> loadsField =
      [&](const Value *V, const std::string &k, int d) -> bool {
    V = peelInt(V->stripPointerCasts());
    if (const auto *L = dyn_cast<LoadInst>(V)) return fieldKey(L, L->getPointerOperand()) == k;
    if (d > 3) return false;
    if (const auto *P = dyn_cast<PHINode>(V)) {
      for (const Value *In : P->incoming_values())
        if (loadsField(In, k, d + 1)) return true;
    } else if (const auto *Sel = dyn_cast<SelectInst>(V)) {
      return loadsField(Sel->getTrueValue(), k, d + 1) || loadsField(Sel->getFalseValue(), k, d + 1);
    }
    return false;
  };

  // The field V is a load of, through casts and -O0 local slots whose every
  // store is such a load of one field; "" if none or several.
  std::function<std::string(const Value *, int)> loadedField = [&](const Value *V, int d) -> std::string {
    V = V->stripPointerCasts();
    const auto *L = dyn_cast<LoadInst>(V);
    if (!L || d > 4) return "";
    if (!localSlot(L->getPointerOperand())) return fieldKey(L, L->getPointerOperand());
    std::string k;
    for (const User *U : L->getPointerOperand()->users())
      if (const auto *S = dyn_cast<StoreInst>(U)) {
        const std::string ks = loadedField(S->getValueOperand(), d + 1);
        if (ks.empty() || (!k.empty() && ks != k)) return "";
        k = ks;
      }
    return k;
  };
  // Does GEP G step back (a negative constant, or the negation of a
  // length: `p - n`)?
  auto stepsBack = [](const GEPOperator *G) {
    for (const Use &Ix : G->indices()) {
      const Value *X = peelInt(Ix.get());
      if (const auto *C = dyn_cast<ConstantInt>(X); C && C->isNegative()) return true;
      if (const auto *BO = dyn_cast<BinaryOperator>(X)) {
        const auto *Z = dyn_cast<ConstantInt>(BO->getOperand(0));
        const auto *M = dyn_cast<ConstantInt>(BO->getOperand(1));
        if (BO->getOpcode() == Instruction::Sub && Z && Z->isZero()) return true;
        if (BO->getOpcode() == Instruction::Mul && M && M->isMinusOne()) return true;
      }
    }
    return false;
  };

  std::set<std::string> handleFields, bumpFields, baseFields; // baseFields: counter carves' M
  // Bumped fields that also move back (`top - 1` stored: a stack, which
  // reads back what it handed out).
  std::map<std::string, const Instruction *> backward;
  // Handle fields that receive pointers into the free space (saved
  // cursors, a queue's tail): their loads are free-space pointers (B).
  std::set<std::string> interior;
  // A pool's bump or base field is refilled with an allocation (a chunk)
  // somewhere; a bumped field never refilled is a cursor over data.
  std::set<std::string> refilled;
  size_t cursors = 0;
  // RF (Fable 2026-10-24): a refill stores the allocation's own result
  // (offset 0, through casts and slots). A pointer at a nonzero offset of
  // an allocation is a refill only as the header form, which the chunk-base
  // walk records in refills (c + HDR from a chunk base whose every holding
  // field the closure joins into the pool); any other is not a refill, and
  // a field with no other refill is a cursor (demoted by the run loop).
  std::set<std::string> refilled0;
  std::map<std::string, std::vector<std::pair<const StoreInst *, const CallBase *>>> interiorRefills;
  std::set<std::string> demotedRefill;
  // Pools: fields joined by a value of one stored into another.
  std::map<std::string, std::string> parent;
  std::function<std::string(const std::string &)> pool = [&](const std::string &f) -> std::string {
    auto it = parent.find(f);
    if (it == parent.end() || it->second == f) return f;
    return it->second = pool(it->second);
  };
  auto join = [&](const std::string &a, const std::string &b) {
    if (a.empty() || b.empty()) return;
    parent.emplace(a, a);
    parent.emplace(b, b);
    const std::string ra = pool(a), rb = pool(b);
    if (ra == rb) return;
    // A placeholder pool ("@" + a chunk source or formal, P1) is never the
    // representative of a set that has a field.
    if (ra[0] == '@' && rb[0] != '@') parent[ra] = rb;
    else parent[rb] = ra;
  };

  struct Carve { const Instruction *I; std::string form, field; CarveSize size; };
  struct Refusal { std::string field, why; const Instruction *I; };
  std::vector<Carve> carves;
  std::vector<Refusal> refusals;
  std::vector<std::pair<const Instruction *, std::string>> rewinds;
  // (e) Refills (Fable 2026-10-23, P1): a chunk base + header stored into a
  // bump field, the cursor set to the chunk's first carve position.
  std::vector<std::pair<const Instruction *, std::string>> refills;
  // A -O0 slot holding a free-space pointer whose load is stored back into a
  // handle field (a saved cursor): followed load by load, not carved at the
  // store. (store into the slot, store back, its handle field)
  struct SavedCursor { const StoreInst *S, *Back; std::string field; };
  std::vector<SavedCursor> savedCursors;
  // (d) Bytes written into the free space before the bump that hands them
  // out (Fable 2026-10-23): byte copies and char-pointer cursors, judged
  // again at the solve.
  std::vector<std::pair<const Instruction *, std::string>> preBump; // (use, what)
  std::vector<std::pair<const Instruction *, std::string>> chunkAllocs; // (allocation call, a field of its pool)
  std::vector<std::pair<const Instruction *, std::string>> preBumpPool; // (use, a field of its pool)
  // The pools' own bookkeeping: stores into handle fields, rewinds,
  // pointer arithmetic on handles (with a field of their pool).
  std::vector<std::pair<const Instruction *, std::string>> bookkeeping;

  // Bumps and counter decrements, per function; counter carves name M.
  std::map<const Function *, std::set<std::string>> bumpIn, counterIn;
  // (b) The bump through a slot (Fable 2026-10-23): `endp = node->first_avail
  // + K` computed first (on one or more paths: the -O0 slot every store of
  // which is H + K, one K), then `node->first_avail = endp` after the carve.
  // Per (function, field): K, and the end stores (the same-node check).
  std::map<std::pair<const Function *, std::string>, int64_t> slotBumpK;
  std::map<std::pair<const Function *, std::string>, std::vector<const StoreInst *>> slotBumpEnds;
  std::map<std::pair<const Function *, std::string>, std::vector<const StoreInst *>> slotBumps;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M) {
      if (unjudged(F)) continue;
      for (const Instruction &I : instructions(F)) {
        const auto *SI = dyn_cast<StoreInst>(&I);
        if (!SI) continue;
        const std::string k = fieldKey(SI, SI->getPointerOperand());
        if (k.empty()) continue;
        const Value *V = SI->getValueOperand();
        if (V->getType()->isPointerTy()) {
          bool inner = false;
          if (const CallBase *CB = allocAt(V, 0, inner)) {
            refilled.insert(k);
            if (!inner) refilled0.insert(k);
            else interiorRefills[k].push_back({SI, CB});
          }
        }
        if (const auto *LE = dyn_cast<LoadInst>(V->stripPointerCasts());
            LE && V->getType()->isPointerTy() && localSlot(LE->getPointerOperand())) {
          int64_t K = -1;
          std::vector<const StoreInst *> ends;
          for (const User *U : LE->getPointerOperand()->users())
            if (const auto *ES = dyn_cast<StoreInst>(U); ES && ES->getPointerOperand() == LE->getPointerOperand()) {
              const auto *EG = dyn_cast<GEPOperator>(ES->getValueOperand()->stripPointerCasts());
              APInt eo(64, 0);
              if (!EG || !EG->accumulateConstantOffset(F.getParent()->getDataLayout(), eo) || eo.getSExtValue() <= 0 ||
                  !loadsField(EG->getPointerOperand(), k, 0) || (K >= 0 && K != eo.getSExtValue())) {
                K = -2;
                break;
              }
              K = eo.getSExtValue();
              ends.push_back(ES);
            }
          if (K > 0) {
            bumpIn[&F].insert(k);
            bumpFields.insert(k);
            slotBumpK[{&F, k}] = K;
            slotBumpEnds[{&F, k}] = ends;
            slotBumps[{&F, k}].push_back(SI);
          }
        }
        if (V->getType()->isPointerTy()) {
          const auto *G = dyn_cast<GEPOperator>(V->stripPointerCasts());
          if (G && !G->hasAllZeroIndices() && loadsField(G->getPointerOperand(), k, 0)) {
            if (stepsBack(G)) {
              backward.emplace(k, SI);
            } else {
              bumpIn[&F].insert(k);
              bumpFields.insert(k);
            }
          }
        } else if (const auto *B = dyn_cast<BinaryOperator>(peelInt(V))) {
          // C - n, or C + (negative constant) at -O3.
          const auto *NC = dyn_cast<ConstantInt>(B->getOperand(1));
          const bool down = B->getOpcode() == Instruction::Sub ||
                            (B->getOpcode() == Instruction::Add && NC && NC->isNegative());
          if (down && loadsField(B->getOperand(0), k, 0)) counterIn[&F].insert(k);
        }
      }
    }
  // (a) A bump through a field of the carved chunk (Fable 2026-10-23, P1):
  // `pool = node->first_avail; pool->self_first_avail = (char *)pool + K;
  // node->first_avail = pool->self_first_avail;`. A field J is a carry of
  // H when EVERY store to J in the program stores (a load of H) + K, one
  // constant K for all; then `H := load J` bumps H by K. Any other store
  // to J: not a carry, and the store is named (carryRefused).
  std::map<std::string, std::pair<std::string, int64_t>> carry; // J -> (H, K)
  std::map<std::string, std::pair<const StoreInst *, std::string>> carryRefused; // J -> (the store that is not H + K, H)
  std::map<std::pair<const Function *, std::string>, int64_t> carryBumpK; // (F, H) -> K of its bump through J
  {
    std::map<std::string, std::vector<const StoreInst *>> storesOf;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        if (!unjudged(F))
          for (const Instruction &I : instructions(F))
            if (const auto *SI = dyn_cast<StoreInst>(&I); SI && SI->getValueOperand()->getType()->isPointerTy())
              if (const std::string k = fieldKey(SI, SI->getPointerOperand()); !k.empty()) storesOf[k].push_back(SI);
    // Every store judged (IR order): the first (H, K) a store gives is the
    // candidate; any store that is not H + K names the field's refusal.
    for (auto &[j, ss] : storesOf) {
      std::string h;
      int64_t K = -1;
      const StoreInst *bad = nullptr;
      for (const StoreInst *SI : ss) {
        const auto *G = dyn_cast<GEPOperator>(SI->getValueOperand()->stripPointerCasts());
        APInt off(64, 0);
        std::string hk;
        if (G && G->accumulateConstantOffset(SI->getModule()->getDataLayout(), off) && off.getSExtValue() > 0)
          hk = loadedField(G->getPointerOperand(), 0);
        if (hk.empty() || hk == j || (!h.empty() && (hk != h || off.getSExtValue() != K))) {
          if (!bad) bad = SI;
          continue;
        }
        if (h.empty()) h = hk, K = off.getSExtValue();
      }
      if (h.empty()) continue; // no store of the form: not a candidate
      if (bad) {
        carryRefused[j] = {bad, h};
        continue;
      }
      carry[j] = {h, K};
    }
    // The bumps through a carry: H := load J.
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        if (!unjudged(F))
          for (const Instruction &I : instructions(F))
            if (const auto *SI = dyn_cast<StoreInst>(&I)) {
              const auto *L = dyn_cast<LoadInst>(SI->getValueOperand()->stripPointerCasts());
              if (!L) continue;
              const std::string j = fieldKey(L, L->getPointerOperand());
              auto c = carry.find(j);
              if (c == carry.end() || fieldKey(SI, SI->getPointerOperand()) != c->second.first) continue;
              bumpIn[&F].insert(c->second.first);
              bumpFields.insert(c->second.first);
              carryBumpK[{&F, c->second.first}] = c->second.second;
            }
  }
  // Counter carves: gep (load M), C with C decremented here (its reload,
  // or the decremented value itself at -O3).
  auto counterCarve = [&](const GEPOperator *G, const Function *F, std::string *cOut = nullptr) -> std::string {
    if (G->getNumIndices() != 1) return "";
    const auto *LM = dyn_cast<LoadInst>(G->getPointerOperand()->stripPointerCasts());
    const Value *X = peelInt(G->idx_begin()->get());
    if (!LM || !counterIn.count(F)) return "";
    // The counter field X is: its reload, the value stored into it, or a
    // join of those (-O3 merges inlined copies).
    std::function<std::string(const Value *, int)> counterOf = [&](const Value *X, int d) -> std::string {
      X = peelInt(X);
      if (const auto *LC = dyn_cast<LoadInst>(X)) return fieldKey(LC, LC->getPointerOperand());
      for (const User *U : X->users())
        if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == X)
          return fieldKey(S, S->getPointerOperand());
      const auto *P = dyn_cast<PHINode>(X);
      if (!P || d > 3) return "";
      std::string c;
      for (const Value *In : P->incoming_values()) {
        const std::string ci = counterOf(In, d + 1);
        if (ci.empty() || (!c.empty() && ci != c)) return "";
        c = ci;
      }
      return c;
    };
    const std::string c = counterOf(X, 0);
    const std::string m = fieldKey(LM, LM->getPointerOperand());
    if (m.empty() || !counterIn[F].count(c)) return "";
    if (m.substr(0, m.rfind('+')) != c.substr(0, c.rfind('+'))) return ""; // one struct
    join(m, c);
    if (cOut) *cOut = c;
    return m;
  };
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      if (!unjudged(F))
        for (const Instruction &I : instructions(F))
          if (const auto *G = dyn_cast<GEPOperator>(&I))
            if (std::string m = counterCarve(G, &F); !m.empty()) baseFields.insert(m);
  for (auto *set : {&bumpFields, &baseFields})
    for (auto it = set->begin(); it != set->end();)
      if (refilled.count(*it)) {
        ++it;
      } else {
        cursors++;
        it = set->erase(it);
      }
  for (auto &[F, ks] : bumpIn)
    for (auto it = ks.begin(); it != ks.end();)
      it = bumpFields.count(*it) ? std::next(it) : ks.erase(it);
  handleFields.insert(bumpFields.begin(), bumpFields.end());
  handleFields.insert(baseFields.begin(), baseFields.end());
  for (const std::string &f : handleFields) parent.emplace(f, f);
  if (handleFields.empty()) {
    CG_LOG("PoolCarve: no pools (" << cursors << " bumped fields never refilled: cursors)\n");
    return;
  }

  // G2 (Fable 2026-10-23, P1): a chunk source is a built function every
  // one of whose returns is a chunk base or null (through slots, joins and
  // casts); its call results are chunk bases of its pool, by name (the call
  // may name a declaration). G1, G2 and G5 depend on each other (a free
  // list's loads are chunk bases when its stores are, which come from the
  // sources' results), so they are the greatest fixpoint: every candidate
  // assumed, the check run from the initial handle fields, the candidates
  // the run contradicts removed, and the check run again until it removes
  // none. Sound: every value a run of the program stores or returns traces
  // to a source that is not an assumption (an allocation, null).
  std::map<std::string, std::string> chunkSources; // name -> a field of its pool
  std::map<std::string, size_t> chunkReturns;
  // G1 (Fable 2026-10-23, P1): link fields (every store a chunk base or
  // null), link-holding fields (every store an address of a link field); a
  // link pointer loads and stores its links. G5: a formal every direct call
  // of whose function passes a chunk base or null is a chunk base (the dual
  // of G2).
  std::map<std::string, std::string> linkFields;                 // key -> a field of its pool
  std::map<std::string, std::set<std::string>> linkHolding;      // key -> the link fields it holds addresses of
  std::map<std::string, size_t> linkGood, holdGood;               // the last round's stores, per field
  std::map<std::string, const Instruction *> linkBad, holdBad;    // the first store that is not one
  std::map<std::pair<std::string, unsigned>, std::string> chunkParams; // (function, arg) -> a field of its pool
  std::map<std::pair<std::string, unsigned>, size_t> paramGood;
  std::set<std::pair<std::string, unsigned>> paramBad;
  std::vector<const Instruction *> linkSteps;                     // L +- constant inside an array link field
  std::map<std::string, std::set<std::string>> holdLast;          // the last round's link addresses stored, per field
  // G3: chunk-base GEPs stored into the same chunk's non-bump header
  // fields (end bounds), by receiving field.
  std::map<std::string, std::set<const Instruction *>> boundStores;
  // Two addresses of one chunk base: the same value, or two loads of one
  // -O0 slot in one block with no store to the slot between them.
  auto sameBase = [&](const Value *A, const Value *B) {
    A = A->stripPointerCasts();
    B = B->stripPointerCasts();
    if (A == B) return true;
    const auto *LA = dyn_cast<LoadInst>(A), *LB = dyn_cast<LoadInst>(B);
    if (!LA || !LB || LA->getPointerOperand() != LB->getPointerOperand() || !localSlot(LA->getPointerOperand()) ||
        LA->getParent() != LB->getParent())
      return false;
    if (LB->comesBefore(LA)) std::swap(LA, LB);
    for (const Instruction *I = LA->getNextNode(); I && I != LB; I = I->getNextNode())
      if (const auto *S = dyn_cast<StoreInst>(I); S && S->getPointerOperand() == LA->getPointerOperand()) return false;
    return true;
  };
  // The candidates (by the IR's shapes; the runs decide).
  std::set<std::string> lmis; // link and link-holding fields whose link pointers a run used otherwise
  std::map<std::string, std::string> lmisAt; // the first such use, per field
  std::map<std::string, bool> srcLast;
  std::map<std::string, const Instruction *> srcWhyLast;
  std::vector<std::string> removedRows; // every candidate a run removed, with its reason
  std::map<std::string, std::string> srcPoolLast;
  {
    // Sources: every return traces (through casts, slots, joins) to null,
    // an allocation call, a call of another candidate, or a load through a
    // link candidate (a link field, or a pointer a slot holds: `*ref`).
    // The same greatest fixpoint: a return of any other shape is never a
    // chunk base, so its function fails every run and is only removed
    // before the first. Computed after the link candidates.
    // Link fields: a pointer field whose address is stored somewhere
    // (&node->next, &free[i]); link-holding fields: a field such addresses,
    // or loads of a link-holding field, are stored into.
    auto linkAddr = [&](const Value *V) -> std::string {
      const auto *G = dyn_cast<GEPOperator>(castsOnly(V));
      if (!G || !G->getResultElementType()->isPointerTy()) return "";
      const auto *I = dyn_cast<Instruction>(G);
      if (!I) return "";
      if (isa<ArrayType>(G->getSourceElementType()) || (structGEP(G) && isa<StructType>(G->getSourceElementType())))
        return fieldKey(I, G);
      return "";
    };
    for (int pass = 0; pass < 2; pass++)
      for (auto &[M, _] : Ctx->Modules)
        for (Function &F : *M)
          if (!unjudged(F))
            for (const Instruction &I : instructions(F))
              if (const auto *S = dyn_cast<StoreInst>(&I); S && S->getValueOperand()->getType()->isPointerTy()) {
                const std::string k = fieldKey(S, S->getPointerOperand());
                if (k.empty()) continue;
                const Value *X = castsOnly(S->getValueOperand());
                if (const std::string l = linkAddr(X); !l.empty()) {
                  linkFields.emplace(l, l);
                  linkHolding[k].insert(l);
                } else if (const auto *L = dyn_cast<LoadInst>(X)) {
                  if (auto lh = linkHolding.find(fieldKey(L, L->getPointerOperand())); lh != linkHolding.end()) {
                    const std::set<std::string> ls = lh->second;
                    linkHolding[k].insert(ls.begin(), ls.end());
                  }
                }
              }
    // &free[i] kept in a slot is a link address too (a store into a slot
    // has no key above).
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        if (!unjudged(F))
          for (const Instruction &I : instructions(F))
            if (const auto *S = dyn_cast<StoreInst>(&I); S && localSlot(S->getPointerOperand()))
              if (const std::string l = linkAddr(S->getValueOperand()); !l.empty()) linkFields.emplace(l, l);
    {
      std::map<std::string, std::set<std::string>> callsOf; // candidate -> the functions its returns call
      std::set<std::string> cand;
      for (auto &[M, _] : Ctx->Modules)
        for (Function &F : *M) {
          if (unjudged(F) || !F.getReturnType()->isPointerTy()) continue;
          std::set<const Value *> seen;
          std::set<std::string> calls;
          std::function<bool(const Value *, int)> shape = [&](const Value *V, int d) -> bool {
            V = castsOnly(V);
            if (isa<ConstantPointerNull>(V) || !seen.insert(V).second) return true;
            if (d > 8) return false;
            if (const auto *L = dyn_cast<LoadInst>(V)) {
              const Value *A = castsOnly(L->getPointerOperand());
              if (!localSlot(A)) {
                if (linkFields.count(fieldKey(L, A))) return true;
                const auto *LA = dyn_cast<LoadInst>(A);
                return LA && localSlot(LA->getPointerOperand()); // *ref
              }
              bool any = false;
              for (const User *U : A->users())
                if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == A) {
                  if (!shape(S->getValueOperand(), d + 1)) return false;
                  any = true;
                }
              return any;
            }
            if (const auto *P = dyn_cast<PHINode>(V)) {
              for (const Value *In : P->incoming_values())
                if (!shape(In, d + 1)) return false;
              return true;
            }
            if (const auto *Sel = dyn_cast<SelectInst>(V))
              return shape(Sel->getTrueValue(), d + 1) && shape(Sel->getFalseValue(), d + 1);
            if (const auto *CB = dyn_cast<CallBase>(V)) {
              if (isAllocCall(CB)) return true;
              const Function *CF = CB->getCalledFunction();
              if (!CF) return false;
              calls.insert(CF->getName().str());
              return true;
            }
            return false;
          };
          bool ok = true, any = false;
          for (const Instruction &I : instructions(F))
            if (const auto *R = dyn_cast<ReturnInst>(&I); R && R->getReturnValue())
              any = true, ok = ok && shape(R->getReturnValue(), 0);
          if (ok && any) cand.insert(F.getName().str()), callsOf[F.getName().str()] = calls;
        }
      for (bool cut = true; cut;) {
        cut = false;
        for (auto it = cand.begin(); it != cand.end();) {
          bool ok = true;
          for (const std::string &c : callsOf[*it]) ok &= cand.count(c) > 0;
          if (ok) ++it;
          else it = cand.erase(it), cut = true;
        }
      }
      for (const std::string &f : cand) chunkSources[f] = "@" + f;
    }
    // Formals: those that reach (through casts and slots) a store into a
    // link field, or a candidate formal of a direct call.
    std::map<std::pair<std::string, unsigned>, std::set<std::pair<std::string, unsigned>>> passesTo;
    std::set<std::pair<std::string, unsigned>> direct;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (unjudged(F) || F.hasAddressTaken()) continue;
        for (const Argument &A : F.args()) {
          if (!A.getType()->isPointerTy()) continue;
          const std::pair<std::string, unsigned> me{F.getName().str(), A.getArgNo()};
          std::vector<const Value *> w{&A};
          std::set<const Value *> seen;
          while (!w.empty()) {
            const Value *V = w.back();
            w.pop_back();
            if (!seen.insert(V).second || seen.size() > 64) continue;
            for (const User *U : V->users()) {
              if (isa<CastInst>(U)) w.push_back(U);
              else if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == V) {
                if (localSlot(S->getPointerOperand())) {
                  for (const User *LU : S->getPointerOperand()->users())
                    if (isa<LoadInst>(LU)) w.push_back(LU);
                } else if (linkFields.count(fieldKey(S, S->getPointerOperand()))) {
                  direct.insert(me);
                }
              } else if (const auto *CB = dyn_cast<CallBase>(U)) {
                if (const Function *CF = CB->getCalledFunction(); CF && !CF->isDeclaration())
                  for (unsigned ai = 0; ai < CB->arg_size(); ai++)
                    if (CB->getArgOperand(ai) == V) passesTo[me].insert({CF->getName().str(), ai});
              }
            }
          }
        }
      }
    std::set<std::pair<std::string, unsigned>> cand = direct;
    for (bool grew = true; grew;) {
      grew = false;
      for (auto &[f, to] : passesTo)
        if (!cand.count(f))
          for (auto &t : to)
            if (cand.count(t)) {
              cand.insert(f);
              grew = true;
              break;
            }
    }
    for (auto &fa : cand) chunkParams[fa] = "@" + fa.first + "#" + std::to_string(fa.second);
  }
  std::set<std::string> handle0 = handleFields;
  const std::set<std::string> candidates0 = handle0; // RF: the rows are of these fields
  const auto parent0 = parent;
  unsigned restarts = 0;
  for (;; restarts++) {
  const auto tRun = std::chrono::steady_clock::now();
  size_t rounds = 0;
  handleFields = handle0;
  parent = parent0;
  interior.clear();
  chunkReturns.clear();
  lmis.clear();
  lmisAt.clear();
  // To a fixpoint over the handle fields; the last round records.
  for (;;) {
    const size_t before = handleFields.size(), beforeInterior = interior.size();
    rounds++;
    std::map<std::string, bool> srcObs;
    std::map<std::string, std::string> srcPoolObs;
    std::map<std::string, const Instruction *> srcWhyObs; // the first return that is not a chunk base
    std::map<std::string, size_t> lg, hg;
    std::map<std::string, const Instruction *> lb, hb;
    std::map<std::pair<std::string, unsigned>, std::string> paramPool;
    // A stored pointer value's class: 'C' chunk base or null, 'L' a link
    // address, ' ' anything else (in the function's own analysis).
    std::map<std::pair<std::string, unsigned>, size_t> pg;
    std::set<std::pair<std::string, unsigned>> pb;
    carves.clear();
    bookkeeping.clear();
    refusals.clear();
    rewinds.clear();
    refills.clear();
    savedCursors.clear();
    preBump.clear();
    chunkAllocs.clear();
    preBumpPool.clear();
    boundStores.clear();
    linkSteps.clear();
    std::map<std::string, std::set<std::string>> holdLinks; // key -> the link fields its L stores address
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (unjudged(F)) continue;
        std::map<const Value *, HV> hv;
        std::vector<const Value *> work;
        std::vector<std::pair<const Value *, HV>> mixed; // values that are a link pointer and a handle
        std::vector<std::pair<const StoreInst *, HV>> linkStores; // stores through link pointers
        std::vector<std::pair<const Instruction *, HV>> pendingSteps; // steps of a link pointer with no array link yet
        std::vector<std::pair<const StoreInst *, HV>> unkeyedStores;   // handles stored where no field key names the address
        // Saved-cursor slots: per slot load, its first carve (one hand-out
        // at most may come out of a saved cursor).
        std::map<const StoreInst *, std::map<const LoadInst *, std::pair<const Instruction *, HV>, IROrder>, IROrder> savedCarves;
        auto add = [&](const Value *V, const HV &h) {
          auto [it, fresh] = hv.emplace(V, h);
          if (fresh) {
            work.push_back(V);
          } else if (h.flavor == 'L' && it->second.flavor == 'L') {
            const size_t b = it->second.links.size();
            it->second.links.insert(h.links.begin(), h.links.end());
            if (it->second.links.size() != b) work.push_back(V);
          } else if ((h.flavor == 'L') != (it->second.flavor == 'L')) {
            // One value, a link pointer by one path and a handle by another.
            const HV &l = h.flavor == 'L' ? h : it->second;
            lmis.insert(l.field);
            mixed.push_back({V, l});
          }
        };
        // Allocations stored (through casts, GEPs, local slots) into a
        // handle field are chunk bases.
        std::set<std::pair<const Value *, int>> seenReach;
        std::function<std::string(const Value *, int)> reachesHandle = [&](const Value *V, int d) -> std::string {
          if (d > 8) return "";
          if (d == 0) seenReach.clear();
          if (!seenReach.insert({V, d}).second) return ""; // walked from here at this depth
          for (const User *U : V->users()) {
            if (const auto *S = dyn_cast<StoreInst>(U)) {
              if (S->getValueOperand() != V) continue;
              if (localSlot(S->getPointerOperand())) {
                for (const User *LU : S->getPointerOperand()->users())
                  if (isa<LoadInst>(LU))
                    if (std::string k = reachesHandle(LU, d + 1); !k.empty()) return k;
              } else if (std::string k = fieldKey(S, S->getPointerOperand()); handleFields.count(k)) {
                return k;
              }
            } else if (isa<CastInst>(U) || isa<GetElementPtrInst>(U)) {
              if (std::string k = reachesHandle(U, d + 1); !k.empty()) return k;
            }
          }
          return "";
        };
        // Chunk bases first: a free-space pointer stored into a chunk's
        // header is a handle, which needs the header's base known.
        std::vector<std::pair<const Value *, HV>> bSeeds;
        for (const Argument &A : F.args())
          if (auto cp = chunkParams.find({F.getName().str(), A.getArgNo()}); cp != chunkParams.end()) {
            HV h;
            h.pool = cp->second;
            add(&A, h);
          }
        // A value stored somewhere (not only used as an address).
        auto storedAsValue = [](const Value *V) {
          for (const User *U : V->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == V) return true;
          return false;
        };
        for (const Instruction &I : instructions(F)) {
          if (const auto *G = dyn_cast<GetElementPtrInst>(&I); G && isa<ArrayType>(G->getSourceElementType()) &&
                                                               storedAsValue(G)) {
            // &free[i] (an element of an array link field) kept in a slot.
            const std::string k = fieldKey(G, G);
            if (auto lf = linkFields.find(k); lf != linkFields.end()) {
              HV h;
              h.flavor = 'L';
              h.links = {k};
              h.field = k;
              h.pool = lf->second;
              add(G, h);
            }
            continue;
          }
          if (const auto *L = dyn_cast<LoadInst>(&I)) {
            if (!L->getType()->isPointerTy()) continue;
            const std::string k = fieldKey(L, L->getPointerOperand());
            if (auto lh = linkHolding.find(k); lh != linkHolding.end() && !lh->second.empty()) {
              HV h;
              h.flavor = 'L';
              h.links = lh->second;
              h.field = k;
              h.pool = linkFields.count(*lh->second.begin()) ? linkFields.at(*lh->second.begin()) : k;
              add(L, h);
              continue;
            }
            if (handleFields.count(k)) {
              HV h;
              h.flavor = (bumpFields.count(k) || baseFields.count(k) || interior.count(k)) ? 'B' : 'C';
              h.field = h.pool = k;
              h.src = L;
              if (h.flavor == 'B') bSeeds.push_back({L, h});
              else add(L, h);
            }
          } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
            if (const Function *CF = CB->getCalledFunction(); CF && CB->getType()->isPointerTy())
              if (auto cs = chunkSources.find(CF->getName().str()); cs != chunkSources.end()) {
                HV h;
                h.alloc = CB;
                h.pool = cs->second;
                add(CB, h);
                bookkeeping.push_back({CB, cs->second}); // the pool's own state: a chunk obtained
                continue;
              }
            if (!isAllocCall(CB) || !CB->getType()->isPointerTy()) continue;
            if (std::string k = reachesHandle(CB, 0); !k.empty()) {
              HV h;
              h.alloc = CB;
              h.pool = k;
              chunkAllocs.push_back({CB, k});
              add(CB, h);
            }
          }
        }
        auto isHandle = [&](const Value *V) {
          return hv.count(V) || isa<ConstantPointerNull>(V->stripPointerCasts());
        };
        // Is V (a B value) the bump: stored into its own field?
        auto isBump = [&](const Value *V, const HV &h) {
          auto se = slotBumpEnds.find({&F, h.field});
          for (const User *U : V->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == V) {
              if (fieldKey(S, S->getPointerOperand()) == h.field) return true;
              // (b) the end, computed first into the end slot
              if (se != slotBumpEnds.end() && std::count(se->second.begin(), se->second.end(), S)) return true;
            }
          return false;
        };
        // A carve's size by its form (CallGraph.h, CarveSize); a size
        // operand of another shape is left unknown. n's from the stores
        // of field k in F whose value step(V) gives: all of them the same.
        auto oneOf = [&](const std::string &k, const std::function<const Value *(const Value *)> &step) {
          const Value *n = nullptr;
          for (const Instruction &J : instructions(F))
            if (const auto *S = dyn_cast<StoreInst>(&J); S && fieldKey(S, S->getPointerOperand()) == k) {
              const Value *x = step(S->getValueOperand());
              if (!x) continue;
              const auto *a = dyn_cast<ConstantInt>(x), *b = dyn_cast_or_null<ConstantInt>(n);
              if (n && x != n && !(a && b && a->getValue() == b->getValue())) return (const Value *)nullptr;
              n = x;
            }
          return n;
        };
        auto scaleOf = [&](const GEPOperator *G) {
          return (uint64_t)F.getParent()->getDataLayout().getTypeAllocSize(G->getSourceElementType());
        };
        auto negated = [&](const Value *X) -> const Value * {
          X = peelInt(X);
          if (const auto *K = dyn_cast<ConstantInt>(X); K && K->isNegative())
            return ConstantInt::get(K->getType(), -K->getValue());
          if (const auto *BO = dyn_cast<BinaryOperator>(X)) {
            const auto *Z = dyn_cast<ConstantInt>(BO->getOperand(0));
            const auto *M = dyn_cast<ConstantInt>(BO->getOperand(1));
            if (BO->getOpcode() == Instruction::Sub && Z && Z->isZero()) return BO->getOperand(1);
            if (BO->getOpcode() == Instruction::Mul && M && M->isMinusOne()) return BO->getOperand(0);
          }
          return nullptr;
        };
        auto sizeOf = [&](const Instruction *I, const std::string &form, const HV &h) {
          CarveSize z;
          const auto *G = dyn_cast<GEPOperator>(I);
          if (form == "minus-len" && G && G->getNumIndices() == 1) {
            if ((z.n = negated(G->idx_begin()->get()))) z.scale = scaleOf(G);
          } else if (form == "counter" && G) {
            std::string c;
            counterCarve(G, &F, &c);
            if (!c.empty()) {
              z.n = oneOf(c, [&](const Value *V) -> const Value * {
                const auto *B = dyn_cast<BinaryOperator>(peelInt(V));
                if (!B || !loadsField(B->getOperand(0), c, 0)) return nullptr;
                if (B->getOpcode() == Instruction::Sub) return B->getOperand(1);
                return B->getOpcode() == Instruction::Add ? negated(B->getOperand(1)) : nullptr;
              });
              z.scale = scaleOf(G);
            }
          } else if (form == "before-bump" && slotBumpK.count({&F, h.field})) {
            // (b): the bump through the end slot: K bytes.
            z.n = ConstantInt::get(Type::getInt64Ty(F.getContext()), slotBumpK.at({&F, h.field}));
            z.scale = 1;
          } else if (form == "before-bump" && carryBumpK.count({&F, h.field})) {
            // (a): the bump through the carry field: K bytes.
            z.n = ConstantInt::get(Type::getInt64Ty(F.getContext()), carryBumpK.at({&F, h.field}));
            z.scale = 1;
          } else if (form == "before-bump") {
            uint64_t sc = 0;
            auto bumpOf = [&](const Value *V) -> const Value * {
              const auto *B = dyn_cast<GEPOperator>(V->stripPointerCasts());
              if (!B || B->getNumIndices() != 1 || stepsBack(B) || !loadsField(B->getPointerOperand(), h.field, 0))
                return nullptr;
              if (sc && sc != scaleOf(B)) sc = UINT64_MAX;
              else sc = scaleOf(B);
              return B->idx_begin()->get();
            };
            z.n = oneOf(h.field, bumpOf);
            if (!z.n) {
              // Two bumps (A2' (1), -O3 bfd_alloc): a variable x, and a
              // constant K only on blocks dominated by the true edge of
              // `x == 0`, x on none of them: "x, K when x == 0".
              sc = 0;
              std::vector<std::pair<const StoreInst *, const Value *>> bs;
              for (const Instruction &J : instructions(F))
                if (const auto *S = dyn_cast<StoreInst>(&J); S && fieldKey(S, S->getPointerOperand()) == h.field)
                  if (const Value *x = bumpOf(S->getValueOperand())) bs.push_back({S, x});
              const Value *X = nullptr;
              const ConstantInt *K = nullptr;
              bool ok = sc && sc != UINT64_MAX;
              for (auto &[S, x] : bs) {
                if (const auto *c = dyn_cast<ConstantInt>(x)) {
                  if (K && K->getValue() != c->getValue()) ok = false;
                  K = c;
                } else if (X && X != x) ok = false;
                else X = x;
              }
              if (ok && X && K && !K->isNegative()) {
                DominatorTree DT(const_cast<Function &>(F));
                // The true edges of the branches on `X == 0`.
                std::vector<BasicBlockEdge> zero;
                for (const User *U : X->users())
                  if (const auto *Cmp = dyn_cast<ICmpInst>(U);
                      Cmp && Cmp->getPredicate() == ICmpInst::ICMP_EQ && Cmp->getOperand(0) == X &&
                      isa<ConstantInt>(Cmp->getOperand(1)) && cast<ConstantInt>(Cmp->getOperand(1))->isZero())
                    for (const User *CU : Cmp->users())
                      if (const auto *Br = dyn_cast<BranchInst>(CU); Br && Br->isConditional() && Br->getCondition() == Cmp)
                        zero.emplace_back(Br->getParent(), Br->getSuccessor(0));
                auto underZero = [&](const StoreInst *S) {
                  for (const BasicBlockEdge &E : zero)
                    if (DT.dominates(E, S->getParent())) return true;
                  return false;
                };
                for (auto &[S, x] : bs) ok = ok && (isa<ConstantInt>(x) ? underZero(S) : !underZero(S));
                if (ok) {
                  z.n = X;
                  z.zeroK = (int64_t)K->getZExtValue();
                  z.how = 'z';
                }
              }
            }
            if (sc == UINT64_MAX || !sc) z.n = nullptr;
            else z.scale = sc;
          } else if (form == "header" && G && h.flavor == 'C' && h.alloc) {
            // c + HDR over the chunk call itself (through casts and a
            // slot stored once).
            const Value *B = G->getPointerOperand()->stripPointerCasts();
            for (int d = 0; d < 4 && B != h.alloc; d++) {
              const auto *L = dyn_cast<LoadInst>(B);
              if (!L || !localSlot(L->getPointerOperand())) break;
              const StoreInst *only = nullptr;
              int stores = 0;
              for (const User *U : L->getPointerOperand()->users())
                if (const auto *S = dyn_cast<StoreInst>(U)) only = S, stores++;
              if (stores != 1) break;
              B = only->getValueOperand()->stripPointerCasts();
            }
            APInt off(64, 0);
            if (B == h.alloc && G->accumulateConstantOffset(F.getParent()->getDataLayout(), off)) {
              z.chunk = h.alloc;
              z.off = off.getSExtValue();
            }
            // A header carve c followed by the store H := c + x into its
            // pool's bump field (A2' (3), -O3 objalloc's new small chunk):
            // the piece is x, the rest of the chunk the later carves' space.
            const Value *x = nullptr;
            uint64_t sc = 0;
            bool one = true;
            for (const User *U : I->users())
              if (const auto *G2 = dyn_cast<GEPOperator>(U); G2 && G2->getPointerOperand() == I && G2->getNumIndices() == 1)
                for (const User *GU : G2->users())
                  if (const auto *S = dyn_cast<StoreInst>(GU); S && S->getValueOperand() == G2) {
                    const std::string k = fieldKey(S, S->getPointerOperand());
                    if (!bumpFields.count(k) || pool(k) != pool(h.pool)) continue;
                    if (x && (x != G2->idx_begin()->get() || sc != scaleOf(G2))) one = false;
                    x = G2->idx_begin()->get();
                    sc = scaleOf(G2);
                  }
            // Also H := chunk + off2 (the GEPs folded: c + 8 written chunk +
            // 24): the constant piece off2 - off.
            if (z.chunk)
              for (const User *U : h.alloc->users())
                if (const auto *G2 = dyn_cast<GEPOperator>(U); G2 && G2 != G && G2->getPointerOperand() == h.alloc)
                  for (const User *GU : G2->users())
                    if (const auto *S = dyn_cast<StoreInst>(GU); S && S->getValueOperand() == G2) {
                      const std::string k = fieldKey(S, S->getPointerOperand());
                      APInt o2(64, 0);
                      if (!bumpFields.count(k) || pool(k) != pool(h.pool) ||
                          !G2->accumulateConstantOffset(F.getParent()->getDataLayout(), o2) || o2.getSExtValue() <= z.off)
                        continue;
                      const Value *c = ConstantInt::get(Type::getInt64Ty(F.getContext()), o2.getSExtValue() - z.off);
                      if (x && (!isa<ConstantInt>(x) || cast<ConstantInt>(x)->getSExtValue() != o2.getSExtValue() - z.off || sc != 1))
                        one = false;
                      x = c;
                      sc = 1;
                    }
            if (x && one && sc) {
              z.n = x;
              z.scale = sc;
              z.how = 'h';
            }
          }
          return z;
        };
        auto carve = [&](const Instruction *I, const std::string &form, const std::string &f, const HV &h) {
          // One pointer, one carve: a cast (or zero-offset GEP) of a carve
          // is that carve, recorded at the value it casts.
          if (const auto *B = dyn_cast<Instruction>(I->stripPointerCasts())) I = B;
          if (h.saved) savedCarves[h.saved].emplace(h.savedLoad, std::make_pair(I, h));
          for (const Carve &c : carves)
            if (c.I == I) return;
          carves.push_back({I, form, f, sizeOf(I, form, h)});
        };
        auto refuse = [&](const HV &h, const std::string &why, const Instruction *at) {
          if (h.flavor == 'L' && !h.field.empty()) lmisAt.emplace(h.field, instLocStr(at) + ": " + why);
          refusals.push_back({h.pool, why, at});
        };
        // A data use of V: the forms, or a refusal.
        // The node a cursor load reads through: the slot it is loaded from
        // (-O0) or the value itself, and its load (the same-node check).
        auto nodeLoadOf = [&](const Value *X) -> const LoadInst * {
          X = X->stripPointerCasts();
          while (const auto *G = dyn_cast<GEPOperator>(X)) X = G->getPointerOperand()->stripPointerCasts();
          const auto *L = dyn_cast<LoadInst>(X);
          if (!L) return nullptr;
          const GEPOperator *NG = structGEP(L->getPointerOperand());
          const auto *N = NG ? dyn_cast<LoadInst>(NG->getPointerOperand()->stripPointerCasts()) : nullptr;
          return N && localSlot(N->getPointerOperand()) ? N : nullptr;
        };
        // The node a field address is of: the -O0 slot load under its GEP.
        auto nodeOfAddr = [&](const Value *A) -> const LoadInst * {
          const GEPOperator *G = structGEP(A);
          const auto *N = G ? dyn_cast<LoadInst>(castsOnly(G->getPointerOperand())) : nullptr;
          return N && localSlot(N->getPointerOperand()) ? N : nullptr;
        };
        // (b) same node: no store to the node's slot can run between the
        // load the end was computed on and the carve's (or the bump's) load.
        // Is To reachable from just after From without passing an
        // instruction of Avoid?
        auto reachAvoiding = [&](const Instruction *From, const Instruction *To,
                                 const std::set<const Instruction *> &Avoid) {
          std::set<const BasicBlock *> seen;
          std::vector<const Instruction *> w{From->getNextNode()};
          while (!w.empty()) {
            const Instruction *I = w.back();
            w.pop_back();
            for (; I; I = I->getNextNode()) {
              if (I == To) return true;
              if (Avoid.count(I)) break;
              if (I->isTerminator())
                for (const BasicBlock *Su : successors(I->getParent()))
                  if (seen.insert(Su).second) w.push_back(&Su->front());
            }
          }
          return false;
        };
        // The end and the carve read one node when no store to the node's
        // slot can run after the end's node load and before the carve's,
        // unless an end store (recomputing the end) follows it first.
        auto sameNode = [&](const LoadInst *Ne, const LoadInst *Nc, const std::set<const Instruction *> &ends) {
          if (!Ne || !Nc || Ne->getPointerOperand() != Nc->getPointerOperand()) return false;
          for (const User *U : Ne->getPointerOperand()->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == Ne->getPointerOperand())
              if (isPotentiallyReachable(Ne, S) && reachAvoiding(S, Nc, ends)) return false;
          return true;
        };
        // (c) The chunk-source call a free-space value's node is, when the
        // node comes from one such call in this function (through a slot
        // every store of which is that call) and does not escape: its uses
        // are header accesses, compares, stores into fields of its own
        // hand-out, and chunk formals; null otherwise.
        std::function<const CallBase *(const Value *, int)> nodeCall = [&](const Value *X, int d) -> const CallBase * {
          X = X->stripPointerCasts();
          if (const auto *CB = dyn_cast<CallBase>(X)) {
            const Function *CF = CB->getCalledFunction();
            return CF && chunkSources.count(CF->getName().str()) ? CB : nullptr;
          }
          const auto *L = dyn_cast<LoadInst>(X);
          if (!L || d > 3 || !localSlot(L->getPointerOperand())) return nullptr;
          const CallBase *one = nullptr;
          for (const User *U : L->getPointerOperand()->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == L->getPointerOperand()) {
              const CallBase *c = nodeCall(S->getValueOperand(), d + 1);
              if (!c || (one && one != c)) return nullptr;
              one = c;
            }
          return one;
        };
        auto handoutNode = [&](const Value *V) -> const CallBase * {
          const Value *X = V->stripPointerCasts();
          while (const auto *G = dyn_cast<GEPOperator>(X)) X = G->getPointerOperand()->stripPointerCasts();
          if (const auto *L = dyn_cast<LoadInst>(X); L && localSlot(L->getPointerOperand())) {
            // A slot of hand-outs (and other pieces): the one node whose
            // hand-out it holds; several such nodes, none.
            const CallBase *one = nullptr;
            for (const User *U : L->getPointerOperand()->users())
              if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == L->getPointerOperand()) {
                const Value *Y = castsOnly(S->getValueOperand());
                while (const auto *G = dyn_cast<GEPOperator>(Y)) Y = castsOnly(G->getPointerOperand());
                const auto *YL = dyn_cast<LoadInst>(Y);
                const GEPOperator *NG = YL ? structGEP(YL->getPointerOperand()) : nullptr;
                const CallBase *c = NG && bumpFields.count(fieldKey(YL, YL->getPointerOperand()))
                                        ? nodeCall(NG->getPointerOperand(), 0) : nullptr;
                if (c && one && one != c) return nullptr;
                if (c) one = c;
              }
            return one;
          }
          const auto *L = dyn_cast<LoadInst>(X);
          const GEPOperator *NG = L ? structGEP(L->getPointerOperand()) : nullptr;
          if (!NG || !bumpFields.count(fieldKey(L, L->getPointerOperand()))) return nullptr;
          return nodeCall(NG->getPointerOperand(), 0);
        };
        std::map<const CallBase *, std::string> escapeOf; // the node call -> "" or its escaping use
        auto escapes = [&](const CallBase *CB) -> std::string {
          if (auto it = escapeOf.find(CB); it != escapeOf.end()) return it->second;
          std::string why;
          std::vector<const Value *> w{CB};
          std::set<const Value *> seen;
          while (!w.empty() && why.empty()) {
            const Value *X = w.back();
            w.pop_back();
            if (!seen.insert(X).second) continue;
            for (const User *U : X->users()) {
              if (isa<ICmpInst>(U) || isa<DbgInfoIntrinsic>(U)) continue;
              if (isa<CastInst>(U)) { w.push_back(U); continue; }
              if (const auto *G = dyn_cast<GEPOperator>(U); G && structGEP(G) && G->getPointerOperand()->stripPointerCasts() == X->stripPointerCasts()) {
                bool header = true; // the node's own fields, read or written
                for (const User *GU : G->users())
                  header &= (isa<LoadInst>(GU)) || (isa<StoreInst>(GU) && cast<StoreInst>(GU)->getPointerOperand() == G);
                if (header) continue;
              }
              if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == X) {
                if (localSlot(S->getPointerOperand())) {
                  for (const User *LU : S->getPointerOperand()->users())
                    if (isa<LoadInst>(LU)) w.push_back(LU);
                  continue;
                }
                if (handoutNode(S->getPointerOperand()) == CB) continue; // into its own hand-out's field
              }
              if (const auto *C = dyn_cast<CallBase>(U); C && C != CB && C->getCalledFunction()) {
                bool ok = true;
                for (unsigned ai = 0; ai < C->arg_size(); ai++)
                  if (C->getArgOperand(ai) == X) ok &= chunkParams.count({C->getCalledFunction()->getName().str(), ai}) > 0;
                if (ok) continue;
              }
              why = isa<Instruction>(U) ? instText(cast<Instruction>(U)) : std::string("a constant");
              break;
            }
          }
          return escapeOf[CB] = why;
        };
        auto dataUse = [&](const Value *V, const HV &h, const Instruction *at) {
          const auto *I = dyn_cast<Instruction>(V);
          if (!I) return refuse(h, "a constant handle used as data: " + instText(at), at);
          if (h.flavor == 'B') {
            if (h.field.empty() && h.alloc) return carve(I, "header", h.pool, h); // a new chunk's first piece
            if (const auto *G = dyn_cast<GEPOperator>(V)) {
              if (!counterCarve(G, &F).empty()) return carve(I, "counter", h.field, h);
            }
            // (c) The whole tail of a node this function obtained and keeps:
            // the free space past its bump (or all of it, with no bump).
            const bool past = isBump(V, h);
            // Is the node bumped in this function (a store into the cursor
            // of that node)? Then a pre-bump read is a before-bump carve.
            auto nodeBumped = [&](const CallBase *CB) {
              for (const Instruction &J : instructions(F))
                if (const auto *S = dyn_cast<StoreInst>(&J); S && fieldKey(S, S->getPointerOperand()) == h.field)
                  if (const GEPOperator *AG = structGEP(S->getPointerOperand()); AG && nodeCall(AG->getPointerOperand(), 0) == CB)
                    return true;
              return false;
            };
            if (const CallBase *CB = handoutNode(V); CB && (past || !nodeBumped(CB))) {
              const std::string why = escapes(CB);
              if (why.empty()) return carve(I, "whole-tail", h.field, h);
              return refuse(h, "a whole tail whose node escapes (" + why + "): " + instText(at), at);
            }
            if (slotBumpK.count({&F, h.field})) {
              // (b) The carve and the bump read the node the end was computed on.
              const LoadInst *Nc = nodeLoadOf(h.src ? h.src : V);
              std::set<const Instruction *> ends(slotBumpEnds[{&F, h.field}].begin(), slotBumpEnds[{&F, h.field}].end());
              for (const StoreInst *E : slotBumpEnds[{&F, h.field}])
                if (!sameNode(nodeLoadOf(E->getValueOperand()), Nc, ends))
                  return refuse(h, "a carve whose end was computed on another node (" + instText(E) + "): " + instText(at), at);
              for (const StoreInst *Bs : slotBumps[{&F, h.field}])
                if (!sameNode(Nc, nodeOfAddr(Bs->getPointerOperand()), {}))
                  return refuse(h, "a carve whose bump writes another node (" + instText(Bs) + "): " + instText(at), at);
            }
            if (bumpIn.count(&F) && bumpIn[&F].count(h.field)) {
              const auto *G = dyn_cast<GEPOperator>(V);
              return carve(I, G && !G->hasAllZeroIndices() ? "minus-len" : "before-bump", h.field, h);
            }
            // (d) pre-bump bytes: a byte copy into or out of the free space,
            // or the free-space pointer (or one past an offset of it) kept
            // only in char-pointer fields (a formatter's cursor and end).
            if (isa<MemTransferInst>(at)) {
              preBump.push_back({at, "a byte copy"});
              preBumpPool.push_back({at, h.pool});
              return;
            }
            {
              const Value *P = isa<GEPOperator>(at) ? static_cast<const Value *>(at) : V;
              std::vector<std::string> keys;
              bool ok = true;
              for (const User *U : P->users()) {
                if (isa<ICmpInst>(U) || isa<PtrToIntInst>(U) || isa<DbgInfoIntrinsic>(U)) continue;
                const auto *S = dyn_cast<StoreInst>(U);
                const std::string k = S && S->getValueOperand() == P ? fieldKey(S, S->getPointerOperand()) : "";
                if (k.empty() || !charPtrField(k)) {
                  ok = false;
                  break;
                }
                keys.push_back(k);
              }
              if (ok && !keys.empty()) {
                preBump.push_back({at, "kept in the char pointer " + keys.front()});
                preBumpPool.push_back({at, h.pool});
                return;
              }
            }
            return refuse(h, "a pointer into the free space used as data where nothing bumps it: " + instText(at), at);
          }
          if (const auto *G = dyn_cast<GEPOperator>(V))
            if (h.alloc && G->hasAllConstantIndices() && !G->hasAllZeroIndices())
              return carve(I, "header", h.pool, h);
          refuse(h, "a chunk base used as data: " + instText(at), at);
        };
        auto drain = [&]() {
          while (!work.empty()) {
            const Value *V = work.back();
            work.pop_back();
            const HV h = hv[V];
            for (const User *U : V->users()) {
              const auto *UI = dyn_cast<Instruction>(U);
              if (!UI || isa<DbgInfoIntrinsic>(UI)) continue;
              if (isa<ICmpInst>(UI)) continue;
              if (h.flavor == 'L') { // a link pointer (G1)
                const std::string l0 = *h.links.begin();
                if (isa<PtrToIntInst>(UI)) {
                  bookkeeping.push_back({UI, l0});
                  continue;
                }
                if (const auto *L = dyn_cast<LoadInst>(UI)) { // a link: a chunk base
                  HV c;
                  c.pool = h.pool;
                  c.field = l0;
                  add(L, c);
                  bookkeeping.push_back({L, l0});
                  continue;
                }
                if (const auto *S = dyn_cast<StoreInst>(UI)) {
                  if (S->getPointerOperand() == V && S->getValueOperand() != V) {
                    // A store into the links: judged with every store to them,
                    // once the function's values are all known.
                    linkStores.push_back({S, h});
                    bookkeeping.push_back({S, l0});
                    continue;
                  }
                  const Value *A = S->getPointerOperand();
                  if (localSlot(A)) {
                    for (const User *LU : A->users())
                      if (isa<LoadInst>(LU)) add(LU, h);
                    continue;
                  }
                  if (const std::string k = fieldKey(S, A); !k.empty()) { // a link-holding field
                    holdLinks[k].insert(h.links.begin(), h.links.end());
                    hg[k]++;
                    handleFields.insert(k);
                    join(h.pool, k);
                    bookkeeping.push_back({S, k});
                    continue;
                  }
                  lmis.insert(h.field), refuse(h, "a link pointer stored where no struct field names it: " + instText(S), S);
                  continue;
                }
                if (isa<CastInst>(UI)) {
                  add(UI, h);
                  continue;
                }
                if (const auto *G = dyn_cast<GetElementPtrInst>(UI)) {
                  // ref +- 1 over free[] (under no-UB, the walk stays inside
                  // it): the step keeps the array links; a scalar link field
                  // stepped would leave its object, which no-UB excludes.
                  HV st = h;
                  st.links.clear();
                  for (const std::string &k : h.links)
                    if (arrayBytes.count(k)) st.links.insert(k);
                  if (G->getNumIndices() == 1 && isa<ConstantInt>(G->idx_begin()->get())) {
                    // Judged once the links are all known (they grow as the
                    // slot's stores arrive; a step is re-run when they do).
                    if (st.links.empty()) {
                      pendingSteps.push_back({G, h});
                    } else {
                      linkSteps.push_back(G);
                      add(G, st);
                    }
                    continue;
                  }
                  lmis.insert(h.field), refuse(h, "a link pointer stepped other than by a constant inside an array link field: " + instText(G), G);
                  continue;
                }
                if (isa<PHINode>(UI) || isa<SelectInst>(UI)) {
                  add(UI, h); // its other incoming values are checked below
                  continue;
                }
                lmis.insert(h.field), refuse(h, "a link pointer used other than to load or store its links: " + instText(UI), UI);
                continue;
              }
            if (isa<PtrToIntInst>(UI)) {
              bookkeeping.push_back({UI, h.pool});
              continue;
            }
              if (const auto *S = dyn_cast<StoreInst>(UI)) {
                if (S->getValueOperand() == V) {
                  const Value *A = S->getPointerOperand();
                  if (localSlot(A)) {
                    // A free-space pointer kept in a -O0 slot is a hand-out: the carve
                    // is the stored value, so every load of the slot sees one object
                    // (each load a carve would split one hand-out). The end slot of a
                    // slot bump ((b)) keeps the pointer a handle: its loads bump.
                    // A slot whose loads are stored back into a handle field
                    // is a saved cursor (a rewind through a local): its loads
                    // are followed, each judged where it is used.
                    auto savedCursor = [&]() {
                      for (const User *LU : A->users())
                        if (isa<LoadInst>(LU))
                          for (const User *SU : LU->users())
                            if (const auto *SS = dyn_cast<StoreInst>(SU); SS && SS->getValueOperand() == LU)
                              if (const std::string k = fieldKey(SS, SS->getPointerOperand());
                                  !k.empty() && (k == h.field || handleFields.count(k))) {
                                if (std::none_of(savedCursors.begin(), savedCursors.end(),
                                                 [&](const SavedCursor &c) { return c.S == S; }))
                                  savedCursors.push_back({S, SS, k});
                                return true;
                              }
                      return false;
                    };
                    auto se = slotBumpEnds.find({&F, h.field});
                    const bool endSlot = se != slotBumpEnds.end() && std::count(se->second.begin(), se->second.end(), S);
                    const bool saved = h.flavor == 'B' && !endSlot && savedCursor();
                    if (h.flavor == 'B' && !endSlot && !saved) {
                      dataUse(V, h, S);
                      continue;
                    }
                    for (const User *LU : A->users())
                      if (const auto *L = dyn_cast<LoadInst>(LU)) {
                        HV hl = h;
                        if (saved) hl.saved = S, hl.savedLoad = L;
                        add(L, hl);
                      }
                    continue;
                  }
                  const std::string k = fieldKey(S, A);
                  if (k.empty()) {
                    if (h.flavor == 'B') dataUse(V, h, S);
                    else unkeyedStores.push_back({S, h}); // through a link pointer, or refused after the drain
                    continue;
                  }
                  if (h.flavor == 'B' && k == h.field) continue; // the bump (or a re-store)
                  // The closure: a chunk base stored anywhere, or a free-space
                  // pointer saved in a chunk's header, makes a handle field.
                  const GEPOperator *AG = structGEP(A);
                  const bool header = AG && hv.count(AG->getPointerOperand()->stripPointerCasts()) &&
                                      hv[AG->getPointerOperand()->stripPointerCasts()].flavor == 'C';
                  if (h.flavor == 'B' && !handleFields.count(k) && !header) {
                    dataUse(V, h, S);
                    continue;
                  }
                  handleFields.insert(k);
                  // A field that receives a pointer into the free space
                  // holds interior pointers: its loads are not chunk starts.
                  if (h.flavor == 'B') interior.insert(k);
                  join(h.pool, k);
                  continue;
                }
                // V as the address: a chunk base's header field.
                if (h.flavor == 'C' && !fieldKey(S, S->getPointerOperand()).empty()) continue;
                if (h.flavor == 'B') dataUse(V, h, S); // through the carve, or refused
                else refuse(h, "written through: " + instText(S), S);
                continue;
              }
              if (const auto *L = dyn_cast<LoadInst>(UI)) {
                if (h.flavor == 'C' && !fieldKey(L, L->getPointerOperand()).empty()) continue;
                if (h.flavor == 'B') dataUse(V, h, L); // through the carve, or refused
                else refuse(h, "read through: " + instText(L), L);
                continue;
              }
              if (const auto *CB = dyn_cast<CallBase>(UI)) {
                bool ok = CB->getCalledOperand() != V;
                const Function *CF = CB->getCalledFunction();
                for (unsigned ai = 0; ok && ai < CB->arg_size(); ai++)
                  if (CB->getArgOperand(ai) == V && !freesArg(CB, ai) &&
                      !(h.flavor == 'C' && CF && chunkParams.count({CF->getName().str(), ai}))) // G5: a chunk formal
                    ok = false;
                if (!ok) dataUse(V, h, CB);
                continue;
              }
              if (isa<CastInst>(UI)) {
                add(UI, h);
                continue;
              }
              if (const auto *G = dyn_cast<GetElementPtrInst>(UI)) {
                if (h.flavor == 'B') {
                  if (isBump(G, h)) {
                    add(G, h);
                    continue;
                  }
                  // Bounds (`p + space` compared) carry nothing.
                  bool cmpOnly = true;
                  for (const User *GU : G->users())
                    cmpOnly &= isa<ICmpInst>(GU) || isa<PtrToIntInst>(GU) || isa<DbgInfoIntrinsic>(GU);
                  if (cmpOnly) continue;
                  // The carve is this GEP in the minus-len and counter
                  // forms; any other GEP uses V, which is the carve
                  // (before-bump) or refused.
                  if (stepsBack(cast<GEPOperator>(G)) || !counterCarve(cast<GEPOperator>(G), &F).empty())
                    dataUse(G, h, G);
                  else
                    dataUse(V, h, G);
                  continue;
                }
                // A chunk base: a header field access (a struct GEP) stays a
                // handle; any other offset is the header carve or a refusal.
                if (structGEP(G) && isa<StructType>(G->getSourceElementType())) {
                  // &node->next kept somewhere: a link pointer (G1).
                  if (const std::string k = fieldKey(G, G); linkFields.count(k) && storedAsValue(G)) {
                    HV l;
                    l.flavor = 'L';
                    l.links = {k};
                    l.field = k;
                    l.pool = h.pool;
                    add(G, l);
                    continue;
                  }
                  add(G, h);
                  continue;
                }
                bool cmpOnly = true, space = false, bound = !G->user_empty();
                for (const User *GU : G->users()) {
                  cmpOnly &= isa<ICmpInst>(GU) || isa<PtrToIntInst>(GU) || isa<DbgInfoIntrinsic>(GU);
                  if (const auto *GS = dyn_cast<StoreInst>(GU))
                    space |= GS->getValueOperand() == G && bumpFields.count(fieldKey(GS, GS->getPointerOperand()));
                  // G3 (Fable 2026-10-23, P1): an end bound, stored only into
                  // non-bump header fields of the same chunk base.
                  const auto *GS = dyn_cast<StoreInst>(GU);
                  const std::string bk = GS && GS->getValueOperand() == G ? fieldKey(GS, GS->getPointerOperand()) : "";
                  const GEPOperator *AG = GS ? structGEP(GS->getPointerOperand()) : nullptr;
                  if (bk.empty() || bumpFields.count(bk) || !AG || !sameBase(AG->getPointerOperand(), G->getPointerOperand()))
                    bound = false;
                }
                if (cmpOnly) continue;
                if (bound && !space) { // the chunk's end, saved in its own header
                  for (const User *GU : G->users())
                    boundStores[fieldKey(cast<StoreInst>(GU), cast<StoreInst>(GU)->getPointerOperand())].insert(
                        cast<StoreInst>(GU));
                  HV b = h;
                  b.flavor = 'B';
                  b.field.clear();
                  add(G, b);
                  continue;
                }
                if (space) { // the chunk's free space, stored into a bump field
                  for (const User *GU : G->users())
                    if (const auto *GS = dyn_cast<StoreInst>(GU); GS && GS->getValueOperand() == G)
                      if (const std::string k = fieldKey(GS, GS->getPointerOperand()); bumpFields.count(k))
                        refills.push_back({GS, k});
                  HV b = h;
                  b.flavor = 'B';
                  b.field.clear();
                  add(G, b);
                  continue;
                }
                dataUse(G, h, G);
                continue;
              }
              if (isa<PHINode>(UI) || isa<SelectInst>(UI)) {
                // A join used only by compares and pointer differences
                // carries no pointer (objalloc_free_block: the saved
                // pointer or the freed block, subtracted).
                bool arith = true;
                for (const User *JU : UI->users())
                  arith &= isa<ICmpInst>(JU) || isa<PtrToIntInst>(JU) || isa<DbgInfoIntrinsic>(JU);
                if (arith) {
                  for (const User *JU : UI->users())
                    if (isa<PtrToIntInst>(JU)) bookkeeping.push_back({cast<Instruction>(JU), h.pool});
                  continue;
                }
                // A chunk base joins others (checked below, once all are known).
                if (h.flavor == 'C') {
                  add(UI, h);
                  continue;
                }
                // -O3 joins the reload of a bump field with a refill's free
                // space: the join is the field's value, when every incoming
                // value is (a reload of the field, a chunk's free space, null,
                // or such a join). A join with anything else (a formal: the
                // caller's `entry`, the uncopied `string`) is a data use of
                // the free-space value, which is the carve.
                std::function<bool(const Value *, const std::string &, int)> spaceJoin =
                    [&](const Value *X, const std::string &k, int d) -> bool {
                  X = X->stripPointerCasts();
                  if (isa<ConstantPointerNull>(X) || loadsField(X, k, 3)) return true;
                  if (const auto *XG = dyn_cast<GEPOperator>(X))
                    if (fromAlloc(XG->getPointerOperand(), 0)) return true; // chunk + HDR
                  if (d > 3) return false;
                  if (const auto *P = dyn_cast<PHINode>(X)) {
                    for (const Value *In : P->incoming_values())
                      if (!spaceJoin(In, k, d + 1)) return false;
                    return true;
                  }
                  if (const auto *Sel = dyn_cast<SelectInst>(X))
                    return spaceJoin(Sel->getTrueValue(), k, d + 1) && spaceJoin(Sel->getFalseValue(), k, d + 1);
                  return false;
                };
                std::string bk;
                for (const std::string &k : bumpFields)
                  if (bk.empty() && loadsField(UI, k, 0) && spaceJoin(UI, k, 0)) bk = k;
                if (!bk.empty()) {
                  HV b = h;
                  b.field = bk;
                  add(UI, b);
                  continue;
                }
                dataUse(V, h, UI);
                continue;
              }
              if (isa<ReturnInst>(UI) && h.flavor == 'C' && chunkSources.count(F.getName().str())) continue;
              dataUse(V, h, UI); // returned, or any other use
            }
          }
        };
        drain();
        for (auto &[V, h] : bSeeds) add(V, h);
        drain();
        // A saved cursor followed load by load hands out at most one of its
        // loads: two loads carved apart would split one hand-out into two
        // objects that do not share their writes.
        for (auto &[S, byLoad] : savedCarves)
          if (byLoad.size() > 1) {
            auto a = byLoad.begin(), b = std::next(a);
            refuse(a->second.second,
                   "saved cursor handed out twice: the slot stored at " + instLocStr(S) + " is carved at " +
                       instLocStr(a->second.first) + " (" + instText(a->second.first) + ") and at " +
                       instLocStr(b->second.first) + " (" + instText(b->second.first) + ")",
                   b->second.first);
          }
        for (auto &[V, h] : mixed)
          if (const auto *I = dyn_cast<Instruction>(V))
            refuse(h, "a value that is a link pointer by one path and a chunk handle by another: " + instText(I), I);
        for (auto &[S, h] : unkeyedStores)
          if (auto it = hv.find(castsOnly(S->getPointerOperand())); it == hv.end() || it->second.flavor != 'L')
            refuse(h, "stored where no struct field names it: " + instText(S), S);
        for (auto &[G, h] : pendingSteps)
          if (!hv.count(G))
            lmis.insert(h.field),
                refuse(h, "a link pointer stepped other than by a constant inside an array link field: " + instText(G), G);
        for (auto &[S, h] : linkStores) {
          const Value *X = castsOnly(S->getValueOperand());
          auto it = hv.find(X);
          const bool ok = isa<ConstantPointerNull>(X) || (it != hv.end() && it->second.flavor == 'C');
          for (const std::string &k : hv[S->getPointerOperand()].links) {
            if (ok) lg[k]++;
            else lb.emplace(k, S);
          }
          if (!ok) refuse(h, "a value that is not a chunk base stored through a link pointer: " + instText(S), S);
        }
        for (auto &[V, h] : hv) {
          const auto *I = dyn_cast<Instruction>(V);
          if (!I || !(isa<PHINode>(I) || isa<SelectInst>(I)) || h.flavor != 'L') continue;
          for (unsigned i = isa<SelectInst>(I) ? 1 : 0; i < I->getNumOperands(); i++) {
            const Value *X = castsOnly(I->getOperand(i));
            if (!isa<ConstantPointerNull>(X) && !(hv.count(X) && hv[X].flavor == 'L'))
              lmis.insert(h.field), refuse(h, "a link pointer joined with another value: " + instText(I), I);
          }
        }
        // A join of chunk bases with anything else is a chunk base used as data.
        for (auto &[V, h] : hv) {
          const auto *I = dyn_cast<Instruction>(V);
          if (!I || !(isa<PHINode>(I) || isa<SelectInst>(I)) || h.flavor != 'C') continue;
          bool formals = true, data = false;
          for (unsigned i = isa<SelectInst>(I) ? 1 : 0; i < I->getNumOperands(); i++)
            if (!isHandle(I->getOperand(i))) {
              data = true;
              formals &= fromFormal(I->getOperand(i), 0);
            }
          if (!data) continue;
          // -O3 joins a saved pointer with the block being freed: a join of
          // handles and formals used only by compares, pointer differences
          // and stores into a bump field (the rewind) carries no pointer.
          bool rewind = formals;
          std::vector<const StoreInst *> rs;
          for (const User *U : I->users()) {
            if (isa<ICmpInst>(U) || isa<PtrToIntInst>(U) || isa<DbgInfoIntrinsic>(U)) continue;
            const auto *RS = dyn_cast<StoreInst>(U);
            rewind &= RS && RS->getValueOperand() == I && bumpFields.count(fieldKey(RS, RS->getPointerOperand()));
            if (RS) rs.push_back(RS);
          }
          if (rewind) {
            for (const StoreInst *RS : rs) {
              rewinds.push_back({RS, fieldKey(RS, RS->getPointerOperand())});
              bookkeeping.push_back({RS, fieldKey(RS, RS->getPointerOperand())});
            }
            continue;
          }
          refuse(h, "a chunk base joined with data: " + instText(I), I);
        }
        // G1: every keyed pointer store, classified for the link fields (a
        // chunk base) and the link-holding fields (a link address); null
        // is both. G5: every direct call's pointer arguments.
        for (const Instruction &I : instructions(F)) {
          if (const auto *S = dyn_cast<StoreInst>(&I); S && S->getValueOperand()->getType()->isPointerTy()) {
            const std::string k = fieldKey(S, S->getPointerOperand());
            if (k.empty()) continue;
            const Value *X = castsOnly(S->getValueOperand());
            if (isa<ConstantPointerNull>(X)) continue;
            auto it = hv.find(X);
            const char c = it == hv.end() ? ' ' : it->second.flavor;
            if (c == 'C') lg[k]++;
            else lb.emplace(k, S);
            if (c != 'L') hb.emplace(k, S);
          } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
            const Function *CF = CB->getCalledFunction();
            if (!CF || CF->isDeclaration() || CB->getCalledOperand()->stripPointerCasts() != CF) continue;
            for (unsigned ai = 0; ai < CB->arg_size() && ai < CF->arg_size(); ai++) {
              const Value *X = castsOnly(CB->getArgOperand(ai));
              if (!X->getType()->isPointerTy() || isa<ConstantPointerNull>(X)) continue;
              auto it = hv.find(X);
              if (it != hv.end() && it->second.flavor == 'C') {
                pg[{CF->getName().str(), ai}]++;
                paramPool.emplace(std::make_pair(CF->getName().str(), ai), it->second.pool);
              } else {
                pb.insert({CF->getName().str(), ai});
              }
            }
          }
        }
        // G2: every return a chunk base or null (through slots every store
        // of which is one, joins and casts): a chunk source.
        if (F.getReturnType()->isPointerTy()) {
          std::set<const Value *> seenC;
          std::string cp;
          const Value *failLeaf = nullptr; // the value that is not a chunk base
          std::function<bool(const Value *, int)> allC = [&](const Value *V, int d) -> bool {
            V = castsOnly(V);
            if (isa<ConstantPointerNull>(V) || !seenC.insert(V).second) return true;
            if (d > 8) return false;
            if (const auto *L = dyn_cast<LoadInst>(V); L && localSlot(L->getPointerOperand())) {
              bool any = false;
              for (const User *U : L->getPointerOperand()->users())
                if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == L->getPointerOperand()) {
                  if (!allC(S->getValueOperand(), d + 1)) return false;
                  any = true;
                }
              return any;
            }
            if (const auto *P = dyn_cast<PHINode>(V)) {
              for (const Value *In : P->incoming_values())
                if (!allC(In, d + 1)) return false;
              return true;
            }
            if (const auto *Sel = dyn_cast<SelectInst>(V))
              return allC(Sel->getTrueValue(), d + 1) && allC(Sel->getFalseValue(), d + 1);
            // A field's address is not the chunk (an all-zero GEP is).
            if (const auto *G = dyn_cast<GEPOperator>(V); G && !G->hasAllZeroIndices()) {
              if (!failLeaf) failLeaf = V;
              return false;
            }
            auto it = hv.find(V);
            if (it == hv.end() || it->second.flavor != 'C') {
              if (!failLeaf) failLeaf = V;
              return false;
            }
            cp = it->second.pool;
            return true;
          };
          bool all = true;
          size_t n = 0;
          for (const Instruction &I : instructions(F))
            if (const auto *R = dyn_cast<ReturnInst>(&I); R && R->getReturnValue()) {
              n++;
              if (all && !allC(R->getReturnValue(), 0)) {
                all = false;
                srcWhyObs[F.getName().str()] = failLeaf && isa<Instruction>(failLeaf) ? cast<Instruction>(failLeaf) : R;
              }
            }
          srcObs[F.getName().str()] = all && n && !cp.empty();
          if (all && n && !cp.empty()) srcPoolObs[F.getName().str()] = cp;
          chunkReturns[F.getName().str()] = n;
        }
        // Stores into handle fields of values that are not handles.
        for (const Instruction &I : instructions(F)) {
          const auto *S = dyn_cast<StoreInst>(&I);
          if (!S || !S->getValueOperand()->getType()->isPointerTy()) continue;
          const std::string k = fieldKey(S, S->getPointerOperand());
          if (!handleFields.count(k)) continue;
          // A typed store into a handle field is the pool's own state once
          // the pool is certified: classified here as a handle store, a
          // bump, a rewind, or a refusal (which refuses the pool). The
          // post-solve pass then looks only at writes this check cannot see.
          bookkeeping.push_back({S, k});
          if (isHandle(S->getValueOperand())) continue;
          bool carved = false;
          for (const Carve &c : carves) carved |= c.I == S->getValueOperand()->stripPointerCasts();
          // The bump after a carve (a new chunk's first piece + n): the
          // pool's free space, its own state.
          if (const auto *BG = dyn_cast<GEPOperator>(S->getValueOperand()->stripPointerCasts());
              BG && bumpFields.count(k)) {
            bool ofCarve = false;
            for (const Carve &c : carves) ofCarve |= c.I == BG->getPointerOperand()->stripPointerCasts();
            if (ofCarve) {
              bookkeeping.push_back({S, k});
              continue;
            }
          }
          if (bumpFields.count(k) && !carved && fromFormal(S->getValueOperand(), 0)) {
            rewinds.push_back({S, k});
            bookkeeping.push_back({S, k});
          } else if (!carved) {
            HV h;
            h.field = k;
            refuse(h, "a value that is not a chunk pointer stored into it: " + instText(S), S);
          }
        }
      }
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        if (!F.isDeclaration() && unjudged(F))
          for (const Instruction &I : instructions(F))
            if (const auto *CB = dyn_cast<CallBase>(&I))
              if (const Function *CF = CB->getCalledFunction())
                for (unsigned ai = 0; ai < CB->arg_size(); ai++) pb.insert({CF->getName().str(), ai});
    // A source's or formal's placeholder pool is the pool its chunk bases
    // come from (the returns' and the calls' pools).
    for (auto &[f, p] : srcPoolObs) join(p, "@" + f);
    for (auto &[fa, p] : paramPool) join(p, "@" + fa.first + "#" + std::to_string(fa.second));
    linkGood = lg, holdGood = hg, linkBad = lb, holdBad = hb, paramGood = pg, paramBad = pb;
    srcLast = srcObs, srcPoolLast = srcPoolObs, srcWhyLast = srcWhyObs;
    holdLast = holdLinks;
    if (handleFields.size() == before && interior.size() == beforeInterior) break;
    for (const std::string &f : handleFields) parent.emplace(f, f);
  }
  // Remove the candidates this run contradicts; run again if any.
  CG_LOG("PoolCarve: run " << restarts + 1 << ": " << rounds << " rounds, "
         << std::chrono::duration<double>(std::chrono::steady_clock::now() - tRun).count() << " s; candidates: "
         << chunkSources.size() << " sources, " << chunkParams.size() << " formals, " << linkFields.size()
         << " link fields, " << linkHolding.size() << " link-holding fields; " << handleFields.size()
         << " handle fields\n");
  bool removed = false;
  const std::string run = "run " + std::to_string(restarts + 1) + ": ";
  for (auto it = chunkSources.begin(); it != chunkSources.end();)
    if (!srcLast[it->first]) {
      const Instruction *W = srcWhyLast.count(it->first) ? srcWhyLast[it->first] : nullptr;
      removedRows.push_back(run + "chunk source " + it->first + " removed: " +
                            (W ? "a returned value that is not a chunk base or null at " + instLocStr(W) + ": " + instText(W)
                               : std::string("no chunk base in its returns")));
      it = chunkSources.erase(it), removed = true;
    } else ++it;
  for (auto it = chunkParams.begin(); it != chunkParams.end();)
    if (paramBad.count(it->first) || !paramGood[it->first]) {
      removedRows.push_back(run + "chunk formal " + it->first.first + " arg" + std::to_string(it->first.second) +
                            " removed: " + (paramBad.count(it->first) ? "a call passes a value that is not a chunk base"
                                                                      : "no direct call passes a chunk base"));
      it = chunkParams.erase(it), removed = true;
    } else ++it;
  for (auto it = linkFields.begin(); it != linkFields.end();)
    if (linkBad.count(it->first) || !linkGood[it->first] || !handleFields.count(it->first) || lmis.count(it->first)) {
      const Instruction *W = linkBad.count(it->first) ? linkBad[it->first] : nullptr;
      removedRows.push_back(run + "link field " + it->first + " removed: " +
                            (W ? "a store that is not a chunk base or null at " + instLocStr(W) + ": " + instText(W)
                             : lmis.count(it->first) ? "a link pointer to it used otherwise at " + lmisAt[it->first]
                             : !linkGood[it->first] ? std::string("no store of a chunk base")
                                                     : std::string("not a handle field")));
      it = linkFields.erase(it), removed = true;
    } else ++it;
  for (auto it = linkHolding.begin(); it != linkHolding.end();) {
    if (holdBad.count(it->first) || !holdGood[it->first] || lmis.count(it->first)) {
      const Instruction *W = holdBad.count(it->first) ? holdBad[it->first] : nullptr;
      removedRows.push_back(run + "link-pointer field " + it->first + " removed: " +
                            (W ? "a store that is not a link address or null at " + instLocStr(W) + ": " + instText(W)
                             : lmis.count(it->first) ? "a link pointer loaded from it used otherwise at " + lmisAt[it->first]
                                                     : std::string("no store of a link address")));
      it = linkHolding.erase(it), removed = true;
      continue;
    }
    std::set<std::string> now;
    for (const std::string &l : holdLast[it->first])
      if (linkFields.count(l)) now.insert(l);
    if (now != it->second) it->second = now, removed = true;
    ++it;
  }
  // RF: a field taken as refilled only by pointers at a nonzero offset of
  // an allocation, none of them a header form this run found, is a cursor.
  for (auto &[k, rs] : interiorRefills) {
    if (refilled0.count(k) || demotedRefill.count(k) || !handle0.count(k)) continue;
    bool header = false;
    for (auto &[S, CB] : rs)
      for (auto &[I, f] : refills) header |= I == S;
    if (header) continue;
    demotedRefill.insert(k);
    bumpFields.erase(k);
    baseFields.erase(k);
    for (auto &[F, ks] : bumpIn) ks.erase(k);
    handle0.erase(k);
    cursors++;
    removedRows.push_back(run + "pool candidate " + k +
                          " removed: refilled only at a nonzero offset of an allocation, not the header form (a cursor)");
    removed = true;
  }
  if (!removed) break;
  }
  // RF rows: every store of a pointer at a nonzero offset of an allocation
  // into a candidate field, the header form or not a refill.
  for (auto &[k, rs] : interiorRefills)
    for (auto &[S, CB] : rs) {
      if (!candidates0.count(k)) continue; // not a pool candidate: its refills decide nothing
      bool header = false;
      for (auto &[I, f] : refills) header |= I == S;
      // The bump after a new chunk's first piece (`o->current_ptr = chunk +
      // HDR + n`, an inlined allocation call after the refill): a carve of
      // k's own pool stepped, the pool's own state.
      bool firstBump = false;
      if (const auto *BG = dyn_cast<GEPOperator>(S->getValueOperand()->stripPointerCasts()))
        for (const Carve &c : carves)
          firstBump |= c.I == BG->getPointerOperand()->stripPointerCasts() && pool(c.field) == pool(k);
      std::string row = "refill at a nonzero offset of an allocation: ";
      if (!header && firstBump) {
        poolInteriorBump++;
        row += "the bump after a new chunk's first piece (pool " + pool(k) + ")";
      } else if (header) {
        poolInteriorHeader++;
        row += "the header form (a chunk base of pool " + pool(k) + " + its header)";
      } else {
        poolInteriorNot++;
        std::string hs;
        for (const std::string &h : holdersOf(CB, S)) hs += (hs.empty() ? "" : " ") + h;
        row += hs.empty() ? "not a refill (not the header form; the chunk is held by no other field)"
                          : "not a refill (the chunk is also held by " + hs + ")";
      }
      row += ": " + k + " at " + instLocStr(S);
      CG_LOG("PoolCarve: " << row << "\n");
      poolInteriorRefillRows.push_back(row);
    }
  for (auto &[f, p] : chunkSources) p = srcPoolLast[f];
  // Report per pool.
  std::map<std::string, std::set<std::string>> fields;
  for (const std::string &f : handleFields) fields[pool(f)].insert(f);
  std::map<std::string, std::map<std::string, size_t>> forms, unsized;
  std::map<std::string, std::vector<const Instruction *>> headerCarves;
  for (const Carve &c : carves) {
    forms[pool(c.field)][c.form]++;
    if (!c.size.n && !c.size.chunk) unsized[pool(c.field)][c.form]++;
    if (c.form == "header") headerCarves[pool(c.field)].push_back(c.I);
  }
  std::map<std::string, std::vector<const Refusal *>> refused;
  for (const Refusal &r : refusals)
    refused[parent.count(r.field) ? pool(r.field) : r.field].push_back(&r);
  // A handle field whose address is taken (`&q->tail` passed to an
  // extend function) is written where the checks do not look.
  std::map<std::string, std::string> addrTaken;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      if (!unjudged(F))
        for (const Instruction &I : instructions(F)) {
          const auto *G = dyn_cast<GetElementPtrInst>(&I);
          // A field's address indexes into the struct; an all-zero GEP is
          // the struct's own address (the field at offset 0, its uses are
          // the struct pointer's), and one index is element arithmetic
          // (`(char *)p + CHUNK_SIZE` as p + 254).
          if (!G || G->hasAllZeroIndices() || G->getNumIndices() < 2) continue;
          const std::string k = fieldKey(G, G);
          if (k.empty() || !handleFields.count(k) || addrTaken.count(pool(k))) continue;
          std::function<const User *(const Value *, int)> badUse = [&](const Value *V, int d) -> const User * {
            for (const User *U : V->users()) {
              if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == V) continue;
              if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand() == V && S->getValueOperand() != V)
                continue;
              // An element of an array field (free[i]), and a link field's
              // address kept as a link pointer (G1: judged as one).
              if (const auto *AG = dyn_cast<GEPOperator>(U);
                  AG && AG->getPointerOperand() == V && isa<ArrayType>(AG->getSourceElementType()) && d < 4) {
                if (const User *B = badUse(U, d + 1)) return B;
                continue;
              }
              if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == V && linkFields.count(k) &&
                                                          (localSlot(S->getPointerOperand()) ||
                                                           linkHolding.count(fieldKey(S, S->getPointerOperand()))))
                continue;
              if (isa<DbgInfoIntrinsic>(U)) continue;
              if (isa<BitCastInst>(U) && d < 4) {
                if (const User *B = badUse(U, d + 1)) return B;
                continue;
              }
              return U;
            }
            return nullptr;
          };
          if (const User *U = badUse(G, 0))
            addrTaken[pool(k)] = "the address of " + k + " is taken at " + instLocStr(G) + ": " +
                                 (isa<Instruction>(U) ? instText(cast<Instruction>(U)) : std::string("a constant"));
        }
  // Structural refusals: a pool hands each piece out once, through one
  // cursor that only moves forward. A cursor that also moves back is a
  // stack, and two cursors through one chunk are a queue: both read back
  // what they handed out.
  std::map<std::string, std::string> structural;
  std::map<std::string, std::set<std::string>> cursorsOf;
  for (const std::string &f : handleFields)
    if (bumpFields.count(f) || baseFields.count(f)) cursorsOf[pool(f)].insert(f);
  for (auto &[p, cs] : cursorsOf)
    if (cs.size() > 1) {
      std::string l;
      for (const std::string &c : cs) l += " " + c;
      structural[p] = "two cursors through one chunk (a queue):" + l;
    }
  for (auto &[k, SI] : backward)
    if (handleFields.count(k))
      structural[pool(k)] = "the cursor " + k + " moves back (a stack) at " + instLocStr(SI) + ": " + instText(SI);
  for (auto &[p, why] : addrTaken) structural.emplace(p, why);
  auto isRefused = [&](const std::string &p) { return refused.count(p) || structural.count(p); };
  size_t nRefused = 0, nPools = 0;
  for (auto &[p, fs] : fields) {
    nPools++;
    std::string fl, fm;
    for (const std::string &f : fs) fl += " " + f + (irFallback.count(f) ? " (IR type at some access)" : "");
    for (auto &[form, n] : forms[p]) {
      fm += " " + form + " " + std::to_string(n);
      if (const size_t u = unsized[p][form]) fm += " (" + std::to_string(u) + " of them size unknown)";
    }
    size_t rw = 0, sc = 0;
    for (auto &[_, f] : rewinds) rw += pool(f) == p;
    for (const SavedCursor &c : savedCursors) sc += pool(c.field) == p;
    auto rit = refused.find(p);
    if (isRefused(p)) nRefused++;
    const std::string verdict = std::string(isRefused(p) ? "REFUSED" : "POOL") + " fields" + fl + "; carves" +
                                (fm.empty() ? " none" : fm) + "; rewinds " + std::to_string(rw) +
                                "; saved cursors " + std::to_string(sc) +
                                (rit == refused.end() ? "" : "; refused by " + std::to_string(rit->second.size()) + " uses");
    poolVerdicts[p] = verdict;
    CG_LOG("PoolCarve: " << verdict << "\n");
    if (auto sit = structural.find(p); sit != structural.end()) {
      poolVerdicts[p] += "; refused: " + sit->second;
      CG_LOG("PoolCarve:   refused: " << sit->second << "\n");
    }
    if (!isRefused(p)) {
      std::set<const Instruction *> hs;
      for (auto &[I, f] : bookkeeping)
        if (isa<StoreInst>(I) && pool(f) == p) hs.insert(I);
      CG_LOG("PoolCarve:   " << hs.size() << " handle stores (the bump, rewinds, refills, chunk links) "
             << (CFLPoolCarves ? "not modeled" : "modeled (--cfl-pool-carves off)") << "\n");
    }
    for (const Instruction *I : headerCarves[p])
      CG_LOG("PoolCarve:   header carve " << instLocStr(I) << ": " << instText(I) << "\n");
    // The first eight uses; every use at --verbose=3.
    if (rit != refused.end())
      for (size_t i = 0; i < rit->second.size(); i++) {
        if (i < 8)
          CG_LOG("PoolCarve:   refusing use " << instLocStr(rit->second[i]->I) << ": " << rit->second[i]->why << "\n");
        else
          CG_DEBUG("PoolCarve:   refusing use " << instLocStr(rit->second[i]->I) << ": " << rit->second[i]->why << "\n");
      }
  }
  for (auto &[I, f] : rewinds) CG_LOG("PoolCarve: rewind " << f << " at " << instLocStr(I) << ": " << instText(I) << "\n");
  for (auto &[I, f] : refills) CG_LOG("PoolCarve: refill " << f << " at " << instLocStr(I) << ": " << instText(I) << "\n");
  for (const SavedCursor &c : savedCursors)
    CG_LOG("PoolCarve: slot followed load by load at " << instLocStr(c.S) << ": saved cursor stored back to " << c.field
           << " at " << instLocStr(c.Back) << ": " << instText(c.Back) << "\n");
  for (auto &[I, what] : preBump)
    CG_LOG("PoolCarve: bytes written before the bump (" << what << ") at " << instLocStr(I) << ": " << instText(I)
           << "; withdrawn if a pointer fact lands in the free space at the solve\n");
  for (auto &[j, hk] : carry)
    if (handleFields.count(hk.first))
      CG_LOG("PoolCarve: carry " << j << " = " << hk.first << " + " << hk.second << " (a load of " << j
             << " stored into " << hk.first << " bumps it by " << hk.second << ")\n");
  CG_LOG("PoolCarve: chunk sources, link fields and chunk formals: the greatest fixpoint after " << restarts + 1
         << " runs of the check\n");
  for (const std::string &r : removedRows) CG_LOG("PoolCarve:   " << r << "\n");
  for (auto &[f, p] : chunkSources)
    if (handleFields.count(p))
      CG_LOG("PoolCarve: chunk source " << f << ": " << chunkReturns[f] << " returns, every one a chunk base of "
             << pool(p) << " or null\n");
  for (auto &[k, ss] : boundStores) {
    size_t loads = 0, other = 0;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        if (!unjudged(F))
          for (const Instruction &I : instructions(F))
            if (const auto *L = dyn_cast<LoadInst>(&I); L && fieldKey(L, L->getPointerOperand()) == k) {
              loads++;
              for (const User *U : L->users())
                if (!isa<ICmpInst>(U) && !isa<PtrToIntInst>(U) && !isa<DbgInfoIntrinsic>(U)) {
                  other++;
                  break;
                }
            }
    CG_LOG("PoolCarve: bound field " << k << ": " << ss.size() << " stores, " << loads << " loads"
           << (other ? ", " + std::to_string(other) + " used otherwise (judged as free-space pointers)"
                     : std::string(" all compared or measured"))
           << "\n");
  }
  for (auto &[k, p] : linkFields)
    CG_LOG("PoolCarve: link field " << k << ": " << linkGood[k] << " stores, all chunk bases or null\n");
  for (auto &[k, ls] : linkHolding) {
    std::string l;
    for (const std::string &x : ls) l += " " + x;
    CG_LOG("PoolCarve: link-pointer field " << k << " holds addresses of" << l << " (" << holdGood[k] << " stores)\n");
  }
  if (!linkSteps.empty())
    CG_LOG("PoolCarve: link pointer steps: " << linkSteps.size()
           << " by a constant over an array link field, under no-UB (the walk stays inside the array)\n");
  for (auto &[fa, p] : chunkParams)
    CG_LOG("PoolCarve: chunk formal " << fa.first << " arg" << fa.second << ": " << paramGood[fa]
           << " direct calls, every one passes a chunk base of " << pool(p) << " or null\n");
  // The bodies not judged that access a handle field.
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M) {
      if (F.isDeclaration() || F.empty() || !unjudged(F)) continue;
      bool touches = false;
      for (const Instruction &I : instructions(F)) {
        const Value *A = nullptr;
        if (const auto *L = dyn_cast<LoadInst>(&I)) A = L->getPointerOperand();
        else if (const auto *S = dyn_cast<StoreInst>(&I)) A = S->getPointerOperand();
        if (A && handleFields.count(fieldKey(&I, A))) touches = true;
      }
      if (!touches) continue;
      auto sit = Ctx->FuncSummaries.find(&F);
      CG_LOG("PoolCarve: body not judged: " << F.getName()
             << (sit != Ctx->FuncSummaries.end() && sit->second->fresh ? " replaced by its summary (FRESH)"
                                                                       : " not built")
             << "\n");
    }
  for (auto &[j, sh] : carryRefused)
    if (handleFields.count(sh.second))
      CG_LOG("PoolCarve: no carry " << j << " of " << sh.second << ": a store into it that is not " << sh.second
             << " + one constant at " << instLocStr(sh.first) << ": " << instText(sh.first) << "\n");
  if (VerboseLevel >= 3)
    for (const Carve &c : carves)
      CG_DEBUG("PoolCarve: carve " << c.form << " " << c.field << " at " << instLocStr(c.I) << ": " << instText(c.I)
               << "; size " << (c.size.n ? instText(c.size.n) + " x " + std::to_string(c.size.scale)
                                : c.size.chunk ? "chunk " + instText(c.size.chunk) + " - " + std::to_string(c.size.off)
                                               : std::string("unknown"))
               << "\n");
  // The effect: certified pools' carves and bookkeeping.
  poolCarves.clear();
  poolCarvePool.clear();
  poolRefusedCarvePool.clear();
  poolCarveSizes.clear();
  poolBookkeeping.clear();
  poolBookkeepingPool.clear();
  poolHandleFields.clear();
  poolHandleStores.clear();
  poolFieldAccess.clear();
  if (CFLPoolCarves) {
    for (auto &[I, f] : bookkeeping)
      if (isa<StoreInst>(I) && !isRefused(pool(f))) poolHandleStores.insert(I);
    poolOfField.clear();
    for (const std::string &f : handleFields)
      if (!isRefused(pool(f))) poolHandleFields.insert(f), poolOfField[f] = pool(f);
    for (const Carve &c : carves)
      if (!isRefused(pool(c.field))) {
        poolCarves[c.I] = c.form;
        poolCarvePool[c.I] = pool(c.field);
        poolCarveSizes[c.I] = c.size;
      } else
        poolRefusedCarvePool[c.I] = pool(c.field);
    for (auto &[I, f] : bookkeeping)
      if (!isRefused(pool(f))) poolBookkeeping.insert(I), poolBookkeepingPool[I] = pool(f);
    // (d): the pools whose free space takes bytes before the bump.
    poolChunkAllocs.clear();
    poolChunkHeader.clear();
    poolPreBump.clear();
    for (auto &[I, f] : preBumpPool)
      if (!isRefused(pool(f))) poolPreBump[pool(f)].push_back(instLocStr(I));
    for (auto &[I, f] : chunkAllocs)
      if (poolPreBump.count(pool(f))) poolChunkAllocs[pool(f)].insert(I);
    for (auto &[I, f] : refills) {
      const auto *S = cast<StoreInst>(I);
      APInt off(64, 0);
      if (const auto *G = dyn_cast<GEPOperator>(castsOnly(S->getValueOperand()));
          G && poolPreBump.count(pool(f)) && G->accumulateConstantOffset(S->getModule()->getDataLayout(), off)) {
        auto [it, fresh] = poolChunkHeader.try_emplace(pool(f), off.getSExtValue());
        if (!fresh) it->second = std::min(it->second, off.getSExtValue());
      }
    }
    // Every load and store of a certified pool's handle field, by pool:
    // the confirmer's certificate-bound exemption (plan 3.55 (a)) reads the
    // same certificate.
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (const Instruction &I : instructions(F)) {
          const Value *A = nullptr;
          if (const auto *L = dyn_cast<LoadInst>(&I)) A = L->getPointerOperand();
          else if (const auto *S = dyn_cast<StoreInst>(&I)) A = S->getPointerOperand();
          if (!A) continue;
          const std::string k = fieldKey(&I, A);
          if (!k.empty() && handleFields.count(k) && !isRefused(pool(k))) poolFieldAccess[&I] = pool(k);
        }
  }
  size_t fb = 0;
  for (const std::string &f : handleFields) fb += irFallback.count(f);
  CG_LOG("PoolCarve: " << nPools << " pools (" << nRefused << " refused), " << handleFields.size()
         << " handle fields (" << fb << " keyed by the IR type at some access: no debug info there), " << carves.size()
         << " carve sites, " << rewinds.size() << " rewinds, " << savedCursors.size() << " saved cursors; " << cursors
         << " bumped fields never refilled (cursors)\n");
}

// S1 (Fable 2026-10-23): a pool withdrawn at the solve leaves the
// certificate built at iteration 0 (checkPoolCarves runs once, before the
// confirmers: run again it would read their FRESH wrappers and could
// certify what the graph never built). Its carves lose their fresh object
// and get the edges of the instruction each is; its handle stores, which
// the build dropped, get a store's edges. The next iteration's solve reads
// the changed edge list.
extern size_t g_poolCarves;
void CallGraphPass::applyPoolWithdrawals() {
  if (poolWithdrawnAtSolve.size() == poolWithdrawnApplied) return;
  poolWithdrawnApplied = poolWithdrawnAtSolve.size();
  auto gone = [&](const std::string &p) { return poolWithdrawnAtSolve.count(p) > 0; };
  std::vector<std::pair<Function *, std::vector<Instruction *>>> released; // in IR order
  size_t carvesReleased = 0, storesReleased = 0;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        const std::string p = poolOfInst(&I);
        if (p.empty() || !gone(p)) continue;
        bool rebuild = false;
        if (poolCarves.erase(&I)) {
          const NodeIndex v = getRepNodeForValue(&I);
          const NodeIndex own = NF.getValueNodeFor(&I);
          const NodeIndex obj = NF.getObjectNodeFor(&I);
          assert(v != AndersNodeFactory::InvalidIndex && obj != AndersNodeFactory::InvalidIndex &&
                 "a certified carve was built as an allocation site");
          const bool removed = Graph.removeDeref(v, obj);
          assert(removed && "a certified carve's object edge is in the graph");
          (void)removed;
          auto &nodes = AllocSiteNodes[v];
          nodes.erase(std::remove(nodes.begin(), nodes.end(), own), nodes.end());
          if (nodes.empty()) AllocSiteNodes.erase(v), AllocSites.erase(v);
          poolRefusedCarvePool[&I] = poolCarvePool.at(&I);
          poolCarvePool.erase(&I);
          poolCarveSizes.erase(&I);
          g_poolCarves--;
          carvesReleased++;
          rebuild = true;
        }
        if (poolHandleStores.erase(&I)) storesReleased++, rebuild = true;
        poolBookkeeping.erase(&I);
        poolBookkeepingPool.erase(&I);
        poolFieldAccess.erase(&I);
        if (!rebuild) continue;
        if (released.empty() || released.back().first != &F) released.push_back({&F, {}});
        released.back().second.push_back(&I);
      }
  for (auto it = poolHandleFields.begin(); it != poolHandleFields.end();)
    it = gone(poolOfField.at(*it)) ? poolHandleFields.erase(it) : std::next(it);
  for (auto &[p, row] : poolWithdrawnAtSolve)
    if (auto v = poolVerdicts.find(p); v != poolVerdicts.end() && v->second.find("; withdrawn at the solve") == std::string::npos)
      v->second += "; withdrawn at the solve: " + row;
  for (auto &[F, insts] : released) {
    // A carve that reloads a summarized local slot is recorded as the
    // slot's load and gets an edge from each value the build saw stored
    // there (poolSlotStoreVals): the slot summary's edges for it. A
    // handle store into a summarized slot cannot be: its loads' edges were
    // emitted at iteration 0.
    collectLocalAllocaSummaries(F);
    InstHandler visitor(*this, F);
    for (Instruction *I : insts) visitor.visit(*I);
    for (auto &[slot, vals] : localAllocaStoreVals)
      if (!vals.empty()) {
        errs() << "ERROR: --cfl-cells: a withdrawn pool's handle store in " << F->getName()
               << " writes a summarized local slot, whose loads' edges were built at iteration 0\n";
        exit(1);
      }
    for (auto &[slot, loads] : localAllocaLoadVals)
      for (auto &[L, l] : loads) {
        auto kept = poolSlotStoreVals.find(L);
        assert(kept != poolSlotStoreVals.end() && "a released carve's slot load was kept at the build");
        for (NodeIndex st : kept->second) addAssignmentEdge(st, l);
      }
    localSummarizedAllocaSlots.clear();
    localAllocaStoreVals.clear();
    localAllocaLoadVals.clear();
    localSlotReachVals.clear();
  }
  CG_LOG("PoolCarve: withdrawn at the solve: " << poolWithdrawnAtSolve.size() << " pools; " << carvesReleased
         << " carves and " << storesReleased << " handle stores built as ordinary code\n");
}
