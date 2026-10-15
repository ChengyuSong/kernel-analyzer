/*
 * Call graph construction
 *
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// Slots.cc: naming a memory slot an access reaches as (struct, byte offset)
// across embedding and -O3 (struct GEPs, and struct-path TBAA when -O3
// dropped an all-zero GEP). Shared by the Driver pre-passes and the
// summary checks (pool closure).

#include "CallGraphInternal.h"
#include "NamedCells.h"
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Operator.h>

// Does struct type T hold a struct named S at byte offset off (itself, or
// through first-member / field embedding)?
bool embedsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL) {
  for (int depth = 0; depth < 32 && T && off >= 0; depth++) {
    auto *ST = dyn_cast<StructType>(T);
    if (!ST || ST->isOpaque()) return false;
    if (off == 0 && ST->hasName() && stripStructNameSuffix(ST->getName()) == S) return true;
    const StructLayout *SL = DL.getStructLayout(ST);
    if ((uint64_t)off >= SL->getSizeInBytes()) return false;
    unsigned i = SL->getElementContainingOffset(off);
    off -= (int64_t)SL->getElementOffset(i);
    T = ST->getElementType(i);
  }
  return false;
}

// The struct GEP an address is (bitcasts only: stripPointerCasts would also
// strip an all-zero GEP, the method at offset 0 of its struct).
const GEPOperator *structGEP(const Value *A) {
  while (const auto *BC = dyn_cast<BitCastOperator>(A)) A = BC->getOperand(0);
  return dyn_cast<GEPOperator>(A);
}

// The (struct, byte offset) an access names: its struct GEP, else its
// struct-path TBAA tag (-O3 drops all-zero GEPs; the tag keeps the base
// struct and the offset).
bool accessSlot(const Instruction *I, const Value *Addr, const DataLayout &DL,
                       StructType *&S, int64_t &off) {
  if (const GEPOperator *G = structGEP(Addr)) {
    S = dyn_cast<StructType>(G->getSourceElementType());
    APInt Ap(64, 0);
    if (S && S->hasName() && G->accumulateConstantOffset(DL, Ap)) {
      off = Ap.getSExtValue();
      return true;
    }
  }
  const MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa);
  if (!Tag || Tag->getNumOperands() < 3 || Tag->getOperand(0) == Tag->getOperand(1)) return false;
  const auto *B = dyn_cast<MDNode>(Tag->getOperand(0));
  const auto *N = B && B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
  const auto *TO = mdconst::dyn_extract<ConstantInt>(Tag->getOperand(2));
  if (!N || !TO) return false;
  S = StructType::getTypeByName(I->getContext(), ("struct." + N->getString()).str());
  if (!S) return false;
  // The tag's offset is relative to the base struct; the address must be
  // the struct's start plus that offset, which the tag asserts.
  off = TO->getSExtValue();
  return true;
}

// Does an access's struct-path TBAA tag reach struct SN (IR name,
// "struct.T") at byte offset o: walking from the tag's base type into the
// member that contains the access offset (an anonymous typedef'd struct
// whose first member is SN: cjpeg's my_memory_mgr { jpeg_memory_mgr pub; }).
bool tbaaReaches(const Instruction *I, StringRef SN, int64_t o) {
  const MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa);
  if (!Tag || Tag->getNumOperands() < 3 || Tag->getOperand(0) == Tag->getOperand(1)) return false;
  const auto *TO = mdconst::dyn_extract<ConstantInt>(Tag->getOperand(2));
  const auto *B = dyn_cast<MDNode>(Tag->getOperand(0));
  if (!TO || !B) return false;
  int64_t off = TO->getSExtValue();
  for (int depth = 0; depth < 16 && B; depth++) {
    const auto *N = B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
    if (N && !N->getString().empty() && ("struct." + N->getString()).str() == SN && off == o)
      return true;
    // Members: (type, offset) pairs after the name.
    const MDNode *next = nullptr;
    int64_t best = -1;
    for (unsigned k = 1; k + 1 < B->getNumOperands(); k += 2) {
      const auto *MO = mdconst::dyn_extract<ConstantInt>(B->getOperand(k + 1));
      if (MO && MO->getSExtValue() <= off && MO->getSExtValue() > best) {
        best = MO->getSExtValue();
        next = dyn_cast<MDNode>(B->getOperand(k));
      }
    }
    if (!next || best < 0) return false;
    off -= best;
    B = next;
  }
  return false;
}

// The innermost named struct holding byte `off` of ST, the offset there,
// and the scalar the byte lies in with the byte's offset inside it.
bool innermostField(Type *T, int64_t off, const DataLayout &DL, std::pair<std::string, int64_t> &K, Type *&leaf,
                    int64_t &inLeaf) {
  K = {"", 0};
  for (int depth = 0; depth < 64 && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return false;
      if (ST->hasName()) K = {stripStructNameSuffix(ST->getName()).str(), off};
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return false;
      const unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    if (auto *AT = dyn_cast<ArrayType>(T)) {
      const int64_t es = (int64_t)DL.getTypeAllocSize(AT->getElementType());
      if (es == 0) return false;
      K.second -= off - off % es; // an array member's elements share its name
      off %= es;
      T = AT->getElementType();
      continue;
    }
    leaf = T;
    inLeaf = off;
    return !K.first.empty();
  }
  return false;
}

// An access through a struct's array member at a variable index
// (xa_node.slots[offset]): the struct GEP whose last index is variable and
// whose prefix names the array; the member's start stands for the slot.
bool arraySlot(const Value *Addr, const DataLayout &DL, StructType *&S, int64_t &off) {
  const GEPOperator *G = structGEP(Addr);
  if (!G || G->getNumIndices() < 3) return false;
  S = dyn_cast<StructType>(G->getSourceElementType());
  if (!S || !S->hasName()) return false;
  SmallVector<Value *, 8> idx(G->idx_begin(), G->idx_end() - 1);
  for (Value *V : idx)
    if (!isa<ConstantInt>(V)) return false;
  if (!isa<ArrayType>(GetElementPtrInst::getIndexedType(S, idx))) return false;
  off = (int64_t)DL.getIndexedOffsetInType(S, idx);
  return true;
}

// A use the linker drops: a global in a ".discard.*" section
// (EXPORT_SYMBOL's __ADDRESSABLE entry) takes no address in the program.
bool PointeeResolver::discarded(const User *U) {
  for (int i = 0; i < 4 && U; i++) {
    if (const auto *GV = dyn_cast<GlobalVariable>(U)) return GV->getSection().starts_with(".discard");
    if (!isa<Constant>(U) || U->getNumUses() != 1) return false;
    U = *U->user_begin();
  }
  return false;
}

StructType *PointeeResolver::atZero(StructType *S) {
  for (int d = 0; d < 32 && S && !S->isOpaque() && S->getNumElements(); d++) {
    auto *E = dyn_cast<StructType>(S->getElementType(0));
    if (!E || !E->hasName() || E->isOpaque()) break;
    S = E;
  }
  return S;
}

// Direct call sites per callee (a defined function and the declarations of
// its name in other modules); callees whose address is taken.
PointeeResolver::PointeeResolver(const GlobalContext *Ctx) {
  std::map<std::string, const Function *> defOf;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      if (!F.isDeclaration() && !F.hasLocalLinkage()) defOf.emplace(F.getName().str(), &F);
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M) {
      const Function *D = &F;
      if (F.isDeclaration()) {
        auto it = defOf.find(F.getName().str());
        if (it == defOf.end()) continue;
        D = it->second;
      }
      for (const Use &U : F.uses()) {
        const auto *CB = dyn_cast<CallBase>(U.getUser());
        if (CB && CB->isCallee(&U)) sites[D].push_back(CB);
        else if (!discarded(U.getUser())) taken.insert(D);
      }
    }
}
StructType *PointeeResolver::get(const Value *A, LLVMContext &C, int depth) {
  A = A->stripPointerCasts();
  if (depth > 6) return nullptr;
  std::string n;
  SmallVector<DbgValueInst *, 2> DVs;
  findDbgValues(DVs, const_cast<Value *>(A));
  for (DbgValueInst *DV : DVs)
    if (n.empty())
      if (const StringRef N = ka::diStructName(DV->getVariable()->getType(), true); !N.empty()) n = "struct." + N.str();
  if (n.empty()) n = diDeclaredStruct(A, true);
  if (n.empty() && (isa<GlobalVariable>(A) || isa<AllocaInst>(A))) n = diDeclaredStruct(A, false);
  if (!n.empty()) return StructType::getTypeByName(C, n);
  // (1b) The object's own declaration (Fable 2026-10-15): a global's or a
  // local's IR value type when it is a named struct (an array of one: its
  // element), normalized to its innermost struct at offset 0. A struct GEP
  // of another struct on the same object is a pun: unnamed.
  {
    Type *T = nullptr;
    if (const auto *GV = dyn_cast<GlobalVariable>(A)) T = GV->getValueType();
    else if (const auto *AI = dyn_cast<AllocaInst>(A)) T = AI->getAllocatedType();
    while (auto *AT = dyn_cast_or_null<ArrayType>(T)) T = AT->getElementType();
    if (auto *ST = dyn_cast_or_null<StructType>(T); ST && ST->hasName() && !ST->isOpaque()) {
      StructType *D = atZero(ST);
      for (const User *U : A->users())
        if (const auto *G = dyn_cast<GEPOperator>(U); G && G->getPointerOperand() == A)
          if (auto *S = dyn_cast<StructType>(G->getSourceElementType()); S && S->hasName() && atZero(S) != D)
            return nullptr;
      return viaDecl = true, D;
    }
  }
  // Sibling GEPs (Fable 2026-10-15): the value is the base of struct GEPs
  // of one struct in its function; the GEP's source type is the program's
  // declaration of that expression. Two structs (after the offset-0
  // normalization) are a pun: unnamed.
  {
    StructType *agreed = nullptr;
    bool clash = false;
    for (const User *U : A->users())
      if (const auto *G = dyn_cast<GEPOperator>(U); G && G->getPointerOperand() == A)
        if (auto *S = dyn_cast<StructType>(G->getSourceElementType()); S && S->hasName()) {
          S = atZero(S);
          clash |= agreed && agreed != S;
          agreed = S;
        }
    if (clash) return nullptr;
    if (agreed) return viaSibling = true, agreed;
  }
  if (const auto *PN = dyn_cast<PHINode>(A)) {
    StructType *agreed = nullptr;
    for (const Value *In : PN->incoming_values()) {
      if (In == PN) continue;
      StructType *S = get(In, C, depth + 1);
      if (!S || (agreed && agreed != S)) return nullptr;
      agreed = S;
    }
    return agreed;
  }
  if (const GEPOperator *G = structGEP(A))
    if (auto *S = dyn_cast<StructType>(G->getResultElementType()); S && S->hasName() && G->hasAllConstantIndices())
      return S;
  if (const auto *Arg = dyn_cast<Argument>(A)) {
    viaFormal = true;
    if (auto it = memo.find(Arg); it != memo.end()) return it->second;
    if (!busy.insert(Arg).second) return nullptr; // a cycle among formals decides nothing
    StructType *agreed = nullptr;
    const Function *F = Arg->getParent();
    auto sit = sites.find(F);
    bool ok = !taken.count(F) && sit != sites.end() && !sit->second.empty();
    for (size_t i = 0; ok && i < sit->second.size(); i++) {
      const CallBase *CB = sit->second[i];
      if (Arg->getArgNo() >= CB->arg_size()) { ok = false; break; }
      StructType *S = get(CB->getArgOperand(Arg->getArgNo()), C, depth + 1);
      if (S) S = atZero(S);
      if (!S || (agreed && agreed != S)) ok = false;
      else agreed = S;
    }
    busy.erase(Arg);
    StructType *R = ok ? agreed : nullptr;
    memo[Arg] = R;
    return R;
  }
  return nullptr;
}

bool namedSlot(const Instruction *I, const Value *Addr, const DataLayout &DL, PointeeResolver &P, StructType *&S,
               int64_t &off) {
  if ((accessSlot(I, Addr, DL, S, off) && S && S->hasName()) || arraySlot(Addr, DL, S, off)) return true;
  P.viaFormal = P.viaSibling = P.viaDecl = false;
  S = P.get(Addr, I->getContext()), off = 0;
  return S != nullptr;
}

// The named structs bytes [lo, hi) of T lie in, outermost first, each with
// the interval inside it (array elements fold to element 0: an interval
// spanning an element boundary wraps).
static void structCoverRec(Type *T, int64_t lo, int64_t hi, const DataLayout &DL,
                           const std::function<void(StructType *, int64_t, int64_t)> &visit,
                           int depth) {
  if (depth > 64 || lo >= hi) return;
  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->isOpaque()) {
      if (ST->hasName()) visit(ST, lo, hi);
      return;
    }
    const StructLayout *SL = DL.getStructLayout(ST);
    const int64_t sz = (int64_t)SL->getSizeInBytes();
    lo = std::max<int64_t>(lo, 0);
    hi = std::min(hi, sz);
    if (lo >= hi) return;
    if (ST->hasName()) visit(ST, lo, hi);
    for (unsigned i = 0; i < ST->getNumElements(); i++) {
      Type *E = ST->getElementType(i);
      const int64_t eo = (int64_t)SL->getElementOffset(i), es = (int64_t)DL.getTypeAllocSize(E);
      if (eo + es <= lo || eo >= hi) continue;
      structCoverRec(E, std::max(lo, eo) - eo, std::min(hi, eo + es) - eo, DL, visit, depth + 1);
    }
    return;
  }
  Type *E = nullptr;
  uint64_t n = 0;
  if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType(), n = AT->getNumElements();
  else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType(), n = VT->getNumElements();
  if (!E || !(E->isStructTy() || E->isArrayTy())) return;
  const int64_t es = (int64_t)DL.getTypeAllocSize(E);
  if (es == 0) return;
  lo = std::max<int64_t>(lo, 0);
  if (n) hi = std::min(hi, es * (int64_t)n);
  if (lo >= hi) return;
  if (hi - lo >= es) return structCoverRec(E, 0, es, DL, visit, depth + 1);
  const int64_t a = lo % es, b = a + (hi - lo);
  if (b <= es) return structCoverRec(E, a, b, DL, visit, depth + 1);
  structCoverRec(E, a, es, DL, visit, depth + 1);
  structCoverRec(E, 0, b - es, DL, visit, depth + 1);
}
void structCover(Type *T, int64_t lo, int64_t hi, const DataLayout &DL,
                 const std::function<void(StructType *, int64_t, int64_t)> &visit) {
  structCoverRec(T, lo, hi, DL, visit, 0);
}

// The debug-info struct a declared object is, or a pointer value points
// to: the declared type of the global, local, formal or spilled slot it
// comes from (through casts; at -O0 a load of a slot reads the slot's
// variable): "struct.<tag>", else "" (no declaration, or not a struct).
std::string diDeclaredStruct(const Value *P, bool pointee) {
  P = P->stripPointerCasts();
  const DIType *T = nullptr;
  auto declOf = [](const AllocaInst *AI) -> const DIType * {
    for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(AI)))
      if (auto *V = DDI->getVariable()) return V->getType();
    return nullptr;
  };
  if (pointee) {
    if (const auto *L = dyn_cast<LoadInst>(P)) {
      if (const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
        T = declOf(AI);
    } else if (const auto *A = dyn_cast<Argument>(P)) {
      if (const DISubprogram *SP = A->getParent()->getSubprogram())
        if (const DISubroutineType *ST = SP->getType()) {
          auto TA = ST->getTypeArray();
          if (A->getArgNo() + 1 < TA.size()) T = TA[A->getArgNo() + 1];
        }
    }
  } else if (const auto *AI = dyn_cast<AllocaInst>(P)) {
    T = declOf(AI);
  } else if (const auto *GV = dyn_cast<GlobalVariable>(P)) {
    SmallVector<DIGlobalVariableExpression *, 1> E;
    GV->getDebugInfo(E);
    if (!E.empty()) T = E[0]->getVariable()->getType();
  }
  if (!T) return "";
  const StringRef N = ka::diStructName(T, pointee);
  return N.empty() ? "" : "struct." + N.str();
}

std::vector<const CallBase *> icallsInIROrder(const GlobalContext *Ctx) {
  std::vector<const CallBase *> out;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F))
        if (const auto *CB = dyn_cast<CallBase>(&I); CB && Ctx->IndirectCallInsts.count(CB)) out.push_back(CB);
  return out;
}
