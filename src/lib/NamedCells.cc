// Access names for named cells; see NamedCells.h.

#include "NamedCells.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <cassert>

using namespace llvm;

// GraphBuild.cc: "struct.foo.12" -> "struct.foo" (one type per name
// across modules).
StringRef stripStructNameSuffix(StringRef Name);

namespace ka {

namespace {

bool isUnion(const StructType *ST) {
  return ST->hasName() && ST->getName().starts_with("union");
}

bool isNamed(const StructType *ST) {
  return !ST->isLiteral() && ST->hasName();
}

bool sameType(Type *A, Type *B) {
  if (A == B)
    return true;
  auto *SA = dyn_cast<StructType>(A), *SB = dyn_cast<StructType>(B);
  return SA && SB && isNamed(SA) && isNamed(SB) &&
         stripStructNameSuffix(SA->getName()) ==
             stripStructNameSuffix(SB->getName());
}

// Is there a T starting at byte `Off` of `Outer`? Descends the layout;
// `ViaUnion` is set when a union lies on the way, `InArray` when the T
// found is an element of an array of T (so arithmetic in units of T
// stays inside that array).
bool typeAt(Type *Outer, uint64_t Off, Type *T, const DataLayout &DL,
            bool &ViaUnion, bool &InArray) {
  Type *Cur = Outer;
  uint64_t Rel = Off;
  while (true) {
    if (Rel == 0 && sameType(Cur, T))
      return true;
    if (auto *ST = dyn_cast<StructType>(Cur)) {
      if (isUnion(ST))
        ViaUnion = true;
      if (ST->isOpaque())
        return false;
      const StructLayout *SL = DL.getStructLayout(ST);
      if (Rel >= SL->getSizeInBytes())
        return false;
      const unsigned I = SL->getElementContainingOffset(Rel);
      const uint64_t EO = SL->getElementOffset(I);
      Type *E = ST->getElementType(I);
      if (Rel - EO >= DL.getTypeAllocSize(E))
        return false; // padding
      Rel -= EO;
      Cur = E;
      continue;
    }
    if (auto *AT = dyn_cast<ArrayType>(Cur)) {
      const uint64_t ES = DL.getTypeAllocSize(AT->getElementType());
      if (ES == 0)
        return false;
      if (Rel % ES == 0 && sameType(AT->getElementType(), T)) {
        InArray = true;
        return true;
      }
      Rel %= ES;
      Cur = AT->getElementType();
      continue;
    }
    return false;
  }
}

} // namespace

const char *AccessNames::whyName(Why W) {
  switch (W) {
  case NoStruct: return "no-struct";
  case OutOfRange: return "out-of-range";
  case Straddle: return "straddle";
  case Union: return "union";
  case Pun: return "pun";
  case NumWhy: break;
  }
  return "?";
}

AccessNames::AccessNames() {
  Names.push_back("<original>");
  Names.push_back("<unnamed>");
}

uint32_t AccessNames::intern(std::string S) {
  auto [It, Ins] = Ids.try_emplace(S, (uint32_t)Names.size());
  if (Ins)
    Names.push_back(std::move(S));
  return It->second;
}

void AccessNames::scanBases(const Module &M) {
  // Struct types each base pointer is indexed as, by its first GEP index
  // (the type the GEP claims the pointed-to object has).
  boost::unordered_flat_map<const Value *, SmallVector<StructType *, 2>> Seen;
  auto note = [&](const GEPOperator *G) {
    auto *ST = dyn_cast<StructType>(G->getSourceElementType());
    if (!ST || !isNamed(ST))
      return;
    const Value *B = G->getPointerOperand()->stripPointerCasts();
    auto &V = Seen[B];
    for (StructType *O : V)
      if (sameType(O, ST))
        return;
    V.push_back(ST);
  };
  for (const Function &F : M)
    for (const BasicBlock &BB : F)
      for (const Instruction &I : BB) {
        if (const auto *G = dyn_cast<GEPOperator>(&I))
          note(G);
        for (const Value *Op : I.operands())
          if (const auto *G = dyn_cast<GEPOperator>(Op))
            note(G); // constant-expression GEPs
      }
  const DataLayout &DL = M.getDataLayout();
  for (auto &[B, Types] : Seen) {
    if (Types.size() < 2)
      continue;
    // Two claimed types are compatible when one sits at offset 0 of the
    // other (a struct and its first embedded member).
    bool Pun = false;
    for (size_t I = 0; I < Types.size() && !Pun; I++)
      for (size_t J = I + 1; J < Types.size() && !Pun; J++) {
        bool U = false, A = false;
        if (!typeAt(Types[I], 0, Types[J], DL, U, A) &&
            !typeAt(Types[J], 0, Types[I], DL, U, A))
          Pun = true;
      }
    if (Pun)
      PunnedBases.insert(B);
  }
}

uint32_t AccessNames::ofSlot(StructType *S, uint64_t Off, uint64_t Size,
                             const DataLayout &DL) {
  assert(S && isNamed(S) && "ofSlot: S must be a named struct");
  if (Size == 0)
    Size = 1;
  Type *T = S;
  StructType *Named = nullptr;
  uint64_t Base = 0; // leaf start in Named, array elements folded
  uint64_t Rel = Off; // offset inside T
  while (true) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (isUnion(ST))
        return miss(Union);
      if (isNamed(ST)) {
        Named = ST;
        Base = 0;
      }
      if (ST->isOpaque())
        return miss(OutOfRange);
      const StructLayout *SL = DL.getStructLayout(ST);
      if (Rel >= SL->getSizeInBytes())
        return miss(OutOfRange);
      const unsigned I = SL->getElementContainingOffset(Rel);
      const uint64_t EO = SL->getElementOffset(I);
      Type *E = ST->getElementType(I);
      if (Rel - EO >= DL.getTypeAllocSize(E))
        return miss(Straddle); // padding
      Rel -= EO;
      Base += EO;
      T = E;
      continue;
    }
    if (auto *AT = dyn_cast<ArrayType>(T)) {
      const uint64_t ES = DL.getTypeAllocSize(AT->getElementType());
      if (ES == 0)
        return miss(OutOfRange);
      Rel %= ES; // fold onto element 0
      T = AT->getElementType();
      continue;
    }
    // Scalar (or vector) leaf.
    if (Rel + Size > DL.getTypeStoreSize(T))
      return miss(Straddle);
    assert(Named && "a named struct encloses every leaf of a named struct");
    return intern((stripStructNameSuffix(Named->getName()) + "+" +
                   std::to_string(Base))
                      .str());
  }
}

uint32_t AccessNames::ofAccess(const Value *Ptr, uint64_t Size,
                               const DataLayout &DL) {
  SmallVector<const GEPOperator *, 4> Chain;
  const Value *P = Ptr->stripPointerCasts();
  while (const auto *G = dyn_cast<GEPOperator>(P)) {
    Chain.push_back(G);
    P = G->getPointerOperand()->stripPointerCasts();
  }
  // Position: the innermost named struct holding the address, and the
  // byte offset in it (array elements folded). Unknown until a typed
  // GEP, or the declared type of a global or stack object, names it.
  StructType *S = nullptr;
  int64_t Off = 0;
  Why Lost = NoStruct;
  auto enter = [&](Type *Ty) -> bool {
    if (auto *ST = dyn_cast<StructType>(Ty)) {
      if (isUnion(ST))
        return false;
      if (isNamed(ST)) {
        S = ST;
        Off = 0;
      }
    }
    return true;
  };
  {
    Type *Decl = nullptr;
    if (const auto *GV = dyn_cast<GlobalVariable>(P))
      Decl = GV->getValueType();
    else if (const auto *AI = dyn_cast<AllocaInst>(P))
      Decl = AI->getAllocatedType();
    while (Decl && Decl->isArrayTy()) // element 0 of a global/stack array
      Decl = Decl->getArrayElementType();
    if (Decl && !enter(Decl))
      return miss(Union);
  }
  for (auto It = Chain.rbegin(); It != Chain.rend(); ++It) {
    const GEPOperator *G = *It;
    if (PunnedBases.count(G->getPointerOperand()->stripPointerCasts()))
      return miss(Pun);
    Type *T = G->getSourceElementType();
    auto Idx = G->idx_begin(), End = G->idx_end();
    if (Idx == End)
      continue;
    // First index: pointer arithmetic in units of T from the position.
    if (S) {
      const auto *C0 = dyn_cast<ConstantInt>(Idx->get());
      bool ViaUnion = false, InArray = false;
      if (C0) {
        const int64_t NOff =
            Off + C0->getSExtValue() * (int64_t)DL.getTypeAllocSize(T);
        if (NOff < 0 ||
            (uint64_t)NOff >= DL.getStructLayout(S)->getSizeInBytes()) {
          S = nullptr; // left the struct (container_of, tail arrays)
          Lost = OutOfRange;
        } else if (T->isAggregateType() &&
                   !typeAt(S, (uint64_t)NOff, T, DL, ViaUnion, InArray)) {
          return miss(Pun);
        } else if (ViaUnion) {
          return miss(Union);
        } else {
          Off = NOff;
        }
      } else if (typeAt(S, (uint64_t)Off, T, DL, ViaUnion, InArray) &&
                 InArray) {
        if (ViaUnion)
          return miss(Union);
        // a variable step through an array of T stays in that array:
        // the folded position is unchanged
      } else {
        S = nullptr;
        Lost = OutOfRange;
      }
    }
    Type *Cur = T;
    if (!enter(Cur))
      return miss(Union);
    for (++Idx; Idx != End; ++Idx) {
      if (auto *ST = dyn_cast<StructType>(Cur)) {
        const unsigned FI =
            (unsigned)cast<ConstantInt>(Idx->get())->getZExtValue();
        if (S)
          Off += (int64_t)DL.getStructLayout(ST)->getElementOffset(FI);
        Cur = ST->getElementType(FI);
      } else if (auto *AT = dyn_cast<ArrayType>(Cur)) {
        Cur = AT->getElementType(); // fold onto element 0
      } else if (auto *VT = dyn_cast<VectorType>(Cur)) {
        Cur = VT->getElementType();
      } else {
        llvm_unreachable("GEP index into a non-aggregate type");
      }
      if (!enter(Cur))
        return miss(Union);
    }
  }
  if (!S)
    return miss(Lost);
  return ofSlot(S, (uint64_t)Off, Size, DL);
}

} // namespace ka
