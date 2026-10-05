// Access names for named cells; see NamedCells.h.

#include "NamedCells.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <algorithm>
#include <cassert>
#include <functional>

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

// The composite a DIType denotes through typedefs and qualifiers (and
// with ThroughPtr one pointer level), with its tag (an anonymous struct
// by its nearest typedef).
static const DICompositeType *diComposite(const DIType *T, bool ThroughPtr,
                                          StringRef &Tag) {
  StringRef Typedef;
  auto strip = [&](const DIType *X) {
    while (const auto *D = dyn_cast_or_null<DIDerivedType>(X)) {
      const unsigned DT = D->getTag();
      if (DT != dwarf::DW_TAG_typedef && DT != dwarf::DW_TAG_const_type &&
          DT != dwarf::DW_TAG_volatile_type && DT != dwarf::DW_TAG_restrict_type)
        break;
      if (DT == dwarf::DW_TAG_typedef)
        Typedef = D->getName();
      X = D->getBaseType();
    }
    return X;
  };
  T = strip(T);
  if (ThroughPtr) {
    const auto *D = dyn_cast_or_null<DIDerivedType>(T);
    if (!D || D->getTag() != dwarf::DW_TAG_pointer_type)
      return nullptr;
    Typedef = "";
    T = strip(D->getBaseType());
  }
  const auto *C = dyn_cast_or_null<DICompositeType>(T);
  if (!C)
    return nullptr;
  Tag = C->getName().empty() ? Typedef : C->getName();
  return C;
}

StringRef diStructName(const DIType *T, bool ThroughPtr) {
  StringRef Tag;
  const DICompositeType *C = diComposite(T, ThroughPtr, Tag);
  return (C && C->getTag() == dwarf::DW_TAG_structure_type) ? Tag : "";
}

StructType *AccessNames::structByTag(const Module *M, StringRef Tag) {
  auto [MIt, MIns] = ByTag.try_emplace(M);
  if (MIns)
    for (StructType *ST : M->getIdentifiedStructTypes())
      if (isNamed(ST) && !isUnion(ST)) {
        StringRef N = stripStructNameSuffix(ST->getName());
        if (N.consume_front("struct.") || N.consume_front("class."))
          MIt->second.try_emplace(N.str(), ST);
      }
  auto SIt = MIt->second.find(Tag.str());
  return SIt == MIt->second.end() ? nullptr : SIt->second;
}

uint32_t AccessNames::ofDISlot(const Module *M, const DICompositeType *C,
                               StringRef Tag, uint64_t Off, uint64_t Size,
                               const DataLayout &DL) {
  if (Size == 0)
    Size = 1;
  uint64_t Base = 0, Rel = Off;
  while (true) {
    if (C->getTag() == dwarf::DW_TAG_union_type)
      return miss(Union);
    if (C->getTag() != dwarf::DW_TAG_structure_type || Tag.empty())
      return miss(NoStruct);
    if (StructType *S = structByTag(M, Tag)) // the IR still has it
      return ofSlot(S, Rel, Size, DL);
    // The member holding Rel.
    const DIDerivedType *Mem = nullptr;
    for (const DINode *E : C->getElements()) {
      const auto *D = dyn_cast<DIDerivedType>(E);
      if (!D || D->getTag() != dwarf::DW_TAG_member || D->isStaticMember())
        continue;
      const uint64_t MO = D->getOffsetInBits() / 8,
                     MS = (D->getSizeInBits() + 7) / 8;
      if (Rel >= MO && Rel < MO + MS) {
        Mem = D;
        break;
      }
    }
    if (!Mem)
      return miss(Straddle); // padding or past the end
    const uint64_t MO = Mem->getOffsetInBits() / 8;
    Rel -= MO;
    Base += MO;
    StringRef T2;
    const DIType *MT = Mem->getBaseType();
    const DICompositeType *CC = diComposite(MT, false, T2);
    // Arrays fold onto element 0.
    while (CC && CC->getTag() == dwarf::DW_TAG_array_type) {
      const DIType *ET = CC->getBaseType();
      StringRef T3;
      const DICompositeType *EC = diComposite(ET, false, T3);
      const uint64_t ES = EC ? (EC->getSizeInBits() + 7) / 8
                             : (ET ? (ET->getSizeInBits() + 7) / 8 : 0);
      if (ES == 0)
        return miss(OutOfRange);
      Rel %= ES;
      CC = EC;
      T2 = T3;
      MT = ET;
    }
    if (CC) {
      C = CC;
      Tag = T2;
      Base = 0;
      continue;
    }
    // Scalar leaf of a debug-info-only struct.
    const uint64_t LS = MT ? (MT->getSizeInBits() + 7) / 8 : 0;
    if (Mem->isBitField() || LS == 0 || Rel + Size > LS)
      return miss(Straddle);
    return intern(("struct." + Tag + "+" + std::to_string(Base)).str());
  }
}

uint32_t AccessNames::ofPosition(const Position &P, uint64_t Size,
                                 const DataLayout &DL) {
  if (P.S)
    return ofSlot(P.S, (uint64_t)P.off, Size, DL);
  if (P.DIS && P.off >= 0)
    return ofDISlot(P.M, P.DIS, P.DITag, (uint64_t)P.off, Size, DL);
  return miss(P.why);
}

AccessNames::BaseType AccessNames::baseStruct(const Value *P) {
  auto [It, Ins] = BaseOf.try_emplace(P);
  if (!Ins)
    return It->second;
  const DICompositeType *C = nullptr;
  StringRef Tag;
  const Module *M = nullptr;
  if (const auto *A = dyn_cast<Argument>(P)) {
    M = A->getParent()->getParent();
    if (const DISubprogram *SP = A->getParent()->getSubprogram())
      if (const DISubroutineType *ST = SP->getType()) {
        auto Types = ST->getTypeArray();
        if (A->getArgNo() + 1 < Types.size())
          C = diComposite(Types[A->getArgNo() + 1], true, Tag);
      }
  } else if (const auto *I = dyn_cast<Instruction>(P)) {
    M = I->getModule();
    // The variable may describe the value or a cast of it (the address
    // chain is stripped of casts, the dbg.value is not).
    SmallVector<Value *, 4> Same{const_cast<Instruction *>(I)};
    for (User *U : const_cast<Instruction *>(I)->users())
      if (auto *CI = dyn_cast<CastInst>(U))
        if (CI->getType()->isPointerTy() && CI->stripPointerCasts() == I)
          Same.push_back(CI);
    for (Value *V : Same) {
      SmallVector<DbgVariableIntrinsic *, 2> Users;
      findDbgUsers(Users, V);
      for (DbgVariableIntrinsic *DI : Users)
        if (isa<DbgValueInst>(DI) && DI->getExpression()->getNumElements() == 0)
          if ((C = diComposite(DI->getVariable()->getType(), true, Tag)))
            break;
      if (C)
        break;
    }
  }
  BaseType B;
  if (C && C->getTag() == dwarf::DW_TAG_structure_type && !Tag.empty() && M) {
    B.S = structByTag(M, Tag);
    if (!B.S) {
      B.C = C;
      B.Tag = Tag;
    }
  }
  BaseOf[P] = B;
  return B;
}

SmallVector<uint32_t, 4> AccessNames::ofLanes(const Value *Ptr,
                                              VectorType *VT,
                                              const DataLayout &DL) {
  SmallVector<uint32_t, 4> Out;
  auto *FT = dyn_cast<FixedVectorType>(VT);
  Position P = position(Ptr, DL);
  if (!FT || (!P.S && !P.DIS))
    return Out;
  const uint64_t ES = DL.getTypeStoreSize(FT->getElementType());
  const int64_t Off0 = P.off;
  for (unsigned L = 0; L < FT->getNumElements(); L++) {
    P.off = Off0 + (int64_t)(L * ES);
    const uint32_t N = ofPosition(P, ES, DL);
    if (N == Unnamed)
      return {};
    Out.push_back(N);
  }
  return Out;
}

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
  Names.push_back("<identity>");
}

uint32_t AccessNames::intern(std::string S) {
  auto [It, Ins] = Ids.try_emplace(S, (uint32_t)Names.size());
  if (Ins)
    Names.push_back(std::move(S));
  return It->second;
}

void AccessNames::scanBases(const Module &M) {
  {
    DebugInfoFinder DIF;
    DIF.processModule(M);
    for (const DIType *T : DIF.types())
      if (const auto *CT = dyn_cast<DICompositeType>(T))
        if (CT->getTag() == dwarf::DW_TAG_structure_type && !CT->getName().empty() &&
            !CT->isForwardDecl())
          DIStruct.try_emplace(CT->getName().str(), CT);
  }
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

uint32_t AccessNames::unionSlot(StructType *S, uint64_t Base, uint64_t Rel,
                                uint64_t Size) {
  StringRef Tag = stripStructNameSuffix(S->getName());
  Tag.consume_front("struct.");
  auto It = DIStruct.find(Tag.str());
  if (It == DIStruct.end())
    return miss(Union);
  // Down the debug-info layout of S to the union starting at Base.
  const DICompositeType *C = It->second;
  uint64_t At = 0;
  for (int Depth = 0; Depth < 8 && C; Depth++) {
    const DIDerivedType *Mem = nullptr;
    for (const DINode *E : C->getElements())
      if (const auto *D = dyn_cast<DIDerivedType>(E))
        if (D->getTag() == dwarf::DW_TAG_member && !D->isStaticMember()) {
          const uint64_t MO = At + D->getOffsetInBits() / 8,
                         MS = (D->getSizeInBits() + 7) / 8;
          if (Base >= MO && Base < MO + std::max<uint64_t>(MS, 1)) {
            Mem = D;
            At = MO;
            break;
          }
        }
    if (!Mem)
      return miss(Union);
    StringRef T2;
    const DICompositeType *MC = diComposite(Mem->getBaseType(), false, T2);
    if (!MC)
      return miss(Union);
    if (MC->getTag() == dwarf::DW_TAG_union_type) {
      if (At != Base)
        return miss(Union);
      // Any struct-typed (or nested union) member over the bytes taints.
      for (const DINode *E : MC->getElements()) {
        const auto *D = dyn_cast<DIDerivedType>(E);
        if (!D || D->getTag() != dwarf::DW_TAG_member)
          continue;
        const uint64_t MO = D->getOffsetInBits() / 8,
                       MS = (D->getSizeInBits() + 7) / 8;
        if (Rel + Size <= MO || Rel >= MO + MS)
          continue;
        const DIType *MT = D->getBaseType();
        while (const auto *DD = dyn_cast_or_null<DIDerivedType>(MT)) {
          const unsigned DT = DD->getTag();
          if (DT != dwarf::DW_TAG_typedef && DT != dwarf::DW_TAG_const_type &&
              DT != dwarf::DW_TAG_volatile_type)
            break;
          MT = DD->getBaseType();
        }
        while (const auto *AC = dyn_cast_or_null<DICompositeType>(MT)) {
          if (AC->getTag() != dwarf::DW_TAG_array_type)
            break;
          MT = AC->getBaseType();
        }
        if (isa_and_nonnull<DICompositeType>(MT))
          return miss(Union);
      }
      return intern((stripStructNameSuffix(S->getName()) + "+" +
                     std::to_string(Base + Rel))
                        .str());
    }
    if (MC->getTag() != dwarf::DW_TAG_structure_type)
      return miss(Union);
    C = MC; // an unnamed (or IR-transparent) struct between S and the union
  }
  return miss(Union);
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
        return Named ? unionSlot(Named, Base, Rel, Size) : miss(Union);
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

AccessNames::Position AccessNames::position(const Value *Ptr,
                                            const DataLayout &DL) {
  Position R;
  SmallVector<const GEPOperator *, 4> Chain;
  const Value *P = Ptr->stripPointerCasts();
  while (const auto *G = dyn_cast<GEPOperator>(P)) {
    Chain.push_back(G);
    P = G->getPointerOperand()->stripPointerCasts();
  }
  // A tainted position (pun, variable offset) is known only to lie in some
  // struct the chain names: every named struct type on it. A union is
  // narrower: names exist only for the structs inside it (a union has no
  // names of its own), so the structs the chain entered before the union
  // are not tainted.
  SmallVector<StructType *, 4> Before; // named structs entered so far
  auto taint = [&](Why W) -> Position {
    Position T;
    T.why = W;
    T.tainted = true;
    auto add = [&](Type *Ty) {
      while (Ty && Ty->isArrayTy())
        Ty = Ty->getArrayElementType();
      if (auto *ST = dyn_cast_or_null<StructType>(Ty))
        if (isNamed(ST) && !isUnion(ST) &&
            !(W == Union &&
              std::find(Before.begin(), Before.end(), ST) != Before.end()) &&
            std::find(T.open.begin(), T.open.end(), ST) == T.open.end())
          T.open.push_back(ST);
    };
    if (const auto *GV = dyn_cast<GlobalVariable>(P))
      add(GV->getValueType());
    else if (const auto *AI = dyn_cast<AllocaInst>(P))
      add(AI->getAllocatedType());
    for (const GEPOperator *G : Chain)
      for (auto GTI = gep_type_begin(G), E = gep_type_end(G); GTI != E; ++GTI)
        add(GTI.getIndexedType());
    if (R.S && W != Union)
      add(R.S);
    return T;
  };
  // Position: the innermost named struct holding the address, and the
  // byte offset in it (array elements folded). Unknown until a typed
  // GEP, or the declared type of a global or stack object, names it.
  StructType *&S = R.S;
  int64_t &Off = R.off;
  Why Lost = NoStruct;
  bool VarLost = false; // a variable step left the last known struct
  bool InUnion = false; // inside a union of S: S and the offset stay
  auto enter = [&](Type *Ty) -> bool {
    if (auto *ST = dyn_cast<StructType>(Ty)) {
      if (isUnion(ST)) {
        if (!S)
          return false; // a union outside any named struct
        InUnion = true;
        return true;
      }
      if (isNamed(ST) && !InUnion) {
        S = ST;
        Off = 0;
        VarLost = false;
        Before.push_back(ST);
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
      return taint(Union);
    if (!Decl) {
      const BaseType B = baseStruct(P); // declared `struct B *`
      if (B.S) {
        enter(B.S);
      } else if (B.C) {
        R.DIS = B.C;
        R.DITag = B.Tag;
        if (const auto *A = dyn_cast<Argument>(P))
          R.M = A->getParent()->getParent();
        else
          R.M = cast<Instruction>(P)->getModule();
      }
    }
  }
  for (auto It = Chain.rbegin(); It != Chain.rend(); ++It) {
    const GEPOperator *G = *It;
    if (PunnedBases.count(G->getPointerOperand()->stripPointerCasts()))
      return taint(Pun);
    if (R.DIS && !S) {
      // A debug-info-only position follows byte arithmetic; any typed
      // GEP names its own position instead.
      const auto *C0 = G->getNumIndices() == 1
                           ? dyn_cast<ConstantInt>(G->idx_begin()->get())
                           : nullptr;
      if (C0 && G->getSourceElementType()->isIntegerTy()) {
        Off += C0->getSExtValue() *
               (int64_t)DL.getTypeAllocSize(G->getSourceElementType());
        continue;
      }
      R.DIS = nullptr;
      Off = 0;
    }
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
          return taint(Pun);
        } else if (ViaUnion) {
          return taint(Union);
        } else {
          Off = NOff;
        }
      } else if (typeAt(S, (uint64_t)Off, T, DL, ViaUnion, InArray) &&
                 InArray) {
        if (ViaUnion)
          return taint(Union);
        // a variable step through an array of T stays in that array:
        // the folded position is unchanged
      } else {
        Position V = taint(OutOfRange); // somewhere in or past S
        if (!V.open.empty()) {
          S = nullptr;
          VarLost = true;
          Lost = OutOfRange;
          R.open = std::move(V.open);
        } else {
          S = nullptr;
          Lost = OutOfRange;
        }
      }
    }
    Type *Cur = T;
    if (!enter(Cur))
      return taint(Union);
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
        return taint(Union);
    }
  }
  if (!S) {
    R.why = Lost;
    R.tainted = VarLost; // R.open: the structs the variable step left
    if (!VarLost)
      R.open.clear();
  }
  return R;
}

uint32_t AccessNames::ofAccess(const Value *Ptr, uint64_t Size,
                               const DataLayout &DL) {
  return ofPosition(position(Ptr, DL), Size, DL);
}

uint32_t AccessNames::ofMemAccess(const Instruction &I, const Value *Ptr,
                                  uint64_t Size, const DataLayout &DL) {
  const Position P = position(Ptr, DL);
  if (P.S || P.DIS)
    return ofPosition(P, Size, DL);
  if (P.tainted) // a union or a pun on the chain: no name, whatever TBAA says
    return miss(P.why);
  // Struct-path tag: !{base type, access type, offset}; a struct access
  // has a base type node of the form !{!"tag", member, offset, ...}
  // distinct from the access type.
  const MDNode *Tag = I.getMetadata(LLVMContext::MD_tbaa);
  if (!Tag || Tag->getNumOperands() < 3)
    return miss(P.why);
  const auto *Base = dyn_cast<MDNode>(Tag->getOperand(0));
  const auto *Acc = dyn_cast<MDNode>(Tag->getOperand(1));
  const auto *OffC = mdconst::dyn_extract<ConstantInt>(Tag->getOperand(2));
  if (!Base || !Acc || Base == Acc || !OffC || Base->getNumOperands() < 3)
    return miss(P.why);
  const auto *TagName = dyn_cast<MDString>(Base->getOperand(0));
  if (!TagName)
    return miss(P.why);
  StructType *S = structByTag(I.getModule(), TagName->getString());
  if (!S)
    return miss(P.why);
  const uint64_t Off = OffC->getZExtValue();
  if (Off >= DL.getTypeAllocSize(S))
    return miss(OutOfRange);
  const uint32_t N = ofSlot(S, Off, Size, DL);
  if (N != Unnamed)
    namedByTBAA++;
  return N;
}

const SmallVector<uint32_t, 8> &AccessNames::leavesOf(StructType *S,
                                                      const DataLayout &DL) {
  auto [It, Ins] = Leaves.try_emplace(S);
  if (!Ins)
    return It->second;
  SmallVector<uint32_t, 8> Out;
  std::function<void(Type *, StructType *, uint64_t)> walk =
      [&](Type *T, StructType *Named, uint64_t Base) {
        if (auto *ST = dyn_cast<StructType>(T)) {
          if (isUnion(ST) && Named) {
            // the union's pointer-sized slots that have a name (unionSlot)
            const uint64_t Z = DL.getTypeAllocSize(ST);
            const uint64_t Saved = unnamedBy[Union]; // probing, not naming
            for (uint64_t K = 0; K + 8 <= Z; K += 8) {
              const uint32_t N = unionSlot(Named, Base, K, 8);
              if (N != Unnamed)
                Out.push_back(N);
            }
            unnamedBy[Union] = Saved;
            return;
          }
          if (isUnion(ST) || ST->isOpaque())
            return; // no names inside a union outside a named struct
          if (isNamed(ST)) {
            Named = ST;
            Base = 0;
          }
          const StructLayout *SL = DL.getStructLayout(ST);
          for (unsigned I = 0; I < ST->getNumElements(); I++)
            walk(ST->getElementType(I), Named, Base + SL->getElementOffset(I));
          return;
        }
        if (auto *AT = dyn_cast<ArrayType>(T)) {
          walk(AT->getElementType(), Named, Base);
          return;
        }
        Out.push_back(intern((stripStructNameSuffix(Named->getName()) + "+" +
                              std::to_string(Base))
                                 .str()));
      };
  walk(S, nullptr, 0);
  std::sort(Out.begin(), Out.end());
  Out.erase(std::unique(Out.begin(), Out.end()), Out.end());
  // try_emplace's iterator may be invalidated by interning (Leaves is a
  // different map, but walk() recursion does not touch it): re-find.
  auto &Slot = Leaves[S];
  Slot = std::move(Out);
  return Slot;
}

} // namespace ka
