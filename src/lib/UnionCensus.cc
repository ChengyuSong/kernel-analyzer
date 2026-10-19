// UnionCensus.cc: --cfl-census-unions. Measurement only (adds no edges).
//
// A C union holds one member at a time; which one is live is decided by
// something else in the program. Without that something, an analysis
// cannot tell a read of one member from the write of another (static type
// confusion), and the sound answer merges the members. This census finds,
// per union field of a struct, whether a DISCRIMINATOR exists that a key
// could use. Verdicts, strongest first:
//  - CALLBACK-keyable: another field written with a function (or an ops
//    table holding functions) at every write of the union, the function
//    determining the member, and every read inside a function paired with
//    its member (the correlated dispatch: `p->f(p)` reads what `p`'s
//    writer paired with `f`; Walker.u);
//  - TAG-verified: every read is KEYED: the facts its dominating branches
//    establish on the object (`f == C`, `f != C`, a flag bit set or clear,
//    a pointer null or not) rule out every write of every other member.
//    Only facts on STABLE fields count: written nowhere but where the
//    union is written (JsonNode.eU), or, for a bit, changed elsewhere only
//    in other bits. A read whose facts rule out its own member's writes
//    is CONTRADICTED (a confusion, or a gap in this census);
//  - TAG-tested: one field is co-written at every union write with a
//    value that determines the member, and a test of it decides the path
//    to every read; whether the field still holds that value at the read
//    is not checked (Expr.flags is set and cleared all over sqlite3).
// Tag values are constants (also those every direct caller passes for a
// parameter), flag bits (`flags |= EP_xIsSelect`), functions and globals.
// The object is followed one or two calls away: its tag may be written in
// the same function, by a callee given the object, by the callee that
// returned it, or by every direct caller passing it; a read may be tested
// at every direct call site. Global initializers are writes.
// Unions come from debug info (IR lowers them to their largest member).
// An access is a load or store whose address is a constant GEP chain
// landing in a union field; its member is inferred from the debug type
// of the value written or read. Plan docs/plan-named-cells.md.

#include "CallGraphInternal.h"
#include <llvm/Analysis/CaptureTracking.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/Support/KnownBits.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Operator.h>
#include <map>
#include <optional>
#include <set>

using namespace llvm;

namespace {

const DIType *stripDI(const DIType *T) {
  while (const auto *D = dyn_cast_or_null<DIDerivedType>(T)) {
    const unsigned tag = D->getTag();
    if (tag == dwarf::DW_TAG_typedef || tag == dwarf::DW_TAG_const_type ||
        tag == dwarf::DW_TAG_volatile_type || tag == dwarf::DW_TAG_member ||
        tag == dwarf::DW_TAG_restrict_type || tag == dwarf::DW_TAG_atomic_type)
      T = D->getBaseType();
    else
      break;
  }
  return T;
}

// A name for what a value of this type is: "ptr:Pointee", "fnptr", or the
// base type's name. Typedef names of the pointee count as the pointee.
// Known bits of an integer value (LLVM's analysis), and for the result of
// a direct call to a defined function, the bits known in every value it
// returns (`flags |= sqlite3IsTrueOrFalse(z)`), two calls deep.
KnownBits knownBitsThroughCalls(const Value *V, const DataLayout &DL, int depth = 2) {
  KnownBits K = computeKnownBits(V, DL);
  const auto *CB = dyn_cast<CallBase>(V->stripPointerCasts());
  const Function *F = CB ? CB->getCalledFunction() : nullptr;
  if (!F || depth == 0 || F->isDeclaration()) return K; // (this module's bodies)
  std::optional<KnownBits> R;
  for (const BasicBlock &B : *F)
    if (const auto *RI = dyn_cast<ReturnInst>(B.getTerminator())) {
      const Value *RV = RI->getReturnValue();
      if (!RV || RV->getType() != V->getType()) return K;
      const KnownBits KR = knownBitsThroughCalls(RV, DL, depth - 1);
      R = R ? R->intersectWith(KR) : KR;
    }
  if (R) K = K.unionWith(*R);
  return K;
}

// The bits of an integer value known zero and known one, as "kb:Z:O";
// empty when nothing is known. Written for tag writes whose exact value is
// not known (`flags = x & M`, `flags |= y`).
std::string knownBitsKey(const Value *V) {
  if (!V->getType()->isIntegerTy() || V->getType()->getIntegerBitWidth() > 64)
    return "";
  const Module *M = nullptr;
  if (const auto *I = dyn_cast<Instruction>(V)) M = I->getModule();
  else if (const auto *A = dyn_cast<Argument>(V)) M = A->getParent()->getParent();
  if (!M) return "";
  const KnownBits K = knownBitsThroughCalls(V, M->getDataLayout());
  const uint64_t Z = K.Zero.getZExtValue(), O = K.One.getZExtValue();
  if (!Z && !O) return "";
  return "kb:" + std::to_string(Z) + ":" + std::to_string(O);
}

std::string typeKey(const DIType *T) {
  T = stripDI(T);
  if (!T)
    return "?";
  if (const auto *D = dyn_cast<DIDerivedType>(T)) {
    if (D->getTag() == dwarf::DW_TAG_pointer_type) {
      const DIType *P = stripDI(D->getBaseType());
      if (!P)
        return "ptr:void";
      if (isa<DISubroutineType>(P))
        return "fnptr";
      if (P->getName().empty() && isa<DIDerivedType>(P))
        return "ptr:" + typeKey(P);
      return "ptr:" + P->getName().str();
    }
  }
  if (isa<DISubroutineType>(T))
    return "fn";
  return T->getName().str();
}

struct UnionField {
  std::string structName, fieldName;
  uint64_t off = 0, size = 0; // bytes
  std::vector<std::pair<std::string, std::string>> members; // name, typeKey
  std::vector<const DIType *> memberTypes;                  // debug type, by member
  // The members whose typed-pointer LLVM type is the union's storage type
  // (clang lowers a union to its first member of largest alignment, then
  // size); every other member is reached through a bitcast.
  std::set<std::string> storageMembers;
};

// The typed-pointer LLVM type a member lowers to, as a class: pointers to
// char-like or void are one type (i8*), pointers to a named struct are
// that struct's pointer, integers by width.
std::string loweredClass(const DIType *T) {
  T = stripDI(T);
  if (!T) return "?";
  if (const auto *D = dyn_cast<DIDerivedType>(T))
    if (D->getTag() == dwarf::DW_TAG_pointer_type) {
      const DIType *P = stripDI(D->getBaseType());
      if (!P) return "i8*";
      if (const auto *B = dyn_cast<DIBasicType>(P))
        if (B->getSizeInBits() == 8) return "i8*";
      if (isa<DISubroutineType>(P)) return "fn*:" + std::to_string((uintptr_t)P);
      return P->getName().empty() ? "anon*" : P->getName().str() + "*";
    }
  if (const auto *B = dyn_cast<DIBasicType>(T))
    return (B->getEncoding() == dwarf::DW_ATE_float ? "f" : "i") +
           std::to_string(B->getSizeInBits());
  return T->getName().str();
}

// Alignment of a member type in bits (natural for scalars and pointers).
uint64_t diAlign(const DIType *T, int depth = 0) {
  T = stripDI(T);
  if (!T || depth > 8) return 8;
  if (T->getAlignInBits()) return T->getAlignInBits();
  if (const auto *C = dyn_cast<DICompositeType>(T)) {
    if (C->getTag() == dwarf::DW_TAG_array_type) return diAlign(C->getBaseType(), depth + 1);
    uint64_t a = 8;
    for (const DINode *E : C->getElements())
      if (const auto *M = dyn_cast<DIDerivedType>(E))
        a = std::max(a, diAlign(M->getBaseType(), depth + 1));
    return a;
  }
  return std::max<uint64_t>(T->getSizeInBits(), 8);
}

SmallVector<DbgValueInst *, 2> dbgValuesOf(const Value *V) {
  SmallVector<DbgValueInst *, 2> out;
  findDbgValues(out, const_cast<Value *>(V));
  return out;
}

// The C tag of a named IR struct (the link rename's ".N" stripped by the
// canonical stripStructNameSuffix). Never called for an anonymous struct
// (isAnonStruct), whose name names nothing.
std::string stripSuffix(StringRef N) {
  N = stripStructNameSuffix(N);
  N.consume_front("struct.");
  N.consume_front("union.");
  return N.str();
}

} // namespace

void CallGraphPass::runUnionCensus() {
  uncheckedReads.clear();
  unionAddrTyped.clear();
  unionEmbedTyped.clear();
  unionCopyOf.clear();
  unionCopyTags.clear();
  unionCopyRows.clear();
  unionCopyVector = unionCopyPhi = 0;
  // ---- 1. Union fields of structs, from debug info ----
  std::map<std::pair<std::string, uint64_t>, UnionField> unions; // (S, off)
  std::map<std::string, std::vector<std::pair<uint64_t, uint64_t>>> fieldsOf;
  std::map<std::pair<std::string, uint64_t>, std::string> fieldType; // typeKey
  // (struct, member offset) -> the named struct embedded there, if any
  std::map<std::pair<std::string, uint64_t>, std::pair<std::string, uint64_t>> embeddedAt;
  for (auto &[M, _] : Ctx->Modules) {
    DebugInfoFinder DIF;
    DIF.processModule(*M);
    for (const DIType *T : DIF.types()) {
      const auto *CT = dyn_cast<DICompositeType>(T);
      if (!CT || CT->getTag() != dwarf::DW_TAG_structure_type ||
          CT->getName().empty())
        continue;
      const std::string S = CT->getName().str();
      for (const DINode *E : CT->getElements()) {
        const auto *Mem = dyn_cast<DIDerivedType>(E);
        if (!Mem || Mem->getTag() != dwarf::DW_TAG_member)
          continue;
        const uint64_t off = Mem->getOffsetInBits() / 8;
        fieldsOf[S].emplace_back(off, Mem->getSizeInBits() / 8);
        fieldType.emplace(std::make_pair(S, off), typeKey(Mem->getBaseType()));
        if (const auto *ET = dyn_cast_or_null<DICompositeType>(stripDI(Mem->getBaseType())))
          if (ET->getTag() == dwarf::DW_TAG_structure_type && !ET->getName().empty())
            embeddedAt[{S, off}] = {ET->getName().str(), Mem->getSizeInBits() / 8};
        const auto *UT = dyn_cast_or_null<DICompositeType>(stripDI(Mem->getBaseType()));
        if (!UT || UT->getTag() != dwarf::DW_TAG_union_type)
          continue;
        auto &U = unions[{S, off}];
        if (!U.members.empty())
          continue; // one per (struct, offset), across modules
        U.structName = S;
        U.fieldName = Mem->getName().empty() ? "<anon>" : Mem->getName().str();
        U.off = off;
        U.size = Mem->getSizeInBits() / 8;
        const DIType *storage = nullptr;
        for (const DINode *UE : UT->getElements())
          if (const auto *UM = dyn_cast<DIDerivedType>(UE)) {
            U.members.emplace_back(UM->getName().str(), typeKey(UM->getBaseType()));
            U.memberTypes.push_back(UM->getBaseType());
            const DIType *MT = UM->getBaseType();
            if (!storage || diAlign(MT) > diAlign(storage) ||
                (diAlign(MT) == diAlign(storage) &&
                 stripDI(MT) && stripDI(storage) &&
                 stripDI(MT)->getSizeInBits() > stripDI(storage)->getSizeInBits()))
              storage = MT;
          }
        if (storage)
          for (const DINode *UE : UT->getElements())
            if (const auto *UM = dyn_cast<DIDerivedType>(UE))
              if (loweredClass(UM->getBaseType()) == loweredClass(storage))
                U.storageMembers.insert(UM->getName().str());
      }
    }
  }
  for (auto &[S, fs] : fieldsOf) {
    std::sort(fs.begin(), fs.end());
    fs.erase(std::unique(fs.begin(), fs.end()), fs.end());
  }
  unionFieldNotes.clear();
  for (auto &[k, U] : unions)
    unionFieldNotes["struct." + k.first][(int64_t)k.second] = {U.fieldName, (int64_t)U.size,
                                                               "no access found by the union census"};

  // ---- 2. Accesses: (struct, byte offset from the object, base) ----
  // The stores into a pointer variable's stack slot (O0 keeps every
  // variable in one; a struct on the stack is an object, not a slot).
  std::map<const AllocaInst *, std::vector<const StoreInst *>> slotStores, scalarStores;
  // Direct calls, by caller and by callee (definitions across modules).
  std::map<const Function *, std::vector<std::pair<const CallBase *, const Function *>>> callsIn;
  std::map<const Function *, std::vector<const CallBase *>> callersOf;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        if (const auto *SI = dyn_cast<StoreInst>(&I))
          if (const auto *A = dyn_cast<AllocaInst>(SI->getPointerOperand()->stripPointerCasts()))
            (A->getAllocatedType()->isPointerTy() ? slotStores : scalarStores)[A].push_back(SI);
        if (const auto *CB = dyn_cast<CallBase>(&I))
          if (Function *T = CB->getCalledFunction())
            if (!T->isIntrinsic()) {
              const Function *D = getFuncDef(T);
              if (!D->isDeclaration()) {
                callsIn[&F].emplace_back(CB, D);
                callersOf[D].push_back(CB);
              }
            }
      }
  const size_t kCallers = 64;
  // The object a pointer value names: the slot it was loaded from, through
  // single-store copies between slots (`retval = pNew`).
  auto resolveBase = [&](const Value *V) -> const Value * {
    for (int i = 0; i < 6; i++) {
      V = V->stripPointerCasts();
      const auto *LI = dyn_cast<LoadInst>(V);
      if (!LI)
        return V;
      const auto *A = dyn_cast<AllocaInst>(LI->getPointerOperand()->stripPointerCasts());
      if (!A || !A->getAllocatedType()->isPointerTy())
        return V;
      auto it = slotStores.find(A);
      if (it != slotStores.end() && it->second.size() == 1)
        if (const auto *L2 = dyn_cast<LoadInst>(it->second[0]->getValueOperand()->stripPointerCasts()))
          if (const auto *A2 = dyn_cast<AllocaInst>(L2->getPointerOperand()->stripPointerCasts());
              A2 && A2->getAllocatedType()->isPointerTy()) {
            V = L2;
            continue;
          }
      return A;
    }
    return V;
  };
  struct Pos {
    std::string S;
    uint64_t off = 0;
    const Value *base = nullptr;
    uint64_t embed = 0; // offset of S inside the object `base` points to
    bool ok = false;
  };
  // Descend into embedded structs (never into a union): the access
  // belongs to the innermost struct holding it (pFix->w.u is Walker.u of
  // the walker embedded in a DbFixer).
  auto descend = [&](Pos &R) {
    for (int d = 0; d < 6; d++) {
      bool moved = false;
      auto fit = fieldsOf.find(R.S);
      if (fit == fieldsOf.end()) break;
      for (auto &[o, sz] : fit->second) {
        if (R.off < o || R.off >= o + std::max<uint64_t>(sz, 1)) continue;
        auto eit = embeddedAt.find({R.S, o});
        if (eit == embeddedAt.end()) break;
        R.S = eit->second.first;
        R.off -= o;
        R.embed += o;
        moved = true;
        break;
      }
      if (!moved) break;
    }
  };
  // The debug type of a value (valueKey, defined below).
  std::function<std::string(const Value *, int)> valueKeyFwd;
  // Addresses whose chain starts at an anonymous struct: positioned by the
  // base pointer's declared struct and offset, or with none (no position,
  // the byte case); counted.
  std::set<const Value *> anonPosNamed, anonPosNone;
  // `depth` is valueKey's, when the debug typing below runs inside it.
  auto position = [&](const Value *P, const DataLayout &DL, int depth = 0) {
    Pos R;
    std::vector<const GEPOperator *> chain;
    const Value *const P0 = P;
    P = P->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(P)) {
      chain.push_back(G);
      P = G->getPointerOperand()->stripPointerCasts();
    }
    const auto *ST = chain.empty() ? nullptr
                                   : dyn_cast<StructType>(chain.back()->getSourceElementType());
    // An anonymous struct's name names nothing (isAnonStruct): its
    // position is the base pointer's, as for a raw pointer.
    if (!ST || !ST->hasName() || isAnonStruct(ST)) {
      // -O3 on a raw pointer (an allocator's result): no GEP (offset 0) or
      // constant byte offsets. Typed by the pointer's debug type
      // (`Expr *pNew`), when it names a struct we know.
      int64_t total = 0;
      for (const GEPOperator *G : chain) {
        APInt O(DL.getIndexTypeSizeInBits(G->getType()), 0);
        if (!G->accumulateConstantOffset(DL, O)) return R;
        total += O.getSExtValue();
      }
      const bool anon = ST && isAnonStruct(ST);
      if (anon) anonPosNone.insert(P0);
      if (total < 0 || !valueKeyFwd) return R;
      const std::string k = valueKeyFwd(P, depth + 1);
      if (k.rfind("ptr:", 0) != 0 || !fieldsOf.count(k.substr(4))) return R;
      if (anon) anonPosNone.erase(P0), anonPosNamed.insert(P0);
      R.S = k.substr(4);
      R.off = (uint64_t)total;
      R.base = resolveBase(P);
      R.ok = true;
      descend(R);
      return R;
    }
    // Arrays are one element: an index over whole elements (the pointer
    // level of &a[i], or an array inside the struct) keeps the position;
    // struct members add their offsets; a byte index must be constant.
    int64_t total = 0;
    for (auto cit = chain.rbegin(); cit != chain.rend(); ++cit) {
      bool first = true;
      for (auto GTI = gep_type_begin(*cit), E = gep_type_end(*cit); GTI != E; ++GTI) {
        const Value *Idx = GTI.getOperand();
        if (StructType *STy = GTI.getStructTypeOrNull()) {
          const auto *CI = dyn_cast<ConstantInt>(Idx);
          if (!CI) return R;
          total += (int64_t)DL.getStructLayout(STy)->getElementOffset(CI->getZExtValue());
        } else {
          const uint64_t esz = DL.getTypeAllocSize(GTI.getIndexedType());
          if (esz == 1 && first) { // byte arithmetic on the pointer
            const auto *CI = dyn_cast<ConstantInt>(Idx);
            if (!CI) return R;
            total += CI->getSExtValue();
          }
          // otherwise: whole elements of an array, one element
        }
        first = false;
      }
    }
    if (total < 0)
      return R;
    R.S = stripSuffix(ST->getName());
    R.off = (uint64_t)total;
    R.base = resolveBase(P);
    R.ok = true;
    descend(R);
    return R;
  };
  auto unionAt = [&](const Pos &Q) -> UnionField * {
    if (!Q.ok)
      return nullptr;
    auto it = unions.upper_bound({Q.S, Q.off});
    if (it == unions.begin())
      return nullptr;
    --it;
    if (it->first.first != Q.S || Q.off < it->second.off ||
        Q.off >= it->second.off + it->second.size)
      return nullptr;
    return &it->second;
  };
  // The field of S containing an offset (its start), or none.
  auto fieldAt = [&](const std::string &S, uint64_t off) -> int64_t {
    auto fit = fieldsOf.find(S);
    if (fit == fieldsOf.end())
      return -1;
    for (auto &[o, sz] : fit->second)
      if (off >= o && off < o + std::max<uint64_t>(sz, 1))
        return (int64_t)o;
    return -1;
  };
  // The debug type of a value: its variable, parameter, global or slot.
  std::function<std::string(const Value *, int)> valueKey =
      [&](const Value *V, int depth) -> std::string {
    if (!V || depth > 4)
      return "?";
    V = V->stripPointerCasts();
    if (isa<Function>(V))
      return "fnptr";
    if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
      return "null";
    if (isa<ConstantInt>(V) || isa<ConstantFP>(V))
      return "const";
    for (auto *DVI : dbgValuesOf(V))
      if (auto *Var = DVI->getVariable())
        return typeKey(Var->getType());
    // The variable may be recorded on a no-op cast of the value (typed
    // IR upgraded to opaque pointers: `%36 = bitcast ptr %35 to ptr`).
    for (const User *U : V->users())
      if (isa<BitCastInst>(U) || isa<AddrSpaceCastInst>(U))
        for (auto *DVI : dbgValuesOf(U))
          if (auto *Var = DVI->getVariable())
            return typeKey(Var->getType());
    if (const auto *AI = dyn_cast<AllocaInst>(V)) {
      for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(AI)))
        if (auto *Var = DDI->getVariable())
          return "ptr:" + stripDI(Var->getType())->getName().str();
      return "?";
    }
    if (const auto *LI = dyn_cast<LoadInst>(V))
      if (const auto *A = dyn_cast<AllocaInst>(LI->getPointerOperand()->stripPointerCasts()))
        for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(A)))
          if (auto *Var = DDI->getVariable())
            return typeKey(Var->getType());
    if (const auto *A = dyn_cast<Argument>(V))
      if (const DISubprogram *SP = A->getParent()->getSubprogram())
        if (auto *STy = SP->getType()) {
          auto TA = STy->getTypeArray();
          if (A->getArgNo() + 1 < TA.size())
            return typeKey(TA[A->getArgNo() + 1]);
        }
    if (const auto *GV = dyn_cast<GlobalVariable>(V)) {
      SmallVector<DIGlobalVariableExpression *, 1> GVEs;
      GV->getDebugInfo(GVEs);
      for (auto *E : GVEs)
        return "ptr:" + stripDI(E->getVariable()->getType())->getName().str();
    }
    // At -O3 a value keeps no variable: a pointer to struct T made by a
    // GEP (&a[i], a struct-typed index), through phis and selects.
    if (const auto *G = dyn_cast<GEPOperator>(V))
      if (const auto *ST = dyn_cast<StructType>(G->getResultElementType()))
        if (ST->hasName() && !isAnonStruct(ST) && G->getNumIndices() == 1)
          return "ptr:" + stripSuffix(ST->getName());
    if (const auto *PN = dyn_cast<PHINode>(V)) {
      std::string k;
      for (const Value *In : PN->incoming_values()) {
        if (isa<ConstantPointerNull>(In)) continue;
        const std::string ki = valueKey(In, depth + 1);
        if (ki == "?" || (!k.empty() && ki != k)) return "?";
        k = ki;
      }
      if (!k.empty()) return k;
    }
    if (const auto *SL = dyn_cast<SelectInst>(V)) {
      const std::string a = valueKey(SL->getTrueValue(), depth + 1),
                        b = valueKey(SL->getFalseValue(), depth + 1);
      if (a == b || b == "null") return a;
      if (a == "null") return b;
    }
    // A call's result: the callee's declared return type.
    if (const auto *CB = dyn_cast<CallBase>(V))
      if (const Function *T = CB->getCalledFunction())
        if (const DISubprogram *SP = getFuncDef(const_cast<Function *>(T))->getSubprogram())
          if (auto *STy = SP->getType())
            if (STy->getTypeArray().size() > 0)
              return typeKey(STy->getTypeArray()[0]);
    // A value loaded from a struct field: the field's declared type.
    if (const auto *LI = dyn_cast<LoadInst>(V)) {
      const Pos Q = position(LI->getPointerOperand(), LI->getModule()->getDataLayout(), depth);
      if (Q.ok && !unionAt(Q)) {
        auto it = fieldType.find({Q.S, Q.off});
        if (it != fieldType.end())
          return it->second;
      }
    }
    return "?";
  };
  valueKeyFwd = valueKey;
  // What a read is used as: the variable it is stored into, or its
  // debug value, or the struct its GEP users index it as.
  // R1 (Fable 2026-10-17, a bug fix): the loaded value's uses are walked
  // through no-op casts (bitcast, addrspacecast: the typed IR clang -O0
  // upgraded to opaque pointers keeps `bitcast ptr %v to ptr`), as valueKey
  // already does for debug values; `casts` false gives the walk before R1
  // (counted).
  auto readKey = [&](const LoadInst *LI, bool casts = true) -> std::string {
    for (auto *DVI : dbgValuesOf(LI))
      if (auto *Var = DVI->getVariable())
        return typeKey(Var->getType());
    std::vector<const User *> usersR(LI->users().begin(), LI->users().end());
    std::vector<const Value *> asLI{LI};
    for (size_t ui = 0; casts && ui < usersR.size(); ui++)
      if (isa<BitCastInst>(usersR[ui]) || isa<AddrSpaceCastInst>(usersR[ui])) {
        asLI.push_back(usersR[ui]);
        for (const User *U2 : usersR[ui]->users()) usersR.push_back(U2);
      }
    auto isLI = [&](const Value *X) { return std::find(asLI.begin(), asLI.end(), X) != asLI.end(); };
    for (const User *U : usersR) {
      if (const auto *SI = dyn_cast<StoreInst>(U))
        if (isLI(SI->getValueOperand()))
          if (const auto *A = dyn_cast<AllocaInst>(SI->getPointerOperand()->stripPointerCasts()))
            for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(A)))
              if (auto *Var = DDI->getVariable())
                return typeKey(Var->getType());
      if (const auto *G = dyn_cast<GetElementPtrInst>(U))
        if (isLI(G->getPointerOperand()))
          if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
            if (ST->hasName() && !isAnonStruct(ST))
              return "ptr:" + stripSuffix(ST->getName());
      if (const auto *CB = dyn_cast<CallBase>(U)) {
        if (isLI(CB->getCalledOperand()))
          return "fnptr";
        // Passed to a call: the callee's declared parameter type.
        if (const Function *T = CB->getCalledFunction())
          if (const DISubprogram *SP = getFuncDef(const_cast<Function *>(T))->getSubprogram())
            if (auto *STy = SP->getType())
              for (unsigned j = 0; j < CB->arg_size(); j++)
                if (isLI(CB->getArgOperand(j)) && j + 1 < STy->getTypeArray().size())
                  return typeKey(STy->getTypeArray()[j + 1]);
      }
    }
    return "?";
  };
  // Does debug type T hold a field of type `key` exactly at byte `rel`
  // (through nested structs, unions and array elements)?
  std::function<bool(const DIType *, int64_t, const std::string &, int)> layoutHas =
      [&](const DIType *T, int64_t rel, const std::string &key, int depth) -> bool {
    T = stripDI(T);
    if (!T || rel < 0 || depth > 8)
      return false;
    if (const auto *C = dyn_cast<DICompositeType>(T)) {
      const unsigned tag = C->getTag();
      if (tag == dwarf::DW_TAG_array_type) {
        const DIType *E = stripDI(C->getBaseType());
        const int64_t es = E ? (int64_t)((E->getSizeInBits() + 7) / 8) : 0;
        return es > 0 && layoutHas(E, rel % es, key, depth + 1);
      }
      if (tag != dwarf::DW_TAG_structure_type && tag != dwarf::DW_TAG_union_type)
        return false;
      for (const DINode *N : C->getElements()) {
        const auto *D = dyn_cast<DIDerivedType>(N);
        if (!D || D->getTag() != dwarf::DW_TAG_member || D->isStaticMember())
          continue;
        const int64_t MO = (int64_t)(D->getOffsetInBits() / 8), MS = (int64_t)((D->getSizeInBits() + 7) / 8);
        if (rel >= MO && rel < MO + std::max<int64_t>(MS, 1) && layoutHas(D->getBaseType(), rel - MO, key, depth + 1))
          return true;
      }
      return false;
    }
    return rel == 0 && typeKey(T) == key;
  };
  // The member an access of type `key` at byte `rel` of the union is: the
  // one whose type is the key; else (plan 3.51 (2), Fable 2026-10-16) the
  // one whose layout holds a field of that type at rel, through nested
  // structs (debug info only: a verdict gained with -g). Several members
  // that fit: not typed, its own class (`shared`).
  size_t r1Reads = 0;                                      // R1: reads typed through a no-op cast
  std::map<std::string, std::pair<size_t, size_t>> r2Pairs; // R2: "T>P" -> (stores, reads) typed by it
  auto memberOf = [&](const UnionField &U, const std::string &key, int64_t rel, bool *byLayout = nullptr,
                      bool *shared = nullptr, std::string *embedVia = nullptr) {
    std::vector<std::string> hits;
    for (auto &[nm, tk] : U.members)
      if (tk == key)
        hits.push_back(nm);
    if (hits.size() == 1)
      return hits[0];
    if (!hits.empty())
      return std::string("ambiguous");
    if (key == "?" || key.empty() || rel < 0)
      return std::string("?");
    // A void * value or use names no member by layout: C converts void * to
    // any member's pointer type (Fable 2026-10-17, (C')), so one member's
    // void * field fitting it types nothing; several fitting stay the shared
    // class. The member declared void * itself is matched above (its own
    // rule, 093752c).
    const bool voidKey = key == "ptr:void";
    for (size_t i = 0; i < U.members.size() && i < U.memberTypes.size(); i++) {
      const auto *C = dyn_cast_or_null<DICompositeType>(stripDI(U.memberTypes[i]));
      if (C && layoutHas(C, rel, key, 0))
        hits.push_back(U.members[i].first);
    }
    if (hits.size() == 1 && !voidKey) {
      if (byLayout) *byLayout = true;
      return hits[0];
    }
    // R2 (Fable 2026-10-17): a pointer to struct T that no member fits fits a
    // member whose field there points to P, P declared T's member at offset
    // 0 (transitively; the DI embedding table): the C upcast, both names of
    // one address. The levels of the chain together fit one member, or none
    // is typed.
    if (hits.empty() && !voidKey && key.rfind("ptr:", 0) == 0) {
      std::set<std::string> eh;
      std::string T = key.substr(4), via;
      for (int lv = 0; lv < 8; lv++) {
        auto eit = embeddedAt.find({T, 0});
        if (eit == embeddedAt.end()) break;
        T = eit->second.first;
        bool fit = false;
        for (size_t i = 0; i < U.members.size() && i < U.memberTypes.size(); i++) {
          const auto *C = dyn_cast_or_null<DICompositeType>(stripDI(U.memberTypes[i]));
          if (C && layoutHas(C, rel, "ptr:" + T, 0)) {
            eh.insert(U.members[i].first);
            fit = true;
          }
        }
        if (fit && via.empty()) via = key.substr(4) + ">" + T;
      }
      if (eh.size() == 1) {
        if (byLayout) *byLayout = true;
        if (embedVia) *embedVia = via;
        return *eh.begin();
      }
      if (eh.size() > 1) {
        if (shared) *shared = true;
        return std::string("ambiguous");
      }
    }
    if (hits.size() <= 1) // none fits; or a void * that one member's void * field fits: no member
      return std::string("?");
    if (shared) *shared = true;
    return std::string("ambiguous");
  };
  // (C', Fable 2026-10-17) A stored value that is a constant address inside
  // a global with debug info (the global, &g[i], &g.f: a constant GEP) has
  // the debug type of every object that starts at that address: walked by
  // byte offset, an array's element, the member of a struct (each member of
  // a union) holding the offset, never a bitfield. A struct starts with its
  // first member (and -O3 folds &g[i] into &g[i].first), so each level that
  // starts there is tried; the store is the one member that, over every
  // level, fits (memberOf), and no member when a level fits several or the
  // levels fit different members. `why` names the type and the global.
  // Not a constant address inside a global: "" (the rule does not apply).
  std::function<void(const DIType *, int64_t, std::vector<const DIType *> &, int)> typesAt =
      [&](const DIType *T, int64_t rel, std::vector<const DIType *> &out, int depth) {
        T = stripDI(T);
        if (!T || rel < 0 || depth > 8) return;
        if (rel == 0) out.push_back(T);
        const auto *C = dyn_cast<DICompositeType>(T);
        if (!C) return;
        if (C->getTag() == dwarf::DW_TAG_array_type) {
          const DIType *E = stripDI(C->getBaseType());
          const int64_t es = E ? (int64_t)((E->getSizeInBits() + 7) / 8) : 0;
          if (es > 0) typesAt(E, rel % es, out, depth + 1);
          return;
        }
        if (C->getTag() != dwarf::DW_TAG_structure_type && C->getTag() != dwarf::DW_TAG_union_type) return;
        for (const DINode *N : C->getElements()) {
          const auto *D = dyn_cast<DIDerivedType>(N);
          if (!D || D->getTag() != dwarf::DW_TAG_member || D->isStaticMember() || D->isBitField()) continue;
          const int64_t MO = (int64_t)(D->getOffsetInBits() / 8), MS = (int64_t)((D->getSizeInBits() + 7) / 8);
          if (rel >= MO && rel < MO + std::max<int64_t>(MS, 1)) typesAt(D->getBaseType(), rel - MO, out, depth + 1);
        }
      };
  auto addrMember = [&](const UnionField &U, const Value *V, int64_t rel, std::string &why) -> std::string {
    V = V->stripPointerCasts();
    const GlobalVariable *GV = dyn_cast<GlobalVariable>(V);
    int64_t off = 0;
    if (!GV)
      if (const auto *G = dyn_cast<GEPOperator>(V)) {
        GV = dyn_cast<GlobalVariable>(G->getPointerOperand()->stripPointerCasts());
        if (!GV) return "";
        APInt O(GV->getParent()->getDataLayout().getIndexTypeSizeInBits(G->getType()), 0);
        if (!G->accumulateConstantOffset(GV->getParent()->getDataLayout(), O)) return "";
        off = O.getSExtValue();
      }
    if (!GV) return "";
    SmallVector<DIGlobalVariableExpression *, 1> GVEs;
    GV->getDebugInfo(GVEs);
    if (GVEs.empty()) return "";
    std::vector<const DIType *> ts;
    typesAt(GVEs[0]->getVariable()->getType(), off, ts, 0);
    if (ts.empty()) return "";
    std::set<std::string> fits;
    std::string names;
    for (const DIType *T : ts) {
      std::string key;
      if (!T->getName().empty()) key = "ptr:" + T->getName().str();
      else if (isa<DIDerivedType>(T)) key = "ptr:" + typeKey(T);
      else continue; // an unnamed struct or array: no key
      const std::string m = memberOf(U, key, rel);
      if (m == "ambiguous") return "?";
      if (m == "?") continue;
      fits.insert(m);
      names += (names.empty() ? "" : ", ") + key.substr(4) + " *";
    }
    if (fits.size() != 1) return fits.empty() ? "" : "?";
    why = names + ", a constant address inside " + GV->getName().str();
    return *fits.begin();
  };
  // (C'') The load a store copies: its value, stripped of no-op casts, a
  // load; or a load of an -O0 spill local (only loads and stores of it as
  // the address, one store) whose stored value, stripped, is a load.
  auto copiedLoad = [&](const StoreInst *SI) -> const LoadInst * {
    const auto *L = dyn_cast<LoadInst>(SI->getValueOperand()->stripPointerCasts());
    if (!L) return nullptr;
    if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
      const StoreInst *only = nullptr;
      for (const User *U : A->users()) {
        if (const auto *LU = dyn_cast<LoadInst>(U); LU && LU->getPointerOperand() == A) continue;
        const auto *S2 = dyn_cast<StoreInst>(U);
        if (!S2 || S2->getPointerOperand() != A || S2->getValueOperand() == A || only) return nullptr;
        only = S2;
      }
      if (!only) return nullptr;
      L = dyn_cast<LoadInst>(only->getValueOperand()->stripPointerCasts());
    }
    return L;
  };
  // A name for a constant written into a field: a tag value.
  auto constKey = [](const Value *V) -> std::string {
    V = V->stripPointerCasts();
    if (const auto *CI = dyn_cast<ConstantInt>(V))
      return "int:" + std::to_string(CI->getSExtValue());
    if (isa<ConstantPointerNull>(V))
      return "null";
    if (const auto *Fn = dyn_cast<Function>(V))
      return "fn:" + Fn->getName().str();
    if (const auto *GV = dyn_cast<GlobalVariable>(V))
      return "gv:" + GV->getName().str();
    if (const auto *CE = dyn_cast<ConstantExpr>(V))
      if (CE->getOpcode() == Instruction::GetElementPtr)
        if (const auto *GV = dyn_cast<GlobalVariable>(CE->getOperand(0)->stripPointerCasts()))
          return "gv:" + GV->getName().str();
    return "";
  };

  // Integer casts carry a tag value unchanged.
  auto peel = [](const Value *V) {
    for (;;) {
      V = V->stripPointerCasts();
      if (isa<ZExtInst>(V) || isa<SExtInst>(V) || isa<TruncInst>(V))
        V = cast<CastInst>(V)->getOperand(0);
      else
        return V;
    }
  };
  // A load of field f of the same object (a read-modify-write of a tag).
  auto isFieldLoad = [&](const Value *V, const std::string &S, uint64_t f,
                         const Value *base, uint64_t embed) {
    const auto *LI = dyn_cast<LoadInst>(peel(V));
    if (!LI)
      return false;
    const Pos Q = position(LI->getPointerOperand(), LI->getModule()->getDataLayout());
    return Q.ok && Q.S == S && fieldAt(S, Q.off) == (int64_t)f && Q.base == base &&
           Q.embed == embed;
  };
  // The parameter a scalar is: the argument, or a slot holding only it.
  auto scalarParam = [&](const Value *V) -> const Argument * {
    V = peel(V);
    if (const auto *A = dyn_cast<Argument>(V))
      return A;
    if (const auto *LI = dyn_cast<LoadInst>(V))
      if (const auto *AI = dyn_cast<AllocaInst>(LI->getPointerOperand()->stripPointerCasts())) {
        auto it = scalarStores.find(AI);
        if (it != scalarStores.end() && it->second.size() == 1)
          return dyn_cast<Argument>(it->second[0]->getValueOperand());
      }
    return nullptr;
  };
  // Is a pointer null (1), non-null (0) or either (-1)? A constant null; a
  // nonnull argument, address or allocation; through the callers of a
  // parameter (all must agree).
  std::function<int(const Value *, int)> ptrNullness = [&](const Value *V,
                                                           int depth) -> int {
    V = V->stripPointerCasts();
    if (isa<ConstantPointerNull>(V)) return 1;
    if (isa<GlobalValue>(V) || isa<AllocaInst>(V)) return 0;
    if (const auto *A = dyn_cast<Argument>(V)) {
      if (A->hasNonNullAttr()) return 0;
      const Function *F = A->getParent();
      auto &callers = callersOf[F];
      if (depth <= 0 || F->hasAddressTaken() || callers.empty() ||
          callers.size() > kCallers)
        return -1;
      int r = -2;
      for (const CallBase *CB : callers) {
        if (CB->paramHasAttr(A->getArgNo(), Attribute::NonNull)) {
          if (r == 1) return -1;
          r = 0;
          continue;
        }
        const int c = ptrNullness(CB->getArgOperand(A->getArgNo()),
                                  callers.size() == 1 ? depth : depth - 1);
        if (c < 0 || (r >= 0 && c != r)) return -1;
        r = c;
      }
      return r < 0 ? -1 : r;
    }
    if (const auto *G = dyn_cast<GEPOperator>(V))
      if (G->isInBounds() && depth > 0) return ptrNullness(G->getPointerOperand(), depth - 1) == 0 ? 0 : -1;
    return -1;
  };
  // The tag values a scalar may hold: constants, through selects, phis,
  // casts, masks (`op & 0xff`) and parameters (the constants every direct
  // caller passes). "?" is a value not known.
  std::function<void(const Value *, int, std::set<std::string> &,
                     SmallPtrSetImpl<const Value *> &)>
      scalarValuesIn = [&](const Value *V, int depth, std::set<std::string> &out,
                           SmallPtrSetImpl<const Value *> &seen) {
    V = peel(V);
    if (!seen.insert(V).second)
      return; // a loop: the other incoming values carry the constants
    if (seen.size() > 64) {
      out.insert("?");
      return;
    }
    auto scalarValues = [&](const Value *X, int d, std::set<std::string> &o) {
      scalarValuesIn(X, d, o, seen);
    };
    if (const auto *SE = dyn_cast<SelectInst>(V)) {
      scalarValues(SE->getTrueValue(), depth, out);
      scalarValues(SE->getFalseValue(), depth, out);
      return;
    }
    if (const auto *PN = dyn_cast<PHINode>(V)) {
      if (PN->getNumIncomingValues() > 8) {
        out.insert("?");
        return;
      }
      for (const Value *In : PN->incoming_values()) scalarValues(In, depth, out);
      return;
    }
    const std::string k = constKey(V);
    if (!k.empty()) {
      out.insert(k);
      return;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(V))
      if (BO->getOpcode() == Instruction::And)
        if (const auto *M = dyn_cast<ConstantInt>(BO->getOperand(1))) {
          std::set<std::string> in;
          scalarValues(BO->getOperand(0), depth, in);
          const uint64_t Mk = M->getZExtValue();
          for (auto &v : in) {
            if (v.rfind("int:", 0) == 0) {
              out.insert("int:" + std::to_string(std::stoll(v.substr(4)) & (int64_t)Mk));
            } else if (v.rfind("kb:", 0) == 0) {
              // x & M: bits outside M become known zero; known ones stay
              // only inside M.
              const size_t c = v.find(':', 3);
              const uint64_t Z = std::stoull(v.substr(3, c - 3)), O = std::stoull(v.substr(c + 1));
              out.insert("kb:" + std::to_string(Z | ~Mk) + ":" + std::to_string(O & Mk));
            } else if (v == "?") {
              out.insert("kb:" + std::to_string(~Mk) + ":0");
            } else {
              out.insert(v);
            }
          }
          return;
        }
    // A comparison is 0 or 1; a null test of a pointer whose nullness is
    // known (a constant null, a nonnull argument or address, through the
    // single caller of a per-call-site clone) is exactly one of them.
    if (const auto *IC = dyn_cast<ICmpInst>(V)) {
      int nul = -1; // 1: null, 0: non-null, -1: either
      if (IC->isEquality()) {
        const Value *X = IC->getOperand(0), *Y = IC->getOperand(1);
        if (isa<ConstantPointerNull>(X)) std::swap(X, Y);
        if (isa<ConstantPointerNull>(Y)) nul = ptrNullness(X, 4);
      }
      if (nul >= 0) {
        const bool isNull = nul == 1;
        const bool eq = IC->getPredicate() == ICmpInst::ICMP_EQ;
        out.insert(isNull == eq ? "int:1" : "int:0");
      } else {
        out.insert("int:0");
        out.insert("int:1");
      }
      return;
    }
    if (V->getType()->isIntegerTy(1)) {
      out.insert("int:0");
      out.insert("int:1");
      return;
    }
    if (const Argument *A = scalarParam(V)) {
      const Function *F = A->getParent();
      auto &callers = callersOf[F];
      if (depth > 0 && !F->hasAddressTaken() && !callers.empty() &&
          callers.size() <= kCallers) {
        // A single caller (a per-call-site clone) costs no depth: the
        // chain of clones ends at the call that fixes the value.
        const int d2 = callers.size() == 1 ? depth : depth - 1;
        for (const CallBase *CB : callers)
          scalarValues(CB->getArgOperand(A->getArgNo()), d2, out);
        return;
      }
    }
    const std::string kb = knownBitsKey(V);
    out.insert(kb.empty() ? "?" : kb);
  };
  auto scalarValues = [&](const Value *V, int depth, std::set<std::string> &out) {
    SmallPtrSet<const Value *, 16> seen;
    scalarValuesIn(V, depth, out, seen);
  };
  // A field's value set: field offset -> tag values. Besides constants:
  // "set:C" (`f |= C`), "clr:C" (`f &= ~C`), "?" (a value not known).
  using CoSet = std::map<uint64_t, std::set<std::string>>;
  auto known = [](const std::string &v) {
    return v != "?" && v != "or:?" && v != "and:?" && v.rfind("clr:", 0) != 0 &&
           v.rfind("or0:", 0) != 0 && v.rfind("and1:", 0) != 0 && v.rfind("kb:", 0) != 0 &&
           v.rfind("rel:", 0) != 0;
  };
  struct Site {
    const Instruction *I = nullptr;      // or a global initializer:
    const GlobalVariable *GV = nullptr;
    std::string member;
    bool byLayout = false, shared = false; // member typed by its layout; a field several members share
    const Value *base = nullptr;
    uint64_t embed = 0;
    CoSet co;          // tag candidates written to the same object
    bool viaCall = false;
    std::string addrWhy; // (C') typed by a constant address's debug type
    const LoadInst *copyOf = nullptr; // (C'') a load of the same union field it copies
    std::string embedVia;              // R2: "T>P", typed by the embedding of P in T
  };
  std::map<const UnionField *, std::vector<Site>> writes, reads;
  // Co-writes into the same object: (function, base, embed, struct) ->
  // stores of a constant / function / global / flag bit into a field.
  using ObjKey = std::tuple<const Function *, const Value *, uint64_t, std::string>;
  std::map<ObjKey, CoSet> coWrites;
  // Loads of each (struct, field): where callback fields are read.
  std::map<std::pair<std::string, uint64_t>, std::vector<const LoadInst *>> loadsAt;
  size_t accesses = 0, membersByShape = 0;
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        // A function nothing calls or refers to (an original replaced by
        // its per-call-site clones) writes and reads nothing.
        if (F.use_empty() && F.hasLocalLinkage()) break;
        // A zeroing memset of a struct writes 0 to every field it covers
        // (`memset(&w, 0, sizeof(w))` before a walker sets its callbacks).
        // At -O3 dead-store elimination trims it to the fields not stored
        // afterwards: a constant offset into the stack struct.
        if (const auto *MS = dyn_cast<MemSetInst>(&I)) {
          const auto *Z = dyn_cast<ConstantInt>(MS->getValue());
          const auto *Len = dyn_cast<ConstantInt>(MS->getLength());
          const Value *Dst = MS->getDest()->stripPointerCasts();
          int64_t at = 0;
          bool constOff = true;
          while (const auto *G = dyn_cast<GEPOperator>(Dst)) {
            APInt O(DL.getIndexTypeSizeInBits(G->getType()), 0);
            if (!G->accumulateConstantOffset(DL, O)) { constOff = false; break; }
            at += O.getSExtValue();
            Dst = G->getPointerOperand()->stripPointerCasts();
          }
          const auto *A = dyn_cast<AllocaInst>(Dst);
          // The struct zeroed: a stack slot's type, else (a heap object,
          // `memset(pNew, 0, sizeof(Expr))` after allocation) the debug
          // type of the pointer.
          std::string S;
          const Value *B = A;
          if (A) {
            if (const auto *ST = dyn_cast<StructType>(A->getAllocatedType()))
              if (ST->hasName() && !isAnonStruct(ST)) S = stripSuffix(ST->getName());
          } else {
            const std::string k = valueKey(Dst, 0);
            if (k.rfind("ptr:", 0) == 0 && fieldsOf.count(k.substr(4))) {
              S = k.substr(4);
              B = resolveBase(Dst);
            }
          }
          if (Z && Z->isZero() && Len && !S.empty() && B && constOff && at >= 0) {
            const uint64_t lo = (uint64_t)at, hi = lo + Len->getZExtValue();
            auto fit = fieldsOf.find(S);
            if (fit != fieldsOf.end())
              for (auto &[o, sz] : fit->second)
                if (o >= lo && o + sz <= hi)
                  coWrites[{&F, B, 0, S}][o].insert("int:0");
          }
          continue;
        }
        const Value *P = nullptr;
        if (const auto *LI = dyn_cast<LoadInst>(&I))
          P = LI->getPointerOperand();
        else if (const auto *SI = dyn_cast<StoreInst>(&I))
          P = SI->getPointerOperand();
        else
          continue;
        const Pos Q = position(P, DL);
        if (!Q.ok)
          continue;
        if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          const int64_t lf = fieldAt(Q.S, Q.off);
          if (lf >= 0)
            loadsAt[{Q.S, (uint64_t)lf}].push_back(LI);
        }
        // A constant vector store (-O3 merges `t.flags = C; t.u.iValue = 0`
        // into one): each element is a constant write of the field it
        // starts.
        if (const auto *SI = dyn_cast<StoreInst>(&I))
          if (const auto *CV = dyn_cast<Constant>(SI->getValueOperand()))
            if (auto *VT = dyn_cast<FixedVectorType>(CV->getType()))
              if (VT->getElementType()->isIntegerTy()) {
                const uint64_t esz = DL.getTypeStoreSize(VT->getElementType());
                for (unsigned k = 0; k < VT->getNumElements(); k++) {
                  const auto *E = dyn_cast_or_null<ConstantInt>(CV->getAggregateElement(k));
                  const uint64_t off = Q.off + k * esz;
                  const int64_t fk = fieldAt(Q.S, off);
                  if (fk < 0) continue;
                  auto &vals = coWrites[{&F, Q.base, Q.embed, Q.S}][(uint64_t)fk];
                  vals.insert(E && (uint64_t)fk == off ? "int:" + std::to_string(E->getSExtValue())
                                                       : std::string("?"));
                }
                continue;
              }
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          const int64_t f = fieldAt(Q.S, Q.off);
          // The stored value (`w.xSelectCallback = cond ? 0 : resolveSelectStep`,
          // `p->op = op` with constant callers); a read-modify-write of the
          // field sets (`f |= C`) or clears (`f &= ~C`) flag bits.
          if (f >= 0) {
            auto &vals = coWrites[{&F, Q.base, Q.embed, Q.S}][(uint64_t)f];
            const Value *V = peel(SI->getValueOperand());
            const auto *BO = dyn_cast<BinaryOperator>(V);
            const ConstantInt *C = nullptr;
            const Value *other = nullptr;
            if (BO && (BO->getOpcode() == Instruction::Or ||
                       BO->getOpcode() == Instruction::And)) {
              C = dyn_cast<ConstantInt>(BO->getOperand(1));
              other = BO->getOperand(0);
              if (!C) {
                C = dyn_cast<ConstantInt>(BO->getOperand(0));
                other = BO->getOperand(1);
              }
            }
            if (C && isFieldLoad(other, Q.S, (uint64_t)f, Q.base, Q.embed)) {
              const unsigned bw = C->getType()->getIntegerBitWidth();
              const uint64_t mask = bw >= 64 ? ~0ULL : ((1ULL << bw) - 1);
              if (BO->getOpcode() == Instruction::Or)
                vals.insert("set:" + std::to_string(C->getZExtValue()));
              else
                vals.insert("clr:" + std::to_string(~C->getZExtValue() & mask));
            } else if (BO && !C &&
                       (BO->getOpcode() == Instruction::Or ||
                        BO->getOpcode() == Instruction::And) &&
                       (isFieldLoad(BO->getOperand(0), Q.S, (uint64_t)f, Q.base, Q.embed) ||
                        isFieldLoad(BO->getOperand(1), Q.S, (uint64_t)f, Q.base, Q.embed))) {
              // `f |= x`: may set any bit x may have, clears none; `f &= x`
              // may clear any bit x may lack. Known bits of x bound them.
              const Value *X = isFieldLoad(BO->getOperand(0), Q.S, (uint64_t)f, Q.base, Q.embed)
                                   ? BO->getOperand(1) : BO->getOperand(0);
              const KnownBits K = knownBitsThroughCalls(X, DL);
              const unsigned bw = K.getBitWidth();
              if (BO->getOpcode() == Instruction::Or) {
                const uint64_t Z = bw <= 64 ? K.Zero.getZExtValue() : 0;
                vals.insert(Z ? "or0:" + std::to_string(Z) : std::string("or:?"));
              } else {
                const uint64_t O = bw <= 64 ? K.One.getZExtValue() : 0;
                vals.insert(O ? "and1:" + std::to_string(O) : std::string("and:?"));
              }
            } else if (V->getType()->isIntegerTy() && V->getType()->getIntegerBitWidth() <= 64) {
              // Relative to the field's current value (-O3 keeps the flags
              // in a register: `flags = phi(load, flags & ~A) & ~B`): the bits
              // the write may newly set and newly clear. "rel:S:C" when some
              // leaf is a load of this field of this object.
              bool fromField = false;
              std::function<std::pair<uint64_t, uint64_t>(const Value *, int)> rel =
                  [&](const Value *X, int d) -> std::pair<uint64_t, uint64_t> {
                X = peel(X);
                if (isFieldLoad(X, Q.S, (uint64_t)f, Q.base, Q.embed)) {
                  fromField = true;
                  return {0, 0};
                }
                auto absolute = [&]() -> std::pair<uint64_t, uint64_t> {
                  const KnownBits K = knownBitsThroughCalls(X, DL);
                  if (K.getBitWidth() > 64) return {~0ULL, ~0ULL};
                  return {~K.Zero.getZExtValue(), ~K.One.getZExtValue()};
                };
                if (d == 0) return absolute();
                if (const auto *PN = dyn_cast<PHINode>(X)) {
                  if (PN->getNumIncomingValues() > 8) return absolute();
                  std::pair<uint64_t, uint64_t> r{0, 0};
                  for (const Value *In : PN->incoming_values()) {
                    if (In == PN) continue;
                    auto [s, c] = rel(In, d - 1);
                    r.first |= s;
                    r.second |= c;
                  }
                  return r;
                }
                if (const auto *SE = dyn_cast<SelectInst>(X)) {
                  auto a = rel(SE->getTrueValue(), d - 1), b = rel(SE->getFalseValue(), d - 1);
                  return {a.first | b.first, a.second | b.second};
                }
                if (const auto *B = dyn_cast<BinaryOperator>(X)) {
                  const Value *A0 = B->getOperand(0), *A1 = B->getOperand(1);
                  auto kz = [&](const Value *Y) { return knownBitsThroughCalls(Y, DL).Zero.getZExtValue(); };
                  auto ko = [&](const Value *Y) { return knownBitsThroughCalls(Y, DL).One.getZExtValue(); };
                  if (B->getOpcode() == Instruction::And) {
                    // and only clears: new ones come from the field side.
                    auto [s, c] = rel(A0, d - 1);
                    return {s & ~kz(A1), c | ~ko(A1)};
                  }
                  if (B->getOpcode() == Instruction::Or) {
                    auto [s, c] = rel(A0, d - 1);
                    return {s | ~kz(A1), c};
                  }
                  if (B->getOpcode() == Instruction::Xor) {
                    auto [s, c] = rel(A0, d - 1);
                    const uint64_t t = ~kz(A1);
                    return {s | t, c | t};
                  }
                }
                return absolute();
              };
              const auto [maySet, mayClear] = rel(V, 6);
              if (fromField)
                vals.insert("rel:" + std::to_string(maySet) + ":" + std::to_string(mayClear));
              else
                scalarValues(V, 2, vals);
            } else {
              const std::string k = constKey(V);
              if (!k.empty())
                vals.insert(k);
              else {
                // Pointers: constants through selects and phis.
                SmallVector<const Value *, 4> work{V};
                SmallPtrSet<const Value *, 8> seen;
                while (!work.empty()) {
                  const Value *X = work.pop_back_val()->stripPointerCasts();
                  if (!seen.insert(X).second) continue;
                  if (seen.size() > 8) { vals.insert("?"); break; }
                  if (const auto *SE = dyn_cast<SelectInst>(X)) {
                    work.push_back(SE->getTrueValue());
                    work.push_back(SE->getFalseValue());
                  } else if (const auto *PN = dyn_cast<PHINode>(X)) {
                    for (const Value *In : PN->incoming_values()) work.push_back(In);
                  } else {
                    const std::string xk = constKey(X);
                    vals.insert(xk.empty() ? "?" : xk);
                  }
                }
              }
            }
          }
        }
        UnionField *U = unionAt(Q);
        if (!U)
          continue;
        accesses++;
        Site s;
        s.I = &I;
        s.base = Q.base;
        s.embed = Q.embed;
        const int64_t rel = (int64_t)Q.off - (int64_t)U->off;
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          std::string why;
          const std::string am = addrMember(*U, SI->getValueOperand(), rel, why);
          if (!am.empty()) {
            s.member = am;
            s.addrWhy = why;
          } else {
            s.member = memberOf(*U, valueKey(SI->getValueOperand(), 0), rel, &s.byLayout, &s.shared, &s.embedVia);
            if (!s.embedVia.empty()) r2Pairs[s.embedVia].first++;
          }
          // (C'') A copy of the same union field from another object.
          auto sameField = [&](const LoadInst *L) {
            const Pos LQ = position(L->getPointerOperand(), DL);
            return unionAt(LQ) == U && (int64_t)LQ.off - (int64_t)U->off == rel &&
                   L->getType() == SI->getValueOperand()->getType();
          };
          if (SI->getValueOperand()->getType()->isPointerTy())
            if (const LoadInst *L = copiedLoad(SI); L && sameField(L)) s.copyOf = L;
          // The -O3 shapes left as ordinary stores (counted): a vector copy
          // of several fields, a phi of loads of the field.
          if (!s.copyOf) {
            const Value *SV = SI->getValueOperand()->stripPointerCasts();
            if (const auto *VL = dyn_cast<LoadInst>(SV); VL && SV->getType()->isVectorTy()) {
              const Pos LQ = position(VL->getPointerOperand(), DL);
              if (unionAt(LQ) == U) unionCopyVector++;
            } else if (const auto *PN = dyn_cast<PHINode>(SV)) {
              bool all = PN->getNumIncomingValues() > 0;
              for (const Value *In : PN->incoming_values()) {
                const auto *IL = dyn_cast<LoadInst>(In->stripPointerCasts());
                all &= IL && sameField(IL);
              }
              if (all) unionCopyPhi++;
            }
          }
        } else
        {
          const std::string rk = readKey(cast<LoadInst>(&I));
          s.member = memberOf(*U, rk, rel, &s.byLayout, &s.shared, &s.embedVia);
          if (rk != "?" && readKey(cast<LoadInst>(&I), false) == "?") r1Reads++; // typed through a no-op cast (R1)
          if (!s.embedVia.empty()) r2Pairs[s.embedVia].second++;
        }
        if (!s.shared && (s.member == "?" || s.member == "ambiguous")) {
          // Typed-pointer IR (upgraded): an access of the storage type is a
          // GEP into the union struct; any other member keeps a no-op
          // bitcast of the union's address. Narrow by that, then by the
          // access's kind (pointer or integer).
          const Value *Ptr = getLoadStorePointerOperand(&I);
          int shape = 0; // 1: storage type, -1: another type
          if (const auto *BC = dyn_cast<BitCastOperator>(Ptr)) {
            if (BC->getSrcTy() == BC->getDestTy()) shape = -1;
          } else if (const auto *G = dyn_cast<GEPOperator>(Ptr)) {
            StructType *last = nullptr;
            for (auto GTI = gep_type_begin(G), E = gep_type_end(G); GTI != E; ++GTI)
              last = GTI.getStructTypeOrNull();
            if (last && last->hasName() && last->getName().starts_with("union."))
              shape = 1;
          }
          if (shape != 0) {
            const Type *AT = getLoadStoreType(const_cast<Instruction *>(&I));
            std::vector<std::string> cand;
            for (auto &[nm, tk] : U->members) {
              const bool inStorage = U->storageMembers.count(nm) != 0;
              if ((shape == 1) != inStorage) continue;
              const bool ptrMember = tk.rfind("ptr:", 0) == 0 || tk == "fnptr";
              if (AT->isPointerTy() != ptrMember) continue;
              cand.push_back(nm);
            }
            if (cand.size() == 1) {
              s.member = cand[0];
              membersByShape++;
            }
          }
        }
        if (isa<StoreInst>(&I)) {
          unionWriteMember[&I] = s.member;
          writes[U].push_back(s);
        } else {
          reads[U].push_back(s);
        }
      }
  }

  // Global initializers are writes: every leaf constant at its byte
  // offset, placed in the struct (and embedded struct) holding it.
  std::function<void(const Constant *, uint64_t, const DataLayout &,
                     std::vector<std::pair<uint64_t, const Constant *>> &)>
      flatten = [&](const Constant *C, uint64_t off, const DataLayout &DL,
                    std::vector<std::pair<uint64_t, const Constant *>> &out) {
        if (const auto *CS = dyn_cast<ConstantStruct>(C)) {
          const StructLayout *SL = DL.getStructLayout(CS->getType());
          for (unsigned i = 0; i < CS->getNumOperands(); i++)
            flatten(CS->getOperand(i), off + SL->getElementOffset(i), DL, out);
        } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
          const uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
          for (unsigned i = 0; i < CA->getNumOperands(); i++)
            flatten(CA->getOperand(i), off + i * es, DL, out);
        } else if ((!isa<ConstantAggregate>(C) && !isa<ConstantData>(C)) ||
                   isa<ConstantInt>(C) || isa<ConstantPointerNull>(C)) {
          out.emplace_back(off, C);
        }
      };
  // The functions a global's initializer holds: an ops table.
  std::map<std::string, std::set<std::string>> fnsInGV;
  size_t initWrites = 0;
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (GlobalVariable &GV : M->globals()) {
      if (!GV.hasInitializer())
        continue;
      std::vector<std::pair<uint64_t, const Constant *>> leaves;
      flatten(GV.getInitializer(), 0, DL, leaves);
      for (auto &[o, C] : leaves)
        if (const auto *Fn = dyn_cast<Function>(C->stripPointerCasts()))
          fnsInGV[GV.getName().str()].insert(Fn->getName().str());
      SmallVector<DIGlobalVariableExpression *, 1> GVEs;
      GV.getDebugInfo(GVEs);
      if (GVEs.empty())
        continue;
      const DIType *T = stripDI(GVEs[0]->getVariable()->getType());
      uint64_t es = 0, n = 1;
      if (const auto *AT = dyn_cast_or_null<DICompositeType>(T))
        if (AT->getTag() == dwarf::DW_TAG_array_type) {
          T = stripDI(AT->getBaseType());
          es = T ? T->getSizeInBits() / 8 : 0;
          if (!es)
            continue;
          n = DL.getTypeAllocSize(GV.getValueType()) / es;
        }
      const auto *ST = dyn_cast_or_null<DICompositeType>(T);
      if (!ST || ST->getTag() != dwarf::DW_TAG_structure_type || ST->getName().empty())
        continue;
      // Per element: (embed, struct) -> co-writes, and its union leaves.
      for (uint64_t k = 0; k < n; k++) {
        std::map<std::pair<uint64_t, std::string>, CoSet> co;
        std::vector<std::tuple<UnionField *, Pos, const Constant *>> ul;
        for (auto &[o, C] : leaves) {
          if (es && (o < k * es || o >= (k + 1) * es))
            continue;
          Pos Q;
          Q.S = ST->getName().str();
          Q.off = es ? o - k * es : o;
          Q.ok = true;
          descend(Q);
          if (UnionField *U = unionAt(Q)) {
            if (!C->isNullValue())
              ul.emplace_back(U, Q, C);
            continue;
          }
          const int64_t f = fieldAt(Q.S, Q.off);
          const std::string vk = constKey(C);
          if (f >= 0 && !vk.empty())
            co[{Q.embed, Q.S}][(uint64_t)f].insert(vk);
        }
        for (auto &[U, Q, C] : ul) {
          Site s;
          s.GV = &GV;
          s.member = memberOf(*U, valueKey(C, 0), (int64_t)Q.off - (int64_t)U->off, &s.byLayout, &s.shared);
          s.embed = Q.embed;
          s.co = co[{Q.embed, Q.S}];
          writes[U].push_back(s);
          initWrites++;
          accesses++;
        }
      }
    }
  }

  // ---- 3. The object one or two calls away ----
  // Which parameter a base is: the argument, or a slot holding only it.
  auto paramIndex = [&](const Function *F, const Value *B) -> int {
    if (const auto *A = dyn_cast<Argument>(B))
      return A->getParent() == F ? (int)A->getArgNo() : -1;
    const auto *AI = dyn_cast<AllocaInst>(B);
    if (!AI || !AI->getAllocatedType()->isPointerTy())
      return -1;
    auto it = slotStores.find(AI);
    if (it == slotStores.end() || it->second.size() != 1)
      return -1;
    if (const auto *A = dyn_cast<Argument>(it->second[0]->getValueOperand()))
      return (int)A->getArgNo();
    return -1;
  };
  // A callee's name for its parameter j: the slot holding it, if any.
  auto paramBase = [&](const Function *G, unsigned j) -> const Value * {
    const Argument *A = G->getArg(j);
    for (const User *U : A->users())
      if (const auto *SI = dyn_cast<StoreInst>(U))
        if (SI->getValueOperand() == A)
          if (const auto *AI = dyn_cast<AllocaInst>(SI->getPointerOperand()->stripPointerCasts()))
            if (AI->getAllocatedType()->isPointerTy() && slotStores[AI].size() == 1)
              return AI;
    return A;
  };
  // The callees whose results a base holds (every definition of it).
  auto resultOf = [&](const Value *B) -> std::vector<const Function *> {
    std::vector<const Value *> defs;
    if (const auto *AI = dyn_cast<AllocaInst>(B)) {
      if (!AI->getAllocatedType()->isPointerTy())
        return {}; // a struct on the stack: the object itself
      auto it = slotStores.find(AI);
      if (it == slotStores.end())
        return {};
      for (const StoreInst *SI : it->second)
        defs.push_back(SI->getValueOperand()->stripPointerCasts());
    } else
      defs.push_back(B);
    std::vector<const Function *> out;
    for (const Value *D : defs) {
      const auto *CB = dyn_cast<CallBase>(D);
      Function *T = CB ? CB->getCalledFunction() : nullptr;
      if (!T)
        return {};
      const Function *G = getFuncDef(T);
      if (G->isDeclaration())
        return {};
      out.push_back(G);
    }
    return out;
  };
  auto merge = [](CoSet &into, const CoSet &from) {
    for (auto &[f, vs] : from) into[f].insert(vs.begin(), vs.end());
  };
  // Fields present in every set (values joined).
  auto meetAll = [](const std::vector<CoSet> &sets) {
    CoSet out;
    if (sets.empty())
      return out;
    out = sets[0];
    for (size_t i = 1; i < sets.size(); i++) {
      CoSet keep;
      for (auto &[f, vs] : out) {
        auto it = sets[i].find(f);
        if (it == sets[i].end()) continue;
        keep[f] = vs;
        keep[f].insert(it->second.begin(), it->second.end());
      }
      out.swap(keep);
    }
    return out;
  };
  std::map<std::tuple<ObjKey, int>, CoSet> coMemo;
  // The tag candidates written to an object: here, by a callee given it,
  // by the callee(s) that returned it, or by every direct caller passing it.
  std::function<CoSet(const Function *, const Value *, uint64_t, const std::string &, int)>
      coFor = [&](const Function *F, const Value *B, uint64_t embed,
                  const std::string &S, int depth) -> CoSet {
    const ObjKey key{F, B, embed, S};
    auto mit = coMemo.find({key, depth});
    if (mit != coMemo.end())
      return mit->second;
    coMemo[{key, depth}] = {}; // recursion guard
    CoSet R;
    auto cit = coWrites.find(key);
    if (cit != coWrites.end())
      R = cit->second;
    if (depth > 0) {
      for (auto &[CB, G] : callsIn[F])
        for (unsigned j = 0; j < CB->arg_size() && j < G->arg_size(); j++)
          if (resolveBase(CB->getArgOperand(j)) == B)
            merge(R, coFor(G, paramBase(G, j), embed, S, depth - 1));
      std::vector<CoSet> res;
      for (const Function *G : resultOf(B)) {
        CoSet one;
        for (const Instruction &I : instructions(*G))
          if (const auto *RI = dyn_cast<ReturnInst>(&I))
            if (const Value *RV = RI->getReturnValue())
              merge(one, coFor(G, resolveBase(RV), embed, S, depth - 1));
        res.push_back(std::move(one));
      }
      merge(R, meetAll(res));
      const int pi = paramIndex(F, B);
      auto &callers = callersOf[F];
      if (pi >= 0 && !F->hasAddressTaken() && !callers.empty() &&
          callers.size() <= kCallers) {
        std::vector<CoSet> cs;
        for (const CallBase *CB : callers)
          cs.push_back(coFor(CB->getFunction(), resolveBase(CB->getArgOperand(pi)),
                             embed, S, depth - 1));
        merge(R, meetAll(cs));
      }
    }
    coMemo[{key, depth}] = R;
    return R;
  };
  // The contexts coFor visits from a write: where its tag may be written.
  std::function<void(const Function *, const Value *, uint64_t, const std::string &, int,
                     std::set<ObjKey> &)>
      ctxKeys = [&](const Function *F, const Value *B, uint64_t embed, const std::string &S,
                    int depth, std::set<ObjKey> &out) {
    if (!out.insert(ObjKey{F, B, embed, S}).second || depth == 0)
      return;
    for (auto &[CB, G] : callsIn[F])
      for (unsigned j = 0; j < CB->arg_size() && j < G->arg_size(); j++)
        if (resolveBase(CB->getArgOperand(j)) == B)
          ctxKeys(G, paramBase(G, j), embed, S, depth - 1, out);
    for (const Function *G : resultOf(B))
      for (const Instruction &I : instructions(*G))
        if (const auto *RI = dyn_cast<ReturnInst>(&I))
          if (const Value *RV = RI->getReturnValue())
            ctxKeys(G, resolveBase(RV), embed, S, depth - 1, out);
    const int pi = paramIndex(F, B);
    auto &callers = callersOf[F];
    if (pi >= 0 && !F->hasAddressTaken() && !callers.empty() && callers.size() <= kCallers)
      for (const CallBase *CB : callers)
        ctxKeys(CB->getFunction(), resolveBase(CB->getArgOperand(pi)), embed, S, depth - 1,
                out);
  };
  // Every context (function, object) that writes a field of struct S.
  std::map<std::pair<std::string, uint64_t>, std::vector<ObjKey>> writersOf;
  for (auto &[K, co] : coWrites)
    for (auto &[f, vs] : co)
      writersOf[{std::get<3>(K), f}].push_back(K);
  std::map<const UnionField *, std::set<ObjKey>> unionCtx;
  for (auto &[U, W] : writes)
    for (Site &s : W)
      if (s.I) {
        ctxKeys(s.I->getFunction(), s.base, s.embed, U->structName, 2, unionCtx[U]);
        const ObjKey key{s.I->getFunction(), s.base, s.embed, U->structName};
        auto cit = coWrites.find(key);
        const size_t here = cit == coWrites.end() ? 0 : cit->second.size();
        s.co = coFor(s.I->getFunction(), s.base, s.embed, U->structName, 2);
        s.viaCall = s.co.size() > here;
      }

  // ---- 4. Per union: candidate discriminators, write and read sides ----
  // --cfl-census-unions-detail=Struct.field (or Struct.): explain one union.
  auto detailed = [&](const UnionField *U) {
    const std::string &d = CFLCensusUnionsDetail;
    if (d.empty())
      return false;
    const std::string name = U->structName + "." + U->fieldName;
    return d == name || (d.back() == '.' && name.rfind(d, 0) == 0);
  };
  const UnionField *detailU = nullptr; // the union keyRead explains
  auto locOf = [](const Instruction *I) {
    std::string l = I->getFunction()->getName().str();
    if (const DILocation *D = I->getDebugLoc())
      l += " " + D->getFilename().str() + ":" + std::to_string(D->getLine());
    return l;
  };
  std::map<const Function *, std::unique_ptr<DominatorTree>> domOf;
  auto domTree = [&](const Function *F) -> DominatorTree & {
    auto &D = domOf[F];
    if (!D)
      D = std::make_unique<DominatorTree>(const_cast<Function &>(*F));
    return *D;
  };
  // ---- Facts a read's dominating branches establish on its object ----
  // `f == C` / `f != C` (comparisons, switch cases, null tests), some bit
  // of M set / every bit of M clear (`(f & M) != 0`).
  // ULT c: the value is below c (unsigned); UGE c: at least c (plan 3.30
  // P3: `icmp ult eU, 2` is `eU == 0 || eU == 1`).
  // FN c: a callback field holds function fnIds[c] (dispatch is the check:
  // inside a callback reached only by `p->f(p, ...)`, p->f is that callback).
  enum class FK { EQ, NE, BSET, BCLR, ULT, UGE, FN };
  std::vector<std::string> fnIds;
  std::map<std::string, uint64_t> fnIdOf;
  auto fnId = [&](const std::string &n) {
    auto [it, ins] = fnIdOf.try_emplace(n, fnIds.size());
    if (ins) fnIds.push_back(n);
    return it->second;
  };
  struct Fact {
    uint64_t f; FK k; uint64_t c;
    // Where the test's true path starts (the first instruction of the
    // edge's successor), and whether the fact still holds at the read the
    // search started from (plan 3.30 P2: path stability).
    const Instruction *from = nullptr;
    bool usable = false;
  };
  // The field f a value loads from the same object, and the bit shift of
  // the loaded piece inside f.
  auto fieldLoad = [&](const Value *V, const std::string &S, const Value *base,
                       uint64_t embed, uint64_t &f, unsigned &shift) {
    const auto *LI = dyn_cast<LoadInst>(peel(V));
    if (!LI)
      return false;
    const Pos Q = position(LI->getPointerOperand(), LI->getModule()->getDataLayout());
    if (!Q.ok || Q.S != S || Q.base != base || Q.embed != embed)
      return false;
    const int64_t fs = fieldAt(S, Q.off);
    if (fs < 0)
      return false;
    f = (uint64_t)fs;
    shift = (unsigned)(Q.off - f) * 8;
    return true;
  };
  std::function<void(const Value *, bool, const std::string &, const Value *, uint64_t,
                     std::vector<Fact> &)>
      condFacts = [&](const Value *C, bool truth, const std::string &S, const Value *base,
                      uint64_t embed, std::vector<Fact> &out) {
    C = peel(C);
    if (const auto *BO = dyn_cast<BinaryOperator>(C)) {
      if (BO->getType()->isIntegerTy(1) &&
          ((BO->getOpcode() == Instruction::And && truth) ||
           (BO->getOpcode() == Instruction::Or && !truth))) {
        condFacts(BO->getOperand(0), truth, S, base, embed, out);
        condFacts(BO->getOperand(1), truth, S, base, embed, out);
      }
      return;
    }
    const auto *IC = dyn_cast<ICmpInst>(C);
    if (!IC)
      return;
    if (IC->isUnsigned() && IC->isRelational()) {
      // X <u c, X <=u c, X >u c, X >=u c (constant on either side).
      ICmpInst::Predicate P = IC->getPredicate();
      const Value *X = IC->getOperand(0);
      const auto *CI = dyn_cast<ConstantInt>(IC->getOperand(1));
      if (!CI) {
        CI = dyn_cast<ConstantInt>(IC->getOperand(0));
        X = IC->getOperand(1);
        P = ICmpInst::getSwappedPredicate(P);
      }
      if (!CI || CI->getBitWidth() > 64) return;
      if (!truth) P = ICmpInst::getInversePredicate(P);
      uint64_t c = CI->getZExtValue();
      FK k;
      switch (P) {
      case ICmpInst::ICMP_ULT: k = FK::ULT; break;
      case ICmpInst::ICMP_ULE: if (c == ~0ULL) return; k = FK::ULT; c += 1; break;
      case ICmpInst::ICMP_UGE: k = FK::UGE; break;
      case ICmpInst::ICMP_UGT: if (c == ~0ULL) return; k = FK::UGE; c += 1; break;
      default: return;
      }
      uint64_t f;
      unsigned sh;
      if (fieldLoad(peel(X), S, base, embed, f, sh) && sh == 0)
        out.push_back({f, k, c});
      return;
    }
    if (!IC->isEquality())
      return;
    const Value *X = IC->getOperand(0), *Y = IC->getOperand(1);
    if (isa<Constant>(X))
      std::swap(X, Y);
    uint64_t cy;
    if (const auto *CI = dyn_cast<ConstantInt>(Y))
      cy = CI->getZExtValue();
    else if (isa<ConstantPointerNull>(Y))
      cy = 0;
    else
      return;
    const bool eq = (IC->getPredicate() == ICmpInst::ICMP_EQ) == truth;
    uint64_t f;
    unsigned sh;
    X = peel(X);
    if (const auto *A = dyn_cast<BinaryOperator>(X))
      if (A->getOpcode() == Instruction::And && cy == 0)
        if (const auto *M = dyn_cast<ConstantInt>(A->getOperand(1)))
          if (fieldLoad(A->getOperand(0), S, base, embed, f, sh)) {
            out.push_back({f, eq ? FK::BCLR : FK::BSET, M->getZExtValue() << sh});
            return;
          }
    if (fieldLoad(X, S, base, embed, f, sh) && sh == 0)
      out.push_back({f, eq ? FK::EQ : FK::NE, cy});
  };
  auto factsHere = [&](const Instruction *I, const std::string &S, const Value *base,
                       uint64_t embed) {
    std::vector<Fact> out;
    DominatorTree &DT = domTree(I->getFunction());
    const BasicBlock *BB = I->getParent();
    const auto *N0 = DT.getNode(BB);
    if (!N0)
      return out;
    for (auto *N = N0->getIDom(); N; N = N->getIDom()) {
      const BasicBlock *NB = N->getBlock();
      const Instruction *T = NB->getTerminator();
      if (const auto *BI = dyn_cast<BranchInst>(T)) {
        if (!BI->isConditional() || BI->getSuccessor(0) == BI->getSuccessor(1))
          continue;
        for (unsigned k = 0; k < 2; k++)
          if (DT.dominates(BasicBlockEdge(NB, BI->getSuccessor(k)), BB)) {
            const size_t n0 = out.size();
            condFacts(BI->getCondition(), k == 0, S, base, embed, out);
            for (size_t i = n0; i < out.size(); i++)
              out[i].from = &*BI->getSuccessor(k)->begin();
          }
      } else if (const auto *SW = dyn_cast<SwitchInst>(T)) {
        uint64_t f;
        unsigned sh;
        if (!fieldLoad(SW->getCondition(), S, base, embed, f, sh) || sh != 0)
          continue;
        for (auto &Case : SW->cases()) {
          const BasicBlock *Succ = Case.getCaseSuccessor();
          if (Succ == SW->getDefaultDest())
            continue;
          if (DT.dominates(BasicBlockEdge(NB, Succ), BB)) {
            out.push_back({f, FK::EQ, Case.getCaseValue()->getZExtValue()});
            out.back().from = &*Succ->begin();
          }
        }
      }
    }
    return out;
  };
  // Does a write's tag knowledge satisfy, violate, or leave open a fact?
  enum class Res { SAT, VIOL, UNK };
  auto evalFact = [&](const CoSet &co, const Fact &g) -> Res {
    auto it = co.find(g.f);
    if (it == co.end())
      return Res::UNK;
    bool unk = false, nz = false;
    std::vector<uint64_t> exact;
    std::vector<std::pair<uint64_t, uint64_t>> kbs; // known zero, known one
    // Bits an unknown `|=` may set / an unknown `&=` may clear.
    uint64_t sets = 0, clrs = 0, orMay = 0, andMay = 0;
    for (auto &v : it->second) {
      if (v == "?") unk = true;
      else if (v == "or:?") orMay = ~0ULL;
      else if (v == "and:?") andMay = ~0ULL;
      else if (v.rfind("or0:", 0) == 0) orMay |= ~std::stoull(v.substr(4));
      else if (v.rfind("and1:", 0) == 0) andMay |= ~std::stoull(v.substr(5));
      else if (v.rfind("rel:", 0) == 0) {
        const size_t c = v.find(':', 4);
        orMay |= std::stoull(v.substr(4, c - 4));
        andMay |= std::stoull(v.substr(c + 1));
      }
      else if (v.rfind("kb:", 0) == 0) {
        const size_t c = v.find(':', 3);
        kbs.push_back({std::stoull(v.substr(3, c - 3)), std::stoull(v.substr(c + 1))});
      }
      else if (v == "null") exact.push_back(0);
      else if (v.rfind("int:", 0) == 0) exact.push_back((uint64_t)std::stoll(v.substr(4)));
      else if (v.rfind("set:", 0) == 0) sets |= std::stoull(v.substr(4));
      else if (v.rfind("clr:", 0) == 0) clrs |= std::stoull(v.substr(4));
      else nz = true; // a function or global: some non-null pointer
    }
    auto all = [](const std::vector<Res> &rs) {
      if (rs.empty()) return Res::UNK;
      for (Res r : rs) if (r != rs[0]) return Res::UNK;
      return rs[0];
    };
    auto inv = [](Res r) { return r == Res::SAT ? Res::VIOL : r == Res::VIOL ? Res::SAT : Res::UNK; };
    auto eqRes = [&](uint64_t c) {
      if (unk || sets || clrs || orMay || andMay) return Res::UNK;
      std::vector<Res> rs;
      for (uint64_t n : exact) rs.push_back(n == c ? Res::SAT : Res::VIOL);
      for (auto [Z, O] : kbs) rs.push_back((c & Z) || (~c & O) ? Res::VIOL : Res::UNK);
      if (nz) rs.push_back(c == 0 ? Res::VIOL : Res::UNK);
      return all(rs);
    };
    // Set bits are taken as the field's final state (the census does not
    // order the writes of one function).
    // An unknown `|=` can only add bits (never undoes SAT); an unknown
    // `&=` can only remove them (never undoes VIOL).
    auto bsetRes = [&](uint64_t m) {
      if ((sets & m) && !(clrs & m) && !(andMay & m)) return Res::SAT;
      if (unk || nz) return Res::UNK;
      Res r = Res::UNK;
      if (!exact.empty() || !kbs.empty()) {
        std::vector<Res> rs;
        for (uint64_t n : exact) rs.push_back((n & m) ? Res::SAT : Res::VIOL);
        for (auto [Z, O] : kbs)
          rs.push_back((O & m) ? Res::SAT : (m & ~Z) == 0 ? Res::VIOL : Res::UNK);
        r = all(rs);
        if (r == Res::VIOL && ((sets & m) || (orMay & m))) return Res::UNK;
        if (r == Res::SAT && ((clrs & m) || (andMay & m))) return Res::UNK;
        return r;
      }
      if ((clrs & m) == m && !(sets & m) && !(orMay & m)) return Res::VIOL;
      return r;
    };
    auto ultRes = [&](uint64_t c) {
      if (unk || nz || sets || clrs || orMay || andMay) return Res::UNK;
      std::vector<Res> rs;
      for (uint64_t n : exact) rs.push_back(n < c ? Res::SAT : Res::VIOL);
      for (auto [Z, O] : kbs)
        // At least the known ones; at most everything not known zero.
        rs.push_back(O >= c ? Res::VIOL : (~Z) < c ? Res::SAT : Res::UNK);
      return all(rs);
    };
    auto fnRes = [&]() {
      // The field holds fnIds[g.c]: another function or null violates it.
      std::vector<Res> rs;
      for (auto &v : it->second) {
        if (v.rfind("fn:", 0) == 0) rs.push_back(v.substr(3) == fnIds[g.c] ? Res::SAT : Res::VIOL);
        else if (v == "null" || v == "int:0") rs.push_back(Res::VIOL);
        else rs.push_back(Res::UNK);
      }
      return all(rs);
    };
    switch (g.k) {
    case FK::EQ: return eqRes(g.c);
    case FK::NE: return inv(eqRes(g.c));
    case FK::BSET: return bsetRes(g.c);
    case FK::BCLR: return inv(bsetRes(g.c));
    case FK::ULT: return ultRes(g.c);
    case FK::UGE: return inv(ultRes(g.c));
    case FK::FN: return fnRes();
    }
    return Res::UNK;
  };
  // A read keyed by facts: VER when every write of another member (and
  // every untyped write) violates some fact while a write of its own
  // member does not; CONTRA when the facts rule out every write of its
  // own member yet admit another's.
  enum class RV { VER, CONTRA, UNK };
  // Only a STABLE field may exclude a write: one written nowhere but in
  // the contexts of union writes, so its value was set with the member
  // (JsonNode.eU). A field other code also writes (Expr.flags, set and
  // cleared all over) may have changed since the write.
  // Per bit: a bit fact stays usable when every write elsewhere sets or
  // clears only other bits (trace_event_call.flags: TRACEPOINT is fixed
  // at definition, other bits change at run time).
  std::set<uint64_t> stable;
  const UnionField *stableU = nullptr;
  std::map<uint64_t, std::set<std::string>> outsideVals; // f -> values written elsewhere
  std::set<uint64_t> outsideDone;
  auto factStable = [&](const Fact &g) {
    if (stable.count(g.f))
      return true;
    if (!outsideDone.count(g.f)) {
      outsideDone.insert(g.f);
      auto wit = writersOf.find({stableU->structName, g.f});
      if (wit != writersOf.end())
        for (const ObjKey &K : wit->second)
          if (!unionCtx[stableU].count(K)) {
            auto &vs = coWrites[K][g.f];
            outsideVals[g.f].insert(vs.begin(), vs.end());
          }
    }
    if (g.k != FK::BSET && g.k != FK::BCLR)
      return false;
    for (const std::string &v : outsideVals[g.f]) {
      if (v.rfind("set:", 0) != 0 && v.rfind("clr:", 0) != 0)
        return false;
      if (std::stoull(v.substr(4)) & g.c)
        return false;
    }
    return true;
  };
  // (A) write -> check (plan 3.31): the tag value written with the union
  // still holds at the test when no write outside the union's write
  // contexts can make the fact TRUE. Outside writes that make it false, or
  // touch only other bits, are harmless (the fact then fails until a union
  // write sets the tag again). Generalizes factStable; bulk copies and
  // zeroing are taken to carry tag and content together (ASSUMPTION).
  // Outside writes that broke a fact: (struct, field, fact) -> value -> functions.
  std::map<std::string, std::map<std::string, std::set<std::string>>> breakers;
  auto factPreserved = [&](const Fact &g) {
    if (factStable(g))
      return true;
    auto harmless = [&](const std::string &v) {
      CoSet one;
      one[g.f] = {v};
      if (evalFact(one, g) == Res::VIOL) return true;
      if (g.k != FK::BSET && g.k != FK::BCLR) return false;
      // Read-modify-writes that leave the tested bits as they were.
      if (v.rfind("set:", 0) == 0 || v.rfind("clr:", 0) == 0)
        return !(std::stoull(v.substr(4)) & g.c);
      if (v.rfind("or0:", 0) == 0) return (~std::stoull(v.substr(4)) & g.c) == 0;
      if (v.rfind("and1:", 0) == 0) return (~std::stoull(v.substr(5)) & g.c) == 0;
      if (v.rfind("rel:", 0) == 0) {
        // Can it make the fact true? bits-set m: only by newly setting a bit
        // of m; bits-clear m: only by newly clearing one.
        const size_t c = v.find(':', 4);
        const uint64_t s = std::stoull(v.substr(4, c - 4)), k = std::stoull(v.substr(c + 1));
        return g.k == FK::BSET ? (s & g.c) == 0 : (k & g.c) == 0;
      }
      return false;
    };
    bool ok = true;
    for (const std::string &v : outsideVals[g.f])
      if (!harmless(v)) { ok = false; break; }
    if (!ok) {
      const char *kn[] = {"==", "!=", "bits-set", "bits-clear", "<u", ">=u", "== fn#"};
      const std::string key = stableU->structName + "@" + std::to_string(g.f) + " " +
                              kn[(int)g.k] + " " + std::to_string(g.c);
      auto &B = breakers[key];
      if (B.empty()) {
        auto wit = writersOf.find({stableU->structName, g.f});
        if (wit != writersOf.end())
          for (const ObjKey &K : wit->second)
            if (!unionCtx[stableU].count(K))
              for (const std::string &v : coWrites[K][g.f])
                if (!harmless(v) && B[v].size() < 4)
                  B[v].insert(std::get<0>(K)->getName().str());
      }
    }
    return ok;
  };
  auto pointerless = [&](const Site &w) {
    const auto *SI = dyn_cast_or_null<StoreInst>(w.I);
    if (!SI) return false;
    const Value *SV = SI->getValueOperand();
    if (isa<ConstantInt>(SV) || isa<ConstantPointerNull>(SV) || isa<UndefValue>(SV))
      return true; // a constant (zeroing the union) carries no pointer
    Type *T = SV->getType();
    if (T->isFloatingPointTy()) return true;
    const DataLayout &DLw = SI->getModule()->getDataLayout();
    return T->isIntegerTy() && T->getIntegerBitWidth() < DLw.getPointerSizeInBits();
  };
  auto judge = [&](const std::vector<Fact> &facts, const std::string &member,
                   const std::vector<Site> &W) {
    auto excluded = [&](const Site &w) {
      for (const Fact &g : facts)
        if (factStable(g) && evalFact(w.co, g) == Res::VIOL) return true;
      return false;
    };
    std::set<std::string> admitted; // members with a write the facts admit
    bool untypedAdmitted = false;
    bool ownWrite = false;
    for (const Site &w : W) {
      const bool typed = w.member != "?" && w.member != "ambiguous";
      if (typed && w.member == member) ownWrite = true;
      if (excluded(w)) continue;
      // Tag keys key pointer content: a write that cannot hold a pointer
      // (a narrow integer, a float) feeds no pointer read.
      if (CFLUnionKeys == "tag" && pointerless(w)) continue;
      if (typed) admitted.insert(w.member);
      else untypedAdmitted = true;
    }
    const bool typedRead = member != "?" && member != "ambiguous";
    if (untypedAdmitted)
      return RV::UNK;
    if (typedRead) {
      if (admitted.count(member) && admitted.size() == 1) return RV::VER;
      if (ownWrite && !admitted.count(member) && !admitted.empty()) return RV::CONTRA;
      return RV::UNK;
    }
    return admitted.size() == 1 ? RV::VER : RV::UNK;
  };
  // Facts here, else (the object a parameter) facts at every call site.
  std::function<RV(const Instruction *, const Value *, uint64_t, const std::string &,
                   const std::string &, const std::vector<Site> &, std::vector<Fact>, int)>
      keyRead = [&](const Instruction *I, const Value *base, uint64_t embed,
                    const std::string &S, const std::string &member,
                    const std::vector<Site> &W, std::vector<Fact> facts, int depth) {
    for (const Fact &g : factsHere(I, S, base, embed)) facts.push_back(g);
    const RV r = judge(facts, member, W);
    if (detailU && depth == 2) {
        const char *kn[] = {"==", "!=", "bits-set", "bits-clear", "<u", ">=u", "== fn#"};
        errs() << "UnionCensus:   read " << member << " at " << locOf(I) << " depth " << depth
               << " ->" << (r == RV::VER ? " VER" : r == RV::CONTRA ? " CONTRA" : " UNK") << "\n";
        for (const Fact &g : facts)
          errs() << "UnionCensus:     fact @" << g.f << " " << kn[(int)g.k] << " " << g.c << "\n";
        for (const Site &w : W) {
          errs() << "UnionCensus:     write " << w.member << " at "
                 << (w.I ? locOf(w.I) : "init") << ":";
          for (const Fact &g : facts) {
            Res e = evalFact(w.co, g);
            errs() << " @" << g.f << (factStable(g) ? "" : "(unstable)") << "="
                   << (e == Res::SAT ? "SAT" : e == Res::VIOL ? "VIOL" : "UNK");
            auto it = w.co.find(g.f);
            if (it != w.co.end()) {
              errs() << "{";
              for (auto &v : it->second) errs() << v << ",";
              errs() << "}";
            }
          }
          errs() << "\n";
        }
      }
    if (r != RV::UNK || depth == 0)
      return r;
    const Function *F = I->getFunction();
    const int pi = paramIndex(F, base);
    auto &callers = callersOf[F];
    if (pi < 0 || F->hasAddressTaken() || callers.empty() || callers.size() > kCallers)
      return RV::UNK;
    bool allVer = true;
    for (const CallBase *CB : callers) {
      const RV c = keyRead(CB, resolveBase(CB->getArgOperand(pi)), embed, S, member, W,
                           facts, depth - 1);
      if (c == RV::CONTRA) return RV::CONTRA;
      allVer &= c == RV::VER;
    }
    return allVer ? RV::VER : RV::UNK;
  };
  // A test of field `f` of the same object decides the path to I: some
  // dominating branch or switch establishes a fact on it.
  auto guardedHere = [&](const Instruction *I, const std::string &S, uint64_t f,
                         const Value *base, uint64_t embed) {
    for (const Fact &g : factsHere(I, S, base, embed))
      if (g.f == f)
        return true;
    return false;
  };
  // Guarded here, or the object is a parameter and every direct call site
  // passing it is guarded.
  std::function<bool(const Instruction *, const Value *, uint64_t,
                     const std::string &, uint64_t, int)>
      guardedBy = [&](const Instruction *I, const Value *base, uint64_t embed,
                      const std::string &S, uint64_t f, int depth) {
    if (guardedHere(I, S, f, base, embed))
      return true;
    if (depth == 0)
      return false;
    const Function *F = I->getFunction();
    const int pi = paramIndex(F, base);
    auto &callers = callersOf[F];
    if (pi < 0 || F->hasAddressTaken() || callers.empty() || callers.size() > kCallers)
      return false;
    for (const CallBase *CB : callers)
      if (!guardedBy(CB, resolveBase(CB->getArgOperand(pi)), embed, S, f, depth - 1))
        return false;
    return true;
  };
  // A read whose value is masked by a small constant: the pointer carries
  // a tag in its low bits (static_key.type & JUMP_TYPE_LINKED).
  auto lowBitTagged = [](const Instruction *LI) {
    SmallVector<const Value *, 8> work{LI};
    SmallPtrSet<const Value *, 16> seen;
    while (!work.empty()) {
      const Value *V = work.pop_back_val();
      if (!seen.insert(V).second || seen.size() > 16)
        continue;
      for (const User *U : V->users()) {
        if (isa<PtrToIntInst>(U) || isa<BitCastInst>(U) || isa<TruncInst>(U) ||
            isa<ZExtInst>(U)) {
          work.push_back(U);
          continue;
        }
        if (const auto *BO = dyn_cast<BinaryOperator>(U))
          if (BO->getOpcode() == Instruction::And)
            for (const Value *Op : BO->operands())
              if (const auto *C = dyn_cast<ConstantInt>(Op)) {
                const uint64_t m = C->getZExtValue();
                if ((m > 0 && m < 8) || (~m < 8))
                  return true;
              }
      }
    }
    return false;
  };
  // A callee's direct callees (two levels) run on the same object:
  // helpers like renumberCursorDoMapping, called with the walker.
  auto calleeClosure = [&](std::set<std::string> &fs) {
    for (int lvl = 0; lvl < 2; lvl++) {
      std::set<std::string> add;
      for (auto &[M2, _2] : Ctx->Modules)
        for (const std::string &fn : fs)
          if (const Function *CF = M2->getFunction(fn))
            for (auto &[CB, G] : callsIn[CF])
              add.insert(G->getName().str());
      fs.insert(add.begin(), add.end());
    }
  };

  // ---- The union-key engine (--cfl-union-keys) ----
  // Definitions by name (callbacks are known by name in the co-write sets).
  std::map<std::string, const Function *> defByName;
  for (auto &[M, _] : Ctx->Modules)
    for (const Function &F : *M)
      if (!F.isDeclaration())
        defByName.emplace(F.getName().str(), &F);
  // The argument of a call that is the object `base` (+ embed) itself.
  auto objArg = [&](const CallBase *CB, const Value *base, uint64_t embed) -> int {
    const DataLayout &DL = CB->getModule()->getDataLayout();
    for (unsigned j = 0; j < CB->arg_size(); j++) {
      const Value *A = CB->getArgOperand(j)->stripPointerCasts();
      int64_t off = 0;
      bool ok = true;
      while (const auto *G = dyn_cast<GEPOperator>(A)) {
        APInt O(DL.getIndexTypeSizeInBits(G->getType()), 0);
        if (!G->accumulateConstantOffset(DL, O)) { ok = false; break; }
        off += O.getSExtValue();
        A = G->getPointerOperand()->stripPointerCasts();
      }
      if (ok && off == (int64_t)embed && resolveBase(A) == base)
        return (int)j;
    }
    return -1;
  };
  // Correlated dispatch: every load of a callback field is called with
  // the object it was loaded from, at one argument position (returned),
  // compared, or stored into a callback field (a copy, seen there as an
  // unknown value). Anything else lets the callback escape: -1.
  auto dispatchArg = [&](const std::string &S, const std::set<uint64_t> &cbFields,
                         std::string &why) -> int {
    int k = -1;
    for (uint64_t f : cbFields)
      for (const LoadInst *L : loadsAt[{S, f}]) {
        const Pos Q = position(L->getPointerOperand(), L->getModule()->getDataLayout());
        for (const User *Us : L->users()) {
          if (const auto *CB = dyn_cast<CallBase>(Us)) {
            if (CB->getCalledOperand()->stripPointerCasts() != L) {
              why = "callback passed as an argument in " + L->getFunction()->getName().str();
              return -1;
            }
            const int j = objArg(CB, Q.base, Q.embed);
            if (j < 0 || (k >= 0 && j != k)) {
              why = "dispatch without its object in " + L->getFunction()->getName().str();
              return -1;
            }
            k = j;
          } else if (isa<ICmpInst>(Us)) {
          } else if (const auto *SI = dyn_cast<StoreInst>(Us)) {
            const Pos T = position(SI->getPointerOperand(), SI->getModule()->getDataLayout());
            if (SI->getValueOperand() != L || !T.ok || T.S != S ||
                !cbFields.count((uint64_t)fieldAt(T.S, T.off))) {
              why = "callback stored elsewhere in " + L->getFunction()->getName().str();
              return -1;
            }
          } else {
            why = "callback value escapes in " + L->getFunction()->getName().str();
            return -1;
          }
        }
      }
    if (k < 0)
      why = "no dispatch site";
    return k;
  };
  // A callback runs only through dispatch: its address is only stored
  // into callback fields of S (through selects and phis) or compared;
  // never passed or put in an initializer. Its direct calls are returned
  // in `direct`: each must hand on the dispatched object (keyUnion).
  auto onlyDispatched = [&](const std::string &c, const std::string &S,
                            const std::set<uint64_t> &cbFields,
                            std::vector<const CallBase *> &direct) {
    bool any = false;
    for (auto &[M, _] : Ctx->Modules) {
      const Function *Fn = M->getFunction(c);
      if (!Fn)
        continue;
      any = true;
      SmallVector<const Value *, 8> work{Fn};
      SmallPtrSet<const Value *, 16> seen;
      while (!work.empty()) {
        const Value *V = work.pop_back_val();
        if (!seen.insert(V).second)
          continue;
        for (const User *Us : V->users()) {
          if (const auto *CE = dyn_cast<ConstantExpr>(Us)) {
            if (CE->isCast()) { work.push_back(CE); continue; }
            return false;
          }
          if (isa<SelectInst>(Us) || isa<PHINode>(Us) || isa<CastInst>(Us)) {
            work.push_back(Us);
            continue;
          }
          if (isa<ICmpInst>(Us))
            continue;
          if (const auto *CB = dyn_cast<CallBase>(Us))
            if (CB->getCalledOperand() == V && V == Fn) {
              direct.push_back(CB);
              continue;
            }
          if (const auto *SI = dyn_cast<StoreInst>(Us)) {
            if (SI->getValueOperand() != V)
              return false;
            const Pos T = position(SI->getPointerOperand(), SI->getModule()->getDataLayout());
            if (!T.ok || T.S != S || !cbFields.count((uint64_t)fieldAt(T.S, T.off)))
              return false;
            continue;
          }
          return false; // a direct call, an argument, an initializer, ...
        }
      }
    }
    return any;
  };
  // Keys of one union: writes by the callbacks co-written with them,
  // reads by the callbacks they run under. Unknown stays unkeyed (the
  // read takes every plane, the write lands where every read sees it).
  auto keyUnion = [&](const UnionField *U, const std::vector<Site> &W,
                      const std::vector<Site> &Rd, const std::set<uint64_t> &cbFields,
                      const std::set<std::string> &governed, bool governsAll,
                      size_t &keyedW, size_t &keyedR, std::string &note) {
    auto keyName = [&](const std::string &v) {
      return "struct." + U->structName + "+" + std::to_string(U->off) + "#" + v;
    };
    if (CFLUnionKeys == "single") {
      for (auto &w : W)
        if (w.I) { unionKeyNames[w.I] = {keyName("all")}; keyedW++; }
      for (auto &r : Rd) { unionKeyNames[r.I] = {keyName("all")}; keyedR++; }
      return;
    }
    if (cbFields.empty()) { note = "no callback field"; return; }
    if (governsAll) { note = "a callback field takes an unknown value"; return; }
    const int kS = dispatchArg(U->structName, cbFields, note);
    if (kS < 0)
      return;
    // Writes: every callback field's value known in the write's context.
    auto fnsOf = [&](const std::string &v, std::set<std::string> &out) {
      if (v.rfind("fn:", 0) == 0) { out.insert(v.substr(3)); return true; }
      if (v.rfind("gv:", 0) == 0) {
        auto git = fnsInGV.find(v.substr(3));
        if (git != fnsInGV.end()) { out.insert(git->second.begin(), git->second.end()); return true; }
        return false;
      }
      return v == "null" || v == "int:0";
    };
    std::set<std::string> stored; // every callback ever stored into the fields
    for (uint64_t f : cbFields) {
      auto wit = writersOf.find({U->structName, f});
      if (wit != writersOf.end())
        for (const ObjKey &K : wit->second)
          for (auto &v : coWrites[K][f]) fnsOf(v, stored);
    }
    size_t partial = 0;
    for (auto &w : W) {
      if (!w.I) continue;
      std::set<std::string> F;
      bool known = true;
      for (uint64_t f : cbFields) {
        auto it = w.co.find(f);
        if (it == w.co.end()) {
          known = false;
          partial++;
          if (detailed(U))
            errs() << "UnionCensus:   unkeyed write " << w.member << " at " << locOf(w.I)
                   << ": callback field @" << f << " not written in its context\n";
          break;
        }
        for (auto &v : it->second) known &= fnsOf(v, F);
      }
      if (!known || F.empty()) continue;
      auto &names = unionKeyNames[w.I];
      for (auto &fn : F) names.push_back(keyName(fn));
      keyedW++;
    }
    // Reads: the function runs only under good callbacks, on the object
    // the dispatch passed (the callback's parameter kS, handed down to
    // helpers whose every caller passes it).
    std::map<std::string, std::set<std::string>> closureOf;
    std::map<std::string, std::vector<const CallBase *>> directOf;
    std::set<std::string> dispatchedOnly, good;
    for (auto &c : stored) {
      std::set<std::string> cl{c};
      calleeClosure(cl);
      closureOf[c] = std::move(cl);
      if (onlyDispatched(c, U->structName, cbFields, directOf[c]))
        dispatchedOnly.insert(c);
    }
    std::map<std::string, int> wpar; // function -> its parameter holding the object
    // A direct call of a callback hands on the dispatched object when its
    // caller runs on that object and passes it at the callback's slot
    // (exprNodeIsConstantOrGroupBy calling exprNodeIsConstant).
    auto handsOn = [&](const CallBase *CB) {
      const Function *G = CB->getFunction();
      auto pit = wpar.find(G->getName().str());
      return pit != wpar.end() && (unsigned)kS < CB->arg_size() &&
             resolveBase(CB->getArgOperand(kS)) == paramBase(G, (unsigned)pit->second);
    };
    std::set<std::string> helpers;
    for (auto &[c, cl] : closureOf) helpers.insert(cl.begin(), cl.end());
    // Greatest fixpoint: assume every dispatched-only callback runs on the
    // dispatched object, derive the helpers, and drop a callback whose
    // direct calls do not hand the object on; repeat until stable. Sound
    // because every chain of direct calls into a callback starts at a
    // dispatch (recursion like resolveExprStep's included).
    good = dispatchedOnly;
    for (bool changed = true; changed;) {
      wpar.clear();
      for (auto &c : good) wpar[c] = kS;
      for (int round = 0; round < 3; round++)
        for (auto &h : helpers) {
          if (wpar.count(h) || stored.count(h)) continue;
          auto dit = defByName.find(h);
          if (dit == defByName.end() || dit->second->hasAddressTaken()) continue;
          auto &callers = callersOf[dit->second];
          if (callers.empty()) continue;
          int j = -1;
          bool ok = true;
          for (const CallBase *CB : callers) {
            const Function *G = CB->getFunction();
            auto pit = wpar.find(G->getName().str());
            if (pit == wpar.end()) { ok = false; break; }
            const Value *wb = paramBase(G, (unsigned)pit->second);
            int jj = -1;
            for (unsigned a = 0; a < CB->arg_size(); a++)
              if (resolveBase(CB->getArgOperand(a)) == wb) { jj = (int)a; break; }
            if (jj < 0 || (j >= 0 && jj != j)) { ok = false; break; }
            j = jj;
          }
          if (ok) wpar[h] = j;
        }
      changed = false;
      for (auto it = good.begin(); it != good.end();)
        if (!std::all_of(directOf[*it].begin(), directOf[*it].end(), handsOn)) {
          it = good.erase(it);
          changed = true;
        } else
          ++it;
    }
    size_t badCb = 0;
    for (auto &c : stored) {
      badCb += !good.count(c);
      if (!good.count(c) && detailed(U))
        errs() << "UnionCensus:   callback " << c << " runs outside dispatch\n";
    }
    for (auto &r : Rd) {
      const Function *RF = r.I->getFunction();
      const std::string rn = RF->getName().str();
      if (governed.count(rn) || r.embed != 0) continue;
      auto pit = wpar.find(rn);
      if (pit == wpar.end() || r.base != paramBase(RF, (unsigned)pit->second)) {
        if (detailed(U))
          errs() << "UnionCensus:   unkeyed read " << r.member << " at " << locOf(r.I)
                 << ": not on the dispatched object\n";
        continue;
      }
      std::set<std::string> K;
      bool ok = true;
      for (auto &[c, cl] : closureOf)
        if (cl.count(rn)) {
          if (!good.count(c)) ok = false;
          K.insert(c);
        }
      if (!ok || K.empty()) {
        if (detailed(U))
          errs() << "UnionCensus:   unkeyed read " << r.member << " at " << locOf(r.I)
                 << (ok ? ": under no callback" : ": under a callback that runs outside dispatch")
                 << "\n";
        continue;
      }
      auto &names = unionKeyNames[r.I];
      for (auto &c : K) names.push_back(keyName(c));
      keyedR++;
    }
    // The rest of this union's accesses keep an unknown key.
    if (keyedW + keyedR > 0) {
      const std::string prefix =
          "struct." + U->structName + "+" + std::to_string(U->off);
      for (auto &w : W)
        if (w.I && !unionKeyNames.count(w.I)) unionUnknownOf[w.I] = prefix;
      for (auto &r : Rd)
        if (!unionKeyNames.count(r.I)) unionUnknownOf[r.I] = prefix;
    }
    note = "dispatch arg " + std::to_string(kS) + ", " + std::to_string(stored.size()) +
           " callbacks (" + std::to_string(badCb) + " not only dispatched), " +
           std::to_string(partial) + " writes with a callback field unset in context";
  };

  size_t nUnions = 0, nTag = 0, nTagVer = 0, nCallback = 0, nNone = 0, nSingle = 0, nUntyped = 0,
         nLowBit = 0, readContra = 0, pointerlessReads = 0;
  // Untested reads by where the search stopped (plan 3.30 P1).
  std::map<std::string, size_t> untestedBy;
  std::map<std::string, size_t> uncheckedBy; // reads keyed by their own member, by why
  std::map<std::string, size_t> blockingWrites; // write of unknown tag -> reads it blocks
  std::map<std::string, std::map<std::string, size_t>> untestedByUnion;
  // --cfl-union-keys=tag: the void * members (by union + "." + member):
  // writes landed where every read sees them, reads of the whole slot, and
  // the reads keyed by another member that see those writes.
  struct GenericUse {
    size_t writes = 0, reads = 0, othersSee = 0, othersUnchecked = 0;
    std::vector<std::string> at;
    std::map<std::string, size_t> seenBy; // the members of those reads
  };
  std::map<std::string, GenericUse> genericOf;
  // --cfl-union-keys=tag: per union, the accesses left unkeyed (the gap:
  // an unkeyed read sees every member). Pointerless writes carry nothing.
  struct Unkeyed {
    size_t writes = 0;                    // pointer writes of unknown member
    std::map<std::string, size_t> readsBy; // unkeyed reads by failed input
    std::vector<std::string> at;
  };
  std::map<std::string, Unkeyed> unkeyedOf;
  struct Line { size_t accesses; std::string text; };
  std::vector<Line> lines;
  std::set<const UnionField *> touched;
  for (auto &[U, _] : writes) touched.insert(U);
  for (auto &[U, _] : reads) touched.insert(U);
  auto real = [](const std::string &m) { return m != "?" && m != "ambiguous"; };
  // ---- Tag keys: one rule (plan 3.17) ----
  // A tagged union is a sum type and its tag the program's own RTTI: a
  // dominating tag test is a dynamic type check. A read's key is the set
  // of members of the writes its tag facts admit; it is keyed when that
  // set has at most one member. The inputs, each derived on its own:
  //   (1) the member a write writes (unknown: the write lands on the
  //       unkeyed side, which every key sees, so it never blocks a key);
  //   (2) the tag value written with it (co-writes; unknown: admitted);
  //   (3) the tag facts at the read (here, else at every call site).
  // A write that carries no pointer feeds no pointer read. The read's own
  // static type is not an input (it only names a contradiction).
  // ---- Path stability (plan 3.30 P2) ----
  // A test at C justifies a read at L when no path C -> L writes the tested
  // bits of the tag or the union slot: kind not modified between check and
  // use (C++: isa<> then use). A write is a store to the field (`f |= K`
  // with K outside the tested bits does not count), a memset/memcpy or a
  // struct store that may cover the struct, or a call whose transitive mod
  // set has the field. Sound only when the field's address is used for
  // nothing but loads and stores (else other pointers write it unseen).
  // ASSUMPTION: a function without a body writes no program struct.
  auto embedsStruct = [&](std::string outer, const std::string &S) {
    std::vector<std::string> work{outer};
    std::set<std::string> seen;
    while (!work.empty()) {
      const std::string X = work.back();
      work.pop_back();
      if (X == S) return true;
      if (!seen.insert(X).second) continue;
      for (auto &[k, v] : embeddedAt)
        if (k.first == X) work.push_back(v.first);
    }
    return false;
  };
  // A bulk write (memset, memcpy, a struct store) that may cover struct S.
  auto bulkMayWrite = [&](const Value *Dst, const DataLayout &DL, const std::string &S) {
    const Pos Q = position(Dst, DL);
    if (Q.ok) return embedsStruct(Q.S, S);
    const Value *U = getUnderlyingObject(Dst);
    if (const auto *A = dyn_cast<AllocaInst>(U)) {
      const auto *ST = dyn_cast<StructType>(A->getAllocatedType());
      if (!ST) return !A->getAllocatedType()->isIntegerTy() &&
                      !A->getAllocatedType()->isArrayTy();
      return !ST->hasName() || isAnonStruct(ST) || embedsStruct(stripSuffix(ST->getName()), S);
    }
    return true; // unknown destination
  };
  auto fieldSize = [&](const std::string &S, uint64_t f) -> uint64_t {
    auto fit = fieldsOf.find(S);
    if (fit != fieldsOf.end())
      for (auto &[o, sz] : fit->second)
        if (o == f) return std::max<uint64_t>(sz, 1);
    return 1;
  };
  // A store through a pointer with no GEP (offset 0 of whatever it points
  // to, e.g. `p->op = x` at -O3): it may write S unless the pointer's
  // debug type names a struct that does not embed S.
  auto untypedMayWrite = [&](const Value *Ptr, const std::string &S) {
    const std::string k = valueKey(Ptr, 0);
    if (k.rfind("ptr:", 0) != 0) return true;
    const std::string X = k.substr(4);
    if (X.empty() || X == "void" || X.find("char") != std::string::npos ||
        X == "u8" || X == "i8")
      return true; // a char lvalue may write any object
    if (!fieldsOf.count(X)) return true; // not a struct we know
    return embedsStruct(X, S);
  };
  // The struct positions an address may be: itself, or every incoming
  // address of a phi/select (-O3 joins `&a->f` and `&b->f`). False when
  // some incoming address is not a struct position.
  std::function<bool(const Value *, const DataLayout &, std::vector<Pos> &, int)>
      addrPositions = [&](const Value *V, const DataLayout &DL, std::vector<Pos> &out,
                          int depth) -> bool {
    V = V->stripPointerCasts();
    const Pos Q = position(V, DL);
    if (Q.ok) { out.push_back(Q); return true; }
    if (depth == 0) return false;
    if (const auto *PN = dyn_cast<PHINode>(V)) {
      for (const Value *X : PN->incoming_values())
        if (X != PN && !addrPositions(X, DL, out, depth - 1)) return false;
      return true;
    }
    if (const auto *SE = dyn_cast<SelectInst>(V))
      return addrPositions(SE->getTrueValue(), DL, out, depth - 1) &&
             addrPositions(SE->getFalseValue(), DL, out, depth - 1);
    return false;
  };
  // Does instruction I (directly) write bits `bits` of field f of S? A
  // store writes every field its bytes overlap (-O3 merges adjacent
  // stores into one wider store).
  auto directWrite = [&](const Instruction &I, const std::string &S, uint64_t f,
                         uint64_t bits) -> bool {
    const DataLayout &DL = I.getModule()->getDataLayout();
    if (const auto *SI = dyn_cast<StoreInst>(&I)) {
      const Type *T = SI->getValueOperand()->getType();
      if (T->isStructTy() || T->isArrayTy())
        return bulkMayWrite(SI->getPointerOperand(), DL, S);
      std::vector<Pos> qs;
      if (!position(SI->getPointerOperand(), DL).ok &&
          addrPositions(SI->getPointerOperand(), DL, qs, 4)) {
        const uint64_t sz = DL.getTypeStoreSize(const_cast<Type *>(T));
        const uint64_t fsz = fieldSize(S, f);
        for (const Pos &P : qs)
          if (P.S == S && !(P.off + sz <= f || f + fsz <= P.off)) return true;
        return false;
      }
      const Pos Q = position(SI->getPointerOperand(), DL);
      if (!Q.ok) {
        // Not a struct-field address (no GEP, a byte GEP, an array of
        // scalars): judged by the object it lands in, offsets ignored.
        const Value *U = getUnderlyingObject(SI->getPointerOperand());
        auto declared = [&](Type *T) {
          while (auto *AT = dyn_cast<ArrayType>(T)) T = AT->getElementType();
          const auto *ST = dyn_cast<StructType>(T);
          return ST && (!ST->hasName() || isAnonStruct(ST) || embedsStruct(stripSuffix(ST->getName()), S));
        };
        if (const auto *A = dyn_cast<AllocaInst>(U)) return declared(A->getAllocatedType());
        if (const auto *G = dyn_cast<GlobalVariable>(U)) return declared(G->getValueType());
        return untypedMayWrite(U, S);
      }
      if (Q.S != S) return false;
      const uint64_t sz = DL.getTypeStoreSize(const_cast<Type *>(T));
      const uint64_t fsz = fieldSize(S, f);
      if (Q.off + sz <= f || f + fsz <= Q.off) return false; // no overlap
      if (Q.off != f || sz != fsz) return true; // part of a wider store
      const Value *V = peel(SI->getValueOperand());
      if (const auto *BO = dyn_cast<BinaryOperator>(V))
        if (BO->getOpcode() == Instruction::Or || BO->getOpcode() == Instruction::And)
          for (unsigned k = 0; k < 2; k++)
            if (const auto *C = dyn_cast<ConstantInt>(BO->getOperand(k)))
              if (isFieldLoad(BO->getOperand(1 - k), Q.S, f, Q.base, Q.embed)) {
                const unsigned bw = C->getType()->getIntegerBitWidth();
                const uint64_t mask = bw >= 64 ? ~0ULL : ((1ULL << bw) - 1);
                const uint64_t touched = BO->getOpcode() == Instruction::Or
                                             ? C->getZExtValue()
                                             : (~C->getZExtValue() & mask);
                return (touched & bits) != 0;
              }
      return true;
    }
    if (const auto *MI = dyn_cast<MemIntrinsic>(&I))
      return bulkMayWrite(MI->getDest(), DL, S);
    if (const auto *CB = dyn_cast<CallBase>(&I)) {
      if (isa<DbgInfoIntrinsic>(I) || CB->isLifetimeStartOrEnd()) return false;
      for (unsigned a = 0; a < CB->arg_size(); a++) {
        const Value *A = CB->getArgOperand(a);
        if (!A->getType()->isPointerTy() || CB->onlyReadsMemory(a)) continue;
        std::vector<Pos> qs;
        if (!addrPositions(A, DL, qs, 4)) continue;
        for (const Pos &P : qs)
          if (P.S == S && fieldAt(S, P.off) == (int64_t)f)
            return true; // the callee may write through the address
      }
    }
    return false;
  };
  // Functions that may write bits of (S, f): directly, or through a call
  // (direct callers; every function with an indirect call once an
  // address-taken writer exists).
  std::vector<const Function *> allFns, indirectCallers;
  for (auto &[M, _] : Ctx->Modules)
    for (const Function &F : *M) {
      if (F.isDeclaration()) continue;
      allFns.push_back(&F);
      for (const Instruction &I : instructions(F))
        if (const auto *CB = dyn_cast<CallBase>(&I))
          if (!CB->getCalledFunction() && !CB->isInlineAsm()) {
            indirectCallers.push_back(&F);
            break;
          }
    }
  std::map<std::tuple<std::string, uint64_t, uint64_t>, std::set<const Function *>> modMemo;
  // Why a function is in a mod set: the direct write, or the call into a
  // member (verbose report).
  std::map<std::tuple<std::string, uint64_t, uint64_t>,
           std::map<const Function *, const Instruction *>> modWhy;
  auto modFns = [&](const std::string &S, uint64_t f, uint64_t bits)
      -> const std::set<const Function *> & {
    auto [it, ins] = modMemo.try_emplace({S, f, bits});
    std::set<const Function *> &M = it->second;
    if (!ins) return M;
    auto &why = modWhy[{S, f, bits}];
    std::vector<const Function *> work;
    for (const Function *F : allFns)
      for (const Instruction &I : instructions(*F))
        if (directWrite(I, S, f, bits) ||
            (isa<CallBase>(I) && cast<CallBase>(I).isInlineAsm())) {
          if (M.insert(F).second) { work.push_back(F); why[F] = &I; }
          break;
        }
    bool indirectDone = false;
    while (!work.empty()) {
      const Function *F = work.back();
      work.pop_back();
      for (const CallBase *CB : callersOf[F])
        if (M.insert(CB->getFunction()).second) {
          work.push_back(CB->getFunction());
          why[CB->getFunction()] = CB;
        }
      if (F->hasAddressTaken() && !indirectDone) {
        indirectDone = true;
        for (const Function *G : indirectCallers)
          if (M.insert(G).second) { work.push_back(G); why[G] = nullptr; }
      }
    }
    return M;
  };
  // Does the address of field f of S escape: stored as a value, turned
  // into an integer, returned? Loads, stores through it, compares, and
  // calls taking it (a call is a write of the field, see directWrite) do
  // not; phis, selects, GEPs and casts of it are followed.
  std::map<std::pair<std::string, uint64_t>, bool> escapeMemo;
  auto fieldEscapes = [&](const std::string &S, uint64_t f) {
    auto [it, ins] = escapeMemo.try_emplace({S, f}, false);
    if (!ins) return it->second;
    std::set<const Value *> seen;
    for (const Function *F : allFns) {
      const DataLayout &DL = F->getParent()->getDataLayout();
      for (const Instruction &I : instructions(*F)) {
        const Value *V = &I;
        if (!isa<GEPOperator>(V)) continue;
        const Pos Q = position(V, DL);
        if (!Q.ok || Q.S != S || fieldAt(Q.S, Q.off) != (int64_t)f) continue;
        std::vector<const Value *> work{V};
        while (!work.empty()) {
          const Value *X = work.back();
          work.pop_back();
          if (!seen.insert(X).second) continue;
          for (const User *U : X->users()) {
            if (isa<LoadInst>(U) || isa<ICmpInst>(U) || isa<DbgInfoIntrinsic>(U))
              continue;
            if (const auto *SI = dyn_cast<StoreInst>(U)) {
              if (SI->getValueOperand() != X) continue;
            } else if (isa<CallBase>(U)) {
              continue;
            } else if (isa<PHINode>(U) || isa<SelectInst>(U) || isa<GEPOperator>(U) ||
                       isa<BitCastOperator>(U) || isa<AddrSpaceCastInst>(U)) {
              work.push_back(U);
              continue;
            }
            it->second = true;
            std::string is;
            raw_string_ostream os(is);
            cast<Instruction>(U)->print(os);
            errs() << "UnionKeys: address of " << S << "+" << f << " escapes in "
                   << cast<Instruction>(U)->getFunction()->getName() << ": "
                   << os.str().substr(0, 160) << "\n";
            return true;
          }
        }
      }
    }
    return false;
  };
  // ---- Capture (for object-sensitive slot checks) ----
  // Which parameters a body may capture (store as a value, turn into an
  // integer, return, or pass to a capturing parameter), inferred from the
  // bodies as LLVM's function-attrs does: the least fixpoint from "none".
  // A call to a function without a body, or an indirect call, captures
  // unless the argument is marked nocapture.
  std::map<std::pair<const Function *, unsigned>, bool> paramCap;
  bool capDone = false;
  std::function<bool(const Value *)> valueCaptured = [&](const Value *V) -> bool {
    SmallVector<const Value *, 16> work{V};
    SmallPtrSet<const Value *, 32> seen;
    while (!work.empty()) {
      const Value *X = work.pop_back_val();
      if (!seen.insert(X).second) continue;
      for (const Use &U : X->uses()) {
        const User *Us = U.getUser();
        if (isa<LoadInst>(Us) || isa<ICmpInst>(Us) || isa<DbgInfoIntrinsic>(Us)) continue;
        if (const auto *SI = dyn_cast<StoreInst>(Us)) {
          if (SI->getValueOperand() == X) return true;
          continue;
        }
        if (isa<GetElementPtrInst>(Us) || isa<BitCastInst>(Us) || isa<PHINode>(Us) ||
            isa<SelectInst>(Us) || isa<AddrSpaceCastInst>(Us)) {
          work.push_back(Us);
          continue;
        }
        if (const auto *CB = dyn_cast<CallBase>(Us)) {
          if (CB->isLifetimeStartOrEnd() || isa<MemIntrinsic>(CB)) continue;
          if (!CB->isArgOperand(&U)) return true; // called through
          const unsigned a = CB->getArgOperandNo(&U);
          if (CB->doesNotCapture(a)) continue;
          const Function *T = CB->getCalledFunction();
          if (!T || T->isDeclaration() || a >= T->arg_size() || T->isVarArg()) return true;
          if (paramCap[{T, a}]) return true;
          continue;
        }
        return true; // ptrtoint, return, insertvalue, ...
      }
    }
    return false;
  };
  auto computeCaptures = [&]() {
    if (capDone) return;
    capDone = true;
    for (bool changed = true; changed;) {
      changed = false;
      for (const Function *F : allFns)
        for (const Argument &A : F->args())
          if (A.getType()->isPointerTy() && !paramCap[{F, A.getArgNo()}] &&
              valueCaptured(&A)) {
            paramCap[{F, A.getArgNo()}] = true;
            changed = true;
          }
    }
  };
  // Does some path from `start` (inclusive) to `to` (exclusive) execute an
  // instruction for which `writes` holds?
  auto pathWrites = [&](const Instruction *start, const Instruction *to,
                        const std::function<bool(const Instruction &)> &writes) {
    const BasicBlock *SB = start->getParent(), *TB = to->getParent();
    if (SB == TB) {
      // Start before `to` in one block: every path reaches `to` first.
      bool before = false;
      for (const Instruction &I : *SB) {
        if (&I == start) { before = true; break; }
        if (&I == to) break;
      }
      if (before) {
        for (const Instruction *I = start; I && I != to; I = I->getNextNode())
          if (writes(*I)) return true;
        return false;
      }
    }
    std::set<const BasicBlock *> fwd, bwd;
    std::vector<const BasicBlock *> work{SB};
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (!fwd.insert(B).second) continue;
      if (B == TB && B != SB) continue; // reached the read
      for (const BasicBlock *X : successors(B)) work.push_back(X);
    }
    work = {TB};
    while (!work.empty()) {
      const BasicBlock *B = work.back();
      work.pop_back();
      if (!bwd.insert(B).second) continue;
      if (B == SB && B != TB) continue;
      for (const BasicBlock *X : predecessors(B)) work.push_back(X);
    }
    // A block on a cycle inside the region is on a path whole.
    auto onCycle = [&](const BasicBlock *B) {
      std::set<const BasicBlock *> seen;
      std::vector<const BasicBlock *> w(succ_begin(B), succ_end(B));
      while (!w.empty()) {
        const BasicBlock *X = w.back();
        w.pop_back();
        if (X == B) return true;
        if (!fwd.count(X) || !bwd.count(X) || !seen.insert(X).second) continue;
        for (const BasicBlock *Y : successors(X)) w.push_back(Y);
      }
      return false;
    };
    for (const BasicBlock *B : fwd) {
      if (!bwd.count(B)) continue;
      const bool whole = onCycle(B);
      bool on = whole || B != SB;
      for (const Instruction &I : *B) {
        if (&I == start) on = true;
        if (!whole && B == TB && &I == to) break;
        if (on && writes(I)) return true;
      }
    }
    return false;
  };
  // A writer predicate for (S, f, bits): direct writes and calls into mod.
  auto writerOf = [&](const std::string &S, uint64_t f, uint64_t bits) {
    const std::set<const Function *> *M = &modFns(S, f, bits);
    bool anyAddrTaken = false;
    for (const Function *F : *M) anyAddrTaken |= F->hasAddressTaken();
    return [=, &directWrite](const Instruction &I) -> bool {
      if (directWrite(I, S, f, bits)) return true;
      const auto *CB = dyn_cast<CallBase>(&I);
      if (!CB || isa<DbgInfoIntrinsic>(I)) return false;
      if (CB->isInlineAsm()) return true;
      if (const Function *T = CB->getCalledFunction()) {
        if (T->isIntrinsic()) return false;
        const Function *D = getFuncDef(const_cast<Function *>(T));
        return M->count(D) != 0;
      }
      return anyAddrTaken; // an indirect call reaches address-taken code
    };
  };
  auto bitsOf = [](const Fact &g) {
    return g.k == FK::BSET || g.k == FK::BCLR ? g.c : ~0ULL;
  };
  // Is fact g (found at a test whose path reaches I) intact at I, and at
  // every lower frame's read point from that frame's entry (`below`)?
  // Why the last path check failed (verbose report: which condition).
  std::map<std::string, std::pair<size_t, std::string>> pathFails;
  auto failAt = [&](const std::string &why, const Instruction *X) {
    auto &e = pathFails[why];
    if (e.first++ == 0 && X) {
      std::string d = X->getFunction()->getName().str();
      if (const DILocation *L = X->getDebugLoc())
        d += ":" + std::to_string(L->getLine());
      std::string is;
      raw_string_ostream os(is);
      X->print(os);
      e.second = d + " " + os.str().substr(0, 120);
    }
  };
  // A usable fact (plan 3.31): (A) write -> check, factPreserved; (B)
  // check -> read: no path from the test to the read (and from each lower
  // frame's entry to its read point) writes the union slot with a write
  // the fact excludes. A write the fact admits is seen by the key anyway;
  // a call that may write the slot, or a write not matched to a union
  // write site, counts.
  auto factUsable = [&](const Fact &g, const Instruction *I, const std::string &S,
                        uint64_t uoff, const std::vector<const Instruction *> &below,
                        const std::vector<Site> &W) {
    if (!factPreserved(g)) { failAt(S + " tag set outside the union's writes", nullptr); return false; }
    if (!g.from) { failAt("no test position", nullptr); return false; }
    if (fieldEscapes(S, uoff)) { failAt(S + " union address escapes", nullptr); return false; }
    auto slot = writerOf(S, uoff, ~0ULL);
    const Instruction *hit = nullptr;
    auto harmful = [&](const Instruction &X) {
      if (!slot(X)) return false;
      if (isa<StoreInst>(X))
        for (const Site &w : W)
          if (w.I == &X) {
            if (evalFact(w.co, g) != Res::VIOL) return false; // admitted
            break;
          }
      hit = &X;
      return true;
    };
    auto what = [&](const Instruction *X) {
      const auto *CB = dyn_cast<CallBase>(X);
      return S + " union written between test and read by " +
             (CB ? (CB->getCalledFunction() ? "a call" : "an indirect call")
                 : isa<MemIntrinsic>(X) ? "a mem intrinsic" : "an excluded write");
    };
    if (pathWrites(g.from, I, harmful)) { failAt(what(hit), hit); return false; }
    for (const Instruction *J : below)
      if (pathWrites(&*J->getFunction()->getEntryBlock().begin(), J, harmful)) {
        failAt(what(hit) + " (a frame below)", hit);
        return false;
      }
    return true;
  };
  size_t factsPathStable = 0, factsReload = 0, writesByTest = 0, dispatchFacts = 0;
  std::set<uint64_t> curCbFields; // the union's callback fields (per union)
  // Do a fact h (holding at a write) and a fact g (at a read), both on the
  // same field, contradict?
  auto contradict = [&](const Fact &h, const Fact &g) {
    if (h.f != g.f) return false;
    if (h.k == FK::FN || g.k == FK::FN)
      return h.k == FK::FN && g.k == FK::FN && h.c != g.c;
    auto eqVs = [](uint64_t c, const Fact &x) { // fact x on value c
      switch (x.k) {
      case FK::EQ: return c == x.c;
      case FK::NE: return c != x.c;
      case FK::BSET: return (c & x.c) != 0;
      case FK::BCLR: return (c & x.c) == 0;
      case FK::ULT: return c < x.c;
      case FK::UGE: return c >= x.c;
      case FK::FN: return true;
      }
      return true;
    };
    if (h.k == FK::EQ) return !eqVs(h.c, g);
    if (g.k == FK::EQ) return !eqVs(g.c, h);
    if (h.k == FK::ULT && g.k == FK::UGE) return h.c <= g.c;
    if (h.k == FK::UGE && g.k == FK::ULT) return g.c <= h.c;
    if (g.k == FK::BSET && h.k == FK::BCLR) return (g.c & ~h.c) == 0;
    if (g.k == FK::BCLR && h.k == FK::BSET) return (h.c & ~g.c) == 0;
    return false;
  };
  // A write excluded by a test that dominates it (`if (!ExprUseXSelect(p))
  // p->x.pList = l`): the write's context writes no value of the field,
  // and no path from the test to the write writes the tested bits.
  auto excludedByTest = [&](const Site &w, const Fact &g, const std::string &S) {
    if (!w.I || w.co.count(g.f)) return false;
    for (const Fact &h : factsHere(w.I, S, w.base, w.embed)) {
      if (!h.from || !contradict(h, g)) continue;
      if (fieldEscapes(S, h.f)) continue;
      auto tag = writerOf(S, h.f, bitsOf(h));
      if (pathWrites(h.from, w.I, tag)) continue;
      return true;
    }
    return false;
  };
  struct Admit {
    std::set<std::string> members;             // of the admitted writes
    bool facts = false;                        // a usable tag fact applied
    bool unstable = false;                     // a test of a field not stable
    std::set<const Instruction *> tagUnknown;  // admitted: tag value unknown
    // Where the backward search for facts stopped while several members
    // were still admitted (one per context; plan 3.30 P1).
    std::set<std::string> stops;
  };
  // A test on another load of the same slot that dominates I (the
  // object reloaded between the test and the read).
  auto reloadTested = [&](const Instruction *I, const Value *base,
                          const std::string &S, uint64_t embed) {
    const auto *L = dyn_cast<LoadInst>(base);
    if (!L) return false;
    const Value *slot = L->getPointerOperand()->stripPointerCasts();
    for (const User *U : slot->users()) {
      const auto *L2 = dyn_cast<LoadInst>(U);
      if (!L2 || L2 == L || L2->getFunction() != I->getFunction()) continue;
      if (!factsHere(I, S, L2, embed).empty()) return true;
    }
    return false;
  };
  // uoff: the union's offset in S. below: the read points of the frames
  // under this one (the read itself, then each call site walked up).
  std::function<Admit(const Instruction *, const Value *, uint64_t,
                      const std::string &, uint64_t, const std::vector<Site> &,
                      std::vector<Fact>, std::vector<const Instruction *>, int)>
      admittedFor = [&](const Instruction *I, const Value *base, uint64_t embed,
                        const std::string &S, uint64_t uoff, const std::vector<Site> &W,
                        std::vector<Fact> facts, std::vector<const Instruction *> below,
                        int depth) -> Admit {
    auto keep = [&](Fact g) {
      if (CFLUnionPathStable) {
        g.usable = factUsable(g, I, S, uoff, below, W);
        if (g.usable && !factStable(g)) factsPathStable++;
      } else {
        g.usable = factStable(g);
      }
      facts.push_back(g);
    };
    for (const Fact &g : factsHere(I, S, base, embed)) keep(g);
    // Reload (C++: dyn_cast on a reloaded pointer): a test on another load
    // L2 of the same slot that dominates this load L, with no write of the
    // slot between L2 and L.
    if (const auto *L = dyn_cast<LoadInst>(base); L && CFLUnionPathStable) {
      const Value *slot = L->getPointerOperand()->stripPointerCasts();
      const DataLayout &DL = L->getModule()->getDataLayout();
      const Pos SQ = position(slot, DL);
      const auto *SA = dyn_cast<AllocaInst>(slot);
      bool slotVisible = false;
      std::function<bool(const Instruction &)> slotWrite;
      // The slot inside a stack object whose address is never captured
      // (stored, returned): only pointers derived from it reach it, so
      // only an instruction given such a pointer can write the slot.
      const auto *SObj = dyn_cast<AllocaInst>(getUnderlyingObject(slot));
      if (SObj) computeCaptures();
      if (SObj && !valueCaptured(SObj)) {
        slotVisible = true;
        slotWrite = [SObj](const Instruction &X) {
          auto fromObj = [&](const Value *P) { return getUnderlyingObject(P) == SObj; };
          if (const auto *SI = dyn_cast<StoreInst>(&X)) return fromObj(SI->getPointerOperand());
          if (const auto *MI = dyn_cast<MemIntrinsic>(&X)) return fromObj(MI->getDest());
          if (const auto *CB = dyn_cast<CallBase>(&X)) {
            if (isa<DbgInfoIntrinsic>(X) || CB->isLifetimeStartOrEnd()) return false;
            for (unsigned a = 0; a < CB->arg_size(); a++)
              if (CB->getArgOperand(a)->getType()->isPointerTy() &&
                  !CB->onlyReadsMemory(a) && fromObj(CB->getArgOperand(a)))
                return true;
            return false;
          }
          return X.mayWriteToMemory() && !isa<FenceInst>(X) &&
                 !isa<LoadInst>(X); // atomics and the like: conservative
        };
      } else if (SQ.ok && !fieldEscapes(SQ.S, (uint64_t)std::max<int64_t>(fieldAt(SQ.S, SQ.off), 0)) &&
          fieldAt(SQ.S, SQ.off) >= 0) {
        slotVisible = true;
        slotWrite = writerOf(SQ.S, (uint64_t)fieldAt(SQ.S, SQ.off), ~0ULL);
      } else if (SA && llvm::all_of(SA->users(), [&](const User *U) {
                   if (isa<LoadInst>(U)) return true;
                   const auto *SI = dyn_cast<StoreInst>(U);
                   return SI && SI->getPointerOperand() == SA;
                 })) {
        slotVisible = true; // a stack slot only loaded and stored
        slotWrite = [SA](const Instruction &X) {
          const auto *SI = dyn_cast<StoreInst>(&X);
          return SI && SI->getPointerOperand()->stripPointerCasts() == SA;
        };
      }
      DominatorTree &DT = domTree(L->getFunction());
      if (slotVisible)
        for (const User *U : slot->users()) {
          const auto *L2 = dyn_cast<LoadInst>(U);
          if (!L2 || L2 == L || L2->getFunction() != L->getFunction() ||
              !DT.dominates(L2, L))
            continue;
          if (pathWrites(L2->getNextNode(), L, slotWrite)) continue;
          for (Fact g : factsHere(I, S, L2, embed)) {
            if (!factUsable(g, I, S, uoff, below, W)) continue;
            g.usable = true;
            facts.push_back(g);
            factsReload++;
          }
        }
    }
    auto admitUnder = [&](const std::vector<Fact> &fs) {
      Admit A;
      for (const Fact &g : fs) {
        A.facts |= g.usable;
        A.unstable |= !g.usable;
      }
      for (const Site &w : W) {
        if (!real(w.member)) continue;         // (1) unknown: unkeyed side
        if (pointerless(w)) continue;          // no pointer to feed a read
        bool excluded = false, unknownTag = false;
        for (const Fact &g : fs) {
          if (!g.usable) continue;
          const Res e = evalFact(w.co, g);     // (2) against (3)
          if (e == Res::VIOL) { excluded = true; break; }
          if (e == Res::UNK && excludedByTest(w, g, S)) {
            excluded = true;
            writesByTest++;
            break;
          }
          unknownTag |= e == Res::UNK;
        }
        if (excluded) continue;
        A.members.insert(w.member);
        if (unknownTag && w.I) A.tagUnknown.insert(w.I);
      }
      return A;
    };
    Admit A = admitUnder(facts);
    if (A.members.size() <= 1) return A;
    // The object a parameter: what each call site's facts admit.
    const Function *F = I->getFunction();
    const int pi = paramIndex(F, base);
    auto &callers = callersOf[F];
    const char *stop = nullptr;
    std::string otherKind;
    if (pi < 0 && !isa<LoadInst>(base) && !isa<CallBase>(base) &&
        !isa<GlobalVariable>(base) && !isa<AllocaInst>(base)) {
      if (const auto *BI = dyn_cast<Instruction>(base))
        otherKind = std::string("object from a ") + BI->getOpcodeName();
      else if (isa<Argument>(base))
        otherKind = "object from an argument (not tracked)";
      else
        otherKind = "object from a constant";
    }
    if (!otherKind.empty()) {
      A.stops.insert(otherKind);
      return A;
    }
    if (pi < 0) {
      stop = reloadTested(I, base, S, embed)  ? "reload of a tested slot"
             : isa<LoadInst>(base)            ? "object loaded from memory"
             : isa<CallBase>(base)            ? "object returned by a call"
             : isa<GlobalVariable>(base)      ? "global object"
             : isa<AllocaInst>(base)          ? "stack object"
                                              : "other object";
    } else if (depth == 0) {
      stop = "caller depth";
    } else if (F->hasAddressTaken()) {
      // Dispatch is the check (plan 3.30): F runs only through
      // `p->f(p, ...)` with p at argument pi, its address stored only in
      // callback field f of S: inside F, p->f == F (C++: `this` in D::f is
      // a D). Direct calls of F add their callers' facts.
      std::vector<const CallBase *> direct;
      std::string why;
      std::set<uint64_t> heldIn;
      if (!curCbFields.empty() &&
          onlyDispatched(F->getName().str(), S, curCbFields, direct) &&
          dispatchArg(S, curCbFields, why) == pi) {
        for (const User *Us : F->users())
          if (const auto *SI = dyn_cast<StoreInst>(Us)) {
            const Pos T = position(SI->getPointerOperand(), SI->getModule()->getDataLayout());
            if (T.ok) heldIn.insert((uint64_t)fieldAt(T.S, T.off));
          }
      }
      if (heldIn.size() == 1) {
        Fact g{*heldIn.begin(), FK::FN, fnId(F->getName().str())};
        g.from = &*F->getEntryBlock().begin();
        g.usable = factUsable(g, I, S, uoff, below, W);
        if (g.usable) {
          std::vector<Fact> fs = facts;
          fs.push_back(g);
          Admit D = admitUnder(fs);
          dispatchFacts++;
          if (direct.empty()) return D;
          // Other ways in: the direct callers' facts, unioned in.
          below.push_back(I);
          for (const CallBase *CB : direct) {
            if (depth == 0 || pi >= (int)CB->arg_size()) {
              // A way in we cannot follow: the dispatch fact alone would
              // be unsound; fall back to what holds without it.
              A.stops.insert("direct call of a callback");
              return A;
            }
            const Admit c = admittedFor(CB, resolveBase(CB->getArgOperand(pi)), embed, S,
                                        uoff, W, facts, below, depth - 1);
            D.members.insert(c.members.begin(), c.members.end());
            D.tagUnknown.insert(c.tagUnknown.begin(), c.tagUnknown.end());
            D.stops.insert(c.stops.begin(), c.stops.end());
          }
          return D;
        }
      }
      stop = "indirect call (address taken)";
    } else if (callers.empty()) {
      stop = "no caller";
    } else if (callers.size() > kCallers) {
      stop = "caller fan-out";
    }
    if (stop) {
      A.stops.insert(stop);
      return A;
    }
    Admit R;
    below.push_back(I);
    for (const CallBase *CB : callers) {
      const Admit c = admittedFor(CB, resolveBase(CB->getArgOperand(pi)), embed, S,
                                  uoff, W, facts, below, depth - 1);
      R.members.insert(c.members.begin(), c.members.end());
      R.facts |= c.facts;
      R.unstable |= c.unstable;
      R.tagUnknown.insert(c.tagUnknown.begin(), c.tagUnknown.end());
      R.stops.insert(c.stops.begin(), c.stops.end());
    }
    return R;
  };
  size_t totLayout = 0, totShared = 0; // accesses typed by member layout; of a shared field
  for (const UnionField *U : touched) {
    nUnions++;
    auto &W = writes[U];
    auto &Rd = reads[U];
    std::set<std::string> realMembers;
    size_t typedW = 0, typedR = 0, nInit = 0, nVia = 0, layoutW = 0, layoutR = 0, sharedW = 0, sharedR = 0;
    for (auto &s : W) {
      typedW += real(s.member);
      layoutW += s.byLayout, sharedW += s.shared;
      nInit += s.GV != nullptr;
      if (real(s.member)) realMembers.insert(s.member);
    }
    for (auto &s : Rd) {
      typedR += real(s.member);
      layoutR += s.byLayout, sharedR += s.shared;
      if (real(s.member)) realMembers.insert(s.member);
    }
    // Candidate fields: co-written at some union write site.
    std::map<uint64_t, size_t> cover, coverVia;
    std::map<uint64_t, std::map<std::string, std::set<std::string>>> fd; // f -> value -> members
    std::set<uint64_t> cands;
    for (auto &s : W)
      for (auto &[f, vs] : s.co) {
        if (f >= U->off && f < U->off + U->size)
          continue; // the union itself
        bool any = false;
        for (auto &v : vs)
          if (known(v)) {
            fd[f][v].insert(s.member);
            any = true;
          }
        if (any) cands.insert(f);
      }
    // A write is covered by f when f is co-written with it, or when a test
    // of f dominates it (the member written agrees with the tag already
    // there: `if (!ExprUseXSelect(p)) p->x.pList = ...`).
    std::map<uint64_t, size_t> coverGuard;
    for (uint64_t f : cands)
      for (auto &s : W) {
        auto cit = s.co.find(f);
        if (cit != s.co.end() && std::any_of(cit->second.begin(), cit->second.end(), known)) {
          cover[f]++;
          coverVia[f] += s.viaCall;
        } else if (s.I && guardedBy(s.I, s.base, s.embed, U->structName, f, 2)) {
          cover[f]++;
          coverGuard[f]++;
        }
      }
    // Reads guarded by a test of field f (here, or at every call site).
    auto guardCount = [&](uint64_t f, size_t *via) {
      size_t g = 0;
      for (auto &s : Rd) {
        if (guardedHere(s.I, U->structName, f, s.base, s.embed))
          g++;
        else if (guardedBy(s.I, s.base, s.embed, U->structName, f, 2)) {
          g++;
          if (via) (*via)++;
        }
      }
      return g;
    };
    // Best candidate: most accesses explained (writes covered + reads
    // guarded), then a functional dependency.
    int64_t best = -1;
    size_t bestScore = 0, bestCov = 0;
    bool bestFD = false;
    for (auto &[f, c] : cover) {
      bool ok = true;
      for (auto &[v, ms] : fd[f]) {
        size_t nreal = 0;
        for (auto &m : ms) nreal += real(m);
        if (nreal > 1) ok = false;
      }
      const size_t score = c + guardCount(f, nullptr);
      if (score > bestScore || (score == bestScore && ok && !bestFD)) {
        best = (int64_t)f;
        bestScore = score;
        bestCov = c;
        bestFD = ok;
      }
    }
    size_t nGuardW = 0;
    if (best >= 0) {
      nVia = coverVia[(uint64_t)best];
      nGuardW = coverGuard[(uint64_t)best];
    }
    // Callback side. Per member: the functions its writers pair with it,
    // stored in the object's function fields or held by a co-written ops
    // table. A callback reader of member m must be one of m's; a function
    // paired with two members breaks the dependency.
    std::map<std::string, std::set<std::string>> cbOf;
    std::map<std::string, std::set<std::string>> memberOfCb;
    size_t writesWithCb = 0;
    for (auto &s : W) {
      std::set<std::string> fns;
      for (auto &[f, vs] : s.co) {
        if (f >= U->off && f < U->off + U->size)
          continue;
        for (auto &v : vs)
          if (v.rfind("fn:", 0) == 0)
            fns.insert(v.substr(3));
          else if (v.rfind("gv:", 0) == 0) {
            auto git = fnsInGV.find(v.substr(3));
            if (git != fnsInGV.end()) fns.insert(git->second.begin(), git->second.end());
          }
      }
      writesWithCb += !fns.empty();
      for (auto &fn : fns) {
        cbOf[s.member].insert(fn);
        if (real(s.member)) memberOfCb[fn].insert(s.member);
      }
    }
    std::set<std::string> readers;
    for (auto &s : Rd) readers.insert(s.I->getFunction()->getName().str());
    bool cbFD = true;
    for (auto &[fn, ms] : memberOfCb)
      if (ms.size() > 1 && readers.count(fn)) {
        cbFD = false;
        if (detailed(U)) {
          errs() << "UnionCensus:   callback " << fn << " paired with members";
          for (auto &m : ms) errs() << " " << m;
          errs() << "\n";
          for (auto &s : W)
            if (s.I)
              for (auto &[f, vs] : s.co)
                if (vs.count("fn:" + fn))
                  errs() << "UnionCensus:     write " << s.member << " at " << locOf(s.I)
                         << (s.viaCall ? " (via call)" : "") << "\n";
        }
      }
    for (auto &[m, fs] : cbOf) calleeClosure(fs);
    std::set<std::string> allCb;
    for (auto &[m, fs] : cbOf) allCb.insert(fs.begin(), fs.end());
    // The other half of the pairing (review of 3.17): a callback field
    // written where the union is not installs a callback that runs on
    // whatever member the object holds. Such a write governs the union
    // reads inside the callback it installs (and its callees); an unknown
    // value governs every read. Governed reads lose the callback key; a
    // write installing null, or a callback that reads no union, is harmless.
    std::set<uint64_t> cbFields;
    for (auto &s : W)
      for (auto &[f, vs] : s.co) {
        if (f >= U->off && f < U->off + U->size)
          continue;
        for (auto &v : vs)
          if (v.rfind("fn:", 0) == 0 ||
              (v.rfind("gv:", 0) == 0 && fnsInGV.count(v.substr(3))))
            cbFields.insert(f);
      }
    curCbFields = cbFields;
    size_t unpairedCb = 0, unpairedGov = 0;
    bool governsAll = false;
    std::set<std::string> governed; // reader functions that lose the key
    for (uint64_t f : cbFields) {
      auto wit = writersOf.find({U->structName, f});
      if (wit == writersOf.end())
        continue;
      for (const ObjKey &K : wit->second) {
        if (unionCtx[U].count(K))
          continue;
        unpairedCb++;
        std::set<std::string> fns;
        bool unknown = false;
        for (auto &v : coWrites[K][f]) {
          if (v.rfind("fn:", 0) == 0)
            fns.insert(v.substr(3));
          else if (v.rfind("gv:", 0) == 0) {
            auto git = fnsInGV.find(v.substr(3));
            if (git != fnsInGV.end()) fns.insert(git->second.begin(), git->second.end());
          } else if (v != "null" && v != "int:0")
            unknown = true;
        }
        calleeClosure(fns);
        bool gov = unknown;
        for (auto &fn : fns)
          if (readers.count(fn)) {
            governed.insert(fn);
            gov = true;
          }
        if (unknown) governsAll = true;
        unpairedGov += gov;
        if (detailed(U)) {
          errs() << "UnionCensus:   unpaired callback write @" << f << " in "
                 << std::get<0>(K)->getName() << ":";
          for (auto &v : coWrites[K][f]) errs() << " " << v;
          errs() << (gov ? "  (governs reads)" : "") << "\n";
        }
      }
    }
    if (governsAll)
      governed = readers;
    if (detailed(U) && best >= 0)
      for (auto &s : W)
        if (!s.co.count((uint64_t)best) &&
            !(s.I && guardedBy(s.I, s.base, s.embed, U->structName, (uint64_t)best, 2)))
          errs() << "UnionCensus:   uncovered write " << s.member << " at "
                 << (s.I ? locOf(s.I) : "init " + s.GV->getName().str()) << "\n";
    stable.clear();
    stableU = U;
    outsideVals.clear();
    outsideDone.clear();
    for (uint64_t f : cands) {
      auto wit = writersOf.find({U->structName, f});
      if (wit == writersOf.end())
        continue;
      bool ok = true;
      for (const ObjKey &K : wit->second)
        if (!unionCtx[U].count(K)) { ok = false; break; }
      if (ok) stable.insert(f);
    }
    size_t guarded = 0, inCallback = 0, guardedVia = 0, lowBit = 0;
    size_t nVer = 0, nContra = 0;
    std::vector<const Instruction *> unguarded, contra;
    for (auto &s : Rd) {
      detailU = detailed(U) ? U : nullptr;
      const RV kr = keyRead(s.I, s.base, s.embed, U->structName, s.member, W, {}, 2);
      detailU = nullptr;
      nVer += kr == RV::VER;
      if (kr == RV::CONTRA) {
        nContra++;
        if (contra.size() < 3) contra.push_back(s.I);
      }
      lowBit += lowBitTagged(s.I);
      const std::string rn = s.I->getFunction()->getName().str();
      const bool cb = !governed.count(rn) &&
                      (real(s.member) ? (cbOf.count(s.member) && cbOf[s.member].count(rn))
                                      : allCb.count(rn) != 0);
      bool g = false;
      if (best >= 0) {
        g = guardedHere(s.I, U->structName, (uint64_t)best, s.base, s.embed);
        if (!g && guardedBy(s.I, s.base, s.embed, U->structName, (uint64_t)best, 2)) {
          g = true;
          guardedVia++;
        }
      }
      guarded += g;
      inCallback += cb;
      if (detailed(U) && !g && !cb)
        errs() << "UnionCensus:   untested read " << s.member << " at " << locOf(s.I) << "\n";
      if (!g && !cb && unguarded.size() < 3) unguarded.push_back(s.I);
    }
    // ---- Keys for the solver (--cfl-union-keys, plan 3.17/3.18) ----
    size_t keyedW = 0, keyedR = 0;
    std::string keyNote;
    if (CFLUnionKeys == "tag" && realMembers.size() > 1) {
      // Tag keys (cell solver): a write is keyed by the member it writes
      // (input 1); a read by the rule (admittedFor). An unkeyed read sees
      // every member; an unkeyed write lands where every read sees it.
      const std::string prefix =
          "struct." + U->structName + "+" + std::to_string(U->off);
      // A member declared `void *` (cv-qualified or not) is the program's
      // generic view of the slot (bfd's tdata.any): C makes void *
      // assignment-compatible with every object pointer, so by name it is
      // compatible with every member. Its writes land where every read sees
      // them (the census catch-all, its own key included), and its reads
      // that no check settles read the whole slot (Fable 2026-10-17).
      std::set<std::string> generic;
      for (auto &[nm, tk] : U->members)
        if (tk == "ptr:void") generic.insert(nm);
      for (auto &w : W) {
        if (!w.I) continue; // initializers write the unkeyed side
        // (C'') A one-field copy: its keys travel from the source (the solver's
        // byte copy); it keeps its own keys only for TaggedFields to give it
        // its tag keys, and is no write of an unknown member.
        if (w.copyOf) {
          unionCopyOf[w.I] = w.copyOf;
          std::string st;
          raw_string_ostream os(st);
          w.I->print(os);
          st = StringRef(os.str()).ltrim().str();
          st = st.substr(0, st.find(", !dbg"));
          const Pos WQ = position(cast<StoreInst>(w.I)->getPointerOperand(), w.I->getModule()->getDataLayout());
          unionCopyRows.push_back("ASSUMPTION a copy of union " + U->structName + "." + U->fieldName + "+" +
                                  std::to_string((int64_t)WQ.off - (int64_t)U->off) +
                                  " between two objects keeps the source's member key under the store's own tag keys: " +
                                  w.I->getFunction()->getName().str() + ": " + st);
          unionUnknownOf[w.I] = prefix;
          continue;
        }
        if (real(w.member) && generic.count(w.member)) {
          unionUnknownOf[w.I] = prefix;
          GenericUse &G = genericOf[prefix + "." + w.member];
          G.writes++;
          if (G.at.size() < 6) G.at.push_back(locOf(w.I));
          continue;
        }
        if (real(w.member)) {
          unionKeyNames[w.I] = {prefix + "#" + w.member};
          keyedW++;
          if (!w.embedVia.empty()) {
            std::string st;
            raw_string_ostream os(st);
            w.I->print(os);
            st = StringRef(os.str()).ltrim().str();
            st = st.substr(0, st.find(", !dbg"));
            const size_t gt = w.embedVia.find('>');
            unionEmbedTyped.push_back("ASSUMPTION a store over union " + U->structName + "." + U->fieldName +
                                      " typed member " + w.member + " by its value's type " + w.embedVia.substr(0, gt) +
                                      " *, which embeds " + w.embedVia.substr(gt + 1) + " at offset 0: " +
                                      w.I->getFunction()->getName().str() + ": " + st);
          }
          if (!w.addrWhy.empty()) {
            std::string st;
            raw_string_ostream os(st);
            w.I->print(os);
            st = StringRef(os.str()).ltrim().str();
            st = st.substr(0, st.find(", !dbg"));
            unionAddrTyped.push_back("ASSUMPTION a store over union " + U->structName + "." + U->fieldName +
                                     " typed as member " + w.member + " by its value's debug type (" + w.addrWhy +
                                     "): " + w.I->getFunction()->getName().str() + ": " + st);
          }
        } else {
          unionUnknownOf[w.I] = prefix;
          if (!pointerless(w)) {
            Unkeyed &K = unkeyedOf[prefix];
            K.writes++;
            if (K.at.size() < 6) {
              std::string d = "write " + locOf(w.I) + " (member unknown";
              auto cit = best >= 0 ? w.co.find((uint64_t)best) : w.co.end();
              if (cit != w.co.end()) {
                d += "; tag @" + std::to_string(best) + " =";
                for (const std::string &v : cit->second) d += " " + v;
              }
              K.at.push_back(d + ")");
            }
          }
        }
      }
      for (auto &r : Rd) {
        // A read that cannot carry a pointer (a narrow integer, a float)
        // needs no key: no pointer flows through it.
        if (const auto *LI = dyn_cast_or_null<LoadInst>(r.I)) {
          Type *T = LI->getType();
          if (T->isFloatingPointTy() ||
              (T->isIntegerTy() && T->getIntegerBitWidth() <
                                       LI->getModule()->getDataLayout().getPointerSizeInBits())) {
            pointerlessReads++;
            continue;
          }
        }
        const Admit A = admittedFor(r.I, r.base, r.embed, U->structName, U->off, W,
                                    {}, {}, 2);
        if (A.members.size() <= 1) {
          // One member (or none: only unkeyed writes reach it).
          const std::string k = A.members.empty() ? "-" : *A.members.begin();
          unionKeyNames[r.I] = {prefix + "#" + k};
          keyedR++;
          // A contradiction: the read's member has typed writes and the
          // facts exclude every one (writes of unknown member are in U).
          const bool ownTyped = real(r.member) &&
              std::any_of(W.begin(), W.end(), [&](const Site &w) {
                return w.member == r.member && !pointerless(w);
              });
          if (ownTyped && k != r.member && !generic.count(r.member)) {
            readContra++; // reads a member its facts rule out
            errs() << "UnionKeys: read of " << r.member << " at " << locOf(r.I)
                   << ": its facts admit only " << k << "\n";
            // Explain: the usable facts, and each own-member write's verdict.
            std::vector<Fact> fs;
            for (const Fact &g : factsHere(r.I, U->structName, r.base, r.embed)) fs.push_back(g);
            const char *kn[] = {"==", "!=", "bits-set", "bits-clear", "<u", ">=u", "== fn#"};
            for (const Fact &g : fs)
              errs() << "UnionKeys:     fact @" << g.f << " " << kn[(int)g.k] << " " << g.c
                     << (factStable(g) ? " (stable)" : "")
                     << (factUsable(g, r.I, U->structName, U->off, {}, W) ? " (usable)" : "")
                     << "\n";
            for (const Site &w : W) {
              if (w.member != r.member || pointerless(w)) continue;
              errs() << "UnionKeys:     write " << w.member << " at "
                     << (w.I ? locOf(w.I) : "init") << ":";
              for (const Fact &g : fs) {
                const Res e = evalFact(w.co, g);
                errs() << " @" << g.f << "=" << (e == Res::SAT ? "SAT" : e == Res::VIOL ? "VIOL" : "UNK");
                auto it = w.co.find(g.f);
                if (it != w.co.end()) {
                  errs() << "{";
                  for (auto &v : it->second) errs() << v << ",";
                  errs() << "}";
                }
              }
              errs() << "\n";
            }
          }
          continue;
        }
        // Which input failed: no facts (3); writes of unknown tag (2); or
        // the facts admit several members.
        const char *why = !A.facts ? (A.unstable ? "tests of an unstable field"
                                                 : "no tag test")
                          : !A.tagUnknown.empty() ? "writes of unknown tag"
                                                  : "facts admit several members";
        // The access states the developer's expectation (user, 2026-10-07):
        // a read of a known member with no check that settles it is keyed by
        // that member, taken as correct, and warned for review of the
        // source; another member reaching it would be a potential bug.
        if (real(r.member) && generic.count(r.member)) {
          unionUnknownOf[r.I] = prefix; // the generic view: every member
          genericOf[prefix + "." + r.member].reads++;
          continue;
        }
        if (real(r.member)) {
          unionKeyNames[r.I] = {prefix + "#" + r.member};
          keyedR++;
          uncheckedBy[why]++;
          uncheckedReads[r.I] = prefix + "#" + r.member;
          std::string others;
          for (const std::string &m : A.members)
            if (m != r.member) others += (others.empty() ? "" : " ") + m;
          errs() << "UnionKeys: UNCHECKED read of " << r.member << " at " << locOf(r.I)
                 << " (" << why << "); other members it would admit: {" << others << "}"
                 << (A.members.count(r.member) ? "" : " (none of its own member's writes admitted)")
                 << "\n";
          continue;
        }
        unionUnknownOf[r.I] = prefix;
        Unkeyed &K = unkeyedOf[prefix];
        K.readsBy[why]++;
        if (A.facts && !A.tagUnknown.empty())
          for (const Instruction *X : A.tagUnknown) blockingWrites[prefix + " " + locOf(X)]++;
        if (!A.facts && !A.unstable) {
          std::string st;
          for (const std::string &x : A.stops) st += (st.empty() ? "" : " + ") + x;
          untestedBy[st.empty() ? "?" : st]++;
          untestedByUnion[prefix][st.empty() ? "?" : st]++;
        }
        if (K.at.size() < 6) {
          std::string d = std::string("read ") + locOf(r.I) + " (" + why;
          if (!A.tagUnknown.empty()) d += ": " + locOf(*A.tagUnknown.begin());
          d += "; {";
          for (const std::string &m : A.members) d += m + " ";
          K.at.push_back(d.substr(0, d.size() - 1) + "})");
        }
      }
      for (const std::string &g : generic) {
        auto git = genericOf.find(prefix + "." + g);
        if (git == genericOf.end() || !git->second.writes) continue;
        for (auto &r : Rd) {
          auto kit = unionKeyNames.find(r.I);
          if (kit == unionKeyNames.end() || kit->second.size() != 1 || kit->second[0] == prefix + "#-" ||
              kit->second[0] == prefix + "#" + g)
            continue;
          git->second.othersSee++;
          git->second.seenBy[r.member]++;
          if (uncheckedReads.count(r.I)) git->second.othersUnchecked++;
        }
      }
      cellUnionSlots.insert({U->structName, U->off, U->size});
    } else if (CFLUnionKeys != "off" && realMembers.size() > 1)
      keyUnion(U, W, Rd, cbFields, governed, governsAll, keyedW, keyedR, keyNote);
    std::string verdict;
    const bool allW = best >= 0 && bestCov == W.size() && bestFD;
    if (realMembers.empty()) {
      // No access typed by member: nothing says one member is used (Fable
      // 2026-10-16); every access is one plane.
      verdict = "no typed access (keyed all)";
      nUntyped++;
    } else if (realMembers.size() == 1) {
      verdict = "one member used";
      nSingle++;
    } else if (writesWithCb == W.size() && cbFD && inCallback == Rd.size()) {
      verdict = "CALLBACK-keyable";
      nCallback++;
    } else if (!Rd.empty() && nVer == Rd.size()) {
      verdict = "TAG-verified";
      nTagVer++;
    } else if (allW && guarded == Rd.size()) {
      verdict = "TAG-tested";
      nTag++;
    } else if (lowBit) {
      verdict = "no discriminator (pointer low-bit tag, " + std::to_string(lowBit) +
                " masked reads)";
      nLowBit++;
      nNone++;
    } else {
      verdict = "no discriminator";
      nNone++;
    }
    std::string t = "UNION " + U->structName + "." + U->fieldName + " (" +
                    std::to_string(U->members.size()) + " members, " +
                    std::to_string(realMembers.size()) + " used): writes " +
                    std::to_string(W.size()) + " (" + std::to_string(typedW) +
                    " typed, " + std::to_string(nInit) + " initializers), reads " +
                    std::to_string(Rd.size()) + " (" + std::to_string(typedR) +
                    " typed); ";
    if (layoutW + layoutR + sharedW + sharedR)
      t += "by member layout (debug info): writes " + std::to_string(layoutW) + ", reads " + std::to_string(layoutR) +
           " typed; a field several members share (not typed): writes " + std::to_string(sharedW) + ", reads " +
           std::to_string(sharedR) + "; ";
    totLayout += layoutW + layoutR, totShared += sharedW + sharedR;
    if (best >= 0) {
      std::string vals;
      size_t nv = 0;
      for (auto &[v, ms] : fd[(uint64_t)best]) {
        if (nv++ == 4) { vals += " ..."; break; }
        vals += (vals.empty() ? "" : " ") + v + "->";
        bool first = true;
        for (auto &m : ms) { vals += (first ? "" : "|") + m; first = false; }
      }
      t += "best field @" + std::to_string(best) + " [" + vals + "]: writes covered " +
           std::to_string(bestCov) + "/" + std::to_string(W.size()) + " (" +
           std::to_string(nVia) + " via calls, " + std::to_string(nGuardW) + " by a test)" +
           (bestFD ? ", value->member OK" : ", value->member BROKEN") +
           ", reads guarded " + std::to_string(guarded) + "/" +
           std::to_string(Rd.size()) + " (" + std::to_string(guardedVia) +
           " at call sites); ";
    } else
      t += "no co-written field; ";
    std::string st;
    for (uint64_t f : stable) st += (st.empty() ? "@" : " @") + std::to_string(f);
    t += "stable fields {" + st + "}; reads keyed by facts " + std::to_string(nVer) + "/" +
         std::to_string(Rd.size()) +
         " (" + std::to_string(nContra) + " contradicted); ";
    // Tag writes elsewhere: contexts writing the best tag field without
    // writing the union.
    size_t unpairedTag = 0;
    if (best >= 0) {
      auto wit = writersOf.find({U->structName, (uint64_t)best});
      if (wit != writersOf.end())
        for (const ObjKey &K : wit->second) unpairedTag += !unionCtx[U].count(K);
    }
    if (best >= 0)
      t += "tag writes without the union " + std::to_string(unpairedTag) + "; ";
    t += "callbacks: writes paired " + std::to_string(writesWithCb) + "/" +
         std::to_string(W.size()) + ", unpaired callback writes " +
         std::to_string(unpairedCb) + " (" + std::to_string(unpairedGov) +
         " govern reads)" + (cbFD ? ", fn->member OK" : ", fn->member BROKEN") +
         ", reads in a paired callback " + std::to_string(inCallback) + "/" +
         std::to_string(Rd.size()) + "; " + verdict;
    if (CFLUnionKeys != "off")
      t += "; keys: writes " + std::to_string(keyedW) + "/" + std::to_string(W.size()) +
           ", reads " + std::to_string(keyedR) + "/" + std::to_string(Rd.size()) +
           (keyNote.empty() ? "" : " (" + keyNote + ")");
    for (const Instruction *I : unguarded)
      t += "\n    unguarded read: " + locOf(I);
    for (const Instruction *I : contra)
      t += "\n    contradicted read: " + locOf(I);
    lines.push_back({W.size() + Rd.size(), t});
    unionFieldNotes["struct." + U->structName][(int64_t)U->off].census =
        "union census: writes " + std::to_string(typedW) + "/" + std::to_string(W.size()) + " and reads " +
        std::to_string(typedR) + "/" + std::to_string(Rd.size()) + " typed by member (" +
        std::to_string(layoutW + layoutR) + " by member layout, " + std::to_string(sharedW + sharedR) +
        " of a field several members share), " +
        (best >= 0 ? "a co-written field @" + std::to_string(best) : std::string("no co-written field")) + "; " +
        verdict +
        (CFLUnionKeys != "off" ? "; keys: writes " + std::to_string(keyedW) + "/" + std::to_string(W.size()) +
                                     ", reads " + std::to_string(keyedR) + "/" + std::to_string(Rd.size())
                               : std::string());
  }
  if (!CFLCensusUnions) {
    errs() << "UnionKeys: " << membersByShape
           << " accesses named by their address shape (storage-type GEP / no-op bitcast)\n";
    errs() << "UnionKeys: " << unionKeyNames.size() << " union accesses keyed ("
           << CFLUnionKeys << "); " << pointerlessReads
           << " reads carry no pointer (no key); facts usable beyond program-wide stability "
           << factsPathStable << ", by a reload " << factsReload
           << "; writes excluded by a test at the write " << writesByTest
           << "; dispatch facts " << dispatchFacts << "; " << readContra
           << " reads of a member their facts rule out\n";
    {
      size_t n = 0;
      std::string t;
      for (auto &[w, c] : uncheckedBy) { n += c; t += ", " + w + " " + std::to_string(c); }
      errs() << "UnionKeys: " << n << " reads keyed by their own member without a settling "
             << "check (warned, see UNCHECKED lines; before tag keys, net count from the tagged fields)" << t << "\n";
    }
    {
      errs() << "UnionKeys: " << r1Reads << " reads typed through a no-op cast of the loaded value (R1)\n";
      {
        size_t ws = 0, rs = 0;
        for (auto &[k, c] : r2Pairs) ws += c.first, rs += c.second;
        errs() << "UnionKeys: " << ws << " stores and " << rs
               << " reads typed by a declared embedding (R2: a pointer to T fits a field pointing to P, T's member at offset 0):";
        for (auto &[k, c] : r2Pairs)
          errs() << " [" << k.substr(0, k.find('>')) << " embeds " << k.substr(k.find('>') + 1) << "] " << c.first
                 << " stores, " << c.second << " reads;";
        errs() << "\n";
      }
      errs() << "UnionKeys: " << unionCopyOf.size()
             << " one-field union copies keep the source's member keys (C''); left as ordinary stores at -O3 shapes: "
             << unionCopyVector << " vector copies of several fields, " << unionCopyPhi << " phis of loads of the field\n";
      for (const std::string &r : unionCopyRows) errs() << "UnionKeys:   " << r << "\n";
      errs() << "UnionKeys: " << unionAddrTyped.size()
             << " stores typed by a constant address's debug type (C': every object starting at the address fits the one member)\n";
      for (const std::string &r : unionAddrTyped) errs() << "UnionKeys:   " << r << "\n";
      size_t gw = 0, gr = 0;
      for (auto &[g, G] : genericOf) gw += G.writes, gr += G.reads;
      errs() << "UnionKeys: " << genericOf.size()
             << " void* members read and written as any member (writes keyed #? too, reads admit every member): "
             << gw << " writes, " << gr << " reads\n";
      for (auto &[g, G] : genericOf) {
        errs() << "UnionKeys:   " << g << ": " << G.writes << " writes, " << G.reads << " reads; "
               << G.othersSee << " reads keyed by another member see its writes (" << G.othersUnchecked
               << " of them UNCHECKED";
        std::vector<std::pair<size_t, std::string>> by;
        for (auto &[m, c] : G.seenBy) by.push_back({c, m});
        std::sort(by.rbegin(), by.rend());
        for (size_t i = 0; i < by.size(); i++) errs() << (i ? ", " : "; by member: ") << by[i].second << " " << by[i].first;
        errs() << ")";
        for (const std::string &a : G.at) errs() << " [" << a << "]";
        errs() << "\n";
      }
    }
    size_t uw = 0, ur = 0;
    std::map<std::string, size_t> byWhy;
    std::vector<std::pair<size_t, std::string>> top;
    for (auto &[u, K] : unkeyedOf) {
      size_t r = 0;
      for (auto &[why, c] : K.readsBy) { r += c; byWhy[why] += c; }
      uw += K.writes;
      ur += r;
      top.push_back({K.writes + r, u});
    }
    std::sort(top.rbegin(), top.rend());
    std::string bw;
    for (auto &[why, c] : byWhy) bw += ", " + why + " " + std::to_string(c);
    errs() << "UnionKeys: unkeyed (the gap): " << uw
           << " pointer writes of unknown member; " << ur << " reads" << bw
           << "; in " << unkeyedOf.size() << " unions\n";
    errs() << "UnionKeys: path checks that failed, by condition:\n";
    std::vector<std::pair<size_t, std::string>> pf;
    for (auto &[w, e] : pathFails) pf.push_back({e.first, w});
    std::sort(pf.rbegin(), pf.rend());
    for (size_t i = 0; i < pf.size() && i < 20; i++)
      errs() << "UnionKeys:   " << pf[i].first << "  " << pf[i].second << "  e.g. "
             << pathFails[pf[i].second].second << "\n";
    errs() << "UnionKeys: facts broken by tag writes outside the union's writes:\n";
    for (auto &[k, B] : breakers) {
      std::string t;
      for (auto &[v, fs] : B) {
        t += "  " + v + " in";
        for (const std::string &f : fs) t += " " + f;
        t += ";";
      }
      errs() << "UnionKeys:   " << k << ":" << t.substr(0, 400) << "\n";
    }
    {
      std::vector<std::pair<size_t, std::string>> bw2;
      for (auto &[w, c] : blockingWrites) bw2.push_back({c, w});
      std::sort(bw2.rbegin(), bw2.rend());
      errs() << "UnionKeys: union writes of unknown tag, by reads they keep unkeyed:\n";
      for (size_t i = 0; i < bw2.size() && i < 25; i++)
        errs() << "UnionKeys:   " << bw2[i].first << "  " << bw2[i].second << "\n";
    }
    errs() << "UnionKeys: untested reads by where the search stopped:\n";
    for (auto &[st, c] : untestedBy) errs() << "UnionKeys:   " << c << "  " << st << "\n";
    for (auto &[u, m] : untestedByUnion) {
      std::string t;
      for (auto &[st, c] : m) t += "; " + st + " " + std::to_string(c);
      errs() << "UnionKeys:   " << u << t << "\n";
    }
    for (size_t i = 0; i < top.size() && i < 12; i++) {
      const Unkeyed &K = unkeyedOf[top[i].second];
      std::string rb;
      for (auto &[why, c] : K.readsBy) rb += ", " + why + " " + std::to_string(c);
      errs() << "UnionKeys:   " << top[i].second << ": " << K.writes
             << " writes of unknown member" << rb << "\n";
      for (const std::string &a : K.at) errs() << "UnionKeys:     " << a << "\n";
    }
    return;
  }
  std::sort(lines.begin(), lines.end(),
            [](const Line &a, const Line &b) { return a.accesses > b.accesses; });
  errs() << "UnionCensus: " << unions.size() << " union fields in debug info, "
         << nUnions << " accessed (" << accesses << " accesses, " << initWrites
         << " in initializers): " << nUntyped << " with no typed access, " << nSingle << " use one member, " << nTagVer
         << " tag-verified, " << nTag << " tag-tested, " << nCallback << " callback-keyable, " << nNone
         << " with no discriminator (" << nLowBit << " pointer low-bit tags)\n";
  errs() << "UnionCensus: accesses typed by member layout (debug info, plan 3.51 (2)): " << totLayout
         << "; of a field several members share (not typed): " << totShared << "\n";
  errs() << "UnionCensus: addresses through an anonymous struct: " << anonPosNamed.size()
         << " positioned by the base pointer's declared struct and offset, " << anonPosNone.size()
         << " with none (no position)\n";
  for (auto &L : lines)
    errs() << "UnionCensus: " << L.text << "\n";
}
