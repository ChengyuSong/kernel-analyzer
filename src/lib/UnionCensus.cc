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
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Operator.h>
#include <map>
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
};

SmallVector<DbgValueInst *, 2> dbgValuesOf(const Value *V) {
  SmallVector<DbgValueInst *, 2> out;
  findDbgValues(out, const_cast<Value *>(V));
  return out;
}

std::string stripSuffix(StringRef N) {
  N.consume_front("struct.");
  N.consume_front("union.");
  size_t dot = N.rfind('.');
  if (dot != StringRef::npos && dot > 0 &&
      N.substr(dot + 1).find_first_not_of("0123456789") == StringRef::npos)
    N = N.substr(0, dot);
  return N.str();
}

} // namespace

void CallGraphPass::runUnionCensus() {
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
        for (const DINode *UE : UT->getElements())
          if (const auto *UM = dyn_cast<DIDerivedType>(UE))
            U.members.emplace_back(UM->getName().str(), typeKey(UM->getBaseType()));
      }
    }
  }
  for (auto &[S, fs] : fieldsOf) {
    std::sort(fs.begin(), fs.end());
    fs.erase(std::unique(fs.begin(), fs.end()), fs.end());
  }

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
  auto position = [&](const Value *P, const DataLayout &DL) {
    Pos R;
    std::vector<const GEPOperator *> chain;
    P = P->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(P)) {
      chain.push_back(G);
      P = G->getPointerOperand()->stripPointerCasts();
    }
    if (chain.empty())
      return R;
    const auto *ST = dyn_cast<StructType>(chain.back()->getSourceElementType());
    if (!ST || !ST->hasName())
      return R;
    int64_t total = 0;
    for (const GEPOperator *G : chain) {
      APInt O(DL.getIndexTypeSizeInBits(G->getType()), 0);
      if (!G->accumulateConstantOffset(DL, O))
        return R; // a variable index: not a fixed position
      total += O.getSExtValue();
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
    // A call's result: the callee's declared return type.
    if (const auto *CB = dyn_cast<CallBase>(V))
      if (const Function *T = CB->getCalledFunction())
        if (const DISubprogram *SP = getFuncDef(const_cast<Function *>(T))->getSubprogram())
          if (auto *STy = SP->getType())
            if (STy->getTypeArray().size() > 0)
              return typeKey(STy->getTypeArray()[0]);
    // A value loaded from a struct field: the field's declared type.
    if (const auto *LI = dyn_cast<LoadInst>(V)) {
      const Pos Q = position(LI->getPointerOperand(), LI->getModule()->getDataLayout());
      if (Q.ok && !unionAt(Q)) {
        auto it = fieldType.find({Q.S, Q.off});
        if (it != fieldType.end())
          return it->second;
      }
    }
    return "?";
  };
  // What a read is used as: the variable it is stored into, or its
  // debug value, or the struct its GEP users index it as.
  auto readKey = [&](const LoadInst *LI) -> std::string {
    for (auto *DVI : dbgValuesOf(LI))
      if (auto *Var = DVI->getVariable())
        return typeKey(Var->getType());
    for (const User *U : LI->users()) {
      if (const auto *SI = dyn_cast<StoreInst>(U))
        if (SI->getValueOperand() == LI)
          if (const auto *A = dyn_cast<AllocaInst>(SI->getPointerOperand()->stripPointerCasts()))
            for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(A)))
              if (auto *Var = DDI->getVariable())
                return typeKey(Var->getType());
      if (const auto *G = dyn_cast<GetElementPtrInst>(U))
        if (G->getPointerOperand() == LI)
          if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
            if (ST->hasName())
              return "ptr:" + stripSuffix(ST->getName());
      if (const auto *CB = dyn_cast<CallBase>(U)) {
        if (CB->getCalledOperand() == LI)
          return "fnptr";
        // Passed to a call: the callee's declared parameter type.
        if (const Function *T = CB->getCalledFunction())
          if (const DISubprogram *SP = getFuncDef(const_cast<Function *>(T))->getSubprogram())
            if (auto *STy = SP->getType())
              for (unsigned j = 0; j < CB->arg_size(); j++)
                if (CB->getArgOperand(j) == LI && j + 1 < STy->getTypeArray().size())
                  return typeKey(STy->getTypeArray()[j + 1]);
      }
    }
    return "?";
  };
  auto memberOf = [&](const UnionField &U, const std::string &key) {
    std::vector<std::string> hits;
    for (auto &[nm, tk] : U.members)
      if (tk == key)
        hits.push_back(nm);
    if (hits.size() == 1)
      return hits[0];
    if (hits.empty())
      return std::string("?");
    return std::string("ambiguous");
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
          for (auto &v : in)
            out.insert(v.rfind("int:", 0) == 0
                           ? "int:" + std::to_string(std::stoll(v.substr(4)) &
                                                     (int64_t)M->getZExtValue())
                           : v);
          return;
        }
    if (const Argument *A = scalarParam(V)) {
      const Function *F = A->getParent();
      auto &callers = callersOf[F];
      if (depth > 0 && !F->hasAddressTaken() && !callers.empty() &&
          callers.size() <= kCallers) {
        for (const CallBase *CB : callers)
          scalarValues(CB->getArgOperand(A->getArgNo()), depth - 1, out);
        return;
      }
    }
    out.insert("?");
  };
  auto scalarValues = [&](const Value *V, int depth, std::set<std::string> &out) {
    SmallPtrSet<const Value *, 16> seen;
    scalarValuesIn(V, depth, out, seen);
  };
  // A field's value set: field offset -> tag values. Besides constants:
  // "set:C" (`f |= C`), "clr:C" (`f &= ~C`), "?" (a value not known).
  using CoSet = std::map<uint64_t, std::set<std::string>>;
  auto known = [](const std::string &v) {
    return v != "?" && v != "or:?" && v != "and:?" && v.rfind("clr:", 0) != 0;
  };
  struct Site {
    const Instruction *I = nullptr;      // or a global initializer:
    const GlobalVariable *GV = nullptr;
    std::string member;
    const Value *base = nullptr;
    uint64_t embed = 0;
    CoSet co;          // tag candidates written to the same object
    bool viaCall = false;
  };
  std::map<const UnionField *, std::vector<Site>> writes, reads;
  // Co-writes into the same object: (function, base, embed, struct) ->
  // stores of a constant / function / global / flag bit into a field.
  using ObjKey = std::tuple<const Function *, const Value *, uint64_t, std::string>;
  std::map<ObjKey, CoSet> coWrites;
  // Loads of each (struct, field): where callback fields are read.
  std::map<std::pair<std::string, uint64_t>, std::vector<const LoadInst *>> loadsAt;
  size_t accesses = 0;
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M)
      for (Instruction &I : instructions(F)) {
        // A zeroing memset of a struct writes 0 to every field it covers
        // (`memset(&w, 0, sizeof(w))` before a walker sets its callbacks).
        if (const auto *MS = dyn_cast<MemSetInst>(&I)) {
          const auto *Z = dyn_cast<ConstantInt>(MS->getValue());
          const auto *Len = dyn_cast<ConstantInt>(MS->getLength());
          const auto *A = dyn_cast<AllocaInst>(MS->getDest()->stripPointerCasts());
          if (Z && Z->isZero() && Len && A)
            if (const auto *ST = dyn_cast<StructType>(A->getAllocatedType()))
              if (ST->hasName()) {
                const std::string S = stripSuffix(ST->getName());
                auto fit = fieldsOf.find(S);
                if (fit != fieldsOf.end())
                  for (auto &[o, sz] : fit->second)
                    if (o + sz <= Len->getZExtValue())
                      coWrites[{&F, A, 0, S}][o].insert("int:0");
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
              // `f |= x`: may set any bit, clears none; `f &= x` the reverse.
              vals.insert(BO->getOpcode() == Instruction::Or ? "or:?" : "and:?");
            } else if (V->getType()->isIntegerTy()) {
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
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          s.member = memberOf(*U, valueKey(SI->getValueOperand(), 0));
          writes[U].push_back(s);
        } else {
          s.member = memberOf(*U, readKey(cast<LoadInst>(&I)));
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
          s.member = memberOf(*U, valueKey(C, 0));
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
  enum class FK { EQ, NE, BSET, BCLR };
  struct Fact { uint64_t f; FK k; uint64_t c; };
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
    if (!IC || !IC->isEquality())
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
          if (DT.dominates(BasicBlockEdge(NB, BI->getSuccessor(k)), BB))
            condFacts(BI->getCondition(), k == 0, S, base, embed, out);
      } else if (const auto *SW = dyn_cast<SwitchInst>(T)) {
        uint64_t f;
        unsigned sh;
        if (!fieldLoad(SW->getCondition(), S, base, embed, f, sh) || sh != 0)
          continue;
        for (auto &Case : SW->cases()) {
          const BasicBlock *Succ = Case.getCaseSuccessor();
          if (Succ == SW->getDefaultDest())
            continue;
          if (DT.dominates(BasicBlockEdge(NB, Succ), BB))
            out.push_back({f, FK::EQ, Case.getCaseValue()->getZExtValue()});
        }
      }
    }
    return out;
  };
  // Does a write's tag knowledge satisfy, violate, or leave open a fact?
  enum class Res { SAT, VIOL, UNK };
  auto evalFact = [](const CoSet &co, const Fact &g) -> Res {
    auto it = co.find(g.f);
    if (it == co.end())
      return Res::UNK;
    bool unk = false, nz = false, orUnk = false, andUnk = false;
    std::vector<uint64_t> exact;
    uint64_t sets = 0, clrs = 0;
    for (auto &v : it->second) {
      if (v == "?") unk = true;
      else if (v == "or:?") orUnk = true;
      else if (v == "and:?") andUnk = true;
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
      if (unk || sets || clrs || orUnk || andUnk) return Res::UNK;
      std::vector<Res> rs;
      for (uint64_t n : exact) rs.push_back(n == c ? Res::SAT : Res::VIOL);
      if (nz) rs.push_back(c == 0 ? Res::VIOL : Res::UNK);
      return all(rs);
    };
    // Set bits are taken as the field's final state (the census does not
    // order the writes of one function).
    // An unknown `|=` can only add bits (never undoes SAT); an unknown
    // `&=` can only remove them (never undoes VIOL).
    auto bsetRes = [&](uint64_t m) {
      if ((sets & m) && !(clrs & m) && !andUnk) return Res::SAT;
      if (unk || nz) return Res::UNK;
      Res r = Res::UNK;
      if (!exact.empty()) {
        std::vector<Res> rs;
        for (uint64_t n : exact) rs.push_back((n & m) ? Res::SAT : Res::VIOL);
        r = all(rs);
        if (r == Res::VIOL && ((sets & m) || orUnk)) return Res::UNK;
        if (r == Res::SAT && ((clrs & m) || andUnk)) return Res::UNK;
        return r;
      }
      if ((clrs & m) == m && !(sets & m) && !orUnk) return Res::VIOL;
      return r;
    };
    switch (g.k) {
    case FK::EQ: return eqRes(g.c);
    case FK::NE: return inv(eqRes(g.c));
    case FK::BSET: return bsetRes(g.c);
    case FK::BCLR: return inv(bsetRes(g.c));
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
    if (g.k != FK::BSET && g.k != FK::BCLR)
      return false;
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
    for (const std::string &v : outsideVals[g.f]) {
      if (v.rfind("set:", 0) != 0 && v.rfind("clr:", 0) != 0)
        return false;
      if (std::stoull(v.substr(4)) & g.c)
        return false;
    }
    return true;
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
        const char *kn[] = {"==", "!=", "bits-set", "bits-clear"};
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
    note = "dispatch arg " + std::to_string(kS) + ", " + std::to_string(stored.size()) +
           " callbacks (" + std::to_string(badCb) + " not only dispatched), " +
           std::to_string(partial) + " writes with a callback field unset in context";
  };

  size_t nUnions = 0, nTag = 0, nTagVer = 0, nCallback = 0, nNone = 0, nSingle = 0,
         nLowBit = 0;
  struct Line { size_t accesses; std::string text; };
  std::vector<Line> lines;
  std::set<const UnionField *> touched;
  for (auto &[U, _] : writes) touched.insert(U);
  for (auto &[U, _] : reads) touched.insert(U);
  auto real = [](const std::string &m) { return m != "?" && m != "ambiguous"; };
  for (const UnionField *U : touched) {
    nUnions++;
    auto &W = writes[U];
    auto &Rd = reads[U];
    std::set<std::string> realMembers;
    size_t typedW = 0, typedR = 0, nInit = 0, nVia = 0;
    for (auto &s : W) {
      typedW += real(s.member);
      nInit += s.GV != nullptr;
      if (real(s.member)) realMembers.insert(s.member);
    }
    for (auto &s : Rd) {
      typedR += real(s.member);
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
    if (CFLUnionKeys != "off" && realMembers.size() > 1)
      keyUnion(U, W, Rd, cbFields, governed, governsAll, keyedW, keyedR, keyNote);
    std::string verdict;
    const bool allW = best >= 0 && bestCov == W.size() && bestFD;
    if (realMembers.size() <= 1) {
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
  }
  if (!CFLCensusUnions) {
    errs() << "UnionKeys: " << unionKeyNames.size() << " union accesses keyed ("
           << CFLUnionKeys << ")\n";
    return;
  }
  std::sort(lines.begin(), lines.end(),
            [](const Line &a, const Line &b) { return a.accesses > b.accesses; });
  errs() << "UnionCensus: " << unions.size() << " union fields in debug info, "
         << nUnions << " accessed (" << accesses << " accesses, " << initWrites
         << " in initializers): " << nSingle << " use one member, " << nTagVer
         << " tag-verified, " << nTag << " tag-tested, " << nCallback << " callback-keyable, " << nNone
         << " with no discriminator (" << nLowBit << " pointer low-bit tags)\n";
  for (auto &L : lines)
    errs() << "UnionCensus: " << L.text << "\n";
}
