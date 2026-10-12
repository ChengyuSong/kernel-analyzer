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
// A use outside these refuses the pool, printed with its site. This file
// recognizes and reports (--verbose=2); the effect is not on yet.

#include "CallGraphInternal.h"
#include "NamedCells.h"

namespace {

std::string instLocStr(const Instruction *I) {
  std::string s = I->getFunction()->getName().str();
  if (const DILocation *L = I->getDebugLoc())
    s += " " + L->getFilename().str() + ":" + std::to_string(L->getLine());
  return s;
}

std::string instText(const Instruction *I) {
  std::string s;
  raw_string_ostream os(s);
  I->print(os);
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
  char flavor = 'C';
  std::string field;               // the field it was loaded from ("" for an allocation)
  const CallBase *alloc = nullptr; // the allocation it is (C), in this function
  std::string pool;                // a field of its pool
};

} // namespace

void CallGraphPass::checkPoolCarves() {
  // A field access's key: the debug-info struct of the base pointer (the
  // IR merges isomorphic structs: objalloc and demangler_engine are one IR
  // type), else the IR struct; "" if the access names no struct field.
  std::set<std::string> irFallback;
  auto fieldKey = [&](const Instruction *I, const Value *Addr) -> std::string {
    if (isa<AllocaInst>(Addr->stripPointerCasts())) return "";
    StructType *S = nullptr;
    int64_t off = 0;
    if (!accessSlot(I, Addr, I->getModule()->getDataLayout(), S, off)) return "";
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

  // Does V come from an allocation (through casts, GEPs, local slots)?
  std::function<bool(const Value *, int)> fromAlloc = [&](const Value *V, int d) -> bool {
    if (d > 8) return false;
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

  std::set<std::string> handleFields, bumpFields, baseFields; // baseFields: counter carves' M
  // A pool's bump or base field is refilled with an allocation (a chunk)
  // somewhere; a bumped field never refilled is a cursor over data.
  std::set<std::string> refilled;
  size_t cursors = 0;
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
    if (ra != rb) parent[rb] = ra;
  };

  struct Carve { const Instruction *I; std::string form, field; };
  struct Refusal { std::string field, why; const Instruction *I; };
  std::vector<Carve> carves;
  std::vector<Refusal> refusals;
  std::vector<std::pair<const Instruction *, std::string>> rewinds;

  // Bumps and counter decrements, per function; counter carves name M.
  std::map<const Function *, std::set<std::string>> bumpIn, counterIn;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M) {
      if (F.isDeclaration()) continue;
      for (const Instruction &I : instructions(F)) {
        const auto *SI = dyn_cast<StoreInst>(&I);
        if (!SI) continue;
        const std::string k = fieldKey(SI, SI->getPointerOperand());
        if (k.empty()) continue;
        const Value *V = SI->getValueOperand();
        if (V->getType()->isPointerTy() && fromAlloc(V, 0)) refilled.insert(k);
        if (V->getType()->isPointerTy()) {
          const auto *G = dyn_cast<GEPOperator>(V->stripPointerCasts());
          if (G && !G->hasAllZeroIndices() && loadsField(G->getPointerOperand(), k, 0)) {
            bumpIn[&F].insert(k);
            bumpFields.insert(k);
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
  // Counter carves: gep (load M), C with C decremented here (its reload,
  // or the decremented value itself at -O3).
  auto counterCarve = [&](const GEPOperator *G, const Function *F) -> std::string {
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
    return m;
  };
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      if (!F.isDeclaration())
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

  // To a fixpoint over the handle fields; the last round records.
  for (;;) {
    const size_t before = handleFields.size();
    carves.clear();
    refusals.clear();
    rewinds.clear();
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (F.isDeclaration()) continue;
        std::map<const Value *, HV> hv;
        std::vector<const Value *> work;
        auto add = [&](const Value *V, const HV &h) {
          if (hv.emplace(V, h).second) work.push_back(V);
        };
        // Allocations stored (through casts, GEPs, local slots) into a
        // handle field are chunk bases.
        std::function<std::string(const Value *, int)> reachesHandle = [&](const Value *V, int d) -> std::string {
          if (d > 8) return "";
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
        for (const Instruction &I : instructions(F)) {
          if (const auto *L = dyn_cast<LoadInst>(&I)) {
            if (!L->getType()->isPointerTy()) continue;
            const std::string k = fieldKey(L, L->getPointerOperand());
            if (handleFields.count(k)) {
              HV h;
              h.flavor = (bumpFields.count(k) || baseFields.count(k)) ? 'B' : 'C';
              h.field = h.pool = k;
              if (h.flavor == 'B') bSeeds.push_back({L, h});
              else add(L, h);
            }
          } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
            if (!isAllocCall(CB) || !CB->getType()->isPointerTy()) continue;
            if (std::string k = reachesHandle(CB, 0); !k.empty()) {
              HV h;
              h.alloc = CB;
              h.pool = k;
              add(CB, h);
            }
          }
        }
        auto isHandle = [&](const Value *V) {
          return hv.count(V) || isa<ConstantPointerNull>(V->stripPointerCasts());
        };
        // Is V (a B value) the bump: stored into its own field?
        auto isBump = [&](const Value *V, const HV &h) {
          for (const User *U : V->users())
            if (const auto *S = dyn_cast<StoreInst>(U))
              if (S->getValueOperand() == V && fieldKey(S, S->getPointerOperand()) == h.field) return true;
          return false;
        };
        auto carve = [&](const Instruction *I, const std::string &form, const std::string &f) {
          for (const Carve &c : carves)
            if (c.I == I) return;
          carves.push_back({I, form, f});
        };
        auto refuse = [&](const HV &h, const std::string &why, const Instruction *at) {
          refusals.push_back({h.pool, why, at});
        };
        // A data use of V: the forms, or a refusal.
        auto dataUse = [&](const Value *V, const HV &h, const Instruction *at) {
          const auto *I = dyn_cast<Instruction>(V);
          if (!I) return refuse(h, "a constant handle used as data: " + instText(at), at);
          if (h.flavor == 'B') {
            if (h.field.empty() && h.alloc) return carve(I, "header", h.pool); // a new chunk's first piece
            if (const auto *G = dyn_cast<GEPOperator>(V)) {
              if (!counterCarve(G, &F).empty()) return carve(I, "counter", h.field);
            }
            if (bumpIn.count(&F) && bumpIn[&F].count(h.field)) {
              const auto *G = dyn_cast<GEPOperator>(V);
              return carve(I, G && !G->hasAllZeroIndices() ? "minus-len" : "before-bump", h.field);
            }
            return refuse(h, "a pointer into the free space used as data where nothing bumps it: " + instText(at), at);
          }
          if (const auto *G = dyn_cast<GEPOperator>(V))
            if (h.alloc && G->hasAllConstantIndices() && !G->hasAllZeroIndices())
              return carve(I, "header", h.pool);
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
              if (isa<ICmpInst>(UI) || isa<PtrToIntInst>(UI)) continue;
              if (const auto *S = dyn_cast<StoreInst>(UI)) {
                if (S->getValueOperand() == V) {
                  const Value *A = S->getPointerOperand();
                  if (localSlot(A)) {
                    for (const User *LU : A->users())
                      if (isa<LoadInst>(LU)) add(LU, h);
                    continue;
                  }
                  const std::string k = fieldKey(S, A);
                  if (k.empty()) {
                    if (h.flavor == 'B') dataUse(V, h, S);
                    else refuse(h, "stored where no struct field names it: " + instText(S), S);
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
                  join(h.pool, k);
                  continue;
                }
                // V as the address: a chunk base's header field.
                if (h.flavor == 'C' && !fieldKey(S, S->getPointerOperand()).empty()) continue;
                refuse(h, "written through: " + instText(S), S);
                continue;
              }
              if (const auto *L = dyn_cast<LoadInst>(UI)) {
                if (h.flavor == 'C' && !fieldKey(L, L->getPointerOperand()).empty()) continue;
                refuse(h, "read through: " + instText(L), L);
                continue;
              }
              if (const auto *CB = dyn_cast<CallBase>(UI)) {
                bool ok = CB->getCalledOperand() != V;
                for (unsigned ai = 0; ok && ai < CB->arg_size(); ai++)
                  if (CB->getArgOperand(ai) == V && !freesArg(CB, ai)) ok = false;
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
                  // A carve unless its only uses compare (bounds: p + space).
                  bool cmpOnly = true;
                  for (const User *GU : G->users())
                    cmpOnly &= isa<ICmpInst>(GU) || isa<PtrToIntInst>(GU) || isa<DbgInfoIntrinsic>(GU);
                  if (cmpOnly) continue;
                  dataUse(G, h, G);
                  continue;
                }
                // A chunk base: a header field access (a struct GEP) stays a
                // handle; any other offset is the header carve or a refusal.
                if (structGEP(G) && isa<StructType>(G->getSourceElementType())) {
                  add(G, h);
                  continue;
                }
                bool cmpOnly = true, space = false;
                for (const User *GU : G->users()) {
                  cmpOnly &= isa<ICmpInst>(GU) || isa<PtrToIntInst>(GU) || isa<DbgInfoIntrinsic>(GU);
                  if (const auto *GS = dyn_cast<StoreInst>(GU))
                    space |= GS->getValueOperand() == G && bumpFields.count(fieldKey(GS, GS->getPointerOperand()));
                }
                if (cmpOnly) continue;
                if (space) { // the chunk's free space, stored into a bump field
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
                // A chunk base joins others (checked below, once all are known).
                if (h.flavor == 'C') {
                  add(UI, h);
                  continue;
                }
                // -O3 joins the reload of a bump field with a refill's free
                // space: the join is the field's value.
                std::string bk;
                for (const std::string &k : bumpFields)
                  if (bk.empty() && loadsField(UI, k, 0)) bk = k;
                if (!bk.empty()) {
                  HV b = h;
                  b.field = bk;
                  add(UI, b);
                  continue;
                }
                dataUse(V, h, UI);
                continue;
              }
              dataUse(V, h, UI); // returned, or any other use
            }
          }
        };
        drain();
        for (auto &[V, h] : bSeeds) add(V, h);
        drain();
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
            for (const StoreInst *RS : rs) rewinds.push_back({RS, fieldKey(RS, RS->getPointerOperand())});
            continue;
          }
          refuse(h, "a chunk base joined with data: " + instText(I), I);
        }
        // Stores into handle fields of values that are not handles.
        for (const Instruction &I : instructions(F)) {
          const auto *S = dyn_cast<StoreInst>(&I);
          if (!S || !S->getValueOperand()->getType()->isPointerTy()) continue;
          const std::string k = fieldKey(S, S->getPointerOperand());
          if (!handleFields.count(k) || isHandle(S->getValueOperand())) continue;
          bool carved = false;
          for (const Carve &c : carves) carved |= c.I == S->getValueOperand()->stripPointerCasts();
          if (bumpFields.count(k) && !carved && fromFormal(S->getValueOperand(), 0)) {
            rewinds.push_back({S, k});
          } else if (!carved) {
            HV h;
            h.field = k;
            refuse(h, "a value that is not a chunk pointer stored into it: " + instText(S), S);
          }
        }
      }
    if (handleFields.size() == before) break;
    for (const std::string &f : handleFields) parent.emplace(f, f);
  }

  // Report per pool.
  std::map<std::string, std::set<std::string>> fields;
  for (const std::string &f : handleFields) fields[pool(f)].insert(f);
  std::map<std::string, std::map<std::string, size_t>> forms;
  std::map<std::string, std::vector<const Instruction *>> headerCarves;
  for (const Carve &c : carves) {
    forms[pool(c.field)][c.form]++;
    if (c.form == "header") headerCarves[pool(c.field)].push_back(c.I);
  }
  std::map<std::string, std::vector<const Refusal *>> refused;
  for (const Refusal &r : refusals)
    refused[handleFields.count(r.field) ? pool(r.field) : r.field].push_back(&r);
  size_t nRefused = 0, nPools = 0;
  for (auto &[p, fs] : fields) {
    nPools++;
    std::string fl, fm;
    for (const std::string &f : fs) fl += " " + f + (irFallback.count(f) ? " (IR type at some access)" : "");
    for (auto &[form, n] : forms[p]) fm += " " + form + " " + std::to_string(n);
    size_t rw = 0;
    for (auto &[_, f] : rewinds) rw += pool(f) == p;
    auto rit = refused.find(p);
    if (rit != refused.end()) nRefused++;
    CG_LOG("PoolCarve: " << (rit == refused.end() ? "POOL" : "REFUSED") << " fields" << fl
           << "; carves" << (fm.empty() ? " none" : fm) << "; rewinds " << rw
           << (rit == refused.end() ? "" : "; refused by " + std::to_string(rit->second.size()) + " uses")
           << "\n");
    for (const Instruction *I : headerCarves[p])
      CG_LOG("PoolCarve:   header carve " << instLocStr(I) << ": " << instText(I) << "\n");
    if (rit != refused.end())
      for (size_t i = 0; i < rit->second.size() && i < 8; i++)
        CG_LOG("PoolCarve:   refusing use " << instLocStr(rit->second[i]->I) << ": " << rit->second[i]->why
               << "\n");
  }
  for (auto &[I, f] : rewinds) CG_LOG("PoolCarve: rewind " << f << " at " << instLocStr(I) << ": " << instText(I) << "\n");
  if (VerboseLevel >= 3)
    for (const Carve &c : carves)
      CG_DEBUG("PoolCarve: carve " << c.form << " " << c.field << " at " << instLocStr(c.I) << ": " << instText(c.I) << "\n");
  size_t fb = 0;
  for (const std::string &f : handleFields) fb += irFallback.count(f);
  CG_LOG("PoolCarve: " << nPools << " pools (" << nRefused << " refused), " << handleFields.size()
         << " handle fields (" << fb << " keyed by the IR type at some access: no debug info there), " << carves.size()
         << " carve sites, " << rewinds.size() << " rewinds; " << cursors
         << " bumped fields never refilled (cursors)\n");
}
