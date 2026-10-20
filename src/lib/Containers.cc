/*
 * Call graph construction
 *
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// Containers.cc: container storage closure (plan 3.55, obligation 1),
// report only (--cfl-container-closure). A container's storage cell is
// (owner, key); storage that is EXCLUSIVELY owned is named by its owner.
// Obligation 1 is the FEED condition (Fable 2026-10-13): every store into a
// struct field K stores a fresh block, null, or a reload of K of the same
// owner. A pointer read from K carries the refined name wherever it goes,
// so the uses of addresses read from K are reported as information only.
// A fed block's site is owner-paired only when the block goes nowhere but
// into K before it is stored (transient uses: casts, steps, local slots,
// compares, writes through it, free, a pool API call); otherwise the site
// keeps its plain object ("closed feed, site not paired"). A pool API
// (3.55 (b)) is a callee whose formal reaches only one certified pool's
// handle fields, scalars of the descriptor, compares and free, recursively.

#include "CallGraphInternal.h"
#include "NamedCells.h"
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Support/Format.h>
#include <chrono>

namespace {

std::string valueText(const Value *V) {
  std::string s;
  raw_string_ostream os(s);
  if (isa<Instruction>(V)) V->print(os);
  else V->printAsOperand(os, true);
  s = os.str();
  if (size_t p = s.find(", !dbg"); p != std::string::npos) s.resize(p);
  size_t b = s.find_first_not_of(' ');
  return b == std::string::npos ? s : s.substr(b);
}

// An alloca used only as the address of loads and stores (a -O0 local).
bool transientSlot(const Value *A) {
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

} // namespace

void CallGraphPass::checkContainerClosure() {
  // A field access's key: its IR struct (linker suffix stripped) and offset,
  // named by its struct GEP or TBAA tag, an array member at a variable index,
  // or at offset 0 with neither by the address's pointee (one naming rule
  // with the link words, plan 3.55 R3 D3). A -O0 slot names no field (it
  // names the local itself); an address-taken local's fields are named as
  // any object's are, field 0 too (its GEP (0, 0) strips to the alloca).
  PointeeResolver pointees(Ctx);
  auto fieldKey = [&](const Instruction *I, const Value *Addr) -> std::string {
    if (transientSlot(Addr->stripPointerCasts())) return "";
    StructType *S = nullptr;
    int64_t off = 0;
    if (!namedSlot(I, Addr, I->getModule()->getDataLayout(), pointees, S, off) || !S || !S->hasName()) return "";
    return stripStructNameSuffix(S->getName()).str() + "+" + std::to_string(off);
  };
  // A constructor's element type (the row object's rule, Fable 2026-10-14):
  // the struct of the fresh block's constant size sz that its derived values
  // step through, else the debug type of a local the constructor T declares
  // as a pointer to a struct of that size; null when neither decides.
  auto structOfSize = [&](const Instruction *I0, uint64_t sz, const Function *T) -> StructType * {
    const DataLayout &EDL = Ctx->Modules.front().first->getDataLayout();
    StructType *found = nullptr;
    SmallVector<const Value *, 8> w{I0};
    SmallPtrSet<const Value *, 16> seenV;
    while (!w.empty() && !found) {
      const Value *V = w.pop_back_val();
      if (!seenV.insert(V).second) continue;
      for (const User *U : V->users()) {
        if (const auto *G = dyn_cast<GEPOperator>(U)) {
          if (auto *ST = dyn_cast<StructType>(G->getSourceElementType());
              ST && ST->isSized() && EDL.getTypeAllocSize(ST) == sz) {
            found = ST;
            break;
          }
          if (G->hasAllZeroIndices()) w.push_back(U);
        } else if (isa<CastInst>(U) || isa<PHINode>(U) || isa<SelectInst>(U)) {
          w.push_back(U);
        } else if (const auto *S = dyn_cast<StoreInst>(U); S && S->getValueOperand() == V) {
          if (transientSlot(S->getPointerOperand()->stripPointerCasts()))
            for (const User *LU : S->getPointerOperand()->stripPointerCasts()->users())
              if (isa<LoadInst>(LU)) w.push_back(LU);
        }
      }
    }
    // No typed step (-O3 steps by bytes): the debug type of a local
    // variable the constructor declares as a pointer to a struct of that size
    // (`struct elf_strtab_hash_entry *ret`, optimized out but declared),
    // by its IR name; two different such structs decide nothing.
    if (!found) {
      std::set<StructType *> cands;
      for (const Instruction &J : instructions(*T)) {
        const auto *DV = dyn_cast<DbgVariableIntrinsic>(&J);
        if (!DV || DV->getVariable()->getArg()) continue; // a local, not a parameter (`table`)
        const DIType *DT = DV->getVariable()->getType();
        bool viaPtr = false;
        for (int k = 0; k < 8 && DT; k++) {
          const auto *D = dyn_cast<DIDerivedType>(DT);
          if (!D) break;
          if (D->getTag() == dwarf::DW_TAG_pointer_type) {
            if (viaPtr) { DT = nullptr; break; }
            viaPtr = true;
          } else if (D->getTag() != dwarf::DW_TAG_typedef && D->getTag() != dwarf::DW_TAG_const_type &&
                     D->getTag() != dwarf::DW_TAG_volatile_type) {
            DT = nullptr;
            break;
          }
          DT = D->getBaseType();
        }
        const auto *CT = dyn_cast_or_null<DICompositeType>(DT);
        if (!viaPtr || !CT || CT->getName().empty() || CT->getSizeInBits() != sz * 8) continue;
        if (auto *ST = StructType::getTypeByName(T->getContext(), ("struct." + CT->getName()).str());
            ST && ST->isSized() && EDL.getTypeAllocSize(ST) == sz)
          cands.insert(ST);
      }
      if (cands.size() == 1) found = *cands.begin();
    }
    return found;
  };
  auto isFresh = [&](const CallBase *CB) {
    const Function *C = CB ? CB->getCalledFunction() : nullptr;
    if (!C) return false;
    if (Ctx->AllocFuncs.count(C)) return true;
    auto it = Ctx->FuncSummaries.find(C);
    return it != Ctx->FuncSummaries.end() && it->second && it->second->fresh;
  };
  // The fresh allocation V stands for (through casts and a local slot
  // stored once), or null.
  // A join of fresh blocks (or null) and a certified pool carve are fresh
  // (objalloc_alloc's statement expression: phi(carve, _objalloc_alloc)).
  std::function<const Value *(const Value *, int)> freshOf = [&](const Value *V, int d) -> const Value * {
    V = V->stripPointerCasts();
    if (const auto *CB = dyn_cast<CallBase>(V)) return isFresh(CB) ? CB : nullptr;
    if (const auto *I = dyn_cast<Instruction>(V); I && poolCarves.count(I)) return I;
    if (const auto *PN = dyn_cast<PHINode>(V); PN && d < 4) {
      const Value *any = nullptr;
      for (const Value *In : PN->incoming_values()) {
        if (isa<ConstantPointerNull>(In->stripPointerCasts())) continue;
        const Value *f = freshOf(In, d + 1);
        if (!f) return nullptr;
        any = f;
      }
      return any ? PN : nullptr;
    }
    if (const auto *L = dyn_cast<LoadInst>(V); L && d < 4 && transientSlot(L->getPointerOperand()->stripPointerCasts())) {
      // A local holding only fresh blocks (or null).
      const Value *any = nullptr;
      for (const User *U : L->getPointerOperand()->stripPointerCasts()->users())
        if (const auto *S = dyn_cast<StoreInst>(U)) {
          if (isa<ConstantPointerNull>(S->getValueOperand()->stripPointerCasts())) continue;
          const Value *f = freshOf(S->getValueOperand(), d + 1);
          if (!f) return nullptr;
          any = f;
        }
      return any;
    }
    return nullptr;
  };
  // The owner an address names: its base pointer under constant field
  // steps; a -O0 local stored once (a spilled formal) stands for its value.
  auto ownerOf = [&](const Value *A) -> const Value * {
    A = A->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(A)) A = G->getPointerOperand()->stripPointerCasts();
    if (const auto *L = dyn_cast<LoadInst>(A))
      if (const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()); S && transientSlot(S)) {
        size_t stores = 0;
        for (const User *U : S->users()) stores += isa<StoreInst>(U);
        if (stores == 1) return S;
      }
    return A;
  };
  // Is V a reload of field K of the same owner (through casts and a local
  // slot)? A re-store moves no block between owners: `a->t = b->t` is
  // another value.
  std::function<bool(const Value *, const std::string &, const Value *, int)> reloadOf =
      [&](const Value *V, const std::string &K, const Value *owner, int d) -> bool {
    V = V->stripPointerCasts();
    const auto *L = dyn_cast<LoadInst>(V);
    if (!L || d > 4) return false;
    if (fieldKey(L, L->getPointerOperand()) == K) return ownerOf(L->getPointerOperand()) == owner;
    if (!transientSlot(L->getPointerOperand()->stripPointerCasts())) return false;
    // A local holding only reloads of K (or null): `old_table =
    // table->table; ... table->table = old_table` (binutils' restore).
    bool any = false;
    for (const User *U : L->getPointerOperand()->stripPointerCasts()->users())
      if (const auto *S = dyn_cast<StoreInst>(U)) {
        if (isa<ConstantPointerNull>(S->getValueOperand()->stripPointerCasts())) continue;
        if (!reloadOf(S->getValueOperand(), K, owner, d + 1)) return false;
        any = true;
      }
    return any;
  };

  // Plan 3.55 (b), closure through a pool API (Fable 2026-10-13): a closed
  // handle value passed to a callee keeps K closed when the callee's formal
  // reaches only a certified pool's handle fields (reads and writes through
  // it: poolFieldAccess, one pool), compares, and the same check through
  // further callees. Stored elsewhere, returned, passed to a bodiless
  // function or anything else: open. The set of functions is what the
  // check finds, never names. Memoized per (function, formal); a cycle is
  // assumed to pass (greatest fixpoint: a recursive call adds no use).
  std::map<std::pair<const Function *, unsigned>, int> formalMemo; // 1 pass, 0 fail, 2 in progress
  std::map<std::pair<const Function *, unsigned>, std::string> formalPool, formalWhy;
  std::set<const Function *> apiPassing;
  std::function<bool(const Function *, unsigned, std::string &)> formalOk;
  // The uses of V (a handle value) inside a function: pool accesses, compares,
  // further pool-API calls. `pool` collects the one pool they touch.
  auto handleUsesOk = [&](const Value *Root, std::string &pool, std::string &why) -> bool {
    std::vector<const Value *> work{Root};
    std::set<const Value *> seen{Root};
    while (!work.empty()) {
      const Value *V = work.back();
      work.pop_back();
      for (const User *U : V->users()) {
        const auto *UI = dyn_cast<Instruction>(U);
        if (!UI || isa<DbgInfoIntrinsic>(UI) || isa<ICmpInst>(UI)) continue;
        if (isa<GetElementPtrInst>(UI) || isa<CastInst>(UI)) {
          if (seen.insert(UI).second) work.push_back(UI);
          continue;
        }
        if (const auto *L = dyn_cast<LoadInst>(UI); L && L->getPointerOperand() == V) {
          // A scalar of the descriptor (objalloc's current_space): no pointer.
          if (!containsPointerType(L->getType())) continue;
          auto it = poolFieldAccess.find(L);
          if (it == poolFieldAccess.end()) { why = "read through it outside a pool's handle fields"; return false; }
          if (!pool.empty() && pool != it->second) { why = "two pools"; return false; }
          pool = it->second;
          continue;
        }
        if (const auto *S = dyn_cast<StoreInst>(UI)) {
          if (S->getPointerOperand() == V && S->getValueOperand() != V) {
            if (!containsPointerType(S->getValueOperand()->getType())) continue; // a scalar of the descriptor
            auto it = poolFieldAccess.find(S);
            if (it == poolFieldAccess.end()) { why = "written through outside a pool's handle fields"; return false; }
            if (!pool.empty() && pool != it->second) { why = "two pools"; return false; }
            pool = it->second;
            continue;
          }
          const Value *A = S->getPointerOperand()->stripPointerCasts();
          if (transientSlot(A)) {
            for (const User *LU : A->users())
              if (isa<LoadInst>(LU) && seen.insert(LU).second) work.push_back(LU);
            continue;
          }
          why = "stored into memory";
          return false;
        }
        if (const auto *CB = dyn_cast<CallBase>(UI)) {
          const Function *C = CB->getCalledFunction();
          // Freeing the descriptor (objalloc_free's free(o)).
          if (C && (C->getName() == "free" || C->getName() == "cfree")) continue;
          if (C)
            if (auto fit = Ctx->FuncSummaries.find(C);
                fit != Ctx->FuncSummaries.end() && fit->second && fit->second->freeArg >= 0)
              continue;
          if (!C || C->isDeclaration()) {
            why = "passed to a bodiless or indirect call (" + (C ? C->getName().str() : std::string("indirect")) + ")";
            return false;
          }
          for (unsigned a = 0; a < CB->arg_size(); a++) {
            if (CB->getArgOperand(a) != V) continue;
            std::string p2;
            if (!formalOk(C, a, p2)) {
              why = "passed to " + C->getName().str() + " (" + formalWhy[{C, a}] + ")";
              return false;
            }
            if (!p2.empty() && !pool.empty() && p2 != pool) { why = "two pools"; return false; }
            if (!p2.empty()) pool = p2;
          }
          continue;
        }
        why = isa<ReturnInst>(UI) ? "returned" : isa<PHINode>(UI) || isa<SelectInst>(UI) ? "joined" : "other use";
        return false;
      }
    }
    return true;
  };
  formalOk = [&](const Function *C, unsigned a, std::string &pool) -> bool {
    const auto key = std::make_pair(C, a);
    if (auto it = formalMemo.find(key); it != formalMemo.end()) {
      pool = formalPool[key];
      return it->second != 0; // in progress: a recursive call adds no use
    }
    if (a >= C->arg_size() || C->isVarArg()) {
      formalMemo[key] = 0;
      formalWhy[key] = "variadic";
      return false;
    }
    formalMemo[key] = 2;
    std::string p, why;
    const bool ok = handleUsesOk(C->getArg(a), p, why);
    formalMemo[key] = ok;
    formalPool[key] = p;
    formalWhy[key] = why;
    if (ok && !p.empty()) apiPassing.insert(C);
    pool = p;
    return ok;
  };

  // A formal the value stands for (through casts and an -O0 slot stored
  // only with it).
  auto formalOf = [&](const Value *V) -> const Argument * {
    V = V->stripPointerCasts();
    if (const auto *A = dyn_cast<Argument>(V)) return A;
    const auto *L = dyn_cast<LoadInst>(V);
    if (!L || !transientSlot(L->getPointerOperand()->stripPointerCasts())) return nullptr;
    const Argument *A = nullptr;
    for (const User *U : L->getPointerOperand()->stripPointerCasts()->users())
      if (const auto *S = dyn_cast<StoreInst>(U)) {
        const auto *SA = dyn_cast<Argument>(S->getValueOperand()->stripPointerCasts());
        if (!SA || (A && A != SA)) return nullptr;
        A = SA;
      }
    return A;
  };
  // Feeds through a formal (Fable 2026-10-14): a formal is a fresh feed
  // when its function's address is never taken, every call site is a
  // direct call, and every actual there is fresh at the caller (or null,
  // or such a formal of the caller, recursively; a cycle fails). Why not,
  // per formal, for the report.
  std::map<const Argument *, int> formalMemo2; // 1 fresh, 0 not, 2 in progress
  std::map<const Argument *, std::string> formalWhy2;
  std::function<bool(const Argument *)> formalFresh = [&](const Argument *A) -> bool {
    if (auto it = formalMemo2.find(A); it != formalMemo2.end()) return it->second == 1;
    formalMemo2[A] = 2;
    const Function *F = A->getParent();
    std::string why;
    bool ok = true;
    for (const User *U : F->users()) {
      const auto *CB = dyn_cast<CallBase>(U);
      if (!CB || CB->getCalledOperand()->stripPointerCasts() != F) {
        ok = false;
        why = "formal of an escaping function";
        break;
      }
      const Value *Act = CB->getArgOperand(A->getArgNo());
      if (isa<ConstantPointerNull>(Act->stripPointerCasts()) || freshOf(Act, 0)) continue;
      if (const Argument *CA = formalOf(Act); CA && formalFresh(CA)) continue;
      ok = false;
      why = "an actual not fresh at " + CB->getFunction()->getName().str();
      break;
    }
    if (F->hasAddressTaken() && ok) ok = false, why = "formal of an escaping function";
    formalMemo2[A] = ok;
    formalWhy2[A] = why;
    return ok;
  };

  struct FieldState {
    size_t viaFormal = 0; // fresh feeds through a formal
    size_t fed = 0, nulls = 0, restores = 0, loads = 0;
    std::vector<std::string> foreign;                   // stores of another value (examples)
    std::vector<const StoreInst *> foreignSI;           // those stores
    std::vector<const StoreInst *> allSI;               // every pointer store into the field
    // Where addresses read from K go (information: the load side opens
    // nothing, Fable 2026-10-13), and why a feed's site is not paired.
    std::map<std::string, std::vector<std::string>> flows, unpairedWhy;
    size_t flowUses = 0, unpaired = 0;
    size_t apiCalls = 0; // handle values passed to a pool API (3.55 (b))
  };
  std::map<std::string, FieldState> fields;
  std::vector<std::pair<std::string, const Value *>> feeds; // (field, the fresh block)
  std::map<std::string, std::map<std::string, size_t>> calledFeeds; // field -> non-fresh callee -> stores

  // Pass 1: what each pointer field is fed.
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (const Instruction &I : instructions(F)) {
        const auto *SI = dyn_cast<StoreInst>(&I);
        if (!SI || !SI->getValueOperand()->getType()->isPointerTy()) continue;
        const std::string K = fieldKey(SI, SI->getPointerOperand());
        if (K.empty()) continue;
        const Value *V = SI->getValueOperand();
        fields[K].allSI.push_back(SI);
        if (const Value *C = freshOf(V, 0)) {
          fields[K].fed++;
          feeds.push_back({K, C});
        } else if (const Argument *FA = formalOf(V); FA && formalFresh(FA)) {
          fields[K].fed++;
          fields[K].viaFormal++;
        } else if (const auto *VC = dyn_cast<CallBase>(V->stripPointerCasts())) {
          const Function *CF = VC->getCalledFunction();
          calledFeeds[K][CF ? CF->getName().str() : std::string("an indirect call")]++;
          fields[K].foreignSI.push_back(SI);
          if (fields[K].foreign.size() < 3) fields[K].foreign.push_back(F.getName().str() + ": " + valueText(SI));
          else fields[K].foreign.push_back("");
        } else if (isa<ConstantPointerNull>(V->stripPointerCasts())) {
          fields[K].nulls++;
        } else if (reloadOf(V, K, ownerOf(SI->getPointerOperand()), 0)) {
          fields[K].restores++;
        } else if (fields[K].foreign.size() < 3) {
          fields[K].foreignSI.push_back(SI);
          fields[K].foreign.push_back(F.getName().str() + ": " + valueText(SI));
        } else {
          fields[K].foreignSI.push_back(SI);
          fields[K].foreign.push_back("");
        }
      }
  // Candidates: fed at least one fresh block.
  std::set<std::string> cand;
  for (auto &[K, st] : fields)
    if (st.fed) cand.insert(K);

  // Pass 2: the address never escapes. Walk the uses of each load of a
  // candidate field and of each fresh block fed to one.
  // `uses` collects where the value goes besides the transient uses (by
  // reason, two examples each); the return value is how many such uses.
  auto walk = [&](const Value *Root, const std::string &K, FieldState &st,
                  std::map<std::string, std::vector<std::string>> &uses) -> size_t {
    size_t n = 0;
    std::vector<const Value *> work{Root};
    std::set<const Value *> seen{Root};
    auto push = [&](const Value *V) {
      if (seen.insert(V).second) work.push_back(V);
    };
    auto fail = [&](const std::string &why, const Instruction *At) {
      n++;
      auto &ex = uses[why];
      if (ex.size() < 2) ex.push_back(At->getFunction()->getName().str() + ": " + valueText(At));
    };
    while (!work.empty()) {
      const Value *V = work.back();
      work.pop_back();
      for (const User *U : V->users()) {
        const auto *UI = dyn_cast<Instruction>(U);
        if (!UI || isa<DbgInfoIntrinsic>(UI)) continue;
        if (const auto *L = dyn_cast<LoadInst>(UI)) {
          if (L->getPointerOperand() == V) continue; // a read through it
        } else if (const auto *S = dyn_cast<StoreInst>(UI)) {
          if (S->getPointerOperand() == V) continue; // a write through it
          const Value *A = S->getPointerOperand()->stripPointerCasts();
          if (fieldKey(S, S->getPointerOperand()) == K) continue; // into its own field
          if (transientSlot(A)) { // a local: its reloads carry it
            for (const User *LU : A->users())
              if (isa<LoadInst>(LU)) push(LU);
            continue;
          }
          const std::string to = fieldKey(S, S->getPointerOperand());
          fail(to.empty() ? "stored into memory no field names" : "stored into another field (" + to + ")", S);
          continue;
        }
        if (isa<GetElementPtrInst>(UI) || isa<CastInst>(UI)) {
          if (isa<PtrToIntInst>(UI)) continue;
          push(UI);
          continue;
        }
        if (isa<ICmpInst>(UI)) continue;
        if (const auto *CB = dyn_cast<CallBase>(UI)) {
          const Function *C = CB->getCalledFunction();
          if (isa<MemIntrinsic>(CB)) continue;
          if (C && (C->getName() == "free" || C->getName() == "cfree")) continue;
          if (C) {
            auto it = Ctx->FuncSummaries.find(C);
            if (it != Ctx->FuncSummaries.end() && it->second && it->second->freeArg >= 0) continue;
          }
          // A pool API (3.55 (b)): every argument position it is passed at
          // reaches only one certified pool's handle fields.
          if (C && !C->isDeclaration()) {
            bool api = true;
            std::string why;
            for (unsigned a = 0; a < CB->arg_size() && api; a++)
              if (CB->getArgOperand(a) == V) {
                std::string p;
                if (!formalOk(C, a, p) || p.empty()) {
                  api = false;
                  why = formalWhy[{C, a}].empty() ? "touches no pool" : formalWhy[{C, a}];
                }
              }
            if (api) {
              st.apiCalls++;
              continue;
            }
            fail("passed to " + C->getName().str() + " (not a pool API: " + why + ")", CB);
            continue;
          }
          fail("passed to " + (C ? C->getName().str() : std::string("an indirect call")), CB);
          continue;
        }
        if (isa<ReturnInst>(UI)) { fail("returned", UI); continue; }
        if (isa<PHINode>(UI) || isa<SelectInst>(UI)) {
          // A join with null only (`pH->ht ? &pH->ht[h] : 0`) adds no block.
          bool nullOnly = true;
          for (const Use &Op : UI->operands()) {
            const Value *O = Op.get()->stripPointerCasts();
            if (isa<SelectInst>(UI) && &Op == &UI->getOperandUse(0)) continue; // the condition
            if (O != V && !isa<ConstantPointerNull>(O)) nullOnly = false;
          }
          if (nullOnly) push(UI);
          else fail("joined with another value", UI);
          continue;
        }
        fail("other use", UI);
      }
    }
    return n;
  };
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (const Instruction &I : instructions(F))
        if (const auto *L = dyn_cast<LoadInst>(&I); L && L->getType()->isPointerTy()) {
          const std::string K = fieldKey(L, L->getPointerOperand());
          if (!cand.count(K)) continue;
          fields[K].loads++;
          fields[K].flowUses += walk(L, K, fields[K], fields[K].flows);
        }
  // A feed's site is owner-paired (3.55 deliverable 1) only when its block
  // goes nowhere but into K (and transient uses) before it is stored.
  for (auto &[K, C] : feeds)
    if (walk(C, K, fields[K], fields[K].unpairedWhy)) fields[K].unpaired++;

  size_t closed = 0, open = 0, feedsUnpaired = 0;
  containerClosureReport.clear();
  auto line = [&](const std::string &l) {
    if (!CFLContainerClosure) return; // computed for the containers; reported with the flag
    CG_LOG("ContainerClosure: " << l << "\n");
    containerClosureReport.push_back(l);
  };
  for (const std::string &K : cand) {
    const FieldState &st = fields[K];
    // Obligation 1 is the feed condition: fresh blocks, null, same-owner
    // re-stores.
    const bool ok = st.foreign.empty();
    (ok ? closed : open)++;
    if (ok) feedsUnpaired += st.unpaired;
    line(std::string(ok ? "CLOSED " : "OPEN ") + K + ": fed " + std::to_string(st.fed) + " fresh blocks (" +
         std::to_string(st.viaFormal) + " through a formal; " +
         std::to_string(st.unpaired) + " of them leave by another way too: site not paired), " +
         std::to_string(st.nulls) + " nulls, " + std::to_string(st.restores) + " re-stores, " +
         std::to_string(st.foreign.size()) + " stores of another value; " + std::to_string(st.loads) + " loads, " +
         std::to_string(st.apiCalls) + " passed to a pool API, " + std::to_string(st.flowUses) +
         " other uses of addresses read from it (information)");
    for (const std::string &f : st.foreign)
      if (!f.empty()) line("  another value stored: " + f);
    for (auto &[why, ex] : st.unpairedWhy) {
      line("  a fed block also " + why);
      for (const std::string &e : ex) line("    " + e);
    }
    for (auto &[why, ex] : st.flows) {
      line("  addresses read from it flow: " + why);
      for (const std::string &e : ex) line("    " + e);
    }
  }
  line(std::to_string(cand.size()) + " fields fed fresh blocks: " + std::to_string(closed) + " closed, " +
       std::to_string(open) + " open; " + std::to_string(feedsUnpaired) +
       " closed feeds whose site is not paired; " + std::to_string(apiPassing.size()) +
       " functions pass the pool-API check (3.55 (b), found by the check)");
  for (const Function *F : apiPassing) CG_DEBUG("ContainerClosure: pool API " << F->getName() << "\n");
  // Fields fed by call results the confirmer does not take as fresh (not
  // candidates): the callee is the reason (verbose=3).
  for (auto &[K, cs] : calledFeeds)
    for (auto &[c, n] : cs)
      CG_DEBUG("ContainerClosure: NOT FED FRESH " << K << ": " << n << " stores of " << c << "'s result (not a fresh source)\n");

  // ---- Containers (plan 3.55 deliverable 1): the obligations per container.
  containerReport.clear();
  containerRowOf.clear();
  containerBodies.clear();
  containerElemSources.clear();
  containerInherit.clear();
  containerCtors.clear();
  containerOwnerCtors.clear();
  containerCtorType.clear();
  snapshotHolders.clear();
  auto cline = [&](const std::string &l) {
    CG_LOG("Container: " << l << "\n");
    containerReport.push_back(l);
  };
  std::map<std::string, const Function *> byName;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      if (!F.isDeclaration()) byName.emplace(F.getName().str(), &F);
  // Carve rows of any container (a leaf premise for O4).
  std::set<std::string> carveFns;
  for (const auto &C : Ctx->Containers)
    for (const auto &[fn, R] : C.rows)
      if (R.role == GlobalContext::ContainerRow::Carve) carveFns.insert(fn);
  // A DI struct's pointer members: (byte offset, the struct the member
  // points to through typedefs and up to two pointer levels; "" if none).
  auto diStrip = [](const DIType *T) {
    for (int i = 0; i < 16 && T; i++) {
      const auto *D = dyn_cast<DIDerivedType>(T);
      if (!D) break;
      const auto tag = D->getTag();
      if (tag != dwarf::DW_TAG_typedef && tag != dwarf::DW_TAG_const_type && tag != dwarf::DW_TAG_volatile_type &&
          tag != dwarf::DW_TAG_restrict_type)
        break;
      T = D->getBaseType();
    }
    return T;
  };
  // The DI structs by tag (accessNames is built later, per module).
  std::map<std::string, const DICompositeType *> diStructs;
  if (!Ctx->Containers.empty())
    for (auto &[M, _] : Ctx->Modules) {
      DebugInfoFinder DF;
      DF.processModule(*M);
      for (const DIType *T : DF.types())
        if (const auto *CT = dyn_cast<DICompositeType>(T);
            CT && CT->getTag() == dwarf::DW_TAG_structure_type && !CT->getName().empty() && !CT->isForwardDecl())
          diStructs.emplace(CT->getName().str(), CT);
    }
  // The struct analyzer's embedding table (transitive, every array element):
  // does struct S of module M hold the struct named T at byte off? Looked
  // up by S's own type (anonymous structs share a name across modules).
  auto tableHolds = [&](StructType *S, int64_t off, StringRef T, const Module *M) {
    Module *MM = const_cast<Module *>(M);
    const StructInfo *SI = Ctx->structAnalyzer.getStructInfo(S, MM);
    StructType *TT = StructType::getTypeByName(M->getContext(), T);
    if (!TT)
      for (StructType *ST : M->getIdentifiedStructTypes())
        if (ST->hasName() && stripStructNameSuffix(ST->getName()) == T) { TT = ST; break; }
    const StructInfo *TI = TT && !TT->isOpaque() ? Ctx->structAnalyzer.getStructInfo(TT, MM) : nullptr;
    if (!SI || !TI) return false;
    const auto &Cs = TI->getContainers();
    auto it = Cs.find(SI->getRealType());
    return it != Cs.end() && it->second.count((unsigned)off);
  };
  // Through debug info, where the program has it: does byte `off` of DI
  // struct S lie in a member (any member of a union) that is or embeds the
  // struct named T at that byte? 1 yes, 0 no, -1 no debug info for S.
  std::function<bool(const DIType *, int64_t, StringRef, int)> diHolds = [&](const DIType *Ty, int64_t off,
                                                                             StringRef T, int d) -> bool {
    for (int i = 0; i < 16 && Ty; i++) {
      const auto *D = dyn_cast<DIDerivedType>(Ty);
      if (!D || D->getTag() == dwarf::DW_TAG_pointer_type || D->getTag() == dwarf::DW_TAG_member) break;
      Ty = D->getBaseType();
    }
    const auto *CT = dyn_cast_or_null<DICompositeType>(Ty);
    if (!CT || d > 32 || off < 0) return false;
    if (CT->getTag() == dwarf::DW_TAG_array_type) {
      const DIType *E = CT->getBaseType();
      const uint64_t es = E ? E->getSizeInBits() / 8 : 0;
      for (int i = 0; i < 16 && E && !es; i++)
        if (const auto *ED = dyn_cast<DIDerivedType>(E)) E = ED->getBaseType();
      const uint64_t es2 = E ? E->getSizeInBits() / 8 : 0;
      return es2 && diHolds(CT->getBaseType(), off % (int64_t)es2, T, d + 1);
    }
    if (CT->getTag() == dwarf::DW_TAG_structure_type && off == 0 && CT->getName() == T) return true;
    for (const DINode *E : CT->getElements()) {
      const auto *Mb = dyn_cast<DIDerivedType>(E);
      if (!Mb || Mb->getTag() != dwarf::DW_TAG_member || Mb->isStaticMember()) continue;
      const int64_t mo = (int64_t)(Mb->getOffsetInBits() / 8), ms = (int64_t)(Mb->getSizeInBits() / 8);
      if (off >= mo && (ms == 0 || off < mo + ms) && diHolds(Mb->getBaseType(), off - mo, T, d + 1)) return true;
    }
    return false;
  };
  auto diThroughUnion = [&](StringRef S, int64_t off, StringRef T) -> int {
    auto it = diStructs.find(S.str());
    if (it == diStructs.end()) return -1;
    return diHolds(it->second, off, T, 0) ? 1 : 0;
  };
  // An anonymous struct member's members are the enclosing struct's, at
  // its offset plus theirs (the IR names them so, Fable 2026-10-16).
  std::function<void(const DICompositeType *, uint64_t, std::vector<std::pair<uint64_t, std::string>> &, int)>
      ptrMembersOf = [&](const DICompositeType *Cc, uint64_t base, std::vector<std::pair<uint64_t, std::string>> &out,
                         int d) {
        for (const DINode *E : Cc->getElements()) {
          const auto *M = dyn_cast<DIDerivedType>(E);
          if (!M || M->getTag() != dwarf::DW_TAG_member || M->isStaticMember()) continue;
          const DIType *T = diStrip(M->getBaseType());
          if (const auto *AS = dyn_cast_or_null<DICompositeType>(T);
              AS && AS->getTag() == dwarf::DW_TAG_structure_type && AS->getName().empty() && d < 8) {
            ptrMembersOf(AS, base + M->getOffsetInBits() / 8, out, d + 1);
            continue;
          }
          const auto *P = dyn_cast_or_null<DIDerivedType>(T);
          if (!P || P->getTag() != dwarf::DW_TAG_pointer_type) continue;
          const DIType *B = diStrip(P->getBaseType());
          if (const auto *P2 = dyn_cast_or_null<DIDerivedType>(B); P2 && P2->getTag() == dwarf::DW_TAG_pointer_type)
            B = diStrip(P2->getBaseType());
          const auto *S = dyn_cast_or_null<DICompositeType>(B);
          out.push_back({base + M->getOffsetInBits() / 8,
                         S && S->getTag() == dwarf::DW_TAG_structure_type ? S->getName().str() : std::string()});
        }
      };
  auto ptrMembers = [&](StringRef Tag) {
    std::vector<std::pair<uint64_t, std::string>> out;
    auto dit = diStructs.find(Tag.str());
    const DICompositeType *Cc = dit == diStructs.end() ? nullptr : dit->second;
    if (Cc) ptrMembersOf(Cc, 0, out, 0);
    return out;
  };
  for (auto &C : Ctx->Containers) {
    using CR = GlobalContext::ContainerRow;
    C.verified = false;
    C.obligations.clear();
    // The body: the row functions, and the functions only they call
    // (direct calls only, address never taken), to a fixpoint.
    std::set<const Function *> body;
    // A deref owner's row (OWNER(*argN@off)) is applied through its body: not
    // part of the body (its callees and fresh blocks are the program's), only
    // its result checked (O2), classified like the body's (Fable 2026-10-16).
    std::set<const Function *> derefFns;
    std::string missing;
    for (const auto &[fn, R] : C.rows) {
      if (R.role == CR::Pure || R.role == CR::Carve) continue;
      auto it = byName.find(fn);
      if (it == byName.end()) missing += (missing.empty() ? "" : ", ") + fn;
      else (R.ownerDeref >= 0 ? derefFns : body).insert(it->second);
    }
    if (body.empty()) continue; // not in this program
    for (bool grew = true; grew;) {
      grew = false;
      for (const Function *F : std::vector<const Function *>(body.begin(), body.end()))
        for (const Instruction &I : instructions(*F))
          if (const auto *CB = dyn_cast<CallBase>(&I))
            if (const Function *G = CB->getCalledFunction(); G && !G->isDeclaration() && !body.count(G) &&
                                                              !C.rows.count(G->getName().str()) &&
                                                              !G->hasAddressTaken()) {
              bool inner = true;
              for (const User *U : G->users())
                if (const auto *UC = dyn_cast<CallBase>(U); !UC || !body.count(UC->getFunction())) inner = false;
              if (inner) {
                body.insert(G);
                grew = true;
              }
            }
    }
    // The owner types: the struct each owner formal points to.
    std::set<std::string> ownerTypes;
    for (const auto &[fn, R] : C.rows) {
      if (R.owner < 0 || R.ownerDeref >= 0) continue;
      auto it = byName.find(fn);
      if (it == byName.end()) continue;
      const DISubprogram *SP = it->second->getSubprogram();
      const DISubroutineType *ST = SP ? SP->getType() : nullptr;
      if (ST && (unsigned)R.owner + 1 < ST->getTypeArray().size())
        if (const StringRef N = ka::diStructName(ST->getTypeArray()[R.owner + 1], true); !N.empty()) {
          ownerTypes.insert("struct." + N.str());
          continue;
        }
      // No debug info (the kernel corpus): the owner formal's pointee by the
      // naming rule (sibling GEPs, phi, formal provenance).
      if ((unsigned)R.owner < it->second->arg_size())
        if (StructType *S = pointees.get(it->second->getArg(R.owner), it->second->getContext()))
          ownerTypes.insert(stripStructNameSuffix(S->getName()).str());
    }
    // OWNER(*argN@off) (Fable 2026-10-16): by debug info, argN points to a
    // struct whose member at byte off points to an owner type (or a struct
    // holding one at +0); checked here, the row applied through its body.
    std::vector<std::string> derefLines, derefFail;
    for (const auto &[fn, R] : C.rows) {
      if (R.ownerDeref < 0) continue;
      auto it = byName.find(fn);
      const std::string at = fn + " OWNER(*arg" + std::to_string(R.owner) + "@" + std::to_string(R.ownerDeref) + ")";
      if (it == byName.end()) continue;
      const DISubprogram *SP = it->second->getSubprogram();
      const DISubroutineType *ST = SP ? SP->getType() : nullptr;
      const StringRef PN = ST && (unsigned)R.owner + 1 < ST->getTypeArray().size()
                               ? ka::diStructName(ST->getTypeArray()[R.owner + 1], true)
                               : StringRef();
      auto dit = PN.empty() ? diStructs.end() : diStructs.find(PN.str());
      if (dit == diStructs.end()) {
        derefFail.push_back(at + ": no debug info for the argument's struct");
        continue;
      }
      const DIDerivedType *Mem = nullptr;
      for (const DINode *E : dit->second->getElements())
        if (const auto *M = dyn_cast<DIDerivedType>(E);
            M && M->getTag() == dwarf::DW_TAG_member && M->getOffsetInBits() == (uint64_t)R.ownerDeref * 8)
          Mem = M;
      const StringRef ON = Mem ? ka::diStructName(Mem->getBaseType(), true) : StringRef();
      // The member's struct is an owner type, or holds one at +0 (bfd_link_hash_table's table).
      std::function<bool(StringRef, int)> holdsOwner = [&](StringRef Tag, int d) -> bool {
        if (ownerTypes.count("struct." + Tag.str())) return true;
        auto sit = diStructs.find(Tag.str());
        if (d > 4 || sit == diStructs.end()) return false;
        for (const DINode *E : sit->second->getElements())
          if (const auto *M = dyn_cast<DIDerivedType>(E); M && M->getTag() == dwarf::DW_TAG_member && M->getOffsetInBits() == 0)
            if (const StringRef N = ka::diStructName(M->getBaseType(), false); !N.empty() && holdsOwner(N, d + 1))
              return true;
        return false;
      };
      if (ON.empty() || !holdsOwner(ON, 0)) {
        derefFail.push_back(at + ": " + PN.str() + "'s member at +" + std::to_string(R.ownerDeref) + " is " +
                            (Mem ? (Mem->getName().str() + (ON.empty() ? " (not a struct pointer)" : " (" + ON.str() + " *)"))
                                 : std::string("none")) +
                            ", not an owner");
        continue;
      }
      derefLines.push_back(at + " = " + PN.str() + "." + Mem->getName().str() + " (" + ON.str() +
                           " *): checked by debug info; applied through its body");
    }
    // O1: every data pointer field of an owner type the body reads or
    // writes is closed (a field whose loads are called is a code field:
    // O4's).
    std::set<std::string> handle, code, open1;
    std::vector<std::string> o1AssumeLines; // O1's copies by name and its assumptions, printed under the block
    size_t nO1Assume = 0;                   // of them, assumptions
    std::vector<std::string> o1ReportLines; // each copy's class and origins: the rule report only
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F)) {
        const Value *A = nullptr;
        Type *T = nullptr;
        if (const auto *L = dyn_cast<LoadInst>(&I)) A = L->getPointerOperand(), T = L->getType();
        else if (const auto *S = dyn_cast<StoreInst>(&I)) A = S->getPointerOperand(), T = S->getValueOperand()->getType();
        if (!A || !T->isPointerTy()) continue;
        const std::string K = fieldKey(&I, A);
        if (K.empty() || !ownerTypes.count(K.substr(0, K.rfind('+')))) continue;
        bool called = false;
        if (const auto *L = dyn_cast<LoadInst>(&I))
          for (const User *U : L->users())
            if (const auto *UC = dyn_cast<CallBase>(U); UC && UC->getCalledOperand() == L) called = true;
        (called ? code : handle).insert(K);
      }
    for (const std::string &K : code) handle.erase(K);
    // Code fields (Fable 2026-10-14): an indirect call through an owner
    // field F calls exactly the function constants fed into F. Every store
    // into F is a function constant, a formal fed only by constants
    // (through non-escaping functions, every call site known), null, or a
    // same-owner reload; anything else, or an aggregate copy of the owner,
    // opens F. The constants join the body.
    std::map<std::string, std::set<const Function *>> codeTargets;
    std::map<std::string, std::string> codeOpen;
    std::function<bool(const Value *, std::set<const Function *> &, std::set<const Argument *> &)> constsOf =
        [&](const Value *V, std::set<const Function *> &out, std::set<const Argument *> &onStack) -> bool {
      V = V->stripPointerCasts();
      if (isa<ConstantPointerNull>(V)) return true;
      if (const auto *Fn = dyn_cast<Function>(V)) { out.insert(Fn); return true; }
      const Argument *A = formalOf(V);
      if (!A || !onStack.insert(A).second) return false; // another value, or a cycle
      const Function *F = A->getParent();
      if (F->hasAddressTaken()) return false;
      for (const User *U : F->users()) {
        const auto *CB = dyn_cast<CallBase>(U);
        if (!CB || CB->getCalledOperand()->stripPointerCasts() != F) return false;
        if (!constsOf(CB->getArgOperand(A->getArgNo()), out, onStack)) return false;
      }
      onStack.erase(A);
      return true;
    };
    // Each feed paired with its owner (Fable 2026-10-14): the owner value
    // the store's base names and the constants fed there; through a formal
    // pair (`table->newfunc = newfunc` in an init function), one pair per
    // call site of that function, with the owner actual.
    std::vector<std::pair<const Value *, std::set<const Function *>>> ownerFeeds;
    for (const std::string &K : code) {
      std::set<const Function *> T;
      for (const StoreInst *S : fields[K].allSI) {
        std::set<const Argument *> onStack;
        {
          const Value *B = S->getPointerOperand()->stripPointerCasts();
          while (const auto *G = dyn_cast<GEPOperator>(B)) B = G->getPointerOperand()->stripPointerCasts();
          const Argument *OA = formalOf(B), *VA = formalOf(S->getValueOperand()->stripPointerCasts());
          // Up the call sites while both the owner and the code value are
          // the caller's formals; pair them where the constant is fed.
          std::function<void(const Argument *, const Argument *, int)> pairUp = [&](const Argument *OF, const Argument *VF,
                                                                                    int depth) {
            const Function *F = OF->getParent();
            if (depth > 8 || F->hasAddressTaken()) return;
            for (const User *U : F->users()) {
              const auto *CB = dyn_cast<CallBase>(U);
              if (!CB || CB->getCalledOperand()->stripPointerCasts() != F) continue;
              const Value *OV = CB->getArgOperand(OF->getArgNo()), *VV = CB->getArgOperand(VF->getArgNo());
              const Argument *OF2 = formalOf(OV->stripPointerCasts()), *VF2 = formalOf(VV->stripPointerCasts());
              if (OF2 && VF2 && OF2->getParent() == VF2->getParent()) {
                pairUp(OF2, VF2, depth + 1);
                continue;
              }
              std::set<const Function *> fs;
              std::set<const Argument *> st;
              if (constsOf(VV, fs, st) && !fs.empty()) ownerFeeds.push_back({OV, fs});
            }
          };
          if (OA && VA && OA->getParent() == VA->getParent()) {
            pairUp(OA, VA, 0);
          } else if (const auto *Fn = dyn_cast<Function>(S->getValueOperand()->stripPointerCasts())) {
            ownerFeeds.push_back({B, {Fn}});
          }
        }
        if (constsOf(S->getValueOperand(), T, onStack)) continue;
        if (reloadOf(S->getValueOperand(), K, ownerOf(S->getPointerOperand()), 0)) continue;
        codeOpen[K] = S->getFunction()->getName().str() + ": " + valueText(S);
        break;
      }
      codeTargets[K] = std::move(T);
    }
    // An aggregate copy into an owner struct writes its code fields where
    // the feed set does not look.
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (const Instruction &I : instructions(F))
          if (const auto *MT = dyn_cast<MemTransferInst>(&I)) {
            const std::string K = fieldKey(MT, MT->getRawDest());
            if (!K.empty() && ownerTypes.count(K.substr(0, K.rfind('+'))))
              for (const std::string &CK : code)
                if (!codeOpen.count(CK)) codeOpen[CK] = "an aggregate copy of the owner in " + F.getName().str();
          }
    size_t codeTargetCount = 0;
    for (auto &[K, T] : codeTargets)
      if (!codeOpen.count(K))
        for (const Function *Fn : T)
          if (!Fn->isDeclaration()) body.insert(Fn), codeTargetCount++;
    // The targets' own callees that only the body calls join it too.
    for (bool grew = true; grew;) {
      grew = false;
      for (const Function *F : std::vector<const Function *>(body.begin(), body.end()))
        for (const Instruction &I : instructions(*F))
          if (const auto *CB = dyn_cast<CallBase>(&I))
            if (const Function *G = CB->getCalledFunction(); G && !G->isDeclaration() && !body.count(G) &&
                                                              !C.rows.count(G->getName().str()) &&
                                                              !G->hasAddressTaken()) {
              bool inner = true;
              for (const User *U : G->users())
                if (const auto *UC = dyn_cast<CallBase>(U); !UC || !body.count(UC->getFunction())) inner = false;
              if (inner) body.insert(G), grew = true;
            }
    }
    // The container's structs: the owner types and what their handle
    // fields point to; LINK fields: pointer members of those structs that
    // point back into them (next, prev, a bucket's chain).
    std::set<std::string> ctypes, links;
    for (const std::string &O : ownerTypes) ctypes.insert(StringRef(O).drop_front(7).str());
    for (const std::string &K : handle) {
      const std::string S = StringRef(K).substr(7, K.rfind('+') - 7).str();
      const uint64_t off = std::stoull(K.substr(K.rfind('+') + 1));
      for (auto &[o, P] : ptrMembers(S))
        if (o == off && !P.empty()) ctypes.insert(P);
    }
    for (bool grew = true; grew;) {
      grew = false;
      for (const std::string &S : std::set<std::string>(ctypes))
        for (auto &[o, P] : ptrMembers(S))
          if (!P.empty() && ctypes.count(P) && !ownerTypes.count("struct." + S) &&
              links.insert("struct." + S + "+" + std::to_string(o)).second)
            grew = true;
    }

    // Declared storage (plan 3.55 R3 D2, Fable 2026-10-15): `@storage`
    // names the handle, link and link-word slots by their innermost struct
    // (rb_root+0 is the rb_root inside any owner). A proposal the engine
    // checks: against debug info where the program has it, from the store
    // side below (every element-derived store lands in a declared slot;
    // every declared slot is written only in the rows and at admitted
    // sites), and a LINKWORD by its R1 verdict. Without debug info (the
    // kernel), the declaration is what names the links.
    const bool declared = !C.storage.empty();
    const DataLayout &CDL = Ctx->Modules.front().first->getDataLayout();
    // "struct.T+off" of the field holding byte off of S (innermost struct).
    auto innerKeyOf = [&](StructType *S, int64_t off) -> std::string {
      std::pair<std::string, int64_t> K;
      Type *leaf = nullptr;
      int64_t in = 0;
      if (!S || !innermostField(S, off, CDL, K, leaf, in)) return "";
      return K.first + "+" + std::to_string(K.second - in);
    };
    // (1c) The rows' premise (Fable 2026-10-15): a row's OWNER formal points
    // to the struct of the block's HANDLE at +0, each ELEM formal to the
    // struct of its LINK/LINKWORD slots. It types those formals in the body
    // and nothing else; it is discharged at every call site below.
    std::map<const Argument *, StructType *> premise;
    auto ckey = [&](const Instruction *I, const Value *A) -> std::string {
      if (!declared) return fieldKey(I, A);
      if (transientSlot(A->stripPointerCasts())) return "";
      StructType *S = nullptr;
      int64_t off = 0;
      if (!namedSlot(I, A, CDL, pointees, S, off) || !S->hasName()) {
        const auto *Arg = dyn_cast<Argument>(A->stripPointerCasts());
        auto pit = Arg ? premise.find(Arg) : premise.end();
        if (pit == premise.end()) return "";
        return innerKeyOf(pit->second, 0);
      }
      return innerKeyOf(S, off);
    };
    std::set<std::string> declHandle, declLink, declWord, unusedDecl;
    StructType *premiseOwnerT = nullptr, *premiseElemT = nullptr;
    std::vector<std::string> diMismatch;
    if (declared) {
      // Each module has its own context: a declared struct is the first
      // defined one of that name (linker suffix stripped) in any module.
      std::map<std::string, StructType *> byStructName;
      for (auto &[M, _] : Ctx->Modules)
        for (StructType *ST : M->getIdentifiedStructTypes())
          if (ST->hasName() && !ST->isOpaque()) byStructName.emplace(stripStructNameSuffix(ST->getName()).str(), ST);
      for (const auto &Sl : C.storage) {
        auto sit = byStructName.find(Sl.type);
        StructType *S = sit == byStructName.end() ? nullptr : sit->second;
        std::string K = innerKeyOf(S, Sl.off);
        if (K.empty()) {
          // A struct this program does not define (rb_root_cached in a
          // program without cached trees): unused, not a disagreement.
          unusedDecl.insert(Sl.type + "+" + std::to_string(Sl.off) + " (no such field here)");
          continue;
        }
        using CS = GlobalContext::ContainerSlot;
        (Sl.kind == CS::Handle ? declHandle : Sl.kind == CS::Link ? declLink : declWord).insert(K);
        unusedDecl.insert(K);
      }
      // Debug info, where the program has it: the links it names (pointer
      // members back into the container's structs) and the handle slots
      // (pointer members of the owner) against the declaration.
      for (const std::string &K : links)
        if (!declLink.count(K)) diMismatch.push_back("debug info names link " + K + ", not declared");
      for (const std::string &K : declLink) {
        const std::string S = StringRef(K).substr(7, K.rfind('+') - 7).str();
        if (diStructs.count(S) && !links.count(K))
          diMismatch.push_back("declared link " + K + " is no pointer back into the container by debug info");
      }
      for (const std::string &K : declHandle) {
        const std::string S = StringRef(K).substr(7, K.rfind('+') - 7).str();
        if (!diStructs.count(S)) continue;
        bool ptr = false;
        for (auto &[o, P] : ptrMembers(S)) ptr |= "struct." + S + "+" + std::to_string(o) == K;
        if (!ptr) diMismatch.push_back("declared handle " + K + " is no pointer member by debug info");
      }
      // The premise's structs: the HANDLE at +0, the LINK/LINKWORD slots'
      // (one struct each, else no premise).
      StructType *ownerT = nullptr, *elemT = nullptr;
      bool ownerOne = true, elemOne = true;
      for (const auto &Sl : C.storage) {
        auto sit = byStructName.find(Sl.type);
        if (sit == byStructName.end()) continue;
        using CS = GlobalContext::ContainerSlot;
        StructType *&T = Sl.kind == CS::Handle ? ownerT : elemT;
        bool &one = Sl.kind == CS::Handle ? ownerOne : elemOne;
        if (Sl.kind == CS::Handle && Sl.off != 0) continue;
        if (T && T != sit->second) one = false;
        T = sit->second;
      }
      if (!ownerOne) ownerT = nullptr;
      if (!elemOne) elemT = nullptr;
      premiseOwnerT = ownerT, premiseElemT = elemT;
      for (const auto &[fn, R] : C.rows) {
        auto it = byName.find(fn);
        if (it == byName.end() || !body.count(it->second)) continue;
        const Function *F = it->second;
        if (ownerT && R.owner >= 0 && R.ownerDeref < 0 && (unsigned)R.owner < F->arg_size()) premise[F->getArg(R.owner)] = ownerT;
        std::vector<int> es = R.moreElems;
        if (R.elem >= 0) es.push_back(R.elem);
        for (int e : es)
          if (elemT && (unsigned)e < F->arg_size()) premise[F->getArg(e)] = elemT;
      }
      handle = declHandle;
      links = declLink;
      links.insert(declWord.begin(), declWord.end());
    }
    const unsigned pw = CDL.getPointerSizeInBits();
    const bool wordInts = !declWord.empty(); // link words carry pointers in integers

    // Owner derivation over the body (a monotone dataflow): each pointer
    // value of a body function, relative to its owner formal: the owner
    // (OWN), derived from it through closed handle fields and then any
    // field or index (DER), null, a fresh block, the result of an insert
    // row, or anything else (OTH). Helpers' owner formals: every body call
    // passes the caller's owner there; their element formals and returns:
    // the join of what the body passes and returns.
    enum : uint8_t { NUL = 1, OWN = 2, DER = 4, FRS = 8, INS = 16, OTH = 32, PAY = 64, SEN = 128 };
    std::map<const Value *, uint8_t> cls;
    // Sentinel elements (Fable 2026-10-14): a zero-initialized global of a
    // container struct the body uses as an element ("absent").
    std::set<const GlobalVariable *> sentinels;
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        for (const Use &U : I.operands())
          if (const auto *GV = dyn_cast<GlobalVariable>(U.get()->stripPointerCasts()))
            if (GV->hasInitializer() && GV->getInitializer()->isNullValue())
              if (const auto *ST = dyn_cast<StructType>(GV->getValueType()); ST && ST->hasName())
                if (ctypes.count(StringRef(stripStructNameSuffix(ST->getName())).drop_front(7).str()))
                  sentinels.insert(GV);
    // Guards: `p->g != null` (or `== null`, its false edge) on an element
    // pointer p (a -O0 slot's reload, or an SSA value): the region the edge
    // dominates. A reload of p there is not the sentinel (its g is null:
    // the induction, checked as s3).
    struct Guard { const Value *base; BasicBlockEdge E; std::string g; };
    std::map<const Function *, std::vector<Guard>> guards;
    std::map<const Function *, std::unique_ptr<DominatorTree>> domOf;
    for (const Function *F : body) {
      domOf[F] = std::make_unique<DominatorTree>(const_cast<Function &>(*F));
      for (const BasicBlock &BB : *F) {
        const auto *BR = dyn_cast<BranchInst>(BB.getTerminator());
        const auto *IC = BR && BR->isConditional() ? dyn_cast<ICmpInst>(BR->getCondition()) : nullptr;
        if (!IC || !IC->isEquality() || !isa<ConstantPointerNull>(IC->getOperand(1))) continue;
        const auto *L = dyn_cast<LoadInst>(IC->getOperand(0));
        if (!L) continue;
        const auto *G = dyn_cast<GEPOperator>(L->getPointerOperand());
        if (!G) continue;
        const Value *P = G->getPointerOperand()->stripPointerCasts();
        if (const auto *PL = dyn_cast<LoadInst>(P); PL && transientSlot(PL->getPointerOperand()->stripPointerCasts()))
          P = PL->getPointerOperand()->stripPointerCasts();
        const BasicBlock *T = BR->getSuccessor(IC->getPredicate() == ICmpInst::ICMP_NE ? 0 : 1);
        guards[F].push_back({P, BasicBlockEdge(&BB, T), fieldKey(L, L->getPointerOperand())});
      }
    }
    std::set<std::string> sentGuardFields;
    auto storesInto = [](const Value *Slot) {
      size_t n = 0;
      for (const User *U : Slot->users())
        if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == Slot) n++;
      return n;
    };
    auto guardedAt = [&](const Value *base, const Instruction *At) {
      auto git = guards.find(At->getFunction());
      if (git == guards.end()) return false;
      for (const Guard &Gd : git->second)
        // The slot is stored once (no store between the test and the
        // reload), or the base is the SSA value itself.
        if (Gd.base == base && (!isa<AllocaInst>(base) || storesInto(base) == 1) &&
            domOf[At->getFunction()]->dominates(Gd.E, At->getParent())) {
          sentGuardFields.insert(Gd.g);
          return true;
        }
      return false;
    };
    std::map<const Function *, int> ownerIdx;
    std::map<const Function *, uint8_t> retCls;
    for (const auto &[fn, R] : C.rows)
      if (auto it = byName.find(fn); it != byName.end() && body.count(it->second) && R.owner >= 0 && R.ownerDeref < 0)
        ownerIdx[it->second] = R.owner;
    // A deref owner's loads: *(argN + off), argN directly or through an -O0
    // slot stored once with it.
    auto derefOwnerLoad = [&](const LoadInst *L, const CR &R) {
      if (!L->getType()->isPointerTy() || (unsigned)R.owner >= L->getFunction()->arg_size()) return false;
      const auto [r, o] = rootOff(L->getPointerOperand(), CDL);
      if (o != R.ownerDeref) return false;
      const Value *B = r->stripPointerCasts();
      if (const auto *BL = dyn_cast<LoadInst>(B))
        if (const Value *SL = BL->getPointerOperand()->stripPointerCasts(); transientSlot(SL)) {
          const StoreInst *only = nullptr;
          for (const User *U : SL->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == SL) {
              if (only) return false;
              only = S;
            }
          if (!only) return false;
          B = only->getValueOperand()->stripPointerCasts();
        }
      return B == L->getFunction()->getArg(R.owner);
    };
    auto rowOf = [&](const Function *G) -> const CR * {
      auto it = G ? C.rows.find(G->getName().str()) : C.rows.end();
      return it == C.rows.end() ? nullptr : &it->second;
    };
    auto get = [&](const Value *V) -> uint8_t {
      V = V->stripPointerCasts();
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return NUL;
      // A link word's null plus tag (declared LINKWORD storage).
      if (const auto *CI = dyn_cast<ConstantInt>(V); CI && CI->getValue().ult(8)) return NUL;
      if (const auto *GV = dyn_cast<GlobalVariable>(V); GV && sentinels.count(GV)) return SEN;
      if (isa<Constant>(V)) return OTH; // a global, a function: not the owner's
      auto it = cls.find(V);
      return it == cls.end() ? 0 : it->second;
    };
    // The class of an address's base (through GEPs and casts).
    auto baseOf = [&](const Value *A) {
      A = A->stripPointerCasts();
      while (const auto *G = dyn_cast<GEPOperator>(A)) A = G->getPointerOperand()->stripPointerCasts();
      return A;
    };
    // The class of what an access at address A reads (an asm's slot: the
    // call itself is the access).
    auto loadClass = [&](const Instruction *L, const Value *A) -> uint8_t {
      const Value *B = baseOf(A);
      if (transientSlot(B)) {
        uint8_t m = 0;
        for (const User *U : B->users())
          if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == B)
            m |= get(S->getValueOperand());
        if ((m & SEN) && guardedAt(B, L)) m &= ~SEN; // under `p->g != null`
        return m;
      }
      // A load through null never executes: the null part of the base
      // adds nothing.
      const uint8_t b = get(B) & ~NUL;
      const std::string K = ckey(L, A);
      uint8_t m = 0;
      if (b & OWN) m |= handle.count(K) ? DER : OTH;
      // Through an element: a link field or a storage slot (an array
      // element, no struct field) stays in the container; another field
      // is the element's payload.
      // A fresh block the body makes is contained (O3 checks it): new
      // storage or a new element, read like a derived one.
      if (b & (DER | FRS)) m |= K.empty() || links.count(K) ? DER : PAY;
      // A sentinel's field is null (s4: every store into it is guarded,
      // checked below; the container fails otherwise).
      if (b & SEN) m |= NUL;
      // Through a payload value: payload again (a cursor chased, `ret =
      // ret->u.i.link`); O2 admits it only where every payload read behind
      // it is a closed cursor field (payloadReads).
      if (b & PAY) m |= PAY;
      if (b & (INS | OTH)) m |= OTH;
      return m ? m : (b ? OTH : 0);
    };
    auto transfer = [&](const Instruction &I) -> uint8_t {
      if (poolCarves.count(&I)) return FRS; // a certified pool carve: a fresh block
      if (const auto *L = dyn_cast<LoadInst>(&I)) return loadClass(L, L->getPointerOperand());
      if (isa<GetElementPtrInst>(&I) || isa<CastInst>(&I)) return get(I.getOperand(0));
      // A link word's arithmetic (tags set, cleared, tested): the pointer it
      // carries (declared LINKWORD storage only).
      if (const auto *BO = dyn_cast<BinaryOperator>(&I)) {
        uint8_t m = 0;
        for (const Value *Op : BO->operands())
          if (!isa<Constant>(Op)) m |= get(Op);
        return m;
      }
      // An inline asm's result: what its slots and raw pointers read, as the
      // graph build models it (asmModel).
      if (const auto *CB = dyn_cast<CallBase>(&I); CB && CB->isInlineAsm()) {
        const AsmModel AM = asmModel(*CB, &CDL);
        uint8_t m = 0;
        for (const AsmModel::Slot &Sl : AM.slots)
          if (!Sl.output && Sl.load.ok) m |= loadClass(CB, Sl.ptr);
        if (AM.resPtrCapable)
          for (const Value *A : AM.rawPtrs) m |= loadClass(CB, A);
        return m ? m : OTH;
      }
      if (const auto *PN = dyn_cast<PHINode>(&I)) {
        uint8_t m = 0;
        for (const Value *In : PN->incoming_values()) m |= get(In);
        return m;
      }
      if (const auto *SL = dyn_cast<SelectInst>(&I)) return get(SL->getTrueValue()) | get(SL->getFalseValue());
      if (const auto *CB = dyn_cast<CallBase>(&I)) {
        const Function *G = CB->getCalledFunction();
        if (!G)
          if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
            const std::string K = fieldKey(CL, CL->getPointerOperand());
            if (code.count(K) && !codeOpen.count(K)) return FRS; // a constructor's new element
          }
        if (G && body.count(G) && !rowOf(G)) return retCls[G];
        if (const CR *R = rowOf(G); R && R->role == CR::Insert) return INS;
        // A lookup row of this block on the body's own owner (at its +0:
        // bfd_link_hash_lookup's `bfd_hash_lookup(&table->table, ...)`): its
        // result is an element of that owner, by the row (its own O2).
        if (const CR *R = rowOf(G); R && R->role == CR::Lookup && R->elem == -1 && R->ownerDeref < 0 &&
                                    (unsigned)R->owner < CB->arg_size()) {
          const auto [r, o] = rootOff(CB->getArgOperand(R->owner), CDL);
          if (o == 0 && get(r) == OWN) return DER | NUL;
        }
        // D7: a traverse row's result is an element of the containers that
        // contain its ELEM argument (rb_erase_cached's `rb_next(node)`).
        if (const CR *R = rowOf(G); R && R->role == CR::Traverse && R->elem >= 0 && (unsigned)R->elem < CB->arg_size())
          if (const uint8_t e = get(CB->getArgOperand(R->elem)); (e & (DER | FRS)) && !(e & ~(DER | FRS | NUL)))
            return DER | NUL;
        if (G && (Ctx->AllocFuncs.count(G) || carveFns.count(G->getName().str()))) return FRS;
        if (G)
          if (auto sit = Ctx->FuncSummaries.find(G); sit != Ctx->FuncSummaries.end() && sit->second && sit->second->fresh)
            return FRS;
        return OTH;
      }
      return OTH;
    };
    for (bool changed = true; changed;) {
      changed = false;
      auto join = [&](const Value *V, uint8_t m) {
        uint8_t &c = cls[V];
        if ((c | m) != c) c |= m, changed = true;
      };
      std::vector<const Function *> classified(body.begin(), body.end());
      classified.insert(classified.end(), derefFns.begin(), derefFns.end());
      for (const Function *F : classified) {
        auto oit = ownerIdx.find(F);
        for (const Argument &A : F->args())
          if (A.getType()->isPointerTy() && oit != ownerIdx.end() && (int)A.getArgNo() == oit->second) join(&A, OWN);
        if (const CR *R = rowOf(F); R && R->ownerDeref >= 0)
          for (const Instruction &I : instructions(*F))
            if (const auto *L = dyn_cast<LoadInst>(&I); L && derefOwnerLoad(L, *R)) join(L, OWN);
        // An insert row's ELEM(argN): the element coming in (O3 checks it
        // goes only into the owner's storage), like a new element.
        if (const CR *R = rowOf(F); R && R->role == CR::Insert) {
          if (R->elem >= 0 && (unsigned)R->elem < F->arg_size()) join(F->getArg(R->elem), FRS);
          for (int e : R->moreElems)
            if ((unsigned)e < F->arg_size()) join(F->getArg(e), FRS);
        }
        // A remove's or a traverse's ELEM(argN): an element already in the
        // container (rb_erase's node, rb_next's start), read like a derived one.
        if (const CR *R = rowOf(F); R && (R->role == CR::Remove || R->role == CR::Traverse) && R->elem >= 0 &&
                                    (unsigned)R->elem < F->arg_size())
          join(F->getArg(R->elem), DER);
        for (const Instruction &I : instructions(*F)) {
          // Pointers; and with declared link words, pointer-width integers
          // (a link word's load, its tags, ptrtoint and inttoptr).
          if (I.getType()->isPointerTy() || (wordInts && I.getType()->isIntegerTy(pw))) join(&I, transfer(I));
          if (const auto *RI = dyn_cast<ReturnInst>(&I); RI && RI->getReturnValue()) {
            uint8_t &r = retCls[F];
            const uint8_t m = get(RI->getReturnValue());
            if ((r | m) != r) r |= m, changed = true;
          }
          // Actuals into a body helper: its owner formal (the caller's
          // owner passed there by every call) and its element formals.
          const auto *CB = dyn_cast<CallBase>(&I);
          const Function *G = CB ? CB->getCalledFunction() : nullptr;
          if (!G || !body.count(G) || rowOf(G)) continue;
          for (unsigned a = 0; a < CB->arg_size() && a < G->arg_size(); a++) {
            if (!G->getArg(a)->getType()->isPointerTy()) continue;
            uint8_t m = get(CB->getArgOperand(a));
            if (m == OWN) {
              auto [it, ins] = ownerIdx.try_emplace(G, (int)a);
              if (ins) changed = true;
              if (it->second == (int)a) continue;
            }
            // A value derived from the caller's owner is derived from the
            // callee's only when the callee's owner formal gets that owner.
            auto git = ownerIdx.find(G);
            const bool sameOwner = git != ownerIdx.end() && oit != ownerIdx.end() &&
                                   get(CB->getArgOperand(git->second)) == OWN;
            if ((m & DER) && !sameOwner) m = (m & ~DER) | OTH;
            join(G->getArg(a), m);
          }
        }
      }
    }
    // Sentinel checks s1-s4 (Fable 2026-10-14), each printed.
    std::vector<std::string> sentLines;
    bool sentOk = true;
    for (const GlobalVariable *GV : sentinels) {
      std::string s1 = "PASS", s3 = "PASS";
      std::function<void(const Value *)> users = [&](const Value *V) {
        for (const User *U : V->users()) {
          if (const auto *CE = dyn_cast<ConstantExpr>(U)) { users(CE); continue; }
          const auto *I = dyn_cast<Instruction>(U);
          if (!I || !body.count(I->getFunction())) s1 = "FAIL(used outside the body)";
        }
      };
      users(GV);
      size_t guardedStores = 0, unguarded = 0;
      for (const Function *F : body)
        for (const Instruction &I : instructions(*F)) {
          const Value *Addr = nullptr;
          if (const auto *S = dyn_cast<StoreInst>(&I)) {
            Addr = S->getPointerOperand();
            const uint8_t v = get(S->getValueOperand());
            if ((v & SEN) && !transientSlot(baseOf(S->getPointerOperand()))) s1 = "FAIL(stored to memory)";
          } else if (const auto *MI = dyn_cast<MemIntrinsic>(&I)) {
            Addr = MI->getDest();
          } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
            const Function *G = CB->getCalledFunction();
            if (!(G && body.count(G) && !rowOf(G)))
              for (const Use &A : CB->args())
                if (get(A.get()) & SEN) s1 = "FAIL(passed to " + (G ? G->getName().str() : std::string("an icall")) + ")";
          } else if (const auto *RI = dyn_cast<ReturnInst>(&I); RI && RI->getReturnValue() && rowOf(F) &&
                                                                 (get(RI->getReturnValue()) & SEN)) {
            s1 = "FAIL(returned by the row " + F->getName().str() + ")";
          }
          if (!Addr) continue;
          // Guarded stores were refined (their pointer is no sentinel): a
          // store whose pointer may still be the sentinel is unguarded.
          if (get(baseOf(Addr)) & SEN) {
            unguarded++;
            if (s3 == "PASS") s3 = "FAIL(" + F->getName().str() + ": " + valueText(&I) + ")";
          }
        }
      for (const auto &[F, gs] : guards)
        for (const Guard &Gd : gs) (void)Gd, guardedStores += 0;
      std::string gf;
      for (const std::string &g : sentGuardFields) gf += (gf.empty() ? "" : " ") + g;
      const bool ok = s1 == "PASS" && s3 == "PASS" && !sentGuardFields.empty();
      sentOk &= ok;
      sentLines.push_back("sentinel element " + GV->getName().str() + ": s1 " + s1 + "; s2 " +
                          (sentGuardFields.empty() ? std::string("FAIL(no guard)") : "PASS(guard field " + gf + ")") +
                          "; s3 " + s3 + "; s4 " + (unguarded ? std::string("FAIL") : std::string("PASS(every field)")) +
                          (ok ? "" : " -> not a sentinel"));
    }
    // O1, element moves within one owner (pending ruling): a store into the
    // owner's handle field, in the body, of a value derived from the same
    // owner.
    size_t moves = 0;
    std::map<const MemTransferInst *, std::string> snapRestores; // a snapshot holder's restores -> the holder
    std::set<const MemTransferInst *> snapUnreachable; // restores of a holder unreachable by name (its ASSUMPTION listed)
    size_t snapMoves = 0, snapUnreach = 0;
    std::map<std::string, const StoreInst *> firstBad1;
    // A store, in the body, into the owner or one of its elements (or a
    // fresh element of the body), of a value derived from the same owner
    // or null: an element moving within one owner.
    auto isMove = [&](const StoreInst *S) {
      const uint8_t a = get(baseOf(S->getPointerOperand())) & ~NUL, v = get(S->getValueOperand());
      return body.count(S->getFunction()) && a && !(a & ~(OWN | DER | FRS)) && v && !(v & ~(DER | NUL | FRS));
    };
    const DataLayout &DL0 = Ctx->Modules.front().first->getDataLayout();
    // (d) Inline inserts (Fable 2026-10-14): the constructors (code-field
    // targets) and the argument the owner is passed at.
    std::map<const Function *, unsigned> ctorsHere;
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        if (const auto *CB = dyn_cast<CallBase>(&I); CB && !CB->getCalledFunction())
          if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
            const std::string K = fieldKey(CL, CL->getPointerOperand());
            if (code.count(K) && !codeOpen.count(K))
              for (unsigned a = 0; a < CB->arg_size(); a++)
                if (get(CB->getArgOperand(a)) == OWN)
                  for (const Function *T : codeTargets[K]) ctorsHere.emplace(T, a);
          }
    // An owner value by its shape: through casts, -O0 slots stored once and
    // constant address steps (`&abfd->section_htab` computed twice is one).
    std::function<std::string(const Value *, int)> ownerShape;
    // S6 (Fable 2026-10-16): two loads of one named slot (the same field key
    // at the same address shape), the first dominating the second, are one
    // value when every write between them is named and its name differs from
    // the slot's (a row call writes its declared storage): checked. An
    // unnamed write or a call to a function that is not a row between them
    // makes the identity a per-site ASSUMPTION "owner re-read from the same
    // slot"; a write of the slot's own name keeps them apart. The earlier
    // read: the nearest, then its own earlier read.
    struct Reread {
      const LoadInst *first = nullptr;
      bool assumed = false;
      bool across = false; // read at the reads' nearest common dominator (S6 across branches)
    };
    std::map<const LoadInst *, Reread> rereadMemo;
    std::map<const Function *, std::map<std::string, std::vector<const LoadInst *>>> loadsByKey;
    std::map<const LoadInst *, Reread> rereadsUsed; // the identities shapes used (listed)
    bool rereadQuiet = false;                       // inside the check itself: not a use
    // The writes on the paths from a read to L2 that run neither again (the
    // rest of the read's block, the blocks between, the head of L2's block);
    // from the end of block BA when L1 is null (a virtual read there). -1:
    // the name written (apart); 0: every write named, none of the name
    // (checked); 1: an unnamed write or a call that is not a row (assumed).
    auto spanCheck = [&](const BasicBlock *BA, const Instruction *L1, const Instruction *L2,
                         const std::string &N) -> int {
      const BasicBlock *BB = L2->getParent();
      std::vector<const Instruction *> span;
      if (BA == BB) {
        if (!L1) return -1; // a virtual read at the end of L2's own block: not built
        for (const Instruction *I = L1->getNextNode(); I && I != L2; I = I->getNextNode()) span.push_back(I);
      } else {
        if (L1)
          for (const Instruction *I = L1->getNextNode(); I; I = I->getNextNode()) span.push_back(I);
        for (const Instruction &I : *BB) {
          if (&I == L2) break;
          span.push_back(&I);
        }
        std::set<const BasicBlock *> fwd, bwd;
        std::vector<const BasicBlock *> wl;
        for (const BasicBlock *S : successors(BA))
          if (S != BA && S != BB && fwd.insert(S).second) wl.push_back(S);
        while (!wl.empty()) {
          const BasicBlock *X = wl.back();
          wl.pop_back();
          for (const BasicBlock *S : successors(X))
            if (S != BA && S != BB && fwd.insert(S).second) wl.push_back(S);
        }
        for (const BasicBlock *P : predecessors(BB))
          if (P != BA && P != BB && bwd.insert(P).second) wl.push_back(P);
        while (!wl.empty()) {
          const BasicBlock *X = wl.back();
          wl.pop_back();
          for (const BasicBlock *P : predecessors(X))
            if (P != BA && P != BB && bwd.insert(P).second) wl.push_back(P);
        }
        for (const BasicBlock *X : fwd)
          if (bwd.count(X))
            for (const Instruction &I : *X) span.push_back(&I);
      }
      const size_t np = N.rfind('+');
      const std::string NS = N.substr(0, np);
      const int64_t NO = std::stoll(N.substr(np + 1));
      bool assumed = false;
      for (const Instruction *W : span) {
        if (!W->mayWriteToMemory() || isa<FenceInst>(W) || isa<DbgInfoIntrinsic>(W)) continue;
        if (const auto *II = dyn_cast<IntrinsicInst>(W);
            II && (II->isAssumeLikeIntrinsic() || II->getIntrinsicID() == Intrinsic::lifetime_start ||
                   II->getIntrinsicID() == Intrinsic::lifetime_end))
          continue;
        const Value *P = nullptr;
        if (const auto *S = dyn_cast<StoreInst>(W)) P = S->getPointerOperand();
        else if (const auto *RMW = dyn_cast<AtomicRMWInst>(W)) P = RMW->getPointerOperand();
        else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(W)) P = CX->getPointerOperand();
        if (P) {
          const std::string K = ckey(W, P);
          if (K.empty()) assumed = true;
          else if (K == N) return -1;
          continue;
        }
        if (const auto *MI = dyn_cast<MemIntrinsic>(W)) {
          StructType *S = nullptr;
          int64_t off = 0;
          const auto *Len = dyn_cast<ConstantInt>(MI->getLength());
          if (!Len || !namedSlot(W, MI->getRawDest(), CDL, pointees, S, off) || !S->hasName()) {
            assumed = true;
            continue;
          }
          bool hits = false;
          structCover(S, off, off + (int64_t)Len->getZExtValue(), CDL, [&](StructType *ST, int64_t lo, int64_t hi) {
            hits |= ST->hasName() && stripStructNameSuffix(ST->getName()) == NS && NO >= lo && NO < hi;
          });
          if (hits) return -1;
          continue;
        }
        if (const auto *CB = dyn_cast<CallBase>(W)) {
          const Function *G = CB->getCalledFunction();
          auto rit = G ? C.rows.find(G->getName().str()) : C.rows.end();
          if (rit != C.rows.end()) {
            if (declHandle.count(N) || declLink.count(N) || declWord.count(N) || handle.count(N) || links.count(N))
              return -1;
            continue;
          }
        }
        assumed = true;
      }
      return assumed ? 1 : 0;
    };
    std::function<Reread(const LoadInst *, int)> sameRead = [&](const LoadInst *L2, int d) -> Reread {
      if (auto it = rereadMemo.find(L2); it != rereadMemo.end()) return it->second;
      rereadMemo[L2] = Reread{}; // a cycle reads as none
      if (d > 4 || !L2->getType()->isPointerTy()) return Reread{};
      const Function *F = L2->getFunction();
      auto lit = loadsByKey.find(F);
      if (lit == loadsByKey.end()) {
        lit = loadsByKey.emplace(F, std::map<std::string, std::vector<const LoadInst *>>()).first;
        for (const Instruction &I : instructions(*F))
          if (const auto *L = dyn_cast<LoadInst>(&I); L && L->getType()->isPointerTy())
            if (std::string K = ckey(L, L->getPointerOperand()); !K.empty()) lit->second[K].push_back(L);
      }
      const std::string N = ckey(L2, L2->getPointerOperand());
      auto kit = N.empty() ? lit->second.end() : lit->second.find(N);
      if (kit == lit->second.end() || kit->second.size() < 2) return Reread{};
      auto &DT = domOf[F];
      if (!DT) DT = std::make_unique<DominatorTree>(const_cast<Function &>(*F));
      const bool q = rereadQuiet;
      rereadQuiet = true;
      const std::string sh2 = ownerShape(L2->getPointerOperand(), d + 1);
      const LoadInst *L1 = nullptr; // the nearest dominating read
      if (!sh2.empty())
        for (const LoadInst *L : kit->second)
          if (L != L2 && DT->dominates(L, L2) && (!L1 || DT->dominates(L1, L)) &&
              ownerShape(L->getPointerOperand(), d + 1) == sh2)
            L1 = L;
      rereadQuiet = q;
      int c = -1;
      Reread out;
      if (L1) {
        c = spanCheck(L1->getParent(), L1, L2, N);
        if (c < 0) return Reread{};
        out = Reread{L1, c == 1, false};
      } else {
        // Across branches (Fable 2026-10-16): an earlier read in a sibling
        // block, the two one value read at their nearest common dominator D
        // when no path from D to either writes the name (S6's write test).
        const bool q2 = rereadQuiet;
        rereadQuiet = true;
        for (const LoadInst *L : kit->second) {
          if (L == L2) break;
          if (DT->dominates(L, L2) || DT->dominates(L2, L) || ownerShape(L->getPointerOperand(), d + 1) != sh2) continue;
          const BasicBlock *D = DT->findNearestCommonDominator(L->getParent(), L2->getParent());
          if (!D || D == L->getParent() || D == L2->getParent()) continue;
          const int a = spanCheck(D, nullptr, L, N), b = spanCheck(D, nullptr, L2, N);
          if (a < 0 || b < 0) continue;
          out = Reread{L, a == 1 || b == 1, true};
          break;
        }
        rereadQuiet = q2;
        if (!out.first) return Reread{};
      }
      L1 = out.first;
      if (const Reread r = sameRead(L1, d + 1); r.first) out = {r.first, out.assumed || r.assumed, out.across || r.across};
      rereadMemo[L2] = out;
      return out;
    };
    ownerShape = [&](const Value *V, int d) -> std::string {
      V = V->stripPointerCasts();
      if (d > 8) return "";
      if (const auto *L = dyn_cast<LoadInst>(V))
        if (const Value *SL = L->getPointerOperand()->stripPointerCasts(); transientSlot(SL)) {
          const StoreInst *only = nullptr;
          for (const User *U : SL->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == SL) {
              if (only) return "";
              only = S;
            }
          return only ? ownerShape(only->getValueOperand(), d + 1) : "";
        }
      // A phi or select whose entries agree is that value (Fable 2026-10-16
      // S3: rb_add_cached computes `&root->rb_root` on both paths).
      if (isa<PHINode>(V) || isa<SelectInst>(V)) {
        std::vector<const Value *> ins;
        if (const auto *PN = dyn_cast<PHINode>(V)) ins.assign(PN->incoming_values().begin(), PN->incoming_values().end());
        else ins = {cast<SelectInst>(V)->getTrueValue(), cast<SelectInst>(V)->getFalseValue()};
        std::string agreed;
        bool ok = true;
        for (const Value *In : ins) {
          if (In->stripPointerCasts() == V) continue;
          const std::string x = d < 6 ? ownerShape(In, d + 2) : "";
          if (x.empty() || (!agreed.empty() && x != agreed)) ok = false;
          agreed = x;
        }
        if (ok && !agreed.empty()) return agreed;
      }
      // Constant steps fold into one offset from the object (Fable
      // 2026-10-15, 4(b)): `&root->rb_root` (+0) is the owner `root`.
      if (const auto *G = dyn_cast<GEPOperator>(V)) {
        APInt Off(64, 0);
        if (!G->accumulateConstantOffset(DL0, Off)) return "";
        const std::string b = ownerShape(G->getPointerOperand(), d + 1);
        if (b.empty()) return "";
        const size_t p = b.find('+');
        const int64_t o = (p == std::string::npos ? 0 : std::stoll(b.substr(p + 1))) + Off.getSExtValue();
        const std::string root = p == std::string::npos ? b : b.substr(0, p);
        return o ? root + "+" + std::to_string(o) : root;
      }
      // A re-read of a named slot is its first read (S6).
      if (const auto *L = dyn_cast<LoadInst>(V))
        if (const Reread r = sameRead(L, d); r.first) {
          if (!rereadQuiet) rereadsUsed.emplace(L, r);
          V = r.first;
        }
      std::string t;
      raw_string_ostream os(t);
      os << (const void *)V;
      return os.str();
    };
    // Outside the body: the owner a value is an element of (a row's or a
    // constructor's result, through casts, -O0 slots whose stores agree,
    // phis and selects whose entries agree, constant steps, and a closed
    // cursor field read from an element); "" if none. kAny agrees with any
    // owner: a cycle through a slot or a cursor (the greatest fixpoint's),
    // or an out-parameter's pointee (Q-c: assumed, listed per site).
    const std::string kAny = "\x01";
    std::set<const Value *> eoOnPath;
    // All container verdicts are one greatest fixpoint (Fable 2026-10-17):
    // whatever is under way, a cursor field or a value, is assumed (closed,
    // an element) inside the evaluations it encloses, and every verdict
    // that rested on it is withdrawn when it ends otherwise. A value under
    // way met by an element test of a cursor's store (elementStored) is
    // assumed an element; the cursor fields whose checks began inside the
    // value's evaluation lean on it (valueLeans).
    std::vector<std::string> cursorStack;                      // cursor fields under way (below)
    std::vector<const Value *> eoHits;                         // values under way an evaluation met
    std::map<const Value *, size_t> eoPathDepth;               // value under way -> cursorStack depth at its start
    std::map<const Value *, std::set<std::string>> valueLeans; // value under way -> fields that assumed it an element
    std::function<void(const std::set<std::string> &)> withdrawCursors;
    // Assumptions an answer rests on, pending until its caller admits it.
    std::vector<std::string> eoPending;
    std::set<std::string> outParamAssumed, cursorInstance, derefReadAssumed;
    std::set<std::string> holderAssumed, holderInstance; // rule A: reads of open holders; closed holders used
    std::set<std::string> p3Assumed; // P3: cursor reads of both schemes, the stores excluded by member name
    std::set<std::string> uncheckedCursor; // "field\tread": a cursor read admitted by an UNCHECKED census key
    std::set<const CallBase *> derefReadChecked; // by instruction: ownerShape re-evaluates a row call's owner
    auto eoMark = [&]() { return eoPending.size(); };
    auto eoSettle = [&](size_t mark, bool admitted) {
      if (admitted)
        for (size_t i = mark; i < eoPending.size(); i++) {
          const std::string &a = eoPending[i];
          (a[0] == 'o'   ? outParamAssumed
           : a[0] == 'c' ? cursorInstance
           : a[0] == 'u' ? uncheckedCursor
           : a[0] == 'h' ? holderAssumed
           : a[0] == 'k' ? holderInstance
           : a[0] == 'x' ? p3Assumed
                         : derefReadAssumed)
              .insert(a.substr(1));
        }
      eoPending.resize(mark);
    };
    // A load of a formal's pointee at +0 (`*hashp`): the caller's out-parameter.
    auto outParamRead = [&](const Value *V) {
      const auto *L = dyn_cast<LoadInst>(V);
      if (!L || !L->getType()->isPointerTy() || body.count(L->getFunction())) return false;
      const auto [r, o] = rootOff(L->getPointerOperand(), CDL);
      if (o != 0) return false;
      const Value *B = r->stripPointerCasts();
      if (const auto *BL = dyn_cast<LoadInst>(B))
        if (const Value *SL = BL->getPointerOperand()->stripPointerCasts(); transientSlot(SL)) {
          const StoreInst *only = nullptr;
          for (const User *U : SL->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == SL) {
              if (only) return false;
              only = S;
            }
          if (!only) return false;
          B = only->getValueOperand()->stripPointerCasts();
        }
      return isa<Argument>(B);
    };
    // The owner shape of a deref row's owner, *(A + off) read at call CB: a
    // real read of that slot in the function it is one value with (S6: the
    // nearest dominating one, else across branches from the nearest common
    // dominator); none, a value of its own.
    auto derefOwnerShape = [&](const CallBase *CB, const Value *A, int64_t off) -> std::string {
      const std::string b = ownerShape(A, 0);
      auto self = [&] {
        std::string t;
        raw_string_ostream os(t);
        os << "*" << (const void *)CB;
        return os.str();
      };
      if (b.empty()) return self();
      const size_t p = b.find('+');
      const int64_t o = (p == std::string::npos ? 0 : std::stoll(b.substr(p + 1))) + off;
      const std::string want = (p == std::string::npos ? b : b.substr(0, p)) + (o ? "+" + std::to_string(o) : "");
      const Function *F = CB->getFunction();
      auto &DT = domOf[F];
      if (!DT) DT = std::make_unique<DominatorTree>(const_cast<Function &>(*F));
      const bool q = rereadQuiet;
      rereadQuiet = true;
      std::vector<const LoadInst *> cands;
      for (const Instruction &I : instructions(*F))
        if (const auto *L = dyn_cast<LoadInst>(&I); L && L->getType()->isPointerTy() && !ckey(L, L->getPointerOperand()).empty() &&
                                                    ownerShape(L->getPointerOperand(), 0) == want)
          cands.push_back(L);
      rereadQuiet = q;
      const LoadInst *L1 = nullptr;
      for (const LoadInst *L : cands)
        if (DT->dominates(L, CB) && (!L1 || DT->dominates(L1, L))) L1 = L;
      int c = -1;
      if (L1) c = spanCheck(L1->getParent(), L1, CB, ckey(L1, L1->getPointerOperand()));
      else
        for (const LoadInst *L : cands) {
          if (DT->dominates(CB, L)) continue;
          const BasicBlock *D = DT->findNearestCommonDominator(L->getParent(), CB->getParent());
          if (!D || D == L->getParent() || D == CB->getParent()) continue;
          const std::string N = ckey(L, L->getPointerOperand());
          const int a = spanCheck(D, nullptr, L, N), e = spanCheck(D, nullptr, CB, N);
          if (a < 0 || e < 0) continue;
          L1 = L, c = a == 1 || e == 1;
          break;
        }
      if (!L1 || c < 0) return self();
      const std::string site = F->getName().str() + ": " + valueText(CB) + " (owner read as " + valueText(L1) + ")";
      if (c == 1) eoPending.push_back("d" + site);
      else derefReadChecked.insert(CB);
      return ownerShape(L1, 0);
    };
    std::function<std::string(const Value *)> cursorClosed;
    std::function<std::string(const std::string &, const LoadInst *)> uncheckedOf; // (below)
    // Named holders (Fable 2026-10-17, rule A): memory that is no field of
    // an element but holds entries, its every store enumerated by name
    // (never by flow facts): (2) a local whose address goes only to call
    // actuals, loads and stores, through each callee formal that receives
    // it, transitively (the formal's uses closed the same way); (3) the
    // pointee array of a named pointer field (elf_obj_tdata's sym_hashes):
    // the stores through pointers derived by name from reads of that field.
    // (1), a field of an element, is the cursor above. A read of a holder
    // whose stores are all null or elements of one owner is an element of
    // it, under the premise that the element stored there is of the same
    // table instance; OPEN-REFUTED (a store of a value known to be no
    // element: a global, a function, an integer) it is no element; OPEN-
    // UNPROVEN (a store of a value of unknown status, a use no rule
    // follows) it is admitted under a per-site ASSUMPTION naming what keeps
    // the holder open. Holder reads are evaluated in the same greatest
    // fixpoint (the holder is a value under way while its stores are).
    struct Holder {
      std::string name;                                            // for reports
      const Value *key = nullptr;                                  // its eoOnPath key
      std::vector<std::pair<const Value *, std::string>> stores;   // stored value, site
      std::vector<std::string> open;                               // uses no rule follows
    };
    std::map<const Value *, Holder> localHolders;
    std::set<const Value *> localArraysRefused; // (3') locals with a fresh block and another store
    std::set<const Value *> afOnPath;           // locals under derivation (arrayFieldOf)
    std::map<std::string, Holder> arrayHolders;
    // A value known to be no element (OPEN-REFUTED), or "".
    auto refutedClass = [&](const Value *V) -> std::string {
      V = V->stripPointerCasts();
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return "";
      if (isa<Function>(V)) return "a function";
      if (isa<IntToPtrInst>(V) || isa<ConstantInt>(V)) return "an integer";
      if (isa<GlobalVariable>(V)) return "a global object";
      if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
        if (CE->getOpcode() == Instruction::IntToPtr) return "an integer";
        if (isa<GlobalVariable>(CE->stripPointerCasts()) || isa<GEPOperator>(CE)) return "a global object";
      }
      return "";
    };
    auto siteOf = [&](const Instruction *I) { return I->getFunction()->getName().str() + ": " + valueText(I); };
    // (2) The uses of a holder pointer (the local, or a formal that receives
    // it, with its -O0 spill reloads): stores into it, reads, actuals of
    // direct calls (followed into the formal); anything else keeps it open.
    std::function<void(const Value *, Holder &, std::set<const Value *> &)> holderUses =
        [&](const Value *P, Holder &H, std::set<const Value *> &seen) {
      if (!seen.insert(P).second) return;
      for (const User *U : P->users()) {
        const auto *I = dyn_cast<Instruction>(U);
        if (!I || isa<DbgInfoIntrinsic>(I)) continue;
        if (const auto *L = dyn_cast<LoadInst>(I); L && L->getPointerOperand() == P) continue;
        if (isa<ICmpInst>(I)) continue; // a comparison of the pointer (`hashp != NULL`) reads nothing
        if (const auto *S = dyn_cast<StoreInst>(I)) {
          if (S->getPointerOperand() == P && S->getValueOperand() != P) {
            H.stores.push_back({S->getValueOperand(), siteOf(S)});
            continue;
          }
          // A formal's -O0 spill: its reloads are the formal.
          if (const auto *A = dyn_cast<Argument>(P); A && S->getValueOperand() == P &&
                                                     transientSlot(S->getPointerOperand()->stripPointerCasts())) {
            const Value *SL = S->getPointerOperand()->stripPointerCasts();
            size_t n = 0;
            for (const User *V : SL->users())
              if (isa<StoreInst>(V)) n++;
            if (n == 1) {
              for (const User *V : SL->users())
                if (const auto *R = dyn_cast<LoadInst>(V)) holderUses(R, H, seen);
              continue;
            }
          }
          H.open.push_back("its address stored at " + siteOf(S));
          continue;
        }
        if (const auto *CB = dyn_cast<CallBase>(I)) {
          const Function *G = CB->getCalledFunction();
          bool followed = false;
          for (unsigned k = 0; k < CB->arg_size(); k++)
            if (CB->getArgOperand(k) == P) {
              if (!G || G->isDeclaration() || k >= G->arg_size()) {
                H.open.push_back("passed to " + std::string(G ? "a bodiless call" : "an indirect call") + " at " +
                                 siteOf(CB));
                followed = true;
                break;
              }
              holderUses(G->getArg(k), H, seen);
              followed = true;
            }
          if (followed) continue;
        }
        H.open.push_back("a use at " + siteOf(I));
      }
    };
    auto localHolder = [&](const AllocaInst *A) -> Holder & {
      auto [it, ins] = localHolders.try_emplace(A);
      if (!ins) return it->second;
      it->second.name = "local " + A->getFunction()->getName().str() + ": " + valueText(A);
      it->second.key = A;
      std::set<const Value *> seen;
      holderUses(A, it->second, seen);
      return it->second;
    };
    // (3) The named pointer field whose pointee array an address derives
    // from (through index steps, -O0 locals whose stores all derive from it,
    // phis), or "".
    std::function<std::string(const Value *, int)> arrayFieldOf = [&](const Value *P, int d) -> std::string {
      P = P->stripPointerCasts();
      if (d > 8) return "";
      if (const auto *G = dyn_cast<GEPOperator>(P)) {
        if (G->getSourceElementType()->isStructTy()) return "";
        return arrayFieldOf(G->getPointerOperand(), d + 1);
      }
      if (const auto *L = dyn_cast<LoadInst>(P)) {
        const Value *SL = L->getPointerOperand()->stripPointerCasts();
        if (transientSlot(SL)) {
          // A local under derivation (`p = p + 1`) agrees with the rest.
          if (!afOnPath.insert(SL).second) return std::string(1, '\x01');
          struct Pop { std::set<const Value *> &s; const Value *v; ~Pop() { s.erase(v); } } pop{afOnPath, SL};
          // (3') A local every store of which is a fresh block (or null)
          // holds the pointee array of that block (Fable 2026-10-17); a
          // local whose stores all derive from one holder is that holder.
          std::string k;
          size_t fresh = 0, other = 0;
          for (const User *U : SL->users())
            if (const auto *S = dyn_cast<StoreInst>(U)) {
              if (isa<ConstantPointerNull>(S->getValueOperand()->stripPointerCasts())) continue;
              if (freshOf(S->getValueOperand(), 0)) { fresh++; continue; }
              const std::string x = arrayFieldOf(S->getValueOperand(), d + 1);
              if (x == std::string(1, '\x01')) continue; // itself, under derivation
              if (x.empty() || (!k.empty() && x != k)) other++;
              else k = x;
            }
          if (fresh && !other && k.empty())
            return "local " + L->getFunction()->getName().str() + ": " + valueText(SL);
          if (fresh) localArraysRefused.insert(SL); // a fresh block, and a store of another pointer
          return other || fresh ? "" : k;
        }
        if (!L->getType()->isPointerTy()) return "";
        return fieldKey(L, L->getPointerOperand());
      }
      if (const auto *PN = dyn_cast<PHINode>(P)) {
        std::string k;
        for (const Value *In : PN->incoming_values()) {
          if (isa<ConstantPointerNull>(In->stripPointerCasts())) continue;
          const std::string x = arrayFieldOf(In, d + 1);
          if (x == std::string(1, '\x01')) continue;
          if (x.empty() || (!k.empty() && x != k)) return "";
          k = x;
        }
        return k;
      }
      return "";
    };
    auto arrayHolder = [&](const std::string &K, const Value *first) -> Holder & {
      auto [it, ins] = arrayHolders.try_emplace(K);
      if (!ins) return it->second;
      Holder &H = it->second;
      H.name = "the array " + K + " points to";
      H.key = first;
      // A local's block (3') is reached by name only in the local's own
      // function (and the callees it passes a pointer into to, followed);
      // a field's array anywhere.
      std::vector<const Function *> scope;
      if (K.rfind("local ", 0) == 0) scope.push_back(cast<Instruction>(first)->getFunction());
      else
        for (auto &[M, _] : Ctx->Modules)
          for (const Function &F : *M) scope.push_back(&F);
      for (const Function *FP : scope)
          for (const Instruction &I : instructions(*FP)) {
            if (const auto *S = dyn_cast<StoreInst>(&I)) {
              if (S->getValueOperand()->getType()->isPointerTy() && arrayFieldOf(S->getPointerOperand(), 0) == K)
                H.stores.push_back({S->getValueOperand(), siteOf(S)});
              else if (S->getValueOperand()->getType()->isPointerTy() &&
                       !transientSlot(S->getPointerOperand()->stripPointerCasts()) &&
                       fieldKey(S, S->getPointerOperand()) != K && arrayFieldOf(S->getValueOperand(), 0) == K)
                H.open.push_back("a pointer into it stored at " + siteOf(S));
              // The field itself: a fresh block (an allocator's result) or
              // null, or another pointer into the same array.
              else if (S->getValueOperand()->getType()->isPointerTy() && fieldKey(S, S->getPointerOperand()) == K) {
                const Value *V = S->getValueOperand()->stripPointerCasts();
                if (!isa<ConstantPointerNull>(V) && !isa<CallBase>(V) && arrayFieldOf(V, 0) != K)
                  H.open.push_back("the field set at " + siteOf(S));
              }
            } else if (const auto *CB = dyn_cast<CallBase>(&I); CB && !isa<MemIntrinsic>(CB)) {
              // A pointer into the array passed on: followed into the
              // callee's formal (its stores through it are the array's),
              // like a local holder's.
              for (unsigned k = 0; k < CB->arg_size(); k++) {
                const Value *A = CB->getArgOperand(k);
                if (!A->getType()->isPointerTy() || arrayFieldOf(A, 0) != K) continue;
                const Function *G = CB->getCalledFunction();
                if (!G || G->isDeclaration() || k >= G->arg_size()) {
                  if (!isa<IntrinsicInst>(CB))
                    H.open.push_back("passed to " + std::string(G ? "a bodiless call" : "an indirect call") + " at " +
                                     siteOf(CB));
                  continue;
                }
                std::set<const Value *> seen;
                holderUses(G->getArg(k), H, seen);
              }
            } else if (const auto *MI = dyn_cast<MemIntrinsic>(&I)) {
              if (arrayFieldOf(MI->getRawDest(), 0) != K) continue;
              if (const auto *MS = dyn_cast<MemSetInst>(MI))
                if (const auto *Z = dyn_cast<ConstantInt>(MS->getValue()); Z && Z->isZero()) continue; // null fill
              H.open.push_back("a block write at " + siteOf(MI));
            }
          }
      return H;
    };
    std::function<std::string(const Value *, int)> elemOwnerR = [&](const Value *V, int d) -> std::string {
      V = V->stripPointerCasts();
      if (d > 12) return "";
      // Several entries (a slot's stores, a phi's or select's values), null
      // aside: every one an element of one owner.
      auto agree = [&](const Value *Key, const std::vector<const Value *> &ins) -> std::string {
        if (!eoOnPath.insert(Key).second) {
          eoHits.push_back(Key);
          return kAny;
        }
        eoPathDepth[Key] = cursorStack.size();
        std::string agreed;
        bool ok = true, any = false;
        for (const Value *In : ins) {
          if (isa<ConstantPointerNull>(In->stripPointerCasts()) || isa<UndefValue>(In)) continue;
          any = true;
          const std::string x = elemOwnerR(In, d + 1);
          if (x.empty() || (x != kAny && !agreed.empty() && x != agreed)) {
            ok = false;
            break;
          }
          if (x != kAny) agreed = x;
        }
        eoOnPath.erase(Key);
        eoPathDepth.erase(Key);
        if (auto lit = valueLeans.find(Key); lit != valueLeans.end()) {
          // Not an element after all: the fields that assumed it decide again.
          const std::set<std::string> leaned = std::move(lit->second);
          valueLeans.erase(lit);
          if (!ok || !any) withdrawCursors(leaned);
        }
        if (!ok || !any) return "";
        return agreed.empty() ? kAny : agreed;
      };
      if (const auto *L = dyn_cast<LoadInst>(V)) {
        if (const Value *SL = L->getPointerOperand()->stripPointerCasts(); transientSlot(SL)) {
          std::vector<const Value *> ins;
          for (const User *U : SL->users())
            if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == SL)
              ins.push_back(S->getValueOperand());
          return agree(SL, ins);
        }
        // Q-c (Fable 2026-10-16): the caller's out-parameter, assumed an element
        // of the owner the other entries agree on.
        if (outParamRead(L)) {
          eoPending.push_back("o" + L->getFunction()->getName().str() + ": " + valueText(L));
          return kAny;
        }
        // A read of a named holder (rule A).
        if (L->getType()->isPointerTy() && !body.count(L->getFunction())) {
          Holder *H = nullptr;
          const Value *SL = L->getPointerOperand()->stripPointerCasts();
          if (const auto *A = dyn_cast<AllocaInst>(SL); A && !transientSlot(A)) H = &localHolder(A);
          else if (fieldKey(L, L->getPointerOperand()).empty())
            if (const std::string K = arrayFieldOf(L->getPointerOperand(), 0); !K.empty())
              H = &arrayHolder(K, L);
          if (H) {
            for (const auto &[v, site] : H->stores)
              if (const std::string c = refutedClass(v); !c.empty()) return ""; // OPEN-REFUTED
            if (!eoOnPath.insert(H->key).second) {
              eoHits.push_back(H->key);
              return kAny;
            }
            eoPathDepth[H->key] = cursorStack.size();
            std::string agreed, unproven;
            bool clash = false, multi = false;
            for (const auto &[v, site] : H->stores) {
              if (isa<ConstantPointerNull>(v->stripPointerCasts()) || isa<UndefValue>(v)) continue;
              const std::string x = elemOwnerR(v, d + 1);
              if (x.empty()) {
                if (unproven.empty()) unproven = "store at " + site;
                continue;
              }
              // Owners are named per function (an owner shape is a value of
              // the function that reads it): a holder's stores in several
              // functions name the table by different values, so they are
              // not compared; the read is an element of the same table
              // instance (the premise listed), of no one owner shape.
              if (x != kAny && !agreed.empty() && x != agreed) multi = true;
              if (x != kAny) agreed = x;
            }
            for (const std::string &o : H->open)
              if (unproven.empty()) unproven = o;
            eoOnPath.erase(H->key);
            eoPathDepth.erase(H->key);
            if (auto lit = valueLeans.find(H->key); lit != valueLeans.end()) {
              const std::set<std::string> leaned = std::move(lit->second);
              valueLeans.erase(lit);
              if (clash) withdrawCursors(leaned);
            }
            if (clash) return "";
            if (!unproven.empty())
              eoPending.push_back("h" + siteOf(L) + ": " + H->name + " open by " + unproven);
            else
              eoPending.push_back("k" + H->name);
            return agreed.empty() || multi ? kAny : agreed;
          }
        }
        // A closed cursor field read from an element: an element of the same
        // owner, the stored one assumed of the same table instance.
        const std::string K = fieldKey(L, L->getPointerOperand());
        if (!K.empty() && L->getType()->isPointerTy() && !handle.count(K) && !links.count(K)) {
          const std::string o = elemOwnerR(baseOf(L->getPointerOperand()), d + 1);
          if (!o.empty() && cursorClosed(L).empty()) {
            eoPending.push_back("c" + K);
            if (const std::string u = uncheckedOf(K, L); !u.empty()) eoPending.push_back("u" + u);
            return o;
          }
        }
        return "";
      }
      if (isa<PHINode>(V) || isa<SelectInst>(V)) {
        std::vector<const Value *> ins;
        if (const auto *PN = dyn_cast<PHINode>(V)) ins.assign(PN->incoming_values().begin(), PN->incoming_values().end());
        else ins = {cast<SelectInst>(V)->getTrueValue(), cast<SelectInst>(V)->getFalseValue()};
        return agree(V, ins);
      }
      if (const auto *G = dyn_cast<GEPOperator>(V)) return elemOwnerR(G->getPointerOperand(), d + 1);
      const auto *CB = dyn_cast<CallBase>(V);
      const Function *G = CB ? CB->getCalledFunction() : nullptr;
      // (d) through a closed code field (Fable 2026-10-16): every member of
      // the closed set is a constructor paired with the owner at one
      // argument, and the call's owner actual there is the object the field
      // is read from (linker.c's `(*info->hash->table.newfunc)(NULL,
      // &info->hash->table, name)`): the result is an element of that owner.
      if (CB && !G)
        if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
          const std::string K = fieldKey(CL, CL->getPointerOperand());
          auto tit = codeTargets.find(K);
          if (!code.count(K) || codeOpen.count(K) || tit == codeTargets.end() || tit->second.empty()) return "";
          int a = -1;
          for (const Function *T : tit->second) {
            auto cit = ctorsHere.find(T);
            if (cit == ctorsHere.end() || (a >= 0 && (int)cit->second != a)) return "";
            a = (int)cit->second;
          }
          if ((unsigned)a >= CB->arg_size()) return "";
          const std::string o = ownerShape(CB->getArgOperand(a), 0), f = ownerShape(CL->getPointerOperand(), 0);
          if (o.empty() || f.empty()) return "";
          const size_t p = o.find('+');
          const int64_t at = (p == std::string::npos ? 0 : std::stoll(o.substr(p + 1))) + std::stoll(K.substr(K.rfind('+') + 1));
          const std::string root = p == std::string::npos ? o : o.substr(0, p);
          return f == (at ? root + "+" + std::to_string(at) : root) ? o : "";
        }
      if (!G) return "";
      // A deref owner's row (OWNER(*argN@off)): the owner read from the argument.
      if (const CR *R = rowOf(G); R && R->ownerDeref >= 0 && R->role == CR::Lookup && R->elem == -1 &&
                                  (unsigned)R->owner < CB->arg_size())
        return derefOwnerShape(CB, CB->getArgOperand(R->owner), R->ownerDeref);
      if (const CR *R = rowOf(G); R && R->owner >= 0 && R->ownerDeref < 0 && (R->role == CR::Lookup || R->role == CR::Insert) &&
                                  R->elem == -1 && (unsigned)R->owner < CB->arg_size())
        return ownerShape(CB->getArgOperand(R->owner), 0);
      if (auto cit = ctorsHere.find(G); cit != ctorsHere.end() && cit->second < CB->arg_size())
        return ownerShape(CB->getArgOperand(cit->second), 0);
      return "";
    };
    auto elemOwner = [&](const Value *V, int d) -> std::string {
      const std::string o = elemOwnerR(V, d);
      return o == kAny ? std::string() : o;
    };
    // Cursor fields on an element (Fable 2026-10-16, Q-a): a pointer field
    // of an element that is not a link (bfd_link_hash_entry's u.i.link: an
    // indirect entry's target) is CLOSED when every store into it program-wide
    // (by name; a block copy covering it) stores null or an element: in the
    // body derived, fresh or inserted; outside it an element of an owner
    // (elemOwner). A greatest fixpoint: a field whose check is under way
    // counts as closed. Its reads from an element are elements of the same
    // owner, the stored element assumed of the same table instance (listed).
    std::map<std::string, std::string> cursorOpen; // field -> "" closed, else the first store that is not
    std::map<std::string, std::string> elemCursorLines; // field -> its line
    // The greatest fixpoint, nested: a field's verdict reached while
    // another field's check was under way, and resting on that field read
    // as closed, holds only if that field ends closed; when it ends open,
    // every verdict that leaned on it is dropped and decided again on its
    // next use.
    std::map<std::string, std::set<std::string>> cursorLeans;  // field -> under-way fields it read as closed
    std::map<const LoadInst *, std::string> cursorReadBad;      // read -> why, once its field's keys refuted it
    std::map<std::string, std::vector<const LoadInst *>> cursorReadsUnderWay; // field -> reads passed while it was under way
    auto elementStored = [&](const Function &F, const Value *V) {
      V = V->stripPointerCasts();
      if (isa<ConstantPointerNull>(V)) return true;
      if (body.count(&F)) {
        const uint8_t m = get(V);
        return m && !(m & ~(DER | FRS | INS | NUL));
      }
      const size_t mark = eoMark(), hits = eoHits.size();
      const std::string o = elemOwnerR(V, 0);
      bool ok = !o.empty() && o != kAny;
      // A read of a holder, closed or admitted under its listed assumption
      // (rule A, OPEN-UNPROVEN), is an element of no one owner shape: an
      // element.
      if (o == kAny)
        for (size_t i = mark; i < eoPending.size() && !ok; i++) ok = eoPending[i][0] == 'h' || eoPending[i][0] == 'k';
      // A value under way (its evaluation encloses this check): assumed an
      // element, the cursor fields begun inside its evaluation leaning on it.
      if (o == kAny)
        for (size_t i = hits; i < eoHits.size(); i++)
          if (auto dit = eoPathDepth.find(eoHits[i]); dit != eoPathDepth.end()) {
            ok = true;
            for (size_t j = dit->second; j < cursorStack.size(); j++) valueLeans[eoHits[i]].insert(cursorStack[j]);
          }
      eoHits.resize(hits);
      eoSettle(mark, ok);
      return ok;
    };
    // A cursor field inside a union (plan 3.55 Q-d, Fable 2026-10-16): a
    // store of another member there is no store of the cursor only by the
    // union keys (3.17 / 3.51, unionKeyNames), never by a discriminator
    // read here; every such store keyed, and every read of the cursor keyed
    // to admit none of their keys (cursorRead). Without keys: "cursor
    // inside union u: no admitted discriminator", with the engines' words.
    std::map<std::string, std::set<std::string>> cursorOtherKeys; // field -> keys of its other members' stores
    auto unionAround = [&](const std::string &KS, int64_t KO) -> std::pair<int64_t, const UnionFieldNote *> {
      auto nit = unionFieldNotes.find(KS);
      if (nit == unionFieldNotes.end()) return {0, nullptr};
      auto uit = nit->second.upper_bound(KO);
      if (uit == nit->second.begin()) return {0, nullptr};
      --uit;
      if (KO >= uit->first + std::max<int64_t>(uit->second.size, 1)) return {0, nullptr};
      return {uit->first, &uit->second};
    };
    // The keys the solver files an access under (GraphBuild), or null when
    // it reaches the slot's unkeyed cell (a write) or the whole slot (a
    // read): key lists the solver does not file per key.
    auto keysOf = [&](const Instruction *I) -> const std::vector<std::string> * {
      auto it = unionKeyNames.find(I);
      if (it == unionKeyNames.end() || it->second.empty()) return nullptr;
      const std::vector<std::string> &ks = it->second;
      return (isa<StoreInst>(I) ? perKeyWrite(ks) : perKeyRead(ks)) ? &ks : nullptr;
    };
    // Withdraw verdicts that rested on an assumption that failed: the fields
    // named, and every field that read one of them as closed while it was
    // under way (transitively); a field still under way stays.
    withdrawCursors = [&](const std::set<std::string> &fs) {
      std::vector<std::string> drop;
      for (const std::string &F : fs)
        if (std::find(cursorStack.begin(), cursorStack.end(), F) == cursorStack.end()) drop.push_back(F);
      for (size_t i = 0; i < drop.size(); i++)
        for (auto &[F, leans] : cursorLeans)
          if (leans.count(drop[i]) && std::find(drop.begin(), drop.end(), F) == drop.end() &&
              std::find(cursorStack.begin(), cursorStack.end(), F) == cursorStack.end())
            drop.push_back(F);
      for (const std::string &F : drop) {
        cursorOpen.erase(F);
        elemCursorLines.erase(F);
        cursorOtherKeys.erase(F);
        cursorLeans.erase(F);
      }
    };
    std::function<std::string(const std::string &)> cursorField, cursorFieldOnce;
    // A read of the cursor checked while the cursor was under way passed
    // (its other members' keys were not known yet); once they are, each such
    // read is checked, and a refuted one makes the field decide again, the
    // read failing from then on.
    std::function<std::string(const std::string &, const LoadInst *)> keyedRead;
    cursorField = [&](const std::string &K) -> std::string {
      if (cursorOpen.count(K)) return cursorFieldOnce(K); // under way, or decided
      for (;;) {
        const std::string why = cursorFieldOnce(K);
        auto pit = cursorReadsUnderWay.find(K);
        if (pit == cursorReadsUnderWay.end()) return why;
        const std::vector<const LoadInst *> reads = std::move(pit->second);
        cursorReadsUnderWay.erase(pit);
        if (!why.empty()) return why;
        bool refuted = false;
        for (const LoadInst *LI : reads)
          if (!cursorReadBad.count(LI))
            if (std::string r = keyedRead(K, LI); !r.empty()) {
              cursorReadBad[LI] = r;
              refuted = true;
            }
        if (!refuted) return why;
        withdrawCursors({K});
      }
    };
    cursorFieldOnce = [&](const std::string &K) -> std::string {
      if (auto cit = cursorOpen.find(K); cit != cursorOpen.end()) {
        // Under way: closed for now; every field above it on the stack
        // leans on it.
        if (auto sit = std::find(cursorStack.begin(), cursorStack.end(), K); sit != cursorStack.end())
          for (auto it = sit + 1; it != cursorStack.end(); ++it) cursorLeans[*it].insert(K);
        return cit->second;
      }
      cursorOpen[K] = ""; // under way: closed (the greatest fixpoint)
      cursorStack.push_back(K);
      const size_t kp = K.rfind('+');
      const std::string KS = K.substr(0, kp);
      const int64_t KO = std::stoll(K.substr(kp + 1));
      const auto [uoff, UN] = unionAround(KS, KO);
      std::string why, firstUnkeyed;
      std::vector<std::string> unkeyedSites; // every store of another member without union keys
      size_t stores = 0, others = 0, unkeyed = 0, wholeCopies = 0, fieldCopies = 0;
      bool othersKeyed = true;
      std::set<std::string> otherKeys;
      // A store that is no element: outside a union, the field is open;
      // inside one, a store of another member, judged by its keys below.
      auto notElement = [&](const Function &F, const Instruction &I, const std::string &text) {
        if (!UN) {
          why = F.getName().str() + ": " + text;
          return;
        }
        others++;
        if (const auto *ks = keysOf(&I)) otherKeys.insert(ks->begin(), ks->end());
        else {
          othersKeyed = false;
          if (!unkeyed++) firstUnkeyed = F.getName().str() + ": " + text;
          auto mit = unionWriteMember.find(&I);
          unkeyedSites.push_back(F.getName().str() + ": " + text + " (member " +
                                 (mit == unionWriteMember.end() || mit->second.empty() ? std::string("untyped")
                                                                                       : mit->second) +
                                 ")");
        }
      };
      for (auto &[M, _] : Ctx->Modules)
        for (const Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            if (!why.empty()) break;
            if (const auto *S = dyn_cast<StoreInst>(&I)) {
              if (!S->getValueOperand()->getType()->isPointerTy() || fieldKey(S, S->getPointerOperand()) != K) continue;
              // A copy of the same union field from another object ((C''),
              // Fable 2026-10-17): its facts keep their keys, so under the
              // cursor's keys it moves the cursor's own content (Q1 (b)'s
              // treatment, one field): no store into the cursor.
              if (unionCopyOf.count(S)) {
                fieldCopies++;
                continue;
              }
              stores++;
              if (!elementStored(F, S->getValueOperand())) notElement(F, I, valueText(S));
            } else if (const auto *MT = dyn_cast<MemTransferInst>(&I)) {
              StructType *DS = nullptr;
              int64_t off = 0;
              const auto *Len = dyn_cast<ConstantInt>(MT->getLength());
              if (!namedSlot(MT, MT->getRawDest(), CDL, pointees, DS, off) || !DS->hasName()) continue;
              bool covers = false;
              structCover(DS, off, off + (Len ? (int64_t)Len->getZExtValue() : 1), CDL,
                          [&](StructType *T, int64_t lo, int64_t hi) {
                            covers |= T->hasName() && stripStructNameSuffix(T->getName()) == KS && KO >= lo && KO < hi;
                          });
              if (!covers) continue;
              // A copy of a whole struct between two objects of it (Fable
              // 2026-10-17, Q1 (b)) is key-preserving: under each key the
              // destination's content is the source's, tag and union bytes
              // moving together (3.53 rule 4, cell to cell), so under the
              // cursor's keys it moves the cursor's own content: no store into
              // the cursor, with no owner condition.
              StructType *SS = nullptr;
              int64_t soff = 0;
              if (Len && off == 0 && DS->isSized() &&
                  (int64_t)Len->getZExtValue() == (int64_t)CDL.getTypeAllocSize(DS) &&
                  namedSlot(MT, MT->getRawSource(), CDL, pointees, SS, soff) && SS && soff == 0 && SS->hasName() &&
                  stripStructNameSuffix(SS->getName()) == stripStructNameSuffix(DS->getName())) {
                wholeCopies++;
                continue;
              }
              stores++;
              if (!elementStored(F, MT->getRawSource())) notElement(F, I, valueText(MT) + " (a block copy)");
            }
          }
      std::string keyed;
      if (why.empty() && UN && others) {
        if (othersKeyed) {
          cursorOtherKeys[K] = otherKeys;
          keyed = ", or " + std::to_string(others) + " stores of other members of union " + UN->field +
                  ", each with union keys; a read of the cursor is closed only if it admits none of them";
        } else {
          std::string engines = UN->census;
          if (auto wit = widenedTagsOf.find(KS); wit != widenedTagsOf.end())
            for (const std::string &w : wit->second) engines += "; " + w;
          why = "cursor inside union " + UN->field + " (" + KS + "+" + std::to_string(uoff) +
                "): no admitted discriminator (" + engines + "); " + std::to_string(unkeyed) + " of " +
                std::to_string(others) + " stores of another member without union keys, e.g. " + firstUnkeyed;
        }
      }
      elemCursorLines[K] = "cursor field " + K + " on an element: " +
                           (why.empty() ? "CLOSED (" + std::to_string(stores) + " stores, each null or an element" +
                                              keyed +
                                              (wholeCopies ? "; " + std::to_string(wholeCopies) +
                                                                 " copies of the whole struct, key-preserving"
                                                           : std::string()) +
                                              (fieldCopies ? "; " + std::to_string(fieldCopies) +
                                                                 " copies of the union field, key-preserving"
                                                           : std::string()) +
                                              ")"
                                        : "not closed (" + why + ")");
      if (!why.empty() && unkeyedSites.size() > 1) {
        elemCursorLines[K] += "; the stores of another member without union keys:";
        for (const std::string &u : unkeyedSites) elemCursorLines[K] += " [" + u + "]";
      }
      cursorOpen[K] = why;
      cursorStack.pop_back();
      if (!why.empty()) {
        // Open: drop every verdict that read K as closed while K was under
        // way (transitively), to be decided again on its next use.
        std::vector<std::string> drop{K};
        for (size_t i = 0; i < drop.size(); i++)
          for (auto &[F, leans] : cursorLeans)
            if (F != K && leans.count(drop[i]) && cursorOpen.count(F) &&
                std::find(drop.begin(), drop.end(), F) == drop.end())
              drop.push_back(F);
        for (size_t i = 1; i < drop.size(); i++) {
          cursorOpen.erase(drop[i]);
          elemCursorLines.erase(drop[i]);
          cursorOtherKeys.erase(drop[i]);
          cursorLeans.erase(drop[i]);
        }
      }
      return why;
    };
    // A read of a cursor field: the field closed, and inside a union the
    // read keyed to admit no store of another member.
    keyedRead = [&](const std::string &K, const LoadInst *LI) -> std::string {
      auto oit = cursorOtherKeys.find(K);
      if (oit == cursorOtherKeys.end()) return "";
      const auto *ks = keysOf(LI);
      if (!ks) return "a read of the cursor inside a union with no union key: " + valueText(LI);
      for (const std::string &k : *ks)
        if (oit->second.count(k)) return "a read of the cursor that admits another member's store: " + valueText(LI);
      return "";
    };
    // A read of both schemes (P3) admits no other member's store only by
    // excluding, by their member names, the stores of other members its tag
    // admits: listed, also for a read admitted while its cursor is under way.
    auto p3Note = [&](const LoadInst *LI) {
      auto pit = p3Excluded.find(LI);
      if (pit == p3Excluded.end() || pit->second.empty()) return;
      size_t un = 0, tg = 0;
      std::set<std::string> sites;
      for (auto &[W, tagged] : pit->second) {
        (tagged ? tg : un)++;
        sites.insert(W->getFunction()->getName().str() + ": " + valueText(W) + (tagged ? " (tagged)" : ""));
      }
      std::string s = LI->getFunction()->getName().str() + ": " + valueText(LI) + ": " + std::to_string(un) +
                      " untagged, " + std::to_string(tg) + " tagged stores:";
      for (const std::string &x : sites) s += " [" + x + "]";
      eoPending.push_back("x" + s);
    };
    auto cursorRead = [&](const std::string &K, const LoadInst *LI) -> std::string {
      if (std::string why = cursorField(K); !why.empty()) return why;
      if (auto bit = cursorReadBad.find(LI); bit != cursorReadBad.end()) return bit->second;
      if (std::find(cursorStack.begin(), cursorStack.end(), K) != cursorStack.end()) {
        cursorReadsUnderWay[K].push_back(LI); // checked when K's keys are known
        p3Note(LI);
        return "";
      }
      std::string r = keyedRead(K, LI);
      if (r.empty()) p3Note(LI);
      return r;
    };
    cursorClosed = [&](const Value *L) {
      const auto *LI = cast<LoadInst>(L);
      return cursorRead(fieldKey(LI, LI->getPointerOperand()), LI);
    };
    // A read of a cursor inside a union admitted by the union census's
    // member key, the read one of its UNCHECKED reads (keyed by its own
    // member with no settling check, the user's rule of 2026-10-07): the
    // closure rests on that assumption, listed. A read a tag pair keys has
    // other keys (checked) and adds nothing.
    uncheckedOf = [&](const std::string &K, const LoadInst *LI) -> std::string {
      auto uit = uncheckedReads.find(LI);
      if (!cursorOtherKeys.count(K) || uit == uncheckedReads.end()) return "";
      const auto *ks = keysOf(LI);
      if (!ks || std::find(ks->begin(), ks->end(), uit->second) == ks->end()) return "";
      return K + "\t" + LI->getFunction()->getName().str() + ": " + valueText(LI);
    };
    std::vector<std::string> inlineSites;
    auto isInlineMove = [&](const StoreInst *S) {
      if (body.count(S->getFunction())) return false;
      const size_t mark = eoMark();
      const std::string a = elemOwner(baseOf(S->getPointerOperand()), 0), v = elemOwner(S->getValueOperand(), 0);
      const bool ok = !a.empty() && a == v;
      eoSettle(mark, ok);
      if (!ok) return false;
      inlineSites.push_back(S->getFunction()->getName().str() + ": " + valueText(S));
      return true;
    };
    // ---- O1 on declared storage (plan 3.55 R3 D2, D5, D6; Fable 2026-10-15).
    // Every write into a declared slot, anywhere in the program (stores,
    // block writes, an asm's stores by the graph build's model), is a row
    // body's, or admitted: null (a wide null store over the slots), a
    // self-link (R2: an element's own address into its own slot), a link
    // word reused as an integer (R4: a constant, or arithmetic over a load of
    // the same cell; an atomic's tied old value is a same-cell re-store), a
    // same-owner re-store in owner code (a value derived from the owner into
    // a slot derived from it), an implicit insert (an element into a derived
    // slot, paired with an insert row call on the same element and owner
    // value in the function), or a link store on that inserted element. And
    // every element-derived store in a body or owner code lands in a
    // declared slot. An access through an owner or element value that no
    // rule names is a naming failure, never a pass.
    std::map<std::string, size_t> o1Admit;
    std::map<std::string, std::vector<std::string>> o1Fail;
    std::vector<std::string> o1Naming, implicitMatched, implicitUnmatched, wordLines, unionSites;
    std::map<std::string, size_t> unionStorage; // class 2: storage inside a union (writes)
    std::vector<std::string> plainFieldSites;   // an element pointer kept in a plain field (examples)
    std::vector<std::string> linkInvariant, traverseJoined; // listed assumptions in owner code
    // S5-S7 (Fable 2026-10-16): union actuals' slots, formal nodes, cursor
    // fields, re-reads; listed.
    std::map<const Value *, std::pair<bool, std::string>> unionActual; // actual -> (by debug info?, its site)
    std::set<std::string> unionSlotActuals;
    size_t unionSlotAddrs = 0;
    std::vector<std::string> formalNodeSites, formalObjSites, cursorLines, cursorAssumed;
    std::set<const Value *> rereadLoads;
    size_t lookupsByDerivation = 0, rowSites = 0;
    // (1c) discharged per call site: agrees, disagrees (FAIL), unnamed
    // (an ASSUMPTION, listed).
    size_t premiseArgs = 0, premiseAgree = 0, premiseNull = 0, premiseByBase = 0;
    std::vector<std::string> premiseFail, premiseAssume, premiseUnion, premisePast, premiseUnionDI, tableDisagree;
    std::set<std::string> ownerValues;
    if (declared) {
      auto siteText = [](const Instruction *I) {
        std::string s = I->getFunction()->getName().str() + ": " + valueText(I);
        return s.size() > 200 ? s.substr(0, 200) : s;
      };
      // Class 3: the last naming stepped past a named base's layout.
      auto pastText = [&]() -> std::string {
        if (!pointees.pastS) return "";
        return " (a step past the layout of " + stripStructNameSuffix(pointees.pastS->getName()).str() +
               (pointees.pastOff < 0 ? "" : "+") + std::to_string(pointees.pastOff) + ")";
      };
      // The declared slot kind an access names ('h', 'l', 'w'; 0 none), by
      // the access (At) or, for an address alone, its struct GEP or pointee.
      auto addrKey = [&](const Value *A) -> std::string {
        if (const auto *G = dyn_cast<GEPOperator>(A)) {
          auto *S = dyn_cast<StructType>(G->getSourceElementType());
          APInt Off(64, 0);
          if (S && S->hasName() && G->accumulateConstantOffset(CDL, Off)) return innerKeyOf(S, Off.getSExtValue());
          return "";
        }
        return innerKeyOf(pointees.get(A, A->getContext()), 0);
      };
      auto kindOf = [&](const std::string &K) -> char {
        return declHandle.count(K) ? 'h' : declLink.count(K) ? 'l' : declWord.count(K) ? 'w' : 0;
      };
      auto slotOf = [&](const Instruction *At, const Value *A) -> char {
        return kindOf(At ? ckey(At, A) : addrKey(A));
      };
      // Owner-code slots named by byte arithmetic from a derived value (S4):
      // address -> its offsets in the element struct.
      std::map<const Value *, std::vector<int64_t>> byteSlotsAll;
      // Slots at a union actual + k, under the premise's assumption (S5).
      std::map<const Value *, std::vector<std::pair<StructType *, int64_t>>> unionSlotsAll;
      // The fields an access at A may write: its own name, or, for a phi or
      // select of field addresses (rb_link_node's `*p`, rb_erase's child
      // slot), every entry's (null entries add none), or the slots byte
      // arithmetic names (S4). Empty: unnamed.
      std::function<bool(const Instruction *, const Value *, std::vector<std::pair<StructType *, int64_t>> &, int)>
          addrSlots = [&](const Instruction *At, const Value *A, std::vector<std::pair<StructType *, int64_t>> &out,
                          int d) -> bool {
        if (auto uit = unionSlotsAll.find(A->stripPointerCasts()); uit != unionSlotsAll.end()) {
          out.insert(out.end(), uit->second.begin(), uit->second.end());
          return true;
        }
        StructType *S = nullptr;
        int64_t off = 0;
        if (namedSlot(At, A, CDL, pointees, S, off) && S->hasName()) {
          out.push_back({S, off});
          return true;
        }
        if (auto bit = byteSlotsAll.find(A->stripPointerCasts()); bit != byteSlotsAll.end() && premiseElemT) {
          for (int64_t k : bit->second) out.push_back({premiseElemT, k});
          return true;
        }
        const Value *V = A->stripPointerCasts();
        if (d > 4 || !(isa<PHINode>(V) || isa<SelectInst>(V))) return false;
        std::vector<const Value *> ins;
        if (const auto *PN = dyn_cast<PHINode>(V)) ins.assign(PN->incoming_values().begin(), PN->incoming_values().end());
        else ins = {cast<SelectInst>(V)->getTrueValue(), cast<SelectInst>(V)->getFalseValue()};
        static thread_local std::set<const Value *> onPath;
        if (!onPath.insert(V).second) return true; // a cycle adds no field
        bool ok = true;
        for (const Value *In : ins)
          if (!isa<ConstantPointerNull>(In) && !isa<UndefValue>(In) && !addrSlots(At, In, out, d + 1)) ok = false;
        onPath.erase(V);
        return ok;
      };
      // Row call sites, grouped per function by owner value (SSA value or
      // constant GEP shape).
      struct Group {
        std::vector<const Value *> owners, elems;
        std::vector<const Value *> assumed;  // inlined removes: elements under the link invariant
        std::vector<const CallBase *> joined; // traverse elements joined to the only owner group (r3)
        std::vector<const CallBase *> inserts;
        std::map<const Value *, uint8_t> cls;
      };
      std::map<const Function *, std::map<std::string, Group>> groups;
      auto rowAt = [&](const CallBase *CB) -> const CR * {
        const Function *G = CB->getCalledFunction();
        if (!G) return nullptr;
        auto it = C.rows.find(G->getName().str());
        return it == C.rows.end() || it->second.role == CR::Pure || it->second.role == CR::Carve ? nullptr
                                                                                                : &it->second;
      };
      for (auto &[M, _] : Ctx->Modules)
        for (const Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            const auto *CB = dyn_cast<CallBase>(&I);
            const CR *R = CB ? rowAt(CB) : nullptr;
            if (!R || R->owner < 0 || (unsigned)R->owner >= CB->arg_size()) continue;
            const Value *o = CB->getArgOperand(R->owner);
            const std::string sh = ownerShape(o, 0);
            Group &Gp = groups[&F][sh.empty() ? valueText(o) : sh];
            // The owner object: a zero step from it is the same owner
            // (4(b): rb_root_cached and its rb_root at +0).
            for (const Value *ob = o->stripPointerCasts();;) {
              Gp.owners.push_back(ob);
              const auto *OG = dyn_cast<GEPOperator>(ob);
              APInt Z(64, 0);
              if (!OG || !OG->accumulateConstantOffset(DL0, Z) || !Z.isZero()) break;
              ob = OG->getPointerOperand()->stripPointerCasts();
            }
            if (!body.count(&F)) rowSites++, ownerValues.insert(F.getName().str() + ":" + (sh.empty() ? valueText(o) : sh));
            if (R->role == CR::Insert) Gp.inserts.push_back(CB);
            else if (R->elem >= 0 && (unsigned)R->elem < CB->arg_size())
              Gp.elems.push_back(CB->getArgOperand(R->elem)->stripPointerCasts());
          }
      // A traverse row has no owner (rb_next(node)): in a function with one
      // owner group, its element is that owner's (an inlined remove's node:
      // `if (root->rb_leftmost == node) root->rb_leftmost = rb_next(node)`).
      for (auto &[F, gs] : groups) {
        if (gs.size() != 1) continue;
        for (const Instruction &I : instructions(*F))
          if (const auto *CB = dyn_cast<CallBase>(&I))
            if (const CR *R = rowAt(CB); R && R->role == CR::Traverse && R->owner < 0 && R->elem >= 0 &&
                                         (unsigned)R->elem < CB->arg_size()) {
              gs.begin()->second.elems.push_back(CB->getArgOperand(R->elem)->stripPointerCasts());
              if (!body.count(F)) gs.begin()->second.joined.push_back(CB);
            }
      }
      // (1c): every row call's OWNER and ELEM actuals against the premise
      // (Fable 2026-10-15, classes 1-3). The actual's name (namedPtr: a
      // GEP's source struct only at leading index 0, else its base's name
      // plus the byte offset) agrees when that struct holds the premise's
      // struct there by the struct analyzer's embedding table (transitive,
      // every array element); a union on the layout path stops the name:
      // with debug info, it agrees through a union member that is or embeds
      // the struct; without, the IR's member is clang's representative, so
      // the site is an ASSUMPTION "inside union U" (the struct must fit).
      // A step past a named base's layout, and an actual named by nothing,
      // are ASSUMPTIONs; any other name disagrees (FAIL).
      for (auto &[M, _] : Ctx->Modules)
        for (const Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            const auto *CB = dyn_cast<CallBase>(&I);
            const CR *R = CB ? rowAt(CB) : nullptr;
            if (!R) continue;
            std::vector<std::pair<int, StructType *>> args;
            if (R->owner >= 0) args.push_back({R->owner, premiseOwnerT});
            if (R->elem >= 0) args.push_back({R->elem, premiseElemT});
            for (int e : R->moreElems) args.push_back({e, premiseElemT});
            for (auto [a, T] : args) {
              if (!T || (unsigned)a >= CB->arg_size()) continue;
              premiseArgs++;
              const Value *V = CB->getArgOperand(a)->stripPointerCasts();
              const std::string TN = stripStructNameSuffix(T->getName()).str();
              const std::string at = siteText(CB) + " (arg" + std::to_string(a) + ", " + TN + ")";
              if (isa<ConstantPointerNull>(V)) { premiseNull++; continue; } // no object
              if (const auto *PA = dyn_cast<Argument>(V); PA && premise.count(PA)) {
                // A row's own premise-typed formal.
                if (premise[PA] == T) premiseAgree++;
                else premiseFail.push_back(at + ": named " + stripStructNameSuffix(premise[PA]->getName()).str());
                continue;
              }
              StructType *S = nullptr;
              int64_t off = 0;
              if (!namedPtr(V, CDL, pointees, S, off) || !S->hasName()) {
                if (pointees.pastS)
                  premisePast.push_back(at + ": " + stripStructNameSuffix(pointees.pastS->getName()).str() +
                                        (pointees.pastOff < 0 ? "" : "+") + std::to_string(pointees.pastOff));
                else
                  premiseAssume.push_back(at);
                continue;
              }
              const bool byBase = pointees.viaBase;
              const std::string SN = stripStructNameSuffix(S->getName()).str();
              const std::string as = SN + "+" + std::to_string(off);
              StructType *U = nullptr;
              int64_t uo = 0, us = 0;
              if (unionOnPath(S, off, CDL, U, uo, us)) {
                const int di = diThroughUnion(StringRef(SN).drop_front(7), off, StringRef(TN).drop_front(7));
                const std::string where = "union at " + SN + "+" + std::to_string(uo) + ", +" + std::to_string(off - uo);
                if (di == 1) {
                  premiseAgree++, premiseUnionDI.push_back(at + ": through the " + where);
                  unionActual.emplace(V, std::make_pair(true, at));
                }
                else if (di == 0) premiseFail.push_back(at + ": named " + as + ", no member of the " + where + " is " + TN);
                else if ((int64_t)CDL.getTypeAllocSize(T) > us - (off - uo))
                  premiseFail.push_back(at + ": named " + as + ", " + TN + " does not fit in the " + where + " (" +
                                        std::to_string(us) + " bytes)");
                else {
                  premiseUnion.push_back(at + ": inside the " + where + " (members not in the IR)");
                  unionActual.emplace(V, std::make_pair(false, at));
                }
                continue;
              }
              const bool agree = (SN == TN && off == 0) || tableHolds(S, off, TN, CB->getModule());
              if (agree != embedsAtThroughArrays(S, off, TN, CDL))
                tableDisagree.push_back(at + ": " + as + " (table " + (agree ? "yes" : "no") + ", layout walk " +
                                        (agree ? "no" : "yes") + ")");
              if (agree) premiseAgree++, premiseByBase += byBase;
              else premiseFail.push_back(at + ": named " + as);
            }
          }
      // The element struct's declared slots, by offset (S4); its LINK slots.
      std::set<int64_t> elemSlotOffs, elemLinkOffs;
      if (premiseElemT)
        for (const std::set<std::string> *D : {&declLink, &declWord})
          for (const std::string &K : *D)
            if (K.compare(0, K.rfind('+'), stripStructNameSuffix(premiseElemT->getName()).str()) == 0) {
              elemSlotOffs.insert(std::stoll(K.substr(K.rfind('+') + 1)));
              if (D == &declLink) elemLinkOffs.insert(std::stoll(K.substr(K.rfind('+') + 1)));
            }
      std::set<int64_t> ownerSlotOffs;
      if (premiseOwnerT)
        for (const std::string &K : declHandle)
          if (K.compare(0, K.rfind('+'), stripStructNameSuffix(premiseOwnerT->getName()).str()) == 0)
            ownerSlotOffs.insert(std::stoll(K.substr(K.rfind('+') + 1)));
      // An object's identity: a re-read of a named slot is its first read (S6).
      auto canonRoot = [&](const Value *V) -> const Value * {
        if (const auto *L = dyn_cast<LoadInst>(V))
          if (const Reread r = sameRead(L, 0); r.first) return r.first;
        return V;
      };
      auto canonRO = [&](const Value *V) {
        auto r = rootOff(V, CDL);
        r.first = canonRoot(r.first);
        return r;
      };
      // An insert row call's element actuals.
      auto insertElems = [&](const CallBase *CB) {
        std::vector<const Value *> v;
        const CR *R = rowAt(CB);
        if (R->elem >= 0 && (unsigned)R->elem < CB->arg_size()) v.push_back(CB->getArgOperand(R->elem)->stripPointerCasts());
        for (int e : R->moreElems)
          if ((unsigned)e < CB->arg_size()) v.push_back(CB->getArgOperand(e)->stripPointerCasts());
        return v;
      };
      // Cursor reads per group (S7): (the load, the element's offset in the
      // object it points to).
      std::map<std::pair<const Function *, std::string>, std::set<std::pair<const Value *, int64_t>>> cursorAt;
      auto deriveAll = [&]() {
        byteSlotsAll.clear(), unionSlotsAll.clear(), linkInvariant.clear(), traverseJoined.clear();
        unionSlotActuals.clear(), formalNodeSites.clear(), formalObjSites.clear(), rereadLoads.clear();
        for (auto &[F, gs] : groups)
          for (auto &[sh, Gp] : gs) {
            std::map<const Value *, std::vector<int64_t>> byteSlots;
            OwnerCodeExtra X;
            X.canon = canonRoot;
            X.ownerSlots = ownerSlotOffs;
            std::vector<std::pair<std::pair<const Value *, int64_t>, std::string>> uActs;
            for (const Value *o : Gp.owners)
              if (auto u = unionActual.find(o); u != unionActual.end())
                X.unionOwnerAt.insert(canonRO(o)), uActs.push_back({canonRO(o), u->second.second});
            std::vector<const Value *> es(Gp.elems.begin(), Gp.elems.end());
            for (const CallBase *CB : Gp.inserts)
              for (const Value *e : insertElems(CB)) es.push_back(e);
            for (const Value *e : es)
              if (auto u = unionActual.find(e); u != unionActual.end())
                X.unionElemAt.insert(canonRO(e)), uActs.push_back({canonRO(e), u->second.second});
            // The element actuals' offsets in their objects (a formal object's
            // node there, Q1; +0 is the formal itself, S7's phi rule).
            for (const Value *e : es)
              if (const int64_t o = canonRO(e).second; o != 0) {
                X.elemOffs.insert(o);
                if (unionActual.count(e)) X.unionElemOffs.insert(o);
              }
            X.elemLinkOffs = elemLinkOffs;
            for (const Value *v : es) X.actualRoots.insert(canonRO(v).first);
            for (const Value *v : Gp.owners) X.actualRoots.insert(canonRO(v).first);
            if (auto cit = cursorAt.find({F, sh}); cit != cursorAt.end()) X.elemAt = cit->second;
            Gp.assumed.clear();
            Gp.cls = deriveOwnerCode(*F, Gp.owners, Gp.elems, slotOf, [&](const CallBase *CB, const OwnerClassFn &g) {
              const CR *R = rowAt(CB);
              if (!R || R->role == CR::Insert) return false;
              if (R->role == CR::Remove && R->elem != -1) return false; // no result
              if (R->owner >= 0 && (unsigned)R->owner < CB->arg_size() && (g(CB->getArgOperand(R->owner)) & OC_OWNER))
                return true;
              return R->elem >= 0 && (unsigned)R->elem < CB->arg_size() && (g(CB->getArgOperand(R->elem)) & OC_VAL);
            }, CDL, body.count(F) ? nullptr : premiseElemT, &Gp.assumed, [&](const Value *A) -> int64_t {
              const std::string K = addrKey(A);
              if (!kindOf(K)) return -1;
              return std::stoll(K.substr(K.rfind('+') + 1));
            }, elemSlotOffs, &byteSlots, &X);
            for (auto &[A, ks] : byteSlots) {
              std::vector<int64_t> &all = byteSlotsAll[A];
              for (int64_t k : ks)
                if (std::find(all.begin(), all.end(), k) == all.end()) all.push_back(k);
            }
            for (auto &[A, hs] : X.unionSlots) {
              std::vector<std::pair<StructType *, int64_t>> &all = unionSlotsAll[A];
              for (auto [own, k] : hs) {
                const std::pair<StructType *, int64_t> sl{own ? premiseOwnerT : premiseElemT, k};
                if (sl.first && std::find(all.begin(), all.end(), sl) == all.end()) all.push_back(sl);
              }
            }
            for (auto &[ra, site] : uActs)
              if (X.unionUsed.count(ra)) unionSlotActuals.insert(site);
            for (const Instruction *I : X.formalNodes) formalNodeSites.push_back(siteText(I));
            for (auto &[A, e] : X.formalObjUsed)
              formalObjSites.push_back(F->getName().str() + ": " + valueText(A) + " at +" + std::to_string(e));
            rereadLoads.insert(X.rereads.begin(), X.rereads.end());
            for (const Value *L : Gp.assumed) linkInvariant.push_back(F->getName().str() + ": read by " + valueText(L));
            for (const CallBase *CB : Gp.joined) traverseJoined.push_back(siteText(CB));
          }
        unionSlotAddrs = unionSlotsAll.size();
      };
      // Cursor fields (S7, Fable 2026-10-16): a pointer field that is not
      // declared storage, of an owner's object, into which owner code stores
      // an element of that owner (derived, a row's result, or an inserted
      // element; through its object at offset e). Every store into the field
      // program-wide (by name) storing null or such an element of the owner
      // whose object holds the field: a CLOSED CURSOR, its reads from an
      // owner's object derived elements at +e. Otherwise each such read is a
      // per-site ASSUMPTION "a node read back from a plain field".
      auto elemOffIn = [&](Group &Gp, const Value *V) -> int64_t {
        for (const Value *W : {V, V->stripPointerCasts()})
          if (auto it = Gp.cls.find(W); it != Gp.cls.end() && (it->second & OC_VAL)) return 0;
        const auto r = canonRO(V);
        std::vector<const Value *> es(Gp.elems.begin(), Gp.elems.end());
        for (const CallBase *CB : Gp.inserts)
          for (const Value *e : insertElems(CB)) es.push_back(e);
        for (const Value *E : es)
          if (const auto re = canonRO(E); re.first == r.first && re.second >= r.second) return re.second - r.second;
        return -1;
      };
      auto ownerObjIn = [&](Group &Gp, const Value *Obj) {
        for (const Value *o : Gp.owners)
          if (canonRO(o).first == Obj) return true;
        return false;
      };
      for (int round = 0;; round++) {
        deriveAll();
        if (round == 3 || !premiseElemT) break;
        // field -> element offsets its owner-code stores carry; stores that are not such
        std::map<std::string, std::set<int64_t>> cursorE;
        for (auto &[F, gs] : groups)
          for (const Instruction &I : instructions(*F))
            if (const auto *S = dyn_cast<StoreInst>(&I); S && S->getValueOperand()->getType()->isPointerTy()) {
              const std::string K = ckey(S, S->getPointerOperand());
              if (K.empty() || kindOf(K)) continue;
              const Value *Obj = canonRO(S->getPointerOperand()).first;
              for (auto &[sh, Gp] : gs)
                if (ownerObjIn(Gp, Obj))
                  if (const int64_t e = elemOffIn(Gp, S->getValueOperand()); e >= 0) cursorE[K].insert(e);
            }
        std::map<std::string, bool> closed;
        for (auto &[K, es] : cursorE) closed[K] = es.size() == 1;
        if (!cursorE.empty())
          for (auto &[M, _] : Ctx->Modules)
            for (const Function &F : *M)
              for (const Instruction &I : instructions(F))
                if (const auto *S = dyn_cast<StoreInst>(&I)) {
                  if (!S->getValueOperand()->getType()->isPointerTy()) continue;
                  const std::string K = ckey(S, S->getPointerOperand());
                  auto cit = closed.find(K);
                  if (cit == closed.end() || !cit->second || isa<ConstantPointerNull>(S->getValueOperand())) continue;
                  bool ok = false;
                  if (auto *gs = groups.count(&F) ? &groups[&F] : nullptr) {
                    const Value *Obj = canonRO(S->getPointerOperand()).first;
                    for (auto &[sh, Gp] : *gs)
                      ok |= ownerObjIn(Gp, Obj) && elemOffIn(Gp, S->getValueOperand()) == *cursorE[K].begin();
                  }
                  if (!ok) cit->second = false;
                }
        // The reads, from an owner's object, in owner code.
        std::map<std::pair<const Function *, std::string>, std::set<std::pair<const Value *, int64_t>>> next;
        cursorLines.clear(), cursorAssumed.clear();
        for (auto &[K, c] : closed) {
          if (cursorE[K].size() > 1) {
            // Elements at several offsets: no one element a read could be.
            std::string os;
            for (int64_t e : cursorE[K]) os += " +" + std::to_string(e);
            cursorLines.push_back(K + " holds elements at several offsets (" + os.substr(1) + "): its reads not derived");
            continue;
          }
          cursorLines.push_back(K + (c ? " CLOSED CURSOR (every store an element of the owner, at +" +
                                             std::to_string(*cursorE[K].begin()) + ")"
                                       : " not closed"));
        }
        std::set<std::string> assumedSeen;
        for (auto &[F, gs] : groups)
          for (const Instruction &I : instructions(*F))
            if (const auto *L = dyn_cast<LoadInst>(&I); L && L->getType()->isPointerTy()) {
              const std::string K = ckey(L, L->getPointerOperand());
              auto cit = closed.find(K);
              if (cit == closed.end() || cursorE[K].size() != 1) continue;
              const int64_t e = *cursorE[K].begin();
              const Value *Obj = canonRO(L->getPointerOperand()).first;
              for (auto &[sh, Gp] : gs)
                if (ownerObjIn(Gp, Obj)) {
                  next[{F, sh}].insert({L, e});
                  const std::string a = siteText(L) + " (" + K + ", +" + std::to_string(e) + ")";
                  if (!cit->second && assumedSeen.insert(a).second) cursorAssumed.push_back(a);
                }
            }
        if (next == cursorAt) break;
        cursorAt = std::move(next);
      }
      auto strip = [](const Value *V) {
        for (int i = 0; i < 8; i++) {
          V = V->stripPointerCasts();
          if (const auto *P = dyn_cast<PtrToIntOperator>(V)) V = P->getPointerOperand();
          else if (const auto *Z = dyn_cast<ZExtInst>(V)) V = Z->getOperand(0);
          else break;
        }
        return V;
      };
      auto isNullV = [](const Value *V) {
        if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return true;
        const auto *CI = dyn_cast<ConstantInt>(V);
        return CI && CI->isZero();
      };
      // R4: arithmetic over loads of the cell at A (or constants).
      std::function<bool(const Value *, const Value *, int)> selfDerived = [&](const Value *V, const Value *A,
                                                                               int d) -> bool {
        if (d > 8) return false;
        if (isa<ConstantInt>(V)) return true;
        if (const auto *L = dyn_cast<LoadInst>(V))
          return L->getPointerOperand()->stripPointerCasts() == A->stripPointerCasts();
        if (const auto *BO = dyn_cast<BinaryOperator>(V))
          return selfDerived(BO->getOperand(0), A, d + 1) && selfDerived(BO->getOperand(1), A, d + 1);
        if (const auto *CI = dyn_cast<CastInst>(V); CI && !isa<PtrToIntInst>(CI)) return selfDerived(CI->getOperand(0), A, d + 1);
        return false;
      };
      auto groupsOf = [&](const Function *F) -> std::map<std::string, Group> * {
        auto it = groups.find(F);
        return it == groups.end() ? nullptr : &it->second;
      };
      // A write by the asm model's raw-pointer rule (every value input
      // through every raw pointer input) fails under its own class.
      bool rawWrite = false;
      auto fail = [&](const std::string &why, const Instruction *I) {
        o1Fail[rawWrite ? "asm model over-approximation (a raw pointer input written): " + why : why].push_back(siteText(I));
      };
      std::set<const Instruction *> implicitSeen;
      // One write: (instruction, address, value or source, bytes, kind).
      enum WK { WStore, WFill, WCopy };
      auto onWrite = [&](const Instruction *I, const Value *A, const Value *V, int64_t bytes, WK wk) {
        const Function *F = I->getFunction();
        const bool inBody = body.count(F);
        auto *gs = groupsOf(F);
        const Value *B = baseOf(A);
        if (isa<AllocaInst>(B)) return;
        // Is the base an owner or element value here (body or owner code)?
        uint8_t ocB = 0;
        bool baseIsInserted = false;
        if (gs)
          for (auto &[sh, Gp] : *gs) {
            (void)sh;
            auto it = Gp.cls.find(B);
            if (it != Gp.cls.end()) ocB |= it->second;
            for (const Value *o : Gp.owners) ocB |= o == B ? OC_OWNER : 0;
            for (const CallBase *CB : Gp.inserts) {
              const CR *R = rowAt(CB);
              auto isE = [&](int e) {
                if (e < 0 || (unsigned)e >= CB->arg_size()) return false;
                const Value *X = CB->getArgOperand(e);
                return baseOf(X) == B || rootOff(X, CDL).first == B || // S3: a phi of equal steps
                       canonRoot(rootOff(X, CDL).first) == canonRoot(B);    // S6: a re-read
              };
              baseIsInserted |= isE(R->elem);
              for (int e : R->moreElems) baseIsInserted |= isE(e);
            }
          }
        const uint8_t bodyB = inBody ? get(B) & ~NUL : 0;
        const bool containerBase =
            (bodyB & (OWN | DER | FRS)) || (ocB & (OC_OWNER | OC_VAL | OC_SLOT)) || baseIsInserted;
        std::vector<std::pair<StructType *, int64_t>> named;
        if (!addrSlots(I, A, named, 0)) {
          if (containerBase)
            o1Naming.push_back(siteText(I) + (rawWrite ? " (an asm raw-pointer write)" : " (a write)") + pastText());
          return;
        }
        // The declared slots [off, off + bytes) covers, for each field the
        // address may name.
        std::vector<std::pair<std::string, char>> covered;
        bool someUncovered = false; // a field the address may name that holds no declared slot
        bool uncoveredDeclared = false; // ... and lies in a struct the block declares slots of
        bool inUnion = false;       // bytes inside a union whose IR member holds a declared slot
        auto declaredIn = [&](StructType *ST, int64_t lo, int64_t h, std::vector<std::pair<std::string, char>> &out) {
          if (!ST->hasName()) return;
          const std::string SN = stripStructNameSuffix(ST->getName()).str();
          const size_t before = out.size();
          bool declStruct = false;
          for (const std::set<std::string> *D : {&declHandle, &declLink, &declWord})
            for (const std::string &K : *D) {
              const size_t p = K.rfind('+');
              if (K.compare(0, p, SN) != 0 || p != SN.size()) continue;
              declStruct = true;
              const int64_t o = std::stoll(K.substr(p + 1));
              if (o >= lo && o < h) out.push_back({K, kindOf(K)});
            }
          uncoveredDeclared |= declStruct && out.size() == before;
        };
        for (auto &[S, off] : named) {
          const size_t before = covered.size();
          bool unionHere = false;
          // A union stops the cover (class 2): its IR member is clang's
          // representative, so a declared slot there is storage inside a
          // union, counted, not a write of that slot.
          structCoverToUnions(
              S, off, bytes < 0 ? INT64_MAX / 2 : off + bytes, CDL,
              [&](StructType *ST, int64_t lo, int64_t h) { declaredIn(ST, lo, h, covered); },
              [&](StructType *U, int64_t lo, int64_t h) {
                std::vector<std::pair<std::string, char>> inside;
                const bool keep = uncoveredDeclared; // a union's members are class 2, not D2
                structCover(U, lo, h, CDL, [&](StructType *ST, int64_t l2, int64_t h2) { declaredIn(ST, l2, h2, inside); });
                uncoveredDeclared = keep;
                unionHere |= !inside.empty();
              });
          inUnion |= unionHere;
          someUncovered |= covered.size() == before && !unionHere;
        }
        if (inUnion && covered.empty()) {
          unionStorage["writes"]++;
          if (unionSites.size() < 8) unionSites.push_back(siteText(I) + " (a write)");
        }
        // D2 (i): an element-derived value stored where the address may name
        // a field outside the declared slots.
        if (someUncovered && wk == WStore && containerBase && V->getType()->isPointerTy()) {
          const uint8_t vb = inBody ? get(V) : 0;
          uint8_t vo = 0;
          if (gs)
            for (auto &SG : *gs)
              if (auto it = SG.second.cls.find(strip(V)); it != SG.second.cls.end()) vo |= it->second;
          // An element pointer kept in a plain field (a cursor: ext4's
          // info->curr_node) is ordinary flow, counted, never a FAIL (Fable
          // 2026-10-16: O1 constrains stores into declared slots and stores
          // of link values, not every copy of an element pointer). A field
          // of a struct the block declares slots of that holds none (a fourth
          // pointer in rb_node) is the declared storage checked from the
          // program's side (D2): it stays a FAIL.
          if ((vb & (DER | FRS)) || (vo & OC_VAL)) {
            if (uncoveredDeclared) {
              fail("an element stored outside the declared storage", I);
            } else {
              o1Admit["an element pointer kept in a plain field"]++;
              if (plainFieldSites.size() < 8) plainFieldSites.push_back(siteText(I));
            }
          }
        }
        if (covered.empty()) return;
        // A copy over exactly the element's declared link record (every
        // LINK and LINKWORD slot of the element struct, its whole size):
        // rb_replace_node's `*new = *victim`, the victim's parent word with
        // its tag included (the new node takes the victim's place).
        bool wholeRecord = false;
        if (wk == WCopy && premiseElemT && named.size() == 1 && named[0].second == 0 &&
            stripStructNameSuffix(named[0].first->getName()) == stripStructNameSuffix(premiseElemT->getName()) &&
            bytes == (int64_t)CDL.getTypeAllocSize(premiseElemT)) {
          std::set<std::string> want, got;
          for (const std::set<std::string> *D : {&declLink, &declWord})
            for (const std::string &K : *D)
              if (K.compare(0, K.rfind('+'), stripStructNameSuffix(premiseElemT->getName())) == 0) want.insert(K);
          for (auto &[K, kind] : covered) got.insert(K);
          wholeRecord = !want.empty() && want == got;
        }
        for (auto &[K, kind] : covered) {
          unusedDecl.erase(K);
          const uint64_t slotBytes = kind == 'w' ? pw / 8 : CDL.getPointerSize();
          if (wk == WFill) {
            if (isNullV(V)) o1Admit["null fills"]++;
            else fail("a block fill of another value over " + K, I);
            continue;
          }
          if (wk == WCopy) {
            // A block copy: the source's fields; an element of the same owner
            // in owner code, a derived or fresh block in the body.
            const Value *SB = baseOf(V);
            uint8_t so = 0;
            if (gs)
              for (auto &[sh, Gp] : *gs) {
                (void)sh;
                if (auto it = Gp.cls.find(SB); it != Gp.cls.end()) so |= it->second;
              }
            if ((inBody && (get(SB) & ~NUL) && !(get(SB) & ~(DER | FRS | NUL))) || (so & OC_VAL))
              o1Admit[wholeRecord ? "copies of an element's links (with the link word's tag)" : "element copies"]++;
            else
              fail("a block copy of another value over " + K, I);
            continue;
          }
          if ((uint64_t)bytes > slotBytes) {
            if (isNullV(V) || (isa<Constant>(V) && cast<Constant>(V)->isNullValue())) o1Admit["wide null stores"]++;
            else fail("a wide store of another value over " + K, I);
            continue;
          }
          if (isNullV(V)) { o1Admit["null stores"]++; continue; }
          if (const auto *CI = dyn_cast<ConstantInt>(V); CI && kind == 'w' && CI->getValue().ult(8)) {
            o1Admit["null plus tag (R1)"]++;
            continue;
          }
          // R2: the element's own address (its object's) into its own slot,
          // tagged or not.
          const Value *SV = strip(V);
          if (const auto *BO = dyn_cast<BinaryOperator>(SV); BO && isa<ConstantInt>(BO->getOperand(1)))
            SV = strip(BO->getOperand(0));
          if (SV->getType()->isPointerTy() && baseOf(SV) == B) {
            o1Admit["self-link stores (R2)"]++;
            continue;
          }
          if (!V->getType()->isPointerTy()) {
            if (const auto *L = dyn_cast<LoadInst>(V); L && L->getPointerOperand()->stripPointerCasts() == A->stripPointerCasts()) {
              o1Admit["same-cell re-stores (R4)"]++;
              continue;
            }
            if (selfDerived(V, A, 0) && !isa<PtrToIntOperator>(strip(V))) {
              o1Admit[isa<ConstantInt>(V) ? "link word reused as integer: constants (R4)"
                                          : "link word reused as integer: self-derived (R4)"]++;
              continue;
            }
          } else if (const auto *L = dyn_cast<LoadInst>(V);
                     L && L->getPointerOperand()->stripPointerCasts() == A->stripPointerCasts()) {
            o1Admit["same-cell re-stores (R4)"]++;
            continue;
          }
          if (inBody) {
            // The body's own stores: a value derived from its owner, an
            // element coming in, or a fresh block (with link words: their
            // tagged words).
            const uint8_t v = get(V), a = bodyB;
            if (a && !(a & ~(OWN | DER | FRS)) && v && !(v & ~(DER | NUL | FRS))) {
              o1Admit["body stores"]++;
              continue;
            }
          }
          bool done = false;
          if (gs)
            for (auto &SG : *gs) {
              Group &Gp = SG.second;
              auto cl = [&](const Value *X) {
                auto it = Gp.cls.find(strip(X));
                uint8_t m = it == Gp.cls.end() ? 0 : it->second;
                for (const Value *e : Gp.elems) m |= e == strip(X) ? OC_VAL : 0;
                for (const Value *o : Gp.owners) m |= o == strip(X) ? OC_OWNER : 0;
                return m;
              };
              const uint8_t ac = cl(A), bc = cl(B), vc = cl(V);
              const bool derivedSlot = (ac & OC_SLOT) || (bc & (OC_OWNER | OC_VAL));
              if (derivedSlot && (vc & (OC_VAL | OC_WORD))) {
                // A relink (4(a)): a derived value into a derived slot
                // (an inlined remove, a rotate, __rb_change_child).
                o1Admit["owner-code relinks"]++;
                done = true;
                break;
              }
              if (derivedSlot && V->getType()->isPointerTy()) {
                // An implicit insert: paired with an insert row call in this
                // function on the same element and owner value.
                bool matched = false;
                for (const CallBase *CB : Gp.inserts) {
                  const CR *R = rowAt(CB);
                  // The same element: the actual itself, or a value it merges
                  // through phis and selects (rb_insert_augmented_cached's
                  // `*link = node` on the empty-tree path).
                  auto isE = [&](int e) {
                    if (e < 0 || (unsigned)e >= CB->arg_size()) return false;
                    // One object and offset (`&it->node` computed twice).
                    if (ownerShape(CB->getArgOperand(e), 0) == ownerShape(V, 0) && !ownerShape(V, 0).empty()) return true;
                    std::vector<const Value *> wl{CB->getArgOperand(e)->stripPointerCasts()};
                    std::set<const Value *> seen(wl.begin(), wl.end());
                    for (size_t k = 0; k < wl.size() && k < 64; k++) {
                      if (wl[k] == V->stripPointerCasts()) return true;
                      auto add = [&](const Value *X) {
                        if (seen.insert(X->stripPointerCasts()).second) wl.push_back(X->stripPointerCasts());
                      };
                      if (const auto *PN = dyn_cast<PHINode>(wl[k]))
                        for (const Value *In : PN->incoming_values()) add(In);
                      else if (const auto *SL = dyn_cast<SelectInst>(wl[k]))
                        add(SL->getTrueValue()), add(SL->getFalseValue());
                    }
                    return false;
                  };
                  matched |= isE(R->elem);
                  for (int e : R->moreElems) matched |= isE(e);
                }
                // One site, whichever slots its address may name.
                if (implicitSeen.insert(I).second) {
                  (matched ? implicitMatched : implicitUnmatched).push_back(siteText(I));
                  if (matched) o1Admit["implicit inserts (matched)"]++;
                  else fail("an implicit insert with no insert row call on the same element and owner", I);
                }
                done = true;
                break;
              }
              if (baseIsInserted && (vc & (OC_VAL | OC_WORD))) {
                o1Admit["link stores on the inserted element"]++;
                done = true;
                break;
              }
            }
          if (!done && !inBody && !gs && kind == 'h' && V->getType()->isPointerTy()) {
            // An element stored into a handle in a function that calls no
            // row (__llist_add, static inline: no symbol to row).
            fail("an inline insert with no row symbol (an element into " + K + " in a function that calls no row)", I);
            done = true;
          }
          if (!done) fail(inBody ? "the body stores another value into " + K : "a store into " + K + " outside the rows", I);
        }
      };
      for (auto &[M, _] : Ctx->Modules)
        for (const Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            if (const auto *S = dyn_cast<StoreInst>(&I)) {
              onWrite(S, S->getPointerOperand(), S->getValueOperand(),
                      (int64_t)CDL.getTypeStoreSize(S->getValueOperand()->getType()), WStore);
            } else if (const auto *MS = dyn_cast<MemSetInst>(&I)) {
              const auto *Len = dyn_cast<ConstantInt>(MS->getLength());
              onWrite(MS, MS->getDest(), MS->getValue(), Len ? (int64_t)Len->getZExtValue() : -1, WFill);
            } else if (const auto *MT = dyn_cast<MemTransferInst>(&I)) {
              const auto *Len = dyn_cast<ConstantInt>(MT->getLength());
              onWrite(MT, MT->getRawDest(), MT->getRawSource(), Len ? (int64_t)Len->getZExtValue() : -1, WCopy);
            } else if (const auto *CB = dyn_cast<CallBase>(&I); CB && CB->isInlineAsm()) {
              // The asm's stores, by the graph build's model.
              const AsmModel AM = asmModel(*CB, &CDL);
              for (const AsmModel::Slot &Sl : AM.slots)
                if (Sl.output)
                  for (const AsmModel::Value_ &In : Sl.stores) onWrite(CB, Sl.ptr, In.val, CDL.getPointerSize(), WStore);
              rawWrite = true;
              if (AM.memEffects)
                for (const Value *P : AM.rawPtrs)
                  for (const AsmModel::Value_ &In : AM.valueInputs)
                    if (In.ok) onWrite(CB, P, In.val, CDL.getPointerSize(), WStore);
              rawWrite = false;
            }
          }
      // Reads: lookups by derivation in owner code, and reads through owner
      // or element values that no rule names (the body's and owner code's).
      for (auto &[M, _] : Ctx->Modules)
        for (const Function &F : *M) {
          auto *gs = groupsOf(&F);
          const bool inBody = body.count(&F);
          if (!gs && !inBody) continue;
          for (const Instruction &I : instructions(F)) {
            const auto *L = dyn_cast<LoadInst>(&I);
            if (!L) continue;
            const Value *B = baseOf(L->getPointerOperand());
            uint8_t oc = 0;
            if (gs)
              for (auto &[sh, Gp] : *gs) {
                (void)sh;
                if (auto it = Gp.cls.find(B); it != Gp.cls.end()) oc |= it->second;
                for (const Value *o : Gp.owners) oc |= o == B ? OC_OWNER : 0;
                if (auto it = Gp.cls.find(L); it != Gp.cls.end() && !inBody && (it->second & (OC_VAL | OC_WORD)))
                  lookupsByDerivation++;
              }
            const bool containerBase = (inBody && (get(B) & (OWN | DER | FRS))) || (oc & (OC_OWNER | OC_VAL | OC_SLOT));
            std::vector<std::pair<StructType *, int64_t>> named;
            if (containerBase && !isa<AllocaInst>(B) && !addrSlots(L, L->getPointerOperand(), named, 0))
              o1Naming.push_back(siteText(L) + " (a read)" + pastText());
          }
        }
      // A LINKWORD's R1 verdict, its assumptions carried.
      for (const std::string &K : declWord) {
        auto it = linkWordVerdicts.find(K);
        if (it == linkWordVerdicts.end()) {
          wordLines.push_back("link word " + K + ": no R1 verdict (never read back as a pointer here)");
          continue;
        }
        wordLines.push_back("link word " + K + ": R1 " + it->second.first);
        for (const std::string &a : it->second.second) wordLines.push_back("  ASSUMPTION " + K + ": " + a);
        if (it->second.first.rfind("PASS", 0) != 0) o1Fail["link word " + K + " fails R1 (" + it->second.first + ")"];
      }
      for (const std::string &m : diMismatch) o1Fail["declared storage disagrees: " + m];
    }

    if (!declared) {
      std::set<std::string> checked1 = handle;
      checked1.insert(links.begin(), links.end());
      for (const std::string &K : checked1) {
        bool ok = true;
        for (const StoreInst *S : fields[K].foreignSI)
          if (isMove(S) || isInlineMove(S)) moves++;
          else if (ok) ok = false, firstBad1[K] = S;
        if (!ok) open1.insert(K);
      }
      // A block copy anywhere whose destination is an element struct (one
      // embedding a container struct) is a store of the source's fields:
      // the source an element of the same owner, or in the body derived or
      // fresh; memset is a null store (Fable 2026-10-14, per-field
      // decomposition). Destinations named by the copy's struct access.
      std::set<std::string> elemStructs;
      for (const std::string &L : links) elemStructs.insert(L.substr(0, L.rfind('+')));
      std::function<bool(StringRef, int)> embedsElem = [&](StringRef Tag, int d) -> bool {
        if (elemStructs.count("struct." + Tag.str())) return true;
        if (d > 4) return false;
        auto dit = diStructs.find(Tag.str());
        if (dit == diStructs.end()) return false;
        for (const DINode *E : dit->second->getElements())
          if (const auto *M = dyn_cast<DIDerivedType>(E); M && M->getTag() == dwarf::DW_TAG_member)
            if (const auto *CT = dyn_cast_or_null<DICompositeType>(diStrip(M->getBaseType()));
                CT && CT->getTag() == dwarf::DW_TAG_structure_type && !CT->getName().empty() && M->getOffsetInBits() == 0 &&
                embedsElem(CT->getName(), d + 1))
              return true;
        return false;
      };
      std::vector<std::string> badCopies; // every failing copy (reported, not only the first)
      std::vector<std::string> o1Unclassified; // block copies whose destination the check cannot classify
      // A destination's origins by name (Fable 2026-10-17): a program-wide
      // walk over the IR only (no solver facts, so no stop changes it).
      // Steps: casts and GEPs to their base; a -O0 local to the values
      // stored into it; a named field S+off to every value stored into
      // S+off and every global initializer's value there (a block copy over
      // the field from another name: unknown); a formal to the actuals of
      // its direct calls (an address-taken function's, or one with no
      // caller: unknown); a call with a body to its returned values. Leaves:
      // an allocation (a pool carve: a chunk), a local, a global, an
      // element (a constructor's allocation, a constructor's or a row's
      // result, a load of a handle, link or closed cursor field), or
      // unknown with its reason. Elements are exactly the constructors'
      // allocations: the block's insert checks (O3, ELEM rows) establish
      // it, and this classification inherits their openness.
      std::map<std::string, std::vector<const Value *>> storedAt; // field key -> values stored there
      std::map<std::string, std::vector<std::string>> fieldUnknown; // field key -> block copies over it from elsewhere
      struct UnnamedSlot { const GlobalVariable *G; int64_t b, size; };
      std::vector<UnnamedSlot> initSlotsUnnamed; // pointer slots no name reads (literal IR struct, no debug type)
      std::vector<std::pair<std::string, const MemTransferInst *>> fieldCopies;
      for (auto &[M, _] : Ctx->Modules) {
        const DataLayout &MDL = M->getDataLayout();
        for (Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            if (const auto *S = dyn_cast<StoreInst>(&I); S && S->getValueOperand()->getType()->isPointerTy()) {
              const std::string K = fieldKey(S, S->getPointerOperand());
              if (!K.empty()) storedAt[K].push_back(S->getValueOperand());
            } else if (const auto *VT = S ? dyn_cast<FixedVectorType>(S->getValueOperand()->getType()) : nullptr;
                       VT && VT->getElementType()->isPointerTy()) {
              // A vector of pointers stored over consecutive fields (-O3's
              // paired stores): each lane's field gets the vector's values.
              const std::string K = fieldKey(S, S->getPointerOperand());
              if (!K.empty()) {
                const std::string SN = K.substr(0, K.rfind('+'));
                const int64_t o0 = std::stoll(K.substr(K.rfind('+') + 1));
                const int64_t w = (int64_t)MDL.getTypeAllocSize(VT->getElementType());
                for (unsigned l = 0; l < VT->getNumElements(); l++)
                  storedAt[SN + "+" + std::to_string(o0 + l * w)].push_back(S->getValueOperand());
              }
            } else if (const auto *MT = dyn_cast<MemTransferInst>(&I)) {
              const std::string K = fieldKey(MT, MT->getRawDest());
              if (!K.empty()) fieldCopies.emplace_back(K, MT);
            }
          }
        // Global initializers: every non-null pointer at each name its slot
        // lies at, the IR named structs around it and the global's debug
        // type (a union initializer makes the IR type literal: its slots are
        // named by the declaration alone). A slot in a literal struct of a
        // global with no debug type has no name: a load of a name that may
        // lie over it is open.
        for (const GlobalVariable &G : M->globals())
          initSlots(G, MDL, [&](const Constant *C, int64_t b, const std::set<std::string> &keys, bool hasDI, bool inLiteral) {
            if (!C->getType()->isPointerTy()) return;
            for (const std::string &k : keys) storedAt[k].push_back(C);
            if (keys.empty() && !hasDI && inLiteral)
              initSlotsUnnamed.push_back({&G, b, (int64_t)MDL.getTypeAllocSize(G.getValueType())});
          });
      }
      // A block copy over a field: from the same field of another object of
      // the struct (a struct copy) it brings that field's own values; from
      // anything else, unknown.
      for (const auto &[K, MT] : fieldCopies) {
        const std::string S = K.substr(0, K.rfind('+'));
        const int64_t off = std::stoll(K.substr(K.rfind('+') + 1));
        const auto *LenC = dyn_cast<ConstantInt>(MT->getLength());
        const int64_t len = LenC ? (int64_t)LenC->getZExtValue() : INT64_MAX / 2;
        const std::string SK = fieldKey(MT, MT->getRawSource());
        bool same = SK == K;
        // From a local of the struct, at the same offset: its fields' values
        // are the writes keyed by the struct (through any pointer to it)
        // and the local's own direct stores (added below).
        const AllocaInst *srcLocal = nullptr;
        {
          APInt SO(64, 0);
          const Value *SB = MT->getRawSource()->stripAndAccumulateConstantOffsets(MT->getModule()->getDataLayout(), SO, true);
          if (const auto *AI = dyn_cast<AllocaInst>(SB))
            if (auto *ST = dyn_cast<StructType>(AI->getAllocatedType());
                ST && ST->hasName() && stripStructNameSuffix(ST->getName()).str() == S && SO.getSExtValue() == off)
              same = true, srcLocal = AI;
        }
        for (auto it = storedAt.lower_bound(S + "+"); it != storedAt.end() && it->first.compare(0, S.size() + 1, S + "+") == 0; ++it) {
          const int64_t o = std::stoll(it->first.substr(S.size() + 1));
          if (o >= off && o < off + len && !same)
            fieldUnknown[it->first].push_back("a block copy from another name: " + MT->getFunction()->getName().str() + ": " + valueText(MT));
        }
        if (srcLocal) {
          const DataLayout &LDL = MT->getModule()->getDataLayout();
          for (const Instruction &J : instructions(*MT->getFunction())) {
            const Value *A = nullptr, *Val = nullptr;
            if (const auto *St = dyn_cast<StoreInst>(&J)) A = St->getPointerOperand(), Val = St->getValueOperand();
            else if (const auto *MJ = dyn_cast<MemTransferInst>(&J)) A = MJ->getRawDest();
            if (!A) continue;
            APInt LO(64, 0);
            if (A->stripAndAccumulateConstantOffsets(LDL, LO, true) != srcLocal) continue;
            if (!Val) { // a block copy into the local: the fields it covers come from elsewhere
              const auto *JL = dyn_cast<ConstantInt>(cast<MemTransferInst>(&J)->getLength());
              const int64_t jl = JL ? (int64_t)JL->getZExtValue() : INT64_MAX / 2;
              const StructLayout *SL = LDL.getStructLayout(cast<StructType>(srcLocal->getAllocatedType()));
              for (unsigned e = 0; e < SL->getMemberOffsets().size(); e++) {
                const int64_t eo = (int64_t)SL->getElementOffset(e);
                if (eo >= LO.getSExtValue() && eo < LO.getSExtValue() + jl)
                  fieldUnknown[S + "+" + std::to_string(eo)].push_back("a block copy into a local the struct is copied from: " + MT->getFunction()->getName().str() + ": " +
                                                                       valueText(&J));
              }
              continue;
            }
            if (Val->getType()->isPointerTy()) storedAt[S + "+" + std::to_string(LO.getSExtValue())].push_back(Val);
          }
        }
      }
      auto callerOf = [](const Function *F, std::vector<const CallBase *> &out) {
        for (const User *U : F->users())
          if (const auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand() == F) out.push_back(CB);
      };
      // Casts only (bitcast, addrspacecast): stripPointerCasts would also
      // drop an all-zero-index GEP, a step the chains below report.
      auto castsOnly = [](const Value *V) {
        while (isa<BitCastOperator>(V) || isa<AddrSpaceCastOperator>(V)) V = cast<Operator>(V)->getOperand(0);
        return V;
      };
      auto snapLoc = [](const Instruction *I) {
        std::string l = I->getFunction()->getName().str();
        if (const DebugLoc &DLc = I->getDebugLoc()) l += " " + DLc->getFilename().str() + ":" + std::to_string(DLc.getLine());
        return l;
      };
      struct Origins {
        std::set<std::string> leaves, unknown, elements;
        std::map<std::string, std::set<std::string>> pools; // certified pool -> its carves reached
        std::set<const Value *> objs;                        // the locals and globals among the leaves
        std::set<const Instruction *, IROrder> allocs;       // the allocations and pool carves among them (their sites, in IR order)
      };
      // The values stored through pointer P (a local or a global whose
      // address is passed on, an output parameter's formal): its own stores,
      // through -O0 slots holding it, casts, the formals of direct callees
      // with bodies it is passed to, and bodiless callees' summaries (a
      // STORE atom into it). Anything else that uses P: unknown.
      std::function<void(const Value *, std::vector<const Value *> &, std::set<std::string> &, std::set<const Value *> &)>
          storesThrough = [&](const Value *P, std::vector<const Value *> &out, std::set<std::string> &unk,
                              std::set<const Value *> &vis) {
            if (!vis.insert(P).second) return;
            for (const User *U : P->users()) {
              const auto *UI = dyn_cast<Instruction>(U);
              if (!UI || isa<DbgInfoIntrinsic>(UI) || UI->isLifetimeStartOrEnd() || isa<ICmpInst>(UI)) continue;
              // A memset through it writes a byte pattern, no pointer value.
              if (const auto *MS = dyn_cast<MemSetInst>(UI); MS && MS->getRawDest() == P) continue;
              if (const auto *L = dyn_cast<LoadInst>(UI); L && L->getPointerOperand() == P) continue;
              if (const auto *S = dyn_cast<StoreInst>(UI)) {
                if (S->getPointerOperand() == P && S->getValueOperand() != P) {
                  out.push_back(S->getValueOperand());
                  continue;
                }
                if (S->getValueOperand() == P && transientSlot(S->getPointerOperand()->stripPointerCasts())) {
                  for (const User *V : S->getPointerOperand()->stripPointerCasts()->users())
                    if (const auto *L = dyn_cast<LoadInst>(V)) storesThrough(L, out, unk, vis);
                  continue;
                }
              }
              if (isa<BitCastInst>(UI) || isa<AddrSpaceCastInst>(UI)) {
                storesThrough(UI, out, unk, vis);
                continue;
              }
              if (const auto *CB = dyn_cast<CallBase>(UI)) {
                const Function *H = CB->getCalledFunction();
                bool ok = H != nullptr;
                for (unsigned a = 0; ok && a < CB->arg_size(); a++) {
                  if (CB->getArgOperand(a) != P) continue;
                  if (!H->isDeclaration() && !H->hasAddressTaken() && a < H->arg_size()) {
                    storesThrough(H->getArg(a), out, unk, vis);
                  } else if (H->isDeclaration()) {
                    auto sit = Ctx->FuncSummaries.find(H);
                    if (sit == Ctx->FuncSummaries.end() || !sit->second) {
                      ok = false;
                      break;
                    }
                    for (const auto &At : sit->second->atoms) {
                      if (At.dst != (int)a) continue;
                      if (At.kind == GlobalContext::SummaryAtom::Store && At.src >= 0 && (unsigned)At.src < CB->arg_size())
                        out.push_back(CB->getArgOperand(At.src));
                      else if (At.kind != GlobalContext::SummaryAtom::Alias)
                        ok = false;
                    }
                  } else {
                    ok = false;
                  }
                }
                if (ok) continue;
              }
              unk.insert("a pointer to a local or global used by " + UI->getFunction()->getName().str() + ": " + valueText(UI));
            }
          };
      // A named field's address that escapes (passed to a callee that
      // stores through it, `*ptr = p`, held in a local): the values stored
      // through it are the field's too; anything else it reaches: the
      // field is unknown.
      for (auto &[M, _] : Ctx->Modules)
        for (Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            if (!isa<GetElementPtrInst>(&I) || !I.getType()->isPointerTy()) continue;
            bool escapes = false;
            for (const User *U : I.users())
              if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == &I) continue;
              else if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand() == &I && St->getValueOperand() != &I) continue;
              else if (isa<DbgInfoIntrinsic>(U) || isa<GetElementPtrInst>(U) || isa<ICmpInst>(U)) continue;
              else escapes = true;
            if (!escapes) continue;
            const std::string FK = fieldKey(&I, &I);
            if (FK.empty()) continue;
            std::set<const Value *> vis;
            std::vector<const Value *> vals;
            std::set<std::string> unk;
            storesThrough(&I, vals, unk, vis);
            if (!unk.empty()) fieldUnknown[FK].push_back(*unk.begin() + " (its address escapes)");
            for (const Value *W : vals) storedAt[FK].push_back(W);
          }
      std::set<const CallBase *> icallClosed; // indirect call sites whose callee closes by name (d)
      std::set<const CallBase *> *icallCount = &icallClosed; // where originsOf records them (a snapshot cover keeps its own)
      // The field keys a load of type T at K reads: K, and for a vector of
      // pointers each lane's field.
      auto laneKeys = [&](const std::string &K, Type *T) {
        std::vector<std::string> ks{K};
        if (const auto *VT = dyn_cast<FixedVectorType>(T); VT && VT->getElementType()->isPointerTy()) {
          const std::string SN = K.substr(0, K.rfind('+'));
          const int64_t o0 = std::stoll(K.substr(K.rfind('+') + 1));
          for (unsigned l = 1; l < VT->getNumElements(); l++)
            ks.push_back(SN + "+" + std::to_string(o0 + l * 8));
        }
        return ks;
      };
      // A by-name load of K that may read an unnamed initializer slot (K's
      // struct fitting over it in the global's bytes): why, or "".
      std::map<std::string, int64_t> structBytes; // a named struct's size, by name
      if (!initSlotsUnnamed.empty())
        for (auto &[M, _] : Ctx->Modules)
          for (StructType *ST : M->getIdentifiedStructTypes())
            if (ST->hasName() && !ST->isOpaque() && ST->isSized())
              structBytes.emplace(stripStructNameSuffix(ST->getName()).str(), (int64_t)M->getDataLayout().getTypeAllocSize(ST));
      auto unnamedSlotUnder = [&](const std::string &K) -> std::string {
        if (initSlotsUnnamed.empty()) return "";
        const size_t p = K.rfind('+');
        const int64_t o = std::stoll(K.substr(p + 1));
        const auto it = structBytes.find(K.substr(0, p));
        const int64_t sz = it == structBytes.end() ? 0 : it->second;
        for (const UnnamedSlot &u : initSlotsUnnamed)
          if (o <= u.b && u.b - o + sz <= u.size)
            return "initializer slots unnamed at @" + u.G->getName().str() + " +" + std::to_string(u.b);
        return "";
      };
      // (f) A formal of an address-taken function F has known callers
      // when F's address only feeds closed code fields (Fable 2026-10-19):
      // every use of F is a direct call, a store of F into a code field
      // closed in O1(d)'s sense whose targets include F, or an actual to
      // a defined init function that is not address-taken, whose formal
      // has one use: (-O0) a store into its slot, loaded once and the
      // slot used no other way; the value is stored into such a field or
      // passed down to another such init function the same way. F's
      // callers are then its direct callers and every indirect call
      // through those fields. Why the rule does not apply, or the field,
      // the init chain and the callers, is kept for the log.
      // (R3, Fable 2026-10-20) F's address may also lie in slots of
      // constant initializers: see r3Slot below. The callers are defined
      // after originsOf, which consults them for an address-taken formal.
      struct Fed { std::vector<const CallBase *> callers; std::string text, why; };
      struct GVByName {
        bool operator()(const GlobalVariable *A, const GlobalVariable *B) const { return A->getName() < B->getName(); }
      };
      std::map<const Function *, Fed> fedOf;
      std::function<const Fed &(const Function *)> fedCallers;
      // R3's read-side census walks block copy sources with every
      // address-taken formal open (no callers consulted).
      bool formalsOpen = false;
      std::function<Origins(const Value *, int)> originsOf = [&](const Value *D0, int depth) {
        Origins O;
        std::set<const Value *> seen;
        std::vector<const Value *> work{D0};
        auto loc = [](const Instruction *I) {
          std::string l = I->getFunction()->getName().str();
          if (const DebugLoc &DLc = I->getDebugLoc()) l += " " + DLc->getFilename().str() + ":" + std::to_string(DLc.getLine());
          return l;
        };
        while (!work.empty()) {
          const Value *V = work.back();
          work.pop_back();
          if (!seen.insert(V).second) continue;
          if (seen.size() > 100000) {
            O.unknown.insert("the walk exceeds 100000 values");
            break;
          }
          if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V) || isa<ConstantAggregateZero>(V)) continue;
          if (const auto *CV = dyn_cast<ConstantVector>(V)) {
            for (const Use &U : CV->operands()) work.push_back(U.get());
            continue;
          }
          if (const auto *G = dyn_cast<GlobalValue>(V)) {
            O.leaves.insert("global " + G->getName().str());
            O.objs.insert(G);
            continue;
          }
          if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
            if (CE->getOpcode() == Instruction::GetElementPtr || CE->isCast()) work.push_back(CE->getOperand(0));
            else O.unknown.insert("a constant expression: " + valueText(CE));
            continue;
          }
          if (const auto *A = dyn_cast<Argument>(V)) {
            const Function *F = A->getParent();
            std::vector<const CallBase *> cs;
            callerOf(F, cs);
            if (F->hasAddressTaken()) {
              // (f) and R3: its callers when the rule applies.
              const Fed *fd = formalsOpen ? nullptr : &fedCallers(F);
              if (!fd || fd->text.empty())
                O.unknown.insert("a formal of address-taken " + F->getName().str() + (fd ? ": " + fd->why : std::string()));
              else if (fd->callers.empty())
                O.unknown.insert("a formal of " + F->getName().str() + ", which has no caller");
              else
                for (const CallBase *CB : fd->callers)
                  if (A->getArgNo() < CB->arg_size()) work.push_back(CB->getArgOperand(A->getArgNo()));
            } else if (cs.empty()) O.unknown.insert("a formal of " + F->getName().str() + ", which has no caller");
            else
              for (const CallBase *CB : cs)
                if (A->getArgNo() < CB->arg_size()) work.push_back(CB->getArgOperand(A->getArgNo()));
            continue;
          }
          const auto *I = dyn_cast<Instruction>(V);
          if (!I) {
            O.unknown.insert("a value: " + valueText(V));
            continue;
          }
          if (isa<AllocaInst>(I)) {
            O.leaves.insert("local " + loc(I));
            O.objs.insert(I);
            continue;
          }
          if (poolCarves.count(I)) {
            if (ctorsHere.count(I->getFunction())) O.elements.insert("a constructor's carve in " + loc(I));
            else O.pools[poolCarvePool.at(I)].insert("a carve in " + loc(I)), O.allocs.insert(I);
            continue;
          }
          if (isa<CastInst>(I) || isa<GetElementPtrInst>(I) || isa<FreezeInst>(I)) {
            if (isa<IntToPtrInst>(I)) O.unknown.insert("an inttoptr in " + loc(I));
            else work.push_back(I->getOperand(0));
            continue;
          }
          if (const auto *PN = dyn_cast<PHINode>(I)) {
            for (const Value *In : PN->incoming_values()) work.push_back(In);
            continue;
          }
          if (const auto *SL = dyn_cast<SelectInst>(I)) {
            work.push_back(SL->getTrueValue());
            work.push_back(SL->getFalseValue());
            continue;
          }
          // Vectors of pointers: a lane's origins are the vector's (its
          // operands, all lanes).
          if (isa<ShuffleVectorInst>(I) || isa<InsertElementInst>(I)) {
            work.push_back(I->getOperand(0));
            work.push_back(I->getOperand(1));
            continue;
          }
          if (isa<ExtractElementInst>(I)) {
            work.push_back(I->getOperand(0));
            continue;
          }
          if (const auto *L = dyn_cast<LoadInst>(I)) {
            const Value *A = L->getPointerOperand()->stripPointerCasts();
            // A load that finds no value is open, never an empty close.
            if (transientSlot(A)) {
              bool any = false;
              for (const User *U : A->users())
                if (const auto *S = dyn_cast<StoreInst>(U)) work.push_back(S->getValueOperand()), any = true;
              if (!any) O.unknown.insert("a load of an -O0 local never stored in " + loc(L));
              continue;
            }
            const std::string K = fieldKey(L, L->getPointerOperand());
            if (!K.empty()) {
              for (const std::string &LK : laneKeys(K, L->getType())) {
                if (handle.count(LK) || links.count(LK) || (cursorOpen.count(LK) && cursorOpen[LK].empty())) {
                  O.elements.insert("a load of " + LK + " in " + loc(L));
                  continue;
                }
                if (auto fu = fieldUnknown.find(LK); fu != fieldUnknown.end()) {
                  O.unknown.insert("field " + LK + " not closed by name: " + fu->second.front());
                  continue;
                }
                if (const std::string un = unnamedSlotUnder(LK); !un.empty()) {
                  O.unknown.insert("a load of " + LK + " in " + loc(L) + ": " + un);
                  continue;
                }
                if (const auto sit = storedAt.find(LK); sit != storedAt.end() && !sit->second.empty())
                  for (const Value *W : sit->second) work.push_back(W);
                else O.unknown.insert("a load of " + LK + " in " + loc(L) + ": no value stored by name");
              }
              continue;
            }
            if (const auto *G = dyn_cast<GlobalVariable>(A)) {
              bool escapes = false;
              for (const User *U : G->users())
                if (const auto *S = dyn_cast<StoreInst>(U)) {
                  if (S->getPointerOperand() == G) work.push_back(S->getValueOperand());
                  else escapes = true;
                } else if (!isa<LoadInst>(U)) {
                  escapes = true;
                }
              if (escapes) O.unknown.insert("a load of global " + G->getName().str() + ", whose address escapes");
              else if (G->hasInitializer()) work.push_back(G->getInitializer());
              else if (std::none_of(G->user_begin(), G->user_end(), [](const User *U) { return isa<StoreInst>(U); }))
                O.unknown.insert("a load of global " + G->getName().str() + ": no initializer, no store");
              continue;
            }
            // Through a pointer: the addresses it can hold by name (a named
            // field's address, a local's, a global's), each read as itself:
            // a field's stored values, the values stored through a local's or
            // a global's address. Anything else: unknown.
            std::set<std::string> fks;
            std::set<const Value *> objs, avis;
            std::string why;
            std::vector<const Value *> aw{A};
            while (!aw.empty() && why.empty()) {
              const Value *X = aw.back();
              aw.pop_back();
              if (!avis.insert(X).second) continue;
              if (avis.size() > 10000) why = "the address walk exceeds 10000 values";
              else if (isa<ConstantPointerNull>(X)) continue;
              else if (isa<AllocaInst>(X) || isa<GlobalVariable>(X)) objs.insert(X);
              else if (const auto *XA = dyn_cast<Argument>(X)) {
                const Function *F = XA->getParent();
                std::vector<const CallBase *> cs;
                callerOf(F, cs);
                if (F->hasAddressTaken() || cs.empty()) why = "the address is a formal of " + F->getName().str() + (F->hasAddressTaken() ? ", address-taken" : ", which has no caller");
                for (const CallBase *CB : cs)
                  if (XA->getArgNo() < CB->arg_size()) aw.push_back(CB->getArgOperand(XA->getArgNo()));
              } else if (const auto *XL = dyn_cast<LoadInst>(X); XL && transientSlot(XL->getPointerOperand()->stripPointerCasts())) {
                for (const User *U : XL->getPointerOperand()->stripPointerCasts()->users())
                  if (const auto *St = dyn_cast<StoreInst>(U)) aw.push_back(St->getValueOperand());
              } else if (isa<BitCastInst>(X) || isa<AddrSpaceCastInst>(X)) {
                aw.push_back(cast<Instruction>(X)->getOperand(0));
              } else if (const auto *XP = dyn_cast<PHINode>(X)) {
                for (const Value *In : XP->incoming_values()) aw.push_back(In);
              } else if (const auto *XI = dyn_cast<Instruction>(X); XI && isa<GetElementPtrInst>(XI)) {
                const std::string FK = fieldKey(XI, XI);
                if (FK.empty()) why = "the address is an unnamed step in " + loc(XI) + ": " + valueText(XI);
                else fks.insert(FK);
              } else {
                why = "the address is " + valueText(X);
              }
            }
            std::set<const Value *> vis;
            std::vector<const Value *> vals;
            std::set<std::string> unk;
            if (why.empty())
              for (const Value *Ob : objs) {
                storesThrough(Ob, vals, unk, vis);
                // A global's own initializer at the address read.
                if (const auto *GV = dyn_cast<GlobalVariable>(Ob); GV && GV->hasInitializer()) {
                  if (Constant *IC = ConstantFoldLoadFromConst(const_cast<Constant *>(GV->getInitializer()), L->getType(), APInt(64, 0),
                                                               GV->getParent()->getDataLayout()))
                    vals.push_back(IC);
                  else unk.insert("the initializer of @" + GV->getName().str() + " read in " + loc(L));
                }
              }
            const size_t elemsBefore = O.elements.size();
            if (why.empty())
              for (const std::string &FK : fks) {
                if (handle.count(FK) || links.count(FK) || (cursorOpen.count(FK) && cursorOpen[FK].empty())) {
                  O.elements.insert("a load of " + FK + " through its address in " + loc(L));
                  continue;
                }
                if (auto fu = fieldUnknown.find(FK); fu != fieldUnknown.end())
                  unk.insert("field " + FK + " not closed by name: " + fu->second.front());
                else if (const std::string un = unnamedSlotUnder(FK); !un.empty())
                  unk.insert("field " + FK + ": " + un);
                else if (const auto sit = storedAt.find(FK); sit != storedAt.end() && !sit->second.empty())
                  vals.insert(vals.end(), sit->second.begin(), sit->second.end());
                else unk.insert("field " + FK + ": no value stored by name");
              }
            if (why.empty() && unk.empty() && vals.empty() && O.elements.size() == elemsBefore)
              why = "no value stored through its addresses";
            if (!why.empty() || !unk.empty()) {
              O.unknown.insert("a load through a pointer in " + loc(L) + ": " + (why.empty() ? *unk.begin() : why));
              continue;
            }
            for (const Value *W : vals) work.push_back(W);
            continue;
          }
          if (const auto *CB = dyn_cast<CallBase>(I)) {
            const Function *G = CB->getCalledFunction();
            if (!G) {
              if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
                const std::string K = fieldKey(CL, CL->getPointerOperand());
                if (code.count(K) && !codeOpen.count(K)) {
                  O.elements.insert("a constructor's result through " + K + " in " + loc(CB));
                  continue;
                }
              }
              // (d) The callee's origins by name (a named field's stores and
              // initializers): every function it can hold, then their
              // returns; any other origin, unknown.
              const Origins OC = depth < 4 ? originsOf(CB->getCalledOperand(), depth + 1) : Origins();
              std::vector<const Function *> fns;
              bool closed = depth < 4 && OC.unknown.empty() && OC.elements.empty() && OC.pools.empty() &&
                            OC.objs.size() == OC.leaves.size() && !OC.objs.empty();
              for (const Value *Ob : OC.objs)
                if (const auto *Fn = dyn_cast<Function>(Ob); Fn && !Fn->isDeclaration()) fns.push_back(Fn);
                else closed = false;
              if (!closed) {
                O.unknown.insert("an indirect call in " + loc(CB) +
                                 (OC.unknown.empty() ? std::string() : " (its callee: " + *OC.unknown.begin() + ")"));
                continue;
              }
              for (const Function *Fn : fns)
                for (const Instruction &RI : instructions(*Fn))
                  if (const auto *Ret = dyn_cast<ReturnInst>(&RI); Ret && Ret->getReturnValue())
                    work.push_back(Ret->getReturnValue());
              O.leaves.insert("returns of " + std::to_string(fns.size()) + " functions the call in " + loc(CB) + " can reach by name");
              icallCount->insert(CB);
              continue;
            }
            if (ctorsHere.count(G)) {
              O.elements.insert("constructor " + G->getName().str() + "'s result in " + loc(CB));
              continue;
            }
            const bool alloc = isFresh(CB) || carveFns.count(G->getName().str());
            if (alloc && ctorsHere.count(CB->getFunction())) {
              O.elements.insert("a constructor's allocation " + G->getName().str() + " in " + loc(CB));
              continue;
            }
            if (carveFns.count(G->getName().str())) {
              // A carve row: the certified pools of its carves (its own, or
              // those of the functions it calls directly).
              std::set<std::string> ps;
              auto carvesIn = [&](const Function *H) {
                for (const Instruction &J : instructions(*H))
                  if (auto pit = poolCarvePool.find(&J); pit != poolCarvePool.end()) ps.insert(pit->second);
              };
              carvesIn(G);
              for (const Instruction &J : instructions(*G))
                if (const auto *CJ = dyn_cast<CallBase>(&J); CJ && CJ->getCalledFunction() && !CJ->getCalledFunction()->isDeclaration())
                  carvesIn(CJ->getCalledFunction());
              if (ps.empty()) O.unknown.insert("carve row " + G->getName().str() + " with no certified pool's carve, in " + loc(CB));
              for (const std::string &pn : ps) O.pools[pn].insert("carve row " + G->getName().str() + " in " + loc(CB));
              if (!ps.empty()) O.allocs.insert(CB);
              continue;
            }
            if (alloc) {
              O.leaves.insert("allocation " + G->getName().str() + " in " + loc(CB));
              O.allocs.insert(CB);
              continue;
            }
            if (const CR *R = rowOf(G); R && R->role != CR::Carve) {
              O.elements.insert("row " + G->getName().str() + "'s result in " + loc(CB));
              continue;
            }
            if (G->isDeclaration()) {
              // A summary's returned values (strrchr's ALIAS(ret<-arg0@X):
              // its argument's origins); a summary that loads the result, or
              // none: unknown.
              auto sit = Ctx->FuncSummaries.find(G);
              bool viaSummary = sit != Ctx->FuncSummaries.end() && sit->second && !sit->second->atoms.empty();
              std::vector<unsigned> from;
              if (viaSummary)
                for (const auto &At : sit->second->atoms) {
                  if (At.dst != -1) continue;
                  if (At.kind == GlobalContext::SummaryAtom::Alias && At.src >= 0 && (unsigned)At.src < CB->arg_size())
                    from.push_back(At.src);
                  else viaSummary = false;
                }
              if (!viaSummary || from.empty()) {
                O.unknown.insert("a call of " + G->getName().str() + " (no body" +
                                 (sit == Ctx->FuncSummaries.end() ? "" : ", its summary names no returned argument") +
                                 ") in " + loc(CB));
                continue;
              }
              for (unsigned a : from) work.push_back(CB->getArgOperand(a));
              continue;
            }
            for (const Instruction &RI : instructions(*G))
              if (const auto *Ret = dyn_cast<ReturnInst>(&RI); Ret && Ret->getReturnValue())
                work.push_back(Ret->getReturnValue());
            continue;
          }
          O.unknown.insert("an instruction in " + loc(I) + ": " + valueText(I));
        }
        return O;
      };
      // (A) The closed code field an indirect call loads its callee from
      // (O4's: every store into it a function constant), or "".
      auto codeFieldOf = [&](const CallBase *CB) -> std::string {
        const auto *Lc = dyn_cast<LoadInst>(castsOnly(CB->getCalledOperand()));
        const std::string CK = Lc ? fieldKey(Lc, Lc->getPointerOperand()) : "";
        auto tit = codeTargets.find(CK);
        if (CK.empty() || !code.count(CK) || codeOpen.count(CK) || tit == codeTargets.end() || tit->second.empty())
          return "";
        return CK;
      };
      // (R3, Fable 2026-10-20) A slot of a constant global's initializer
      // holding F at a key S+o is closed when (a) no write in a body lies
      // over S+o under S or any name embedding S there (a constant-zero
      // memset and a store of null excepted), and (r) every read of S+o by
      // name is an indirect call's callee: each load named S+o is only
      // called, compared, or kept in -O0 slots read only that way, and no
      // block copy reads it by name. The callers are then the indirect
      // calls those loads reach as callee (directly or through -O0 slots),
      // any base: (a) and the
      // global being an IR constant take the role of O4's closed code
      // field (no write changes the slot), and an open base costs
      // precision at the actuals only. "" when closed, else why not.
      struct R3Span { int64_t lo, hi; const Instruction *I; };
      std::map<std::string, std::vector<R3Span>> r3WritesAt, r3CopiesAt; // struct name -> spans
      std::map<std::string, std::vector<const LoadInst *>> r3LoadsAt;    // key -> its loads
      bool r3Indexed = false;
      std::map<std::string, std::string> r3SlotWhy;
      std::map<std::string, std::vector<const CallBase *>> r3CallsAt; // key -> the indirect calls its loads reach as callee
      auto r3Index = [&] {
        r3Indexed = true;
        for (auto &[M, _] : Ctx->Modules) {
          const DataLayout &MDL = M->getDataLayout();
          for (const Function &G : *M)
            for (const Instruction &I : instructions(G)) {
              const Value *Addr = nullptr;
              int64_t len = 0;
              bool none = false; // writes no function: null, or a constant-zero memset
              if (const auto *St = dyn_cast<StoreInst>(&I)) {
                Addr = St->getPointerOperand(), len = (int64_t)MDL.getTypeStoreSize(St->getValueOperand()->getType());
                none = isa<ConstantPointerNull>(St->getValueOperand()->stripPointerCasts());
              } else if (const auto *RMW = dyn_cast<AtomicRMWInst>(&I)) {
                Addr = RMW->getPointerOperand(), len = (int64_t)MDL.getTypeStoreSize(RMW->getValOperand()->getType());
              } else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(&I)) {
                Addr = CX->getPointerOperand(), len = (int64_t)MDL.getTypeStoreSize(CX->getNewValOperand()->getType());
              } else if (const auto *MI = dyn_cast<MemIntrinsic>(&I)) {
                Addr = MI->getRawDest();
                const auto *Len = dyn_cast<ConstantInt>(MI->getLength());
                len = Len ? (int64_t)Len->getZExtValue() : (int64_t)1 << 40;
                if (const auto *MS = dyn_cast<MemSetInst>(MI))
                  if (const auto *CV = dyn_cast<ConstantInt>(MS->getValue())) none = CV->isZero();
                if (const auto *MT = dyn_cast<MemTransferInst>(MI)) {
                  StructType *SS = nullptr;
                  int64_t soff = 0;
                  if (len > 0 && namedSlot(MT, MT->getRawSource(), MDL, pointees, SS, soff) && SS && SS->hasName())
                    structCover(SS, soff, soff + len, MDL, [&](StructType *ST, int64_t lo, int64_t hi) {
                      if (ST->hasName()) r3CopiesAt[stripStructNameSuffix(ST->getName()).str()].push_back({lo, hi, MT});
                    });
                }
              } else if (const auto *L = dyn_cast<LoadInst>(&I)) {
                if (const std::string K = fieldKey(L, L->getPointerOperand()); !K.empty())
                  for (const std::string &k : laneKeys(K, L->getType())) r3LoadsAt[k].push_back(L);
                continue;
              }
              StructType *WS = nullptr;
              int64_t woff = 0;
              if (!Addr || none || len <= 0 || (isa<StoreInst>(&I) && transientSlot(Addr->stripPointerCasts())) ||
                  !namedSlot(&I, Addr, MDL, pointees, WS, woff) || !WS || !WS->hasName())
                continue;
              structCover(WS, woff, woff + len, MDL, [&](StructType *ST, int64_t lo, int64_t hi) {
                if (ST->hasName()) r3WritesAt[stripStructNameSuffix(ST->getName()).str()].push_back({lo, hi, &I});
              });
            }
        }
      };
      auto r3Slot = [&](const std::string &k) -> const std::string & {
        if (auto it = r3SlotWhy.find(k); it != r3SlotWhy.end()) return it->second;
        if (!r3Indexed) r3Index();
        const size_t p = k.rfind('+');
        const std::string KS = k.substr(0, p);
        const int64_t KO = std::stoll(k.substr(p + 1));
        std::string why;
        // (a) a write in a body over the key, by its name or an embedding one.
        if (auto it = r3WritesAt.find(KS); it != r3WritesAt.end())
          for (const R3Span &w : it->second)
            if (w.lo < KO + 8 && KO < w.hi) {
              why = "a write in a body over it: " + snapLoc(w.I) + ": " + valueText(w.I);
              break;
            }
        // (r) a read by name other than an indirect call's callee.
        if (why.empty())
          if (auto it = r3CopiesAt.find(KS); it != r3CopiesAt.end())
            for (const R3Span &c : it->second)
              if (c.lo < KO + 8 && KO < c.hi) {
                why = "a block copy of it by name: " + snapLoc(c.I);
                break;
              }
        if (why.empty())
          if (auto it = r3LoadsAt.find(k); it != r3LoadsAt.end())
            for (const LoadInst *L : it->second) {
              std::vector<const Value *> w{L};
              std::set<const Value *> seen;
              while (!w.empty() && why.empty()) {
                const Value *X = w.back();
                w.pop_back();
                if (!seen.insert(X).second) continue;
                for (const User *XU : X->users()) {
                  if (const auto *CB = dyn_cast<CallBase>(XU); CB && castsOnly(CB->getCalledOperand()) == X &&
                                                               llvm::none_of(CB->args(), [&](const Use &A) { return A.get() == X; })) {
                    r3CallsAt[k].push_back(CB);
                    continue;
                  }
                  if (isa<ICmpInst>(XU)) continue;
                  if (isa<BitCastOperator>(XU) || isa<AddrSpaceCastOperator>(XU)) {
                    w.push_back(XU);
                    continue;
                  }
                  if (const auto *St = dyn_cast<StoreInst>(XU); St && St->getValueOperand() == X && transientSlot(castsOnly(St->getPointerOperand()))) {
                    for (const User *SU : castsOnly(St->getPointerOperand())->users())
                      if (isa<LoadInst>(SU)) w.push_back(SU);
                    continue;
                  }
                  why = "its load " + snapLoc(L) + " has another use: " +
                        (isa<Instruction>(XU) ? snapLoc(cast<Instruction>(XU)) + ": " : std::string()) + valueText(XU);
                  break;
                }
              }
              if (!why.empty()) break;
            }
        return r3SlotWhy[k] = why;
      };
      // (R3, D1) The read side's block copies: a copy whose source no name
      // reads may copy out of a vector global. Each source is walked once,
      // with every address-taken formal open. A copy whose source is
      // named reads that name's cells (the name premise). An unnamed
      // source whose known origins hold one of F's globals makes F open;
      // one whose origins are open rests on the byte-cell premise (plan
      // 3.53: a pointer copied as bytes would be a leak), each copy an
      // ASSUMPTION row of the rule report.
      bool r3Census = false;
      size_t r3NamedOpen = 0;
      std::vector<std::pair<const MemTransferInst *, std::set<const Value *>>> r3Unnamed; // unnamed sources, IR order
      std::vector<const MemTransferInst *> r3ByteRows;                                  // of them, the open ones
      auto r3Copies = [&](const std::set<const GlobalVariable *, GVByName> &Gs) -> std::string {
        if (!r3Census) {
          r3Census = true;
          const bool was = formalsOpen;
          formalsOpen = true;
          for (auto &[M, _] : Ctx->Modules)
            for (const Function &G : *M)
              for (const Instruction &I : instructions(G)) {
                const auto *MT = dyn_cast<MemTransferInst>(&I);
                if (!MT) continue;
                StructType *SS = nullptr;
                int64_t soff = 0;
                const bool named = namedSlot(MT, MT->getRawSource(), MT->getModule()->getDataLayout(), pointees, SS, soff) && SS &&
                                   SS->hasName();
                const Origins O = originsOf(MT->getRawSource(), 0);
                if (named) {
                  if (!O.unknown.empty()) r3NamedOpen++;
                  continue;
                }
                r3Unnamed.emplace_back(MT, O.objs);
                if (!O.unknown.empty()) r3ByteRows.push_back(MT);
              }
          formalsOpen = was;
        }
        for (const auto &[MT, objs] : r3Unnamed)
          for (const GlobalVariable *GV : Gs)
            if (objs.count(GV)) return "a byte copy from @" + GV->getName().str() + ": " + snapLoc(MT);
        return "";
      };
      fedCallers = [&](const Function *F) -> const Fed & {
        if (auto it = fedOf.find(F); it != fedOf.end()) return it->second;
        Fed R;
        std::set<std::string> ks;
        std::vector<std::string> chains;
        // V (F's address, or the init formal it arrives in) goes only into
        // closed code fields of F, or down a chain of init functions.
        std::set<const Argument *> onPath, done;
        std::function<bool(const Value *, const Function *, std::string)> feeds =
            [&](const Value *V, const Function *H, std::string chain) -> bool {
          const Value *X = V;
          if (H) {
            // An init formal: one use, a store into its -O0 slot loaded
            // once (or, without a slot, the use itself).
            if (!X->hasOneUse()) return R.why = "the formal of " + H->getName().str() + " has " +
                                                std::to_string(X->getNumUses()) + " uses", false;
            if (const auto *St = dyn_cast<StoreInst>(*X->user_begin());
                St && St->getValueOperand() == X && transientSlot(castsOnly(St->getPointerOperand()))) {
              const Value *SL = castsOnly(St->getPointerOperand());
              const LoadInst *L = nullptr;
              for (const User *U : SL->users()) {
                if (U == St) continue;
                const auto *LU = dyn_cast<LoadInst>(U);
                if (!LU || L) return R.why = "the slot of " + H->getName().str() + "'s formal has a second use", false;
                L = LU;
              }
              if (!L) return R.why = "the slot of " + H->getName().str() + "'s formal is never read", false;
              X = L;
            }
          }
          for (const User *U : X->users()) {
            if (const auto *CB = dyn_cast<CallBase>(U); CB && !H && CB->getCalledOperand() == X) continue;
            if (!H && isa<Constant>(U)) continue; // an initializer slot (R3, below)
            if (const auto *St = dyn_cast<StoreInst>(U); St && St->getValueOperand() == X) {
              const std::string K = fieldKey(St, St->getPointerOperand());
              auto tit = codeTargets.find(K);
              if (K.empty() || !code.count(K) || codeOpen.count(K) || tit == codeTargets.end() || !tit->second.count(F))
                return R.why = "a store of it not into a closed code field of it: " + snapLoc(St), false;
              ks.insert(K);
              chains.push_back(chain + (chain.empty() ? "" : " -> ") + "stored into " + K + " " + snapLoc(St));
              continue;
            }
            const auto *CB = dyn_cast<CallBase>(U);
            const Function *G = CB ? CB->getCalledFunction() : nullptr;
            if (!G || G->isDeclaration() || G->hasAddressTaken())
              return R.why = "passed to " + (G ? G->getName().str() + (G->isDeclaration() ? ", no body" : ", address-taken")
                                               : std::string("an indirect call")) +
                             (CB ? " " + snapLoc(CB) : std::string()),
                     false;
            for (unsigned a = 0; a < CB->arg_size(); a++) {
              if (CB->getArgOperand(a) != X) continue;
              const Argument *A = G->getArg(a);
              if (done.count(A)) continue;
              if (!onPath.insert(A).second) return R.why = "a cycle of init functions at " + G->getName().str(), false;
              if (!feeds(A, G, chain + (chain.empty() ? "" : " -> ") + G->getName().str())) return false;
              onPath.erase(A);
              done.insert(A);
            }
          }
          return true;
        };
        bool ok = F->hasAddressTaken();
        if (!ok) R.why = "not address-taken";
        // (R3) An address in a constant: the globals whose initializers
        // hold it; a constant used any other way is refused.
        std::set<const GlobalVariable *, GVByName> inits;
        for (const User *U : F->users()) {
          if (!ok || isa<Instruction>(U)) continue;
          std::vector<const User *> w{U};
          std::set<const User *> seen;
          while (ok && !w.empty()) {
            const User *X = w.back();
            w.pop_back();
            if (!seen.insert(X).second) continue;
            if (const auto *GV = dyn_cast<GlobalVariable>(X)) {
              inits.insert(GV);
              continue;
            }
            if (!isa<Constant>(X) || isa<GlobalValue>(X)) {
              R.why = "its address in a constant used " + (isa<Instruction>(X) ? "in a body: " + snapLoc(cast<Instruction>(X))
                                                                                   : "otherwise: " + valueText(X)),
              ok = false;
              break;
            }
            for (const User *XU : X->users()) w.push_back(XU);
          }
        }
        std::set<std::string> r3ks;
        for (const GlobalVariable *GV : inits) {
          if (!ok) break;
          if (!GV->isConstant()) {
            R.why = "writable global @" + GV->getName().str(), ok = false;
            break;
          }
          bool found = false;
          initSlots(*GV, GV->getParent()->getDataLayout(),
                    [&](const Constant *C, int64_t b, const std::set<std::string> &keys, bool, bool) {
                      if (!ok || C->stripPointerCasts() != F) return;
                      found = true;
                      const std::string at = "@" + GV->getName().str() + " +" + std::to_string(b);
                      if (keys.empty()) return (void)(R.why = "initializer slot unnamed at " + at, ok = false);
                      std::string kl;
                      for (const std::string &k : keys) {
                        if (const std::string &why = r3Slot(k); !why.empty())
                          return (void)(R.why = "initializer slot " + at + ": " + k + ": " + why, ok = false);
                        r3ks.insert(k);
                        kl += (kl.empty() ? "" : "/") + k;
                      }
                      chains.push_back("initializer slot " + at + " [" + kl + "]");
                    });
          if (ok && !found) R.why = "its address in @" + GV->getName().str() + " at no slot", ok = false;
        }
        if (ok && !inits.empty())
          if (const std::string why = r3Copies(inits); !why.empty()) R.why = why, ok = false;
        if (ok) ok = feeds(F, nullptr, "");
        if (ok && ks.empty() && r3ks.empty()) R.why = "its address feeds no code field and lies in no initializer", ok = false;
        if (ok) {
          for (const User *U : F->users())
            if (const auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand() == F) R.callers.push_back(CB);
          // Every indirect call, in IR order (the context's set of them is
          // not filled yet here; runOnFunction checks the two agree).
          for (auto &[M, _] : Ctx->Modules)
            for (const Function &G : *M)
              for (const Instruction &I : instructions(G))
                if (const auto *CB = dyn_cast<CallBase>(&I); CB && isIndirectCallSite(CB) && ks.count(codeFieldOf(CB)))
                  R.callers.push_back(CB);
          // R3: the indirect calls a slot key's loads reach as callee, directly
          // or through -O0 slots ((r) walked them), in IR order.
          std::set<const Instruction *, IROrder> r3Calls;
          for (const std::string &k : r3ks)
            for (const CallBase *CB : r3CallsAt[k])
              if (isIndirectCallSite(CB) && llvm::find(R.callers, CB) == R.callers.end()) r3Calls.insert(CB);
          for (const Instruction *CI : r3Calls) R.callers.push_back(cast<CallBase>(CI));
          std::string fs, cs;
          for (const std::string &c : chains) fs += (fs.empty() ? "" : "; ") + c;
          for (const CallBase *CB : R.callers)
            cs += (cs.empty() ? "" : ", ") + std::string(CB->getCalledFunction() ? "direct " : "indirect ") + snapLoc(CB);
          R.text = fs + "; callers: " + (cs.empty() ? std::string("none") : cs);
        }
        return fedOf[F] = R;
      };
      // Snapshot holders ((3''), Fable 2026-10-17/18): a fresh block whose
      // every use, by name, is a save of the owner's handle array at its
      // start, a save of the same owner's elements (each of the owner's
      // entsize) into a region begun by a runtime-offset step of the handle
      // save's length, a copy out, a null test or free holds only that
      // owner's handle and element content: a copy out of it into the
      // owner's handle array or into an element of the owner is a move
      // within one owner. The solver makes it two objects (the handle image
      // and one struct of the element type) when the entsize premise holds.
      {
        // One value by name: the same SSA value, or a load of one -O0
        // local whose stores are its entry-block zero initializer and one
        // more store dominating the block's allocation (every read made
        // while the block exists sees that store's value).
        auto oneValue = [&](const Value *V, const Instruction *A) -> const Value * {
          V = V->stripPointerCasts();
          const auto *L = dyn_cast<LoadInst>(V);
          const Value *SL = L ? L->getPointerOperand()->stripPointerCasts() : nullptr;
          if (!L || !transientSlot(SL)) return V;
          const StoreInst *only = nullptr;
          for (const User *U : SL->users())
            if (const auto *S = dyn_cast<StoreInst>(U)) {
              const auto *K = dyn_cast<ConstantInt>(S->getValueOperand());
              if (K && K->isZero() && S->getParent() == &S->getFunction()->getEntryBlock()) continue;
              if (only) return nullptr;
              only = S;
            }
          if (!only || only->getFunction() != A->getFunction()) return nullptr;
          DominatorTree DT(const_cast<Function &>(*A->getFunction()));
          return DT.dominates(only, A) ? SL : nullptr;
        };
        // An owner's handle array: a load of a handle field; its owner shape
        // (the struct the field is in) and the outermost struct its address
        // steps through from its base.
        auto handleLoad = [&](const Value *V, std::string &owner, std::string &outer) {
          const auto *L = dyn_cast<LoadInst>(V->stripPointerCasts());
          if (!L) return false;
          const std::string K = fieldKey(L, L->getPointerOperand());
          if (!handle.count(K)) return false;
          const std::string sh = ownerShape(L->getPointerOperand(), 0);
          if (sh.empty()) return false;
          const int64_t ko = std::stoll(K.substr(K.rfind('+') + 1));
          const size_t p = sh.find('+');
          const int64_t at = (p == std::string::npos ? 0 : std::stoll(sh.substr(p + 1))) - ko;
          const std::string root = p == std::string::npos ? sh : sh.substr(0, p);
          owner = at ? root + "+" + std::to_string(at) : root;
          outer = K.substr(0, K.rfind('+'));
          for (const Value *A = castsOnly(L->getPointerOperand()); const auto *G = dyn_cast<GEPOperator>(A);
               A = castsOnly(G->getPointerOperand()))
            if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()); ST && ST->hasName())
              outer = stripStructNameSuffix(ST->getName()).str();
          return true;
        };
        // The owner's entsize: a load (through integer casts) of an owner
        // struct's field; its key.
        auto sizeField = [&](const Value *V) -> std::string {
          while (const auto *C = dyn_cast<CastInst>(V)) V = C->getOperand(0);
          const auto *L = dyn_cast<LoadInst>(V);
          if (!L || !L->getType()->isIntegerTy()) return "";
          return fieldKey(L, L->getPointerOperand());
        };
        // An element of the owner by name: a read of a slot of its handle
        // array, or of a link or closed cursor field of such an element,
        // through casts, offset-0 steps, -O0 locals and joins; a cycle
        // (`p = p->next`) holds (the greatest fixpoint, as for cursors).
        std::set<const Value *> ownPath;
        std::function<bool(const Value *, const std::string &, int)> ownElem = [&](const Value *V, const std::string &own,
                                                                                    int d) -> bool {
          V = V->stripPointerCasts();
          if (isa<ConstantPointerNull>(V)) return true;
          if (d > 16) return false;
          if (!ownPath.insert(V).second) return true;
          bool ok = false;
          if (const auto *L = dyn_cast<LoadInst>(V)) {
            const Value *P = L->getPointerOperand()->stripPointerCasts();
            if (transientSlot(P)) {
              // The local's address is never taken: the nearest store to it
              // before the read, in its block or up the chain of unique
              // predecessors, is the only one that reaches it; else every
              // store to it.
              const StoreInst *last = nullptr;
              const BasicBlock *BB = L->getParent();
              const Instruction *I = L->getPrevNode();
              for (int hops = 0; !last && BB && hops < 64; hops++) {
                for (; I && !last; I = I->getPrevNode())
                  if (const auto *S = dyn_cast<StoreInst>(I); S && S->getPointerOperand()->stripPointerCasts() == P) last = S;
                BB = BB->getUniquePredecessor();
                I = BB ? &BB->back() : nullptr;
              }
              if (last) {
                ok = ownElem(last->getValueOperand(), own, d + 1);
              } else {
                for (const User *U : P->users())
                  if (const auto *S = dyn_cast<StoreInst>(U)) {
                    ok = ownElem(S->getValueOperand(), own, d + 1);
                    if (!ok) break;
                  }
              }
            } else if (const std::string K = fieldKey(L, L->getPointerOperand());
                       !K.empty() && !handle.count(K) && (links.count(K) || cursorClosed(L).empty())) {
              ok = ownElem(baseOf(L->getPointerOperand()), own, d + 1);
            } else if (const auto *G = dyn_cast<GEPOperator>(P); G && G->getNumIndices() == 1) {
              std::string o, x;
              ok = handleLoad(G->getPointerOperand(), o, x) && o == own;
            }
          } else if (isa<PHINode>(V) || isa<SelectInst>(V)) {
            const auto *I = cast<Instruction>(V);
            ok = true;
            for (unsigned k = isa<SelectInst>(I) ? 1 : 0; k < I->getNumOperands() && ok; k++)
              ok = ownElem(I->getOperand(k), own, d + 1);
          } else if (const auto *G = dyn_cast<GEPOperator>(V)) {
            APInt Off(64, 0);
            ok = G->accumulateConstantOffset(DL0, Off) && Off.isZero() && ownElem(G->getPointerOperand(), own, d + 1);
          }
          ownPath.erase(V);
          return ok;
        };
        std::set<const Instruction *, IROrder> cands; // rows and holders in IR order, not by pointer
        for (auto &[M, _] : Ctx->Modules)
          for (const Function &F : *M)
            for (const Instruction &I : instructions(F))
              if (const auto *MT = dyn_cast<MemTransferInst>(&I)) {
                std::string o, x;
                if (!handleLoad(MT->getRawSource(), o, x)) continue;
                if (const auto *A = dyn_cast_or_null<Instruction>(freshOf(MT->getRawDest(), 0)); A && isa<CallBase>(A))
                  cands.insert(A);
              }
        for (const Instruction *A : cands) {
          const std::string hname = snapLoc(A);
          std::map<const Value *, int> region; // 0: the handle region (the block's start), 1: the element region
          std::vector<std::pair<const Value *, int>> work{{A, 0}};
          std::string fail, owner, outer, entsizeKey;
          std::vector<const MemTransferInst *> hSaves, eSaves, hOuts, eOuts;
          std::vector<const Value *> starts, hLens; // region-start offsets, handle-copy lengths
          std::vector<const Value *> elemPtrs;
          std::map<const Value *, int> slots; // -O0 locals it occupies, by region
          std::vector<const Value *> slotOrder; // the same, in the order met (the walk's IR use order)
          std::vector<const Value *> joins; // phis and selects: every entry derived
          auto setFail = [&](const std::string &w) {
            if (fail.empty()) fail = w;
          };
          while (!work.empty() && fail.empty()) {
            auto [V, r] = work.back();
            work.pop_back();
            if (auto it = region.find(V); it != region.end()) {
              if (it->second != r) setFail("a value in both regions: " + valueText(V));
              continue;
            }
            region[V] = r;
            for (const User *U : V->users()) {
              const auto *UI = dyn_cast<Instruction>(U);
              if (!UI) {
                setFail("a constant use");
                break;
              }
              if (isa<DbgInfoIntrinsic>(UI) || UI->isLifetimeStartOrEnd() || isa<ICmpInst>(UI)) continue;
              if (isa<CastInst>(UI)) {
                work.push_back({UI, r});
              } else if (isa<PHINode>(UI) || isa<SelectInst>(UI)) {
                if (const auto *SI = dyn_cast<SelectInst>(UI); SI && SI->getCondition() == V) continue;
                joins.push_back(UI);
                work.push_back({UI, r});
              } else if (const auto *S = dyn_cast<StoreInst>(UI)) {
                const Value *SL = S->getPointerOperand()->stripPointerCasts();
                if (S->getValueOperand() != V || !transientSlot(SL)) {
                  setFail("a store " + (S->getValueOperand() == V ? std::string("of it into memory: ")
                                                                    : std::string("into it: ")) + siteOf(S));
                  break;
                }
                if (auto [sit, ins] = slots.emplace(SL, r); ins) slotOrder.push_back(SL);
                else if (sit->second != r) {
                  setFail("a local holding both regions: " + siteOf(S));
                  break;
                }
                for (const User *LU : SL->users())
                  if (isa<LoadInst>(LU)) work.push_back({LU, r});
              } else if (const auto *G = dyn_cast<GetElementPtrInst>(UI)) {
                if (G->getPointerOperand() != V) {
                  setFail("an index use: " + siteOf(G));
                  break;
                }
                APInt Off(64, 0);
                if (G->accumulateConstantOffset(DL0, Off)) {
                  if (!Off.isZero()) {
                    setFail("a constant step: " + siteOf(G));
                    break;
                  }
                  work.push_back({G, r});
                  continue;
                }
                const bool bytes = G->getNumIndices() == 1 && G->getSourceElementType()->isIntegerTy(8);
                const Value *Ix = G->getOperand(1);
                if (!bytes) {
                  setFail("a step not in bytes: " + siteOf(G));
                  break;
                }
                if (r == 0) {
                  starts.push_back(Ix); // the element region starts here
                } else if (!isa<ZExtInst>(Ix) && !(isa<ConstantInt>(Ix) && !cast<ConstantInt>(Ix)->isNegative())) {
                  setFail("a step that may be negative: " + siteOf(G));
                  break;
                }
                elemPtrs.push_back(G);
                work.push_back({G, 1});
              } else if (const auto *MT = dyn_cast<MemTransferInst>(UI)) {
                const bool into = MT->getArgOperand(0) == V;
                if (into && MT->getArgOperand(1) == V) {
                  setFail("a copy within it: " + siteOf(MT));
                  break;
                }
                if (r == 0) {
                  hLens.push_back(MT->getLength());
                  if (into) {
                    std::string o, x;
                    if (!handleLoad(MT->getRawSource(), o, x)) {
                      setFail("a copy into its start from no handle array: " + siteOf(MT));
                      break;
                    }
                    if (!owner.empty() && o != owner) {
                      setFail("handle saves of two owners: " + siteOf(MT));
                      break;
                    }
                    owner = o;
                    outer = x;
                    hSaves.push_back(MT);
                  } else {
                    hOuts.push_back(MT);
                  }
                } else {
                  const std::string E = sizeField(MT->getLength());
                  if (E.empty() || (!entsizeKey.empty() && E != entsizeKey)) {
                    setFail("an element copy whose length is no one owner field: " + siteOf(MT));
                    break;
                  }
                  entsizeKey = E;
                  (into ? eSaves : eOuts).push_back(MT);
                }
              } else if (const auto *CB = dyn_cast<CallBase>(UI)) {
                const Function *G = CB->getCalledFunction();
                if (!G || (G->getName() != "free" && G->getName() != "cfree")) {
                  setFail("passed to " + (G ? G->getName().str() : std::string("an indirect call")) + ": " + siteOf(CB));
                  break;
                }
              } else {
                setFail("a use: " + siteOf(UI));
                break;
              }
            }
          }
          // Every store into a slot it occupies, and every entry of a join,
          // null or derived in the same region.
          for (const Value *SL : slotOrder) {
            const int r = slots[SL];
            for (const User *U : SL->users())
              if (const auto *S = dyn_cast<StoreInst>(U); S && fail.empty()) {
                const Value *v = S->getValueOperand();
                if (isa<ConstantPointerNull>(v->stripPointerCasts())) continue;
                auto it = region.find(v);
                if (it == region.end() || it->second != r) setFail("a local also holding another value: " + siteOf(S));
              }
          }
          for (const Value *J : joins) {
            if (!fail.empty()) break;
            const auto *I = cast<Instruction>(J);
            for (unsigned k = isa<SelectInst>(I) ? 1 : 0; k < I->getNumOperands(); k++) {
              const Value *v = I->getOperand(k);
              if (isa<ConstantPointerNull>(v->stripPointerCasts())) continue;
              if (!region.count(v)) setFail("a join with another value: " + siteOf(I));
            }
          }
          if (fail.empty() && hSaves.empty()) setFail("no handle save");
          if (fail.empty() && eSaves.empty()) setFail("no element save");
          // The element region begins where the handle copies end (Fable
          // 2026-10-18): every start offset and every handle copy's length
          // one value by name.
          const Value *tab = nullptr;
          if (fail.empty()) {
            std::vector<const Value *> all(starts);
            all.insert(all.end(), hLens.begin(), hLens.end());
            for (const Value *v : all) {
              const Value *c = oneValue(v, A);
              if (!c || (tab && c != tab)) {
                setFail("an element region not begun at the handle copies' length: " + valueText(v));
                break;
              }
              tab = c;
            }
          }
          // The element saves: elements of the same owner, by name.
          if (fail.empty())
            for (const MemTransferInst *MT : eSaves)
              if (!ownElem(MT->getRawSource(), owner, 0)) {
                setFail("an element save from no element of the owner: " + siteOf(MT));
                break;
              }
          if (!fail.empty()) {
            o1AssumeLines.push_back("  snapshot holder candidate " + hname + ": no holder (" + fail + ")");
            continue;
          }
          // R2 (Fable 2026-10-20, (ii')): a restore gives back what a save
          // read when the two are paired: the restore's source base and the
          // save's destination base are one value, and so are their sizes;
          // one value is the same SSA value or loads of a -O0 slot whose
          // stores are exactly one, not counting a store of constant 0 into
          // a size slot (a copy of zero bytes writes nothing) or of null
          // into a base slot (null names no object). Path-insensitive. Any
          // other restore stays OPEN: "ranges not paired".
          std::set<const MemTransferInst *> pairedRestores;
          std::map<const MemTransferInst *, std::string> unpairedWhy;
          {
            auto slotName = [&](const Value *SL) {
              for (DbgDeclareInst *D : findDbgDeclares(const_cast<Value *>(SL)))
                return D->getVariable()->getName().str();
              return std::string("a -O0 local");
            };
            // The value V is, or null with the reason it is none.
            auto oneOf = [&](const Value *V, bool size, std::string &why) -> const Value * {
              V = castsOnly(V);
              while (const auto *C = dyn_cast<CastInst>(V)) V = castsOnly(C->getOperand(0));
              const auto *L = dyn_cast<LoadInst>(V);
              const Value *SL = L ? castsOnly(L->getPointerOperand()) : nullptr;
              if (!L || !transientSlot(SL)) return V;
              size_t n = 0;
              bool cursor = false;
              for (const User *U : SL->users())
                if (const auto *S = dyn_cast<StoreInst>(U)) {
                  const Value *SV = castsOnly(S->getValueOperand());
                  if (size ? isa<ConstantInt>(SV) && cast<ConstantInt>(SV)->isZero() : isa<ConstantPointerNull>(SV))
                    continue;
                  n++;
                  if (const auto *G = dyn_cast<GEPOperator>(SV))
                    if (const auto *GL = dyn_cast<LoadInst>(castsOnly(G->getPointerOperand()));
                        GL && castsOnly(GL->getPointerOperand()) == SL)
                      cursor = true;
                }
              if (n == 1) return SL;
              why = slotName(SL) + ": " + std::to_string(n) + " stores" + (cursor ? ", a cursor" : "");
              return nullptr;
            };
            auto pairOf = [&](const std::vector<const MemTransferInst *> &outs,
                              const std::vector<const MemTransferInst *> &saves) {
              for (const MemTransferInst *R : outs) {
                std::string why;
                for (const MemTransferInst *Sv : saves) {
                  std::string wb, ws, wb2, ws2;
                  const Value *rb = oneOf(R->getRawSource(), false, wb), *sb = oneOf(Sv->getRawDest(), false, wb2);
                  const Value *rs = oneOf(R->getLength(), true, ws), *ss = oneOf(Sv->getLength(), true, ws2);
                  if (rb && rb == sb && rs && rs == ss) {
                    pairedRestores.insert(R);
                    CG_LOG("Container: snapshot holder " << hname << ": restore " << snapLoc(R)
                                                         << ": paired with save " << snapLoc(Sv) << "\n");
                    why.clear();
                    break;
                  }
                  if (why.empty()) {
                    std::vector<std::string> ps;
                    if (!rb || !sb || rb != sb)
                      ps.push_back("base: " + (!wb.empty() ? wb : !wb2.empty() ? wb2 : std::string("two values")));
                    if (!rs || !ss || rs != ss)
                      ps.push_back("size: " + (!ws.empty() ? ws : !ws2.empty() ? ws2 : std::string("two values")));
                    for (const std::string &x : ps) why += (why.empty() ? "" : "; ") + x;
                    why += " (save " + snapLoc(Sv) + ")";
                  }
                }
                if (pairedRestores.count(R)) continue;
                unpairedWhy[R] = "ranges not paired (" + why + ")";
                CG_LOG("Container: snapshot holder " << hname << ": restore " << snapLoc(R) << ": " << unpairedWhy[R]
                                                     << "\n");
              }
            };
            pairOf(hOuts, hSaves);
            pairOf(eOuts, eSaves);
          }
          // The entsize premise: every store into the size field that can
          // reach this owner, walked back through formals to direct actuals
          // with the table pointer and the code field's value along, stores
          // sizeof(T), T the type its constructor allocates; one T.
          const size_t ep = entsizeKey.rfind('+');
          const std::string ES = entsizeKey.substr(0, ep);
          struct Path { std::vector<std::string> chain; const Value *tbl, *size, *nf; std::string open; int64_t off = 0; };
          std::vector<Path> paths;
          auto resolve = [&](const Value *V) {
            for (int k = 0; k < 8; k++) {
              V = castsOnly(V);
              if (const auto *C = dyn_cast<CastInst>(V); C && C->getOperand(0)->getType()->isIntegerTy()) {
                V = C->getOperand(0);
                continue;
              }
              const auto *L = dyn_cast<LoadInst>(V);
              const Value *SL = L ? castsOnly(L->getPointerOperand()) : nullptr;
              if (!L || !transientSlot(SL)) break;
              const StoreInst *only = nullptr;
              for (const User *U : SL->users())
                if (const auto *S = dyn_cast<StoreInst>(U)) {
                  if (only) return V;
                  only = S;
                }
              if (!only) break;
              V = only->getValueOperand();
            }
            return V;
          };
          std::function<void(Path, int)> walk = [&](Path P, int d) {
            P.tbl = resolve(P.tbl);
            if (P.size) P.size = resolve(P.size);
            if (P.nf) P.nf = resolve(P.nf);
            while (const auto *G = dyn_cast<GEPOperator>(P.tbl)) {
              if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()); ST && ST->hasName())
                P.chain.push_back(stripStructNameSuffix(ST->getName()).str());
              APInt Off(64, 0);
              if (P.off != INT64_MIN && G->accumulateConstantOffset(DL0, Off)) P.off += Off.getSExtValue();
              else P.off = INT64_MIN;
              P.tbl = resolve(G->getPointerOperand());
            }
            const Function *F = nullptr;
            for (const Value *v : {P.tbl, P.size, P.nf})
              if (const auto *Ar = dyn_cast_or_null<Argument>(v)) F = Ar->getParent();
            if (!F || d > 8) {
              if (d > 8) P.open = "too deep";
              paths.push_back(P);
              return;
            }
            std::vector<const CallBase *> cs;
            for (const User *U : F->users())
              if (const auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand() == F) cs.push_back(CB);
            if (F->hasAddressTaken() || cs.empty()) {
              P.open = "a formal of " + F->getName().str() + (F->hasAddressTaken() ? ", address-taken" : ", which has no caller");
              paths.push_back(P);
              return;
            }
            for (const CallBase *CB : cs) {
              Path Q = P;
              auto sub = [&](const Value *v) -> const Value * {
                const auto *Ar = dyn_cast_or_null<Argument>(v);
                return Ar && Ar->getParent() == F && Ar->getArgNo() < CB->arg_size() ? CB->getArgOperand(Ar->getArgNo()) : v;
              };
              Q.tbl = sub(P.tbl);
              Q.size = sub(P.size);
              Q.nf = sub(P.nf);
              walk(Q, d + 1);
            }
          };
          for (auto &[M, _] : Ctx->Modules)
            for (const Function &F : *M)
              for (const Instruction &I : instructions(F))
                if (const auto *S = dyn_cast<StoreInst>(&I); S && fieldKey(S, S->getPointerOperand()) == entsizeKey) {
                  // The table: the size field's base; the newfunc: the code
                  // field stored on the same base in the same function.
                  const auto *G = dyn_cast<GEPOperator>(castsOnly(S->getPointerOperand()));
                  const Value *tbl = G ? castsOnly(G->getPointerOperand()) : nullptr;
                  const Value *nf = nullptr;
                  for (const Instruction &J : instructions(F))
                    if (const auto *S2 = dyn_cast<StoreInst>(&J); S2 && code.count(fieldKey(S2, S2->getPointerOperand())))
                      if (const auto *G2 = dyn_cast<GEPOperator>(castsOnly(S2->getPointerOperand()));
                          G2 && tbl && resolve(G2->getPointerOperand()) == resolve(tbl))
                        nf = S2->getValueOperand();
                  Path P{{}, tbl ? tbl : S->getPointerOperand(), S->getValueOperand(), nf, tbl ? "" : "a size store at no field step"};
                  // The size field's offset from the table (the object
                  // identity below names the field's own address).
                  if (APInt Off(64, 0); G && G->accumulateConstantOffset(DL0, Off)) P.off = Off.getSExtValue();
                  else P.off = INT64_MIN;
                  if (!P.open.empty()) paths.push_back(P);
                  else walk(P, 0);
                }
          // Object identity by name (Fable 2026-10-19, (a)): the objects
          // an address can be, as (allocation site, offset): through
          // casts, -O0 locals (every store), constant steps, joins, formals
          // to direct actuals, a defined callee's returns (an allocator
          // wrapper, every return a noalias extern call or null at +0, is
          // its call site), a load of a named field (every store of that
          // key in the program). Anything else is open, by its reason.
          using Obj = std::pair<std::string, int64_t>;
          // A global initializer is a write too: each of its non-null pointer
          // slots is named by every struct around it, the IR's named structs
          // and the global's debug type (a union initializer makes the IR
          // type literal); a slot no type names opens every field load.
          std::map<std::string, std::vector<const Constant *>> initVals;
          std::vector<std::string> initUnnamed;
          // Every non-zero initializer slot of any type, by the structs
          // around it: (struct, offset in it, bytes, global); for a word's
          // initial value ((b)).
          struct InitSlot { std::string S; int64_t off, len; std::string gv; };
          std::vector<InitSlot> initNonZero;
          bool initDone = false;
          // Every named write's bytes, for a field's cover check: a store
          // (its value's store size) or a memory intrinsic (its length; a
          // runtime length to the end of the struct) at its named slot.
          struct NamedWrite { StructType *S; int64_t off, len; const Instruction *I; };
          std::vector<NamedWrite> namedWrites;
          // Every write with no named slot (R1, Fable 2026-10-19), in IR
          // order: decided by its destination's origins (originsOf), as
          // writing any byte of each origin object.
          struct UnnamedWrite { const Instruction *I; const Value *dest; };
          std::vector<UnnamedWrite> unnamedWrites;
          std::map<const Instruction *, Origins> unnamedOrigins;
          std::map<std::string, std::string> unnamedDone; // K (+"#W" for check (2)) -> its reason
          std::vector<std::string> coverLog;
          // Each unnamed-destination write that is a reason, once, with the
          // keys it is one for (listed in IR order).
          struct CoverReason { const Instruction *I; std::string why; std::vector<std::string> keys; };
          std::vector<CoverReason> coverReasons;
          std::map<std::string, size_t> coverReasonAt;
          std::set<const CallBase *> coverIcalls; // indirect call sites the covers' origin walks follow through closed code fields
          bool writesDone = false;
          std::set<std::string> keysWalked, keysCovered; // for the log
          std::set<std::string> nullWrites; // constant-zero memsets over a walked field: null, no object (listed)
          // Why a field's bytes may hold what its own named stores do not:
          // a write named otherwise over them (a store named at an outer
          // struct or at another offset, a store of another width, a block
          // copy, a memset), or "".
          auto KO_of = [](const std::string &K) { return (int64_t)std::stoll(K.substr(K.rfind('+') + 1)); };
          // R2 (Fable 2026-10-20, (i)): a block copy over K whose source is
          // read under a name that puts the same key K at the same place in
          // the copy brings K's own values: a cycle, nothing added. It rests
          // on the name premise (the writes named otherwise over K are
          // counted by name program-wide), so the source object needs no
          // condition of its own. Every overlap of K must be whole.
          std::set<const MemTransferInst *> kToKCopies; // for the log
          auto kToK = [&](const MemTransferInst *MT, StructType *WS, int64_t woff, int64_t len, const std::string &KS,
                          int64_t KO, int64_t size) {
            const DataLayout &MDL = MT->getModule()->getDataLayout();
            StructType *SS = nullptr;
            int64_t soff = 0;
            if (len <= 0 || len >= ((int64_t)1 << 40) || !namedSlot(MT, MT->getRawSource(), MDL, pointees, SS, soff) ||
                !SS || !SS->hasName())
              return false;
            // Does K (KS's byte KO) begin at byte x of T?
            auto keyAt = [&](Type *T, int64_t x) {
              for (int d = 0; d < 64 && x >= 0; d++) {
                if (auto *ST = dyn_cast<StructType>(T)) {
                  if (ST->isOpaque()) return false;
                  if (ST->hasName() && stripStructNameSuffix(ST->getName()) == KS && x == KO)
                    return true;
                  const StructLayout *SL = MDL.getStructLayout(ST);
                  if (x >= (int64_t)SL->getSizeInBytes()) return false;
                  const unsigned i = SL->getElementContainingOffset((uint64_t)x);
                  x -= (int64_t)SL->getElementOffset(i);
                  T = ST->getElementType(i);
                } else if (auto *AT = dyn_cast<ArrayType>(T)) {
                  const int64_t es = (int64_t)MDL.getTypeAllocSize(AT->getElementType());
                  if (es <= 0 || x >= es * (int64_t)AT->getNumElements()) return false;
                  x %= es;
                  T = AT->getElementType();
                } else {
                  return false;
                }
              }
              return false;
            };
            bool any = false;
            for (int64_t p = 1 - size; p < len; p++) {
              if (!keyAt(WS, woff + p)) continue;
              if (p < 0 || p + size > len || !keyAt(SS, soff + p)) return false;
              any = true;
            }
            return any;
          };
          auto coverOpen = [&](const std::string &K, int64_t size) -> std::string {
            if (!writesDone) {
              writesDone = true;
              for (auto &[M, _] : Ctx->Modules) {
                const DataLayout &MDL = M->getDataLayout();
                for (const Function &F : *M)
                  for (const Instruction &I : instructions(F)) {
                    const Value *Addr = nullptr;
                    int64_t len = 0;
                    if (const auto *St = dyn_cast<StoreInst>(&I))
                      Addr = St->getPointerOperand(), len = (int64_t)MDL.getTypeStoreSize(St->getValueOperand()->getType());
                    else if (const auto *RMW = dyn_cast<AtomicRMWInst>(&I))
                      Addr = RMW->getPointerOperand(), len = (int64_t)MDL.getTypeStoreSize(RMW->getValOperand()->getType());
                    else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(&I))
                      Addr = CX->getPointerOperand(), len = (int64_t)MDL.getTypeStoreSize(CX->getNewValOperand()->getType());
                    else if (const auto *MI = dyn_cast<MemIntrinsic>(&I)) {
                      Addr = MI->getRawDest();
                      const auto *Len = dyn_cast<ConstantInt>(MI->getLength());
                      len = Len ? (int64_t)Len->getZExtValue() : (int64_t)1 << 40;
                    }
                    StructType *WS = nullptr;
                    int64_t woff = 0;
                    // A store into a -O0 slot names no field (it names the
                    // local itself).
                    if (!Addr || (isa<StoreInst>(&I) && transientSlot(Addr->stripPointerCasts()))) continue;
                    const bool named = namedSlot(&I, Addr, MDL, pointees, WS, woff) && WS && WS->hasName();
                    if (len <= 0) continue;
                    if (!named) {
                      unnamedWrites.push_back({&I, Addr});
                      continue;
                    }
                    namedWrites.push_back({WS, woff, len, &I});
                  }
              }
            }
            const size_t p = K.rfind('+');
            const std::string KS = K.substr(0, p);
            const int64_t KO = std::stoll(K.substr(p + 1));
            std::string why;
            size_t n = 0;
            for (const NamedWrite &W : namedWrites) {
              const bool own = isa<StoreInst>(W.I) && W.len == size && W.off == KO &&
                               stripStructNameSuffix(W.S->getName()) == KS;
              if (own) continue;
              const auto *MS = dyn_cast<MemSetInst>(W.I);
              const bool zero = MS && isa<ConstantInt>(MS->getValue()) && cast<ConstantInt>(MS->getValue())->isZero();
              bool hits = false;
              structCover(W.S, W.off, W.off + W.len, W.I->getModule()->getDataLayout(),
                          [&](StructType *ST, int64_t lo, int64_t hi) {
                            hits |= ST->hasName() && stripStructNameSuffix(ST->getName()) == KS && lo < KO + size && KO < hi;
                          });
              if (!hits) continue;
              std::string tail;
              if (const auto *MT = dyn_cast<MemTransferInst>(W.I)) {
                // A paired restore gives back what its save read under the
                // same name: a cycle.
                if (pairedRestores.count(MT)) continue;
                if (auto u = unpairedWhy.find(MT); u != unpairedWhy.end()) tail = ": " + u->second;
                else if (kToK(MT, W.S, W.off, W.len, KS, KO, size)) {
                  kToKCopies.insert(MT);
                  continue;
                }
              }
              // Zero bytes are null, and null names no object (Fable
              // 2026-10-19): listed, not open.
              if (zero) {
                nullWrites.insert("a memset 0 named " + stripStructNameSuffix(W.S->getName()).str() + "+" +
                                  std::to_string(W.off) + " (" + std::to_string(W.len) + " bytes) over " + K + " " +
                                  snapLoc(W.I));
                continue;
              }
              if (!n++)
                why = std::string(isa<MemSetInst>(W.I)        ? "a memset"
                                  : isa<MemTransferInst>(W.I) ? "a block copy"
                                  : isa<StoreInst>(W.I)       ? "a store"
                                                              : "an atomic write") +
                      " named " + stripStructNameSuffix(W.S->getName()).str() + "+" + std::to_string(W.off) + " (" +
                      (W.len >= ((int64_t)1 << 40) ? std::string("a runtime length") : std::to_string(W.len) + " bytes") +
                      ") over " + K + " " + snapLoc(W.I) + tail;
            }
            return n ? std::to_string(n) + " writes named otherwise over " + K + ", e.g. " + why : std::string();
          };
          // Does a struct named Inner lie anywhere in one named Outer (the
          // embedding table, by name in module M)?
          auto structByName = [](const Module *M, StringRef N) -> StructType * {
            for (StructType *ST : M->getIdentifiedStructTypes())
              if (ST->hasName() && stripStructNameSuffix(ST->getName()) == N && !ST->isOpaque()) return ST;
            return nullptr;
          };
          auto holdsAny = [&](StructType *Outer, StringRef Inner, const Module *M) {
            StructType *IT = structByName(M, Inner);
            const StructInfo *OI = Outer ? Ctx->structAnalyzer.getStructInfo(Outer, const_cast<Module *>(M)) : nullptr;
            const StructInfo *II = IT ? Ctx->structAnalyzer.getStructInfo(IT, const_cast<Module *>(M)) : nullptr;
            return OI && II && II->getContainers().count(OI->getRealType());
          };
          // R1 (Fable 2026-10-19): the writes with no named slot over field
          // K, by their destinations' origins. An open origin, or an
          // allocation with no declared type (walk covers), is OPEN; a
          // local or global whose declared type holds K's struct, or an
          // element of a struct that is, embeds or is embedded with it,
          // reaches K. For check (2) (W: the word's objects, a closed set)
          // an allocation, local or global reaches only if it is in W.
          // Constant-zero memsets write null. One reason per key.
          // The container's element struct that is, embeds or is embedded
          // with KS (anywhere, transitively), or "".
          auto elemRel = [&](const std::string &KS, const Module *M) -> std::string {
            for (const std::string &E : elemStructs) {
              StructType *ET = structByName(M, StringRef(E).drop_front(7));
              StructType *KT = structByName(M, StringRef(KS).drop_front(7));
              bool rel = E == KS || (KT && holdsAny(KT, StringRef(E).drop_front(7), M)) ||
                         (ET && holdsAny(ET, StringRef(KS).drop_front(7), M));
              if (!rel && ET)
                if (const StructInfo *EI = Ctx->structAnalyzer.getStructInfo(ET, const_cast<Module *>(M)))
                  for (const auto &[CT, offs] : EI->getContainers())
                    if (auto *CST = const_cast<StructType *>(CT);
                        CST && ((CST->hasName() && stripStructNameSuffix(CST->getName()) == KS) ||
                                holdsAny(CST, StringRef(KS).drop_front(7), M))) {
                      rel = true;
                      break;
                    }
              if (rel) return E;
            }
            return "";
          };
          auto unnamedOpen = [&](const std::string &K, const std::set<const Value *> *W) -> std::string {
            const std::string ck = K + (W ? "#W" : "");
            if (auto d = unnamedDone.find(ck); d != unnamedDone.end()) return d->second;
            const std::string KS = K.substr(0, K.rfind('+'));
            size_t nClose = 0, nReach = 0, nOpen = 0, nNull = 0;
            std::vector<std::string> reasons;
            for (const UnnamedWrite &U : unnamedWrites) {
              if (const auto *MS = dyn_cast<MemSetInst>(U.I);
                  MS && isa<ConstantInt>(MS->getValue()) && cast<ConstantInt>(MS->getValue())->isZero()) {
                nNull++;
                continue;
              }
              // A paired restore gives back what its save read (R2): close.
              if (const auto *MT = dyn_cast<MemTransferInst>(U.I); MT && pairedRestores.count(MT)) {
                nClose++;
                continue;
              }
              auto it = unnamedOrigins.find(U.I);
              if (it == unnamedOrigins.end()) {
                std::set<const CallBase *> *const own = icallCount;
                icallCount = &coverIcalls;
                Origins O = originsOf(U.dest, 0);
                icallCount = own;
                it = unnamedOrigins.emplace(U.I, std::move(O)).first;
              }
              const Origins &O = it->second;
              const Module *M = U.I->getModule();
              std::string why;
              bool open = false;
              if (!O.unknown.empty()) {
                why = "its origins are open (" + *O.unknown.begin() + ")", open = true;
              } else {
                for (const Value *Al : O.allocs) {
                  if (W) {
                    if (W->count(Al)) {
                      why = "its destination may be the word's object at " + snapLoc(cast<Instruction>(Al));
                      break;
                    }
                    continue;
                  }
                  // This holder's block H carries exactly its saves' sources:
                  // the handle array's pointers and the owner's elements (the
                  // recognition above checked every use of H).
                  if (Al == A) {
                    if (const std::string E = elemRel(KS, M); !E.empty()) {
                      why = "its destination may be the snapshot holder's block " + snapLoc(A) + " (element bytes of " + E +
                            ", which is, embeds or is embedded with " + KS + ")";
                      break;
                    }
                    continue;
                  }
                  const auto *CB = dyn_cast<CallBase>(Al);
                  const std::string an = CB && CB->getCalledFunction() ? CB->getCalledFunction()->getName().str()
                                                                         : std::string("a pool carve");
                  why = "origins include an untyped allocation (" + an + " at " + snapLoc(cast<Instruction>(Al)) +
                        "), not typed",
                  open = true;
                  break;
                }
                // In a fixed order (globals by name, then locals in IR order),
                // so the reason names the same object on every run.
                std::vector<const Value *> objs(O.objs.begin(), O.objs.end());
                std::stable_sort(objs.begin(), objs.end(), [](const Value *x, const Value *y) {
                  const auto *ix = dyn_cast<Instruction>(x), *iy = dyn_cast<Instruction>(y);
                  if (!ix || !iy) return !ix && (iy || x->getName() < y->getName());
                  return irOrderLess(ix, iy);
                });
                for (const Value *Ob : objs) {
                  if (!why.empty()) break;
                  if (W) {
                    if (W->count(Ob)) why = "its destination may be the word's object " + Ob->getName().str();
                    continue;
                  }
                  Type *T = nullptr;
                  if (const auto *AI = dyn_cast<AllocaInst>(Ob)) T = AI->getAllocatedType();
                  else if (const auto *GV = dyn_cast<GlobalVariable>(Ob)) T = GV->getValueType();
                  if (!T || !T->isSized()) continue;
                  const DataLayout &ODL = isa<Instruction>(Ob) ? cast<Instruction>(Ob)->getModule()->getDataLayout()
                                                                : cast<GlobalValue>(Ob)->getParent()->getDataLayout();
                  bool holds = false;
                  structCover(T, 0, (int64_t)ODL.getTypeAllocSize(T), ODL, [&](StructType *ST, int64_t, int64_t) {
                    holds |= ST->hasName() && stripStructNameSuffix(ST->getName()) == KS;
                  });
                  if (holds)
                    why = std::string("its destination may be ") + (isa<AllocaInst>(Ob) ? "a local" : "global") + " " +
                          (isa<AllocaInst>(Ob) ? snapLoc(cast<Instruction>(Ob)) : Ob->getName().str()) +
                          ", whose declared type holds " + KS;
                }
                if (why.empty() && !O.elements.empty())
                  if (const std::string E = elemRel(KS, M); !E.empty())
                    why = "its destination may be an element (" + *O.elements.begin() + ") of " + E +
                          ", which is, embeds or is embedded with " + KS;
              }
              if (why.empty()) {
                nClose++;
                continue;
              }
              (open ? nOpen : nReach)++;
              reasons.push_back("an unnamed-destination write over " + K + ": " + why + " " + snapLoc(U.I));
              const std::string rk = snapLoc(U.I) + ": " + why;
              auto [rit, fresh] = coverReasonAt.try_emplace(rk, coverReasons.size());
              if (fresh) coverReasons.push_back({U.I, why, {}});
              coverReasons[rit->second].keys.push_back(K + (W ? " (check (2))" : ""));
            }
            coverLog.push_back("cover " + K + (W ? " (check (2), against the word's objects)" : "") + ": " +
                               std::to_string(nClose + nReach + nOpen) + " unnamed-destination writes: " +
                               std::to_string(nClose) + " close, " + std::to_string(nReach) + " reach, " +
                               std::to_string(nOpen) + " open (" + std::to_string(nNull) + " constant-zero memsets, null)");
            std::string res;
            if (!reasons.empty())
              res = reasons.front() + (reasons.size() > 1 ? " (and " + std::to_string(reasons.size() - 1) + " more)" : "");
            return unnamedDone[ck] = res;
          };
          auto buildInit = [&]() {
            if (initDone) return;
            initDone = true;
            for (auto &[M, _] : Ctx->Modules) {
              const DataLayout &MDL = M->getDataLayout();
              for (const GlobalVariable &GV : M->globals())
                initSlots(GV, MDL, [&](const Constant *C, int64_t b, const std::set<std::string> &keys, bool hasDI, bool) {
                  if (!C->getType()->isPointerTy()) {
                    // A non-zero scalar or data slot: named like a pointer slot.
                    const int64_t len = (int64_t)MDL.getTypeStoreSize(C->getType());
                    for (const std::string &k : keys) {
                      const size_t q = k.rfind('+');
                      initNonZero.push_back({k.substr(0, q), std::stoll(k.substr(q + 1)), len, GV.getName().str()});
                    }
                    return;
                  }
                  // A global with a debug type names its slots: one in no
                  // struct (a scalar or an array of pointers) is no field.
                  if (keys.empty() && !hasDI) initUnnamed.push_back("@" + GV.getName().str() + " +" + std::to_string(b));
                  for (const std::string &k : keys) initVals[k].push_back(C);
                });
            }
          };
          // For the guard word's log: cycle cuts, fields whose every store
          // was cut, union reads walked by key, stores they excluded.
          size_t cycleCuts = 0;
          std::set<std::string> cutEmpty, keysUnionWalked, unionExcluded;
          // Object identity is a least fixpoint over nodes (a value, a field
          // read under its keys, a handle array's elements): a node's objects
          // are the union of its successors', each shifted by its step's
          // offset. The walk is depth-first with Tarjan's SCCs: a node met
          // again while its SCC is under way adds nothing there (a cycle cut;
          // its objects arrive at the SCC's root), and every member of a
          // finished SCC has the root's objects, shifted by its offset from
          // the root. A cycle whose steps do not sum to offset 0 is OPEN.
          // Only a finished SCC's results are kept, each relative to its
          // node; a result under a budget cut is not kept. Past the node
          // budget, a node not yet walked is OPEN by name.
          using ORes = std::pair<std::set<Obj>, std::set<std::string>>;
          std::map<std::string, ORes> nodeMemo;
          std::map<std::string, std::pair<size_t, int64_t>> onStack; // (index, offset) of a node whose SCC is under way
          std::vector<std::string> nodeStack;
          std::vector<size_t *> lowStack;
          const size_t nodeBudget = 200000;
          size_t nodeCount = 0, budgetCuts = 0, offCycles = 0;
          double walkSecs = 0; // the walks' own time, from each top-level node
          auto visit = [&](const std::string &key, const std::function<std::string()> &name, int64_t off,
                           std::set<Obj> &out, std::set<std::string> &open,
                           const std::function<void(int64_t, std::set<Obj> &, std::set<std::string> &)> &body) {
            if (auto it = nodeMemo.find(key); it != nodeMemo.end()) {
              for (const Obj &x : it->second.first) out.insert({x.first, x.second + off});
              open.insert(it->second.second.begin(), it->second.second.end());
              return;
            }
            if (auto it = onStack.find(key); it != onStack.end()) {
              if (it->second.second != off)
                offCycles++, open.insert("a cycle through " + name() + " stepping the offset by " +
                                         std::to_string(off - it->second.second));
              else
                cycleCuts++;
              if (!lowStack.empty()) *lowStack.back() = std::min(*lowStack.back(), it->second.first);
              return;
            }
            if (nodeCount >= nodeBudget) return (void)(budgetCuts++, open.insert("budget exhausted at " + name()));
            const bool top = lowStack.empty();
            const auto t0 = std::chrono::steady_clock::now();
            const size_t idx = nodeCount++;
            size_t low = idx;
            onStack[key] = {idx, off};
            nodeStack.push_back(key);
            lowStack.push_back(&low);
            const size_t b0 = budgetCuts;
            ORes r;
            body(off, r.first, r.second);
            lowStack.pop_back();
            if (!lowStack.empty()) *lowStack.back() = std::min(*lowStack.back(), low);
            if (low == idx)
              for (bool more = true; more;) {
                const std::string m = nodeStack.back();
                nodeStack.pop_back();
                const int64_t mo = onStack[m].second;
                onStack.erase(m);
                more = m != key;
                if (budgetCuts != b0) continue;
                ORes &mr = nodeMemo[m];
                for (const Obj &x : r.first) mr.first.insert({x.first, x.second - mo});
                mr.second = r.second;
              }
            out.insert(r.first.begin(), r.first.end());
            open.insert(r.second.begin(), r.second.end());
            if (top) walkSecs += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
          };
          std::function<void(const Value *, int64_t, std::set<Obj> &, std::set<std::string> &)> objsOf;
          std::map<std::string, const Value *> objSite; // an object's name -> its allocation (call, alloca, global)
          // An object made by a certified pool's carves (Carves.cc): its pools.
          std::map<std::string, std::set<std::string>> objPools;
          // An allocator wrapper: every return a noalias extern call, a
          // certified pool's carve (its own allocation site, Carves.cc), a
          // wrapper's call, or null; a recursive call adds what the other
          // returns give (the least fixpoint). A refused pool's carve is no
          // allocation.
          std::set<std::string> wrapPools;
          std::set<const Function *> wrapStack;
          std::function<bool(const Function *, int)> isWrapper = [&](const Function *F, int d) {
            if (d > 3 || F->isDeclaration()) return false;
            if (!wrapStack.insert(F).second) return true;
            struct Pop { std::set<const Function *> &s; const Function *f; ~Pop() { s.erase(f); } } pop{wrapStack, F};
            bool any = false;
            for (const Instruction &I : instructions(*F))
              if (const auto *R = dyn_cast<ReturnInst>(&I); R && R->getReturnValue()) {
                std::vector<const Value *> vs{R->getReturnValue()};
                std::set<const Value *> seen;
                while (!vs.empty()) {
                  const Value *V = castsOnly(vs.back());
                  vs.pop_back();
                  if (!seen.insert(V).second || isa<ConstantPointerNull>(V)) continue;
                  if (const auto *L = dyn_cast<LoadInst>(V); L && transientSlot(castsOnly(L->getPointerOperand()))) {
                    for (const User *U : castsOnly(L->getPointerOperand())->users())
                      if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == castsOnly(L->getPointerOperand()))
                        vs.push_back(St->getValueOperand());
                    continue;
                  }
                  if (const auto *PN = dyn_cast<PHINode>(V)) {
                    for (const Value *In : PN->incoming_values()) vs.push_back(In);
                    continue;
                  }
                  if (const auto *CI = dyn_cast<Instruction>(V)) {
                    if (auto pit = poolCarvePool.find(CI); pit != poolCarvePool.end()) {
                      wrapPools.insert(pit->second);
                      any = true;
                      continue;
                    }
                    if (poolRefusedCarvePool.count(CI)) return false;
                  }
                  const auto *CB = dyn_cast<CallBase>(V);
                  const Function *G = CB ? CB->getCalledFunction() : nullptr;
                  if (!G || !(G->isDeclaration() ? G->hasRetAttribute(Attribute::NoAlias) : isWrapper(G, d + 1))) return false;
                  any |= !wrapStack.count(G);
                }
              }
            return any;
          };
          std::set<std::string> codeCallsWalked;
          // (A) A handle field's array (Fable 2026-10-19): the handle field K
          // whose array V is, by name: a load of K, or a value stored into K
          // (a new table before `table->table = newtable`), through -O0
          // slots; "" otherwise.
          std::function<std::string(const Value *, int)> arrayOf = [&](const Value *V, int d) -> std::string {
            V = castsOnly(V);
            if (d > 4 || !isa<Instruction>(V)) return ""; // null, a global, a formal: no array by name
            if (const auto *L = dyn_cast<LoadInst>(V)) {
              const Value *SL = castsOnly(L->getPointerOperand());
              if (transientSlot(SL)) {
                std::string k;
                for (const User *U : SL->users())
                  if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == SL) {
                    if (isa<ConstantPointerNull>(castsOnly(St->getValueOperand()))) continue;
                    const std::string a = arrayOf(St->getValueOperand(), d + 1);
                    if (a.empty() || (!k.empty() && a != k)) return "";
                    k = a;
                  }
                return k;
              }
              if (const std::string K = fieldKey(L, L->getPointerOperand()); handle.count(K)) return K;
            }
            // A value stored into K, through -O0 slots (a statement
            // expression's temporary, then the local).
            std::vector<std::pair<const Value *, int>> w{{V, 0}};
            while (!w.empty()) {
              auto [X, h] = w.back();
              w.pop_back();
              for (const User *U : X->users()) {
                if (isa<CastInst>(U)) {
                  w.push_back({U, h});
                  continue;
                }
                const auto *St = dyn_cast<StoreInst>(U);
                if (!St || St->getValueOperand() != X) continue;
                const Value *SP = castsOnly(St->getPointerOperand());
                if (const std::string K = fieldKey(St, St->getPointerOperand()); handle.count(K)) return K;
                if (transientSlot(SP) && h < 4)
                  for (const User *LU : SP->users())
                    if (isa<LoadInst>(LU)) w.push_back({LU, h + 1});
              }
            }
            return "";
          };
          // The slots an address can be: a named field "K", or an element of
          // handle field K's array "K[]" (one index over pointers, any value),
          // through -O0 slots holding addresses; false when one is neither.
          std::function<bool(const Instruction *, const Value *, std::set<std::string> &, int)> slotsOf =
              [&](const Instruction *I, const Value *P, std::set<std::string> &ks, int d) -> bool {
            P = castsOnly(P);
            if (d > 4) return false;
            if (const auto *L = dyn_cast<LoadInst>(P); L && transientSlot(castsOnly(L->getPointerOperand()))) {
              bool any = false;
              for (const User *U : castsOnly(L->getPointerOperand())->users())
                if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == castsOnly(L->getPointerOperand())) {
                  if (isa<ConstantPointerNull>(castsOnly(St->getValueOperand()))) continue;
                  if (!slotsOf(I, St->getValueOperand(), ks, d + 1)) return false;
                  any = true;
                }
              return any;
            }
            if (const auto *G = dyn_cast<GEPOperator>(P); G && G->getNumIndices() == 1 && G->getSourceElementType()->isPointerTy())
              if (const std::string K = arrayOf(G->getPointerOperand(), 0); !K.empty()) return ks.insert(K + "[]"), true;
            if (const std::string K = arrayOf(P, 0); !K.empty()) return ks.insert(K + "[]"), true;
            if (isa<AllocaInst>(P)) return false;
            if (const std::string K = fieldKey(I, P); !K.empty()) return ks.insert(K), true;
            return false;
          };
          // Handle field K's array: what flows out of an element is what
          // flows in, by name: every store into an element, a memset 0 null;
          // a block copy into it, or the array passing where elements are
          // written unseen (a call, a store elsewhere), is OPEN.
          std::set<std::string> elemWalked;
          std::function<void(const std::string &, int64_t, std::set<Obj> &, std::set<std::string> &)> walkElems =
              [&](const std::string &K, int64_t off, std::set<Obj> &out, std::set<std::string> &open) {
            const std::string MK = K + "[]";
            visit("f" + MK, [&] { return MK; }, off, out, open,
                  [&](int64_t off, std::set<Obj> &out, std::set<std::string> &open) {
              elemWalked.insert(K);
              for (auto &[M, _] : Ctx->Modules)
                for (const Function &F : *M)
                  for (const Instruction &I : instructions(F)) {
                    std::set<std::string> ks;
                    if (const auto *St = dyn_cast<StoreInst>(&I)) {
                      if (transientSlot(castsOnly(St->getPointerOperand())) || !slotsOf(St, St->getPointerOperand(), ks, 0) ||
                          !ks.count(MK))
                        continue;
                      if (St->getValueOperand()->getType()->isPointerTy())
                        objsOf(St->getValueOperand(), off, out, open);
                      else
                        open.insert("a store of a non-pointer value into " + K + "'s array " + snapLoc(St));
                    } else if (const auto *MI = dyn_cast<MemIntrinsic>(&I)) {
                      if (!slotsOf(MI, MI->getRawDest(), ks, 0) || !ks.count(MK)) continue;
                      const auto *MS = dyn_cast<MemSetInst>(MI);
                      if (MS && isa<ConstantInt>(MS->getValue()) && cast<ConstantInt>(MS->getValue())->isZero()) continue;
                      if (const auto *MT = dyn_cast<MemTransferInst>(MI); MT && pairedRestores.count(MT)) continue;
                      const auto *MT = dyn_cast<MemTransferInst>(MI);
                      auto u = MT ? unpairedWhy.find(MT) : unpairedWhy.end();
                      open.insert("a block copy into " + K + "'s array " + snapLoc(MI) +
                                  (u != unpairedWhy.end() ? ": " + u->second : std::string()));
                    } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
                      for (const Value *A : CB->args())
                        if (A->getType()->isPointerTy() && !arrayOf(A, 0).empty() && arrayOf(A, 0) == K)
                          open.insert(K + "'s array passed to " +
                                      (CB->getCalledFunction() ? CB->getCalledFunction()->getName().str()
                                                               : std::string("an indirect call")) +
                                      " " + snapLoc(CB));
                    }
                  }
            });
          };
          // A field read: the objects of every store of K (and K's covering
          // writes and initializers), kept per (K, the read's keys).
          std::function<void(const std::string &, const LoadInst *, int64_t, std::set<Obj> &, std::set<std::string> &)>
              walkField = [&](const std::string &K, const LoadInst *L, int64_t off, std::set<Obj> &out,
                              std::set<std::string> &open) {
            // A union read keyed by the census or a tag pair (keysOf: what
            // the solver files it under) reads only the stores its keys
            // admit: a store keyed by another key is another member's; an
            // unkeyed store (the slot's catch-all) is admitted.
            const std::vector<std::string> *rk = keysOf(L);
            std::string MK = K, rkCatch;
            if (rk) {
              for (const std::string &k : *rk) MK += "\t" + k;
              rkCatch = rk->front().substr(0, rk->front().rfind('#')) + "#?";
            }
            auto admits = [&](const StoreInst *St) {
              const std::vector<std::string> *sk = rk ? keysOf(St) : nullptr;
              if (!sk) return true;
              for (const std::string &k : *sk)
                if (k == rkCatch || std::find(rk->begin(), rk->end(), k) != rk->end()) return true;
              return false;
            };
            // A cycle through K adds nothing (the least fixpoint: what the
            // other stores give), and is counted apart: a field whose every
            // store is cut so is empty, not open for want of a store.
            visit("f" + MK, [&] { return K; }, off, out, open,
                  [&](int64_t off, std::set<Obj> &out, std::set<std::string> &open) {
              const size_t cuts0 = cycleCuts;
              for (auto &[M, _] : Ctx->Modules)
                for (const Function &F : *M)
                  for (const Instruction &I : instructions(F))
                    if (const auto *St = dyn_cast<StoreInst>(&I); St && fieldKey(St, St->getPointerOperand()) == K) {
                      if (!admits(St)) {
                        unionExcluded.insert(snapLoc(St));
                        continue;
                      }
                      if (St->getValueOperand()->getType()->isPointerTy())
                        objsOf(St->getValueOperand(), off, out, open);
                      else
                        open.insert("a store of a non-pointer value into " + K + " " + snapLoc(St));
                    }
              if (rk) keysUnionWalked.insert(K);
              keysWalked.insert(K);
              if (std::string c = coverOpen(K, (int64_t)L->getModule()->getDataLayout().getTypeStoreSize(L->getType()));
                  !c.empty())
                open.insert(c), keysCovered.insert(K);
              if (std::string u = unnamedOpen(K, nullptr); !u.empty()) open.insert(u), keysCovered.insert(K);
              buildInit();
              if (auto iv = initVals.find(K); iv != initVals.end())
                for (const Constant *C : iv->second) objsOf(C, off, out, open);
              if (!initUnnamed.empty())
                open.insert(std::to_string(initUnnamed.size()) + " initializer pointers no type names (" +
                            initUnnamed.front() + ")");
              if (out.empty() && open.empty()) {
                if (cycleCuts > cuts0) cutEmpty.insert(MK);
                else open.insert("no pointer store of " + K);
              }
            });
          };
          objsOf = [&](const Value *V, int64_t off, std::set<Obj> &out, std::set<std::string> &open) {
            V = castsOnly(V);
            if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return;
            visit("v" + std::to_string((uintptr_t)V), [&] { return valueText(V); }, off, out, open,
                  [&](int64_t off, std::set<Obj> &out, std::set<std::string> &open) {
              if (const auto *CI = dyn_cast<Instruction>(V)) {
                if (auto pit = poolCarvePool.find(CI); pit != poolCarvePool.end()) {
                  const std::string on = "a carve of pool " + pit->second + " at " + snapLoc(CI);
                  objSite.emplace(on, CI);
                  objPools[on].insert(pit->second);
                  return (void)out.insert({on, off});
                }
                if (auto rit = poolRefusedCarvePool.find(CI); rit != poolRefusedCarvePool.end())
                  return (void)open.insert("a carve of pool " + rit->second + " at " + snapLoc(CI) + " (" +
                                           poolVerdicts[rit->second] + ")");
              }
              if (const auto *G = dyn_cast<GEPOperator>(V)) {
                APInt Off(64, 0);
                if (!G->accumulateConstantOffset(DL0, Off)) return (void)open.insert("a runtime step " + valueText(V));
                return objsOf(G->getPointerOperand(), off + Off.getSExtValue(), out, open);
              }
              if (const auto *PN = dyn_cast<PHINode>(V)) {
                for (const Value *In : PN->incoming_values()) objsOf(In, off, out, open);
                return;
              }
              if (const auto *SI = dyn_cast<SelectInst>(V)) {
                objsOf(SI->getTrueValue(), off, out, open);
                objsOf(SI->getFalseValue(), off, out, open);
                return;
              }
              if (const auto *L = dyn_cast<LoadInst>(V)) {
                const Value *SL = castsOnly(L->getPointerOperand());
                if (transientSlot(SL)) {
                  for (const User *U : SL->users())
                    if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == SL)
                      objsOf(St->getValueOperand(), off, out, open);
                  return;
                }
                const std::string K = fieldKey(L, L->getPointerOperand());
                if (!K.empty()) return walkField(K, L, off, out, open);
                // A load through an address no field names: each address it
                // can be (through -O0 slots) is a named field or an element of
                // a handle field's array (an array index at run time).
                std::set<std::string> ks;
                if (!slotsOf(L, L->getPointerOperand(), ks, 0))
                  return (void)open.insert("a load of no named field " + valueText(V));
                for (const std::string &k : ks)
                  if (k.back() == ']') walkElems(k.substr(0, k.size() - 2), off, out, open);
                  else walkField(k, L, off, out, open);
                return;
              }
              if (const auto *Ar = dyn_cast<Argument>(V)) {
                const Function *F = Ar->getParent();
                bool any = false;
                if (F->hasAddressTaken()) {
                  const Fed &fd = fedCallers(F);
                  if (fd.text.empty()) return (void)open.insert("a formal of " + F->getName().str() + ", address-taken: " + fd.why);
                  for (const CallBase *CB : fd.callers)
                    if (Ar->getArgNo() < CB->arg_size()) any = true, objsOf(CB->getArgOperand(Ar->getArgNo()), off, out, open);
                } else
                  for (const User *U : F->users())
                    if (const auto *CB = dyn_cast<CallBase>(U); CB && CB->getCalledOperand() == F && Ar->getArgNo() < CB->arg_size())
                      any = true, objsOf(CB->getArgOperand(Ar->getArgNo()), off, out, open);
                if (!any) open.insert("a formal of " + F->getName().str() + ", which has no caller");
                return;
              }
              if (const auto *CB = dyn_cast<CallBase>(V)) {
                // (A) An indirect call through a closed code field returns
                // what its targets return.
                std::vector<const Function *> Gs;
                if (const Function *G = CB->getCalledFunction()) Gs.push_back(G);
                else {
                  const std::string CK = codeFieldOf(CB);
                  if (CK.empty()) return (void)open.insert("an indirect call's result " + snapLoc(CB));
                  codeCallsWalked.insert(CK);
                  Gs.assign(codeTargets[CK].begin(), codeTargets[CK].end());
                }
                for (const Function *G : Gs) {
                  wrapPools.clear();
                  if (G->isDeclaration() ? G->hasRetAttribute(Attribute::NoAlias) : isWrapper(G, 0)) {
                    const std::string on = G->getName().str() + " at " + snapLoc(CB);
                    objSite.emplace(on, CB);
                    if (!wrapPools.empty()) objPools[on].insert(wrapPools.begin(), wrapPools.end());
                    out.insert({on, off});
                    continue;
                  }
                  if (G->isDeclaration()) {
                    open.insert("an extern call's result " + snapLoc(CB));
                    continue;
                  }
                  for (const Instruction &I : instructions(*G))
                    if (const auto *R = dyn_cast<ReturnInst>(&I); R && R->getReturnValue())
                      objsOf(R->getReturnValue(), off, out, open);
                }
                return;
              }
              if (isa<AllocaInst>(V) || isa<GlobalValue>(V)) {
                const std::string on = isa<GlobalValue>(V) ? "@" + V->getName().str() : "local " + valueText(V);
                objSite.emplace(on, V);
                return (void)out.insert({on, off});
              }
              open.insert("a value no rule follows " + valueText(V));
            });
          };
          auto objText = [](const std::set<Obj> &o, const std::set<std::string> &op) {
            std::string t;
            for (const Obj &x : o) t += (t.empty() ? "" : "; ") + x.first + " +" + std::to_string(x.second);
            for (const std::string &x : op) t += (t.empty() ? "" : "; ") + std::string("OPEN ") + x;
            return t.empty() ? std::string("none") : t;
          };
          // The holder end: the entsize field the element copies' length reads.
          std::set<Obj> hObjs;
          std::set<std::string> hOpen;
          {
            const Value *Ln = eSaves.empty() ? nullptr : eSaves.front()->getLength();
            while (Ln && isa<CastInst>(Ln)) Ln = cast<CastInst>(Ln)->getOperand(0);
            if (const auto *L = dyn_cast_or_null<LoadInst>(Ln)) objsOf(L->getPointerOperand(), 0, hObjs, hOpen);
            else hOpen.insert("an element copy length read from no load");
          }
          // A path is relevant unless object identity by name refutes it: its
          // size store's field and the holder's are both closed (no OPEN
          // reason) and share no object. A GEP's struct is a declared type
          // (C casts it away), so the table's struct steps decide nothing;
          // the chain is printed, not used (Fable 2026-10-18).
          StructType *T = nullptr;
          std::string premiseOpen;
          std::map<std::string, StructType *> elemTs; // element type by name, over the relevant paths
          std::vector<std::string> pathLines, refutedLines;
          size_t relevant = 0;
          for (const Path &P : paths) {
            std::string chain;
            for (auto it = P.chain.rbegin(); it != P.chain.rend(); ++it) chain += (chain.empty() ? "" : ".") + *it;
            const auto *K = dyn_cast_or_null<ConstantInt>(P.size);
            const auto *NF = dyn_cast_or_null<Function>(P.nf ? P.nf->stripPointerCasts() : nullptr);
            std::string line = "table " + (chain.empty() ? std::string("(no struct step)") : chain) + ", entsize " +
                               (K ? std::to_string(K->getZExtValue()) : P.size ? valueText(P.size) : std::string("?")) +
                               ", newfunc " + (NF ? NF->getName().str() : P.nf ? valueText(P.nf) : std::string("?"));
            std::set<Obj> po;
            std::set<std::string> pOpen;
            if (P.off != INT64_MIN) objsOf(P.tbl, P.off, po, pOpen);
            else pOpen.insert("a runtime step on the table's chain");
            bool meets = false;
            for (const Obj &x : po) meets |= hObjs.count(x) > 0;
            line += ", entsize field at " + objText(po, pOpen);
            if (hOpen.empty() && pOpen.empty() && !meets) {
              refutedLines.push_back(line);
              continue;
            }
            relevant++;
            std::string why = P.open;
            StructType *PT = nullptr;
            if (why.empty() && !K) why = "entsize not constant";
            if (why.empty() && !NF) why = "newfunc not a function";
            if (why.empty()) {
              // The constructor's element: a fresh block of constant size it
              // makes itself (not through another constructor of the body).
              for (const Instruction &I : instructions(*NF)) {
                uint64_t sz = 0;
                if (const auto *CB = dyn_cast<CallBase>(&I)) {
                  if (!CB->getType()->isPointerTy() || !(get(CB) & FRS)) continue;
                  if (const Function *Gf = CB->getCalledFunction(); Gf && body.count(Gf)) continue;
                  unsigned consts = 0;
                  uint64_t prod = 1;
                  for (const Value *Arg : CB->args())
                    if (const auto *C = dyn_cast<ConstantInt>(Arg); C && C->getBitWidth() >= 32) prod *= C->getZExtValue(), consts++;
                  if (consts == 0 || consts > 2) continue;
                  sz = prod;
                } else {
                  continue;
                }
                if (StructType *ST = structOfSize(&I, sz, NF)) {
                  if (PT && PT != ST) why = "two element structs in " + NF->getName().str();
                  PT = ST;
                }
              }
              if (why.empty() && !PT) why = "no element struct of " + NF->getName().str();
              if (why.empty() && (uint64_t)DL0.getTypeAllocSize(PT) != K->getZExtValue())
                why = "entsize " + std::to_string(K->getZExtValue()) + " is not sizeof " + PT->getName().str() + " (" +
                      std::to_string(DL0.getTypeAllocSize(PT)) + ")";
            }
            // The element type is the set over the relevant paths (Fable
            // 2026-10-19), not the first path's: each path names its own.
            if (why.empty()) elemTs[PT->getName().str()] = PT;
            else if (premiseOpen.empty()) premiseOpen = line + ": " + why;
            pathLines.push_back(line + (why.empty() ? ": T = " + PT->getName().str() + " (sizeof)" : ": OPEN " + why));
          }
          if (premiseOpen.empty() && elemTs.size() > 1) {
            std::string ts;
            for (const auto &[n, _] : elemTs) ts += (ts.empty() ? "" : ", ") + n;
            premiseOpen = "element types {" + ts + "} over the relevant paths, more than one";
          }
          T = premiseOpen.empty() && elemTs.size() == 1 ? elemTs.begin()->second : nullptr;
          if (paths.empty()) premiseOpen = "no store of " + entsizeKey;
          else if (!relevant) premiseOpen = "every init path refuted by object identity";
          auto locs = [&](const std::vector<const MemTransferInst *> &v) {
            std::string s;
            for (const MemTransferInst *MT : v) s += (s.empty() ? "" : ", ") + snapLoc(MT);
            return s.empty() ? std::string("none") : s;
          };
          std::vector<const MemTransferInst *> outs(hOuts);
          outs.insert(outs.end(), eOuts.begin(), eOuts.end());
          std::string prem;
          for (const std::string &p : pathLines) prem += " [" + p + "]";
          prem += "; holder's entsize field at " + objText(hObjs, hOpen) + "; " + std::to_string(refutedLines.size()) +
                  " paths refuted by object identity (closed, no object of the holder's)";
          for (const std::string &p : refutedLines) prem += " [REFUTED " + p + "]";
          prem += "; " + std::to_string(nullWrites.size()) + " null writes over a walked field (constant-zero memsets, no object)";
          for (const std::string &w : nullWrites) prem += " [" + w + "]";
          {
            std::string ks;
            for (const std::string &k : keysCovered) ks += (ks.empty() ? "" : ", ") + k;
            CG_LOG("Container: snapshot holder " << hname << ": object identity walked " << keysWalked.size()
                   << " field keys, " << keysCovered.size() << " open by writes named otherwise" << (ks.empty() ? "" : ": ")
                   << ks << "\n");
          }
          o1AssumeLines.push_back("  snapshot holder of " + outer + " (the table its handle saves read): H " + hname +
                                  "; handle save " + locs(hSaves) + "; element saves " + locs(eSaves) +
                                  " (each " + entsizeKey + " bytes); restores " + locs(outs) + "; premise " +
                                  (premiseOpen.empty() ? "PROVEN, element struct " + T->getName().str() + ":"
                                                       : "OPEN-UNPROVEN (" + premiseOpen + "):") +
                                  prem);
          // Unreachable by name (Fable 2026-10-19, (b); the known bits of
          // plan 3.51(3), for a guard): the nearest conditional branch above
          // H's allocation whose edge into it requires a nonzero mask of a
          // named word W (icmp eq/ne 0 of and-by-constant, lshr-by-constant,
          // zext and trunc ending at W's load). H never runs when every object
          // of W is zero at allocation and every write of W keeps the mask
          // from the same word or clears it: no write names W otherwise, and
          // no initializer is non-zero over it. The graph is not pruned.
          {
            const Function *HF = A->getFunction();
            DominatorTree GDT(const_cast<Function &>(*HF));
            const DataLayout &HDL = HF->getParent()->getDataLayout();
            // The nearest guard above I (of the word named wantK, if given):
            // (branch, its edge, W's load, mask).
            struct Guard { const BranchInst *BR = nullptr; int edge = -1; const LoadInst *W = nullptr; APInt mask; };
            auto guardOf = [&](const Instruction *I, const std::string &wantK) {
              Guard g;
              for (const DomTreeNode *N = GDT.getNode(I->getParent())->getIDom(); N && !g.W; N = N->getIDom()) {
                const auto *BR = dyn_cast<BranchInst>(N->getBlock()->getTerminator());
                if (!BR || !BR->isConditional()) continue;
                int edge = -1;
                for (int k = 0; k < 2; k++)
                  if (GDT.dominates(BasicBlockEdge(N->getBlock(), BR->getSuccessor(k)), I->getParent())) edge = k;
                const auto *IC = dyn_cast<ICmpInst>(BR->getCondition());
                const auto *Z = IC ? dyn_cast<ConstantInt>(IC->getOperand(1)) : nullptr;
                if (edge < 0 || !IC || !IC->isEquality() || !Z || !Z->isZero() || !IC->getOperand(0)->getType()->isIntegerTy())
                  continue;
                if ((IC->getPredicate() == ICmpInst::ICMP_NE) != (edge == 0)) continue; // the edge requires no bit set
                const Value *X = IC->getOperand(0);
                APInt m = APInt::getAllOnes(X->getType()->getIntegerBitWidth());
                for (int k = 0; k < 16; k++) {
                  if (const auto *L = dyn_cast<LoadInst>(X)) {
                    if (L->getType()->isIntegerTy() && !m.isZero() &&
                        (wantK.empty() || fieldKey(L, L->getPointerOperand()) == wantK))
                      g.W = L, g.mask = m, g.BR = BR, g.edge = edge;
                    break;
                  }
                  const auto *BO = dyn_cast<BinaryOperator>(X);
                  const auto *C = BO ? dyn_cast<ConstantInt>(BO->getOperand(1)) : nullptr;
                  if (const auto *ZX = dyn_cast<ZExtInst>(X)) m = m.trunc(ZX->getSrcTy()->getIntegerBitWidth()), X = ZX->getOperand(0);
                  else if (const auto *T = dyn_cast<TruncInst>(X)) m = m.zext(T->getSrcTy()->getIntegerBitWidth()), X = T->getOperand(0);
                  else if (C && BO->getOpcode() == Instruction::And) m &= C->getValue(), X = BO->getOperand(0);
                  else if (C && BO->getOpcode() == Instruction::LShr && C->getValue().ult(m.getBitWidth()))
                    m = m.shl(C->getZExtValue()), X = BO->getOperand(0);
                  else break; // another shape: no guard
                }
              }
              return g;
            };
            const Guard G0 = guardOf(A, "");
            const BranchInst *GBR = G0.BR;
            const LoadInst *W = G0.W;
            const APInt mask = G0.mask;
            if (W) {
              std::string decline;
              const std::string K = fieldKey(W, W->getPointerOperand());
              const int64_t wlen = (int64_t)HDL.getTypeStoreSize(W->getType());
              if (K.empty()) decline = "the guard's word is named by no field";
              // Every save and restore of H under a guard of its own (Fable:
              // "every use ... dominated by a test"): of the same word, its
              // mask within W's, so the one proof covers it.
              std::set<std::string> guardLocs{snapLoc(GBR)};
              for (const auto *v : {&hSaves, &eSaves, &hOuts, &eOuts})
                for (const MemTransferInst *MT : *v) {
                  if (!decline.empty()) break;
                  const Guard g = MT->getFunction() == HF ? guardOf(MT, K) : Guard();
                  if (!g.W || fieldKey(g.W, g.W->getPointerOperand()) != K || g.mask.getBitWidth() != mask.getBitWidth() ||
                      !g.mask.isSubsetOf(mask))
                    decline = "a copy of the holder under no guard of the word: " + snapLoc(MT);
                  else
                    guardLocs.insert(snapLoc(g.BR));
                }
              // (1) Every object of W is zero at allocation: calloc, or a
              // function every non-null result of which is memset to 0 over
              // its allocation's size on every path to its return.
              std::function<void(const Value *, std::set<const Value *> &, std::set<const Value *> &)> defsOf =
                  [&](const Value *V, std::set<const Value *> &out, std::set<const Value *> &seen) {
                    V = castsOnly(V);
                    if (isa<ConstantPointerNull>(V) || !seen.insert(V).second) return;
                    if (const auto *L = dyn_cast<LoadInst>(V); L && transientSlot(castsOnly(L->getPointerOperand()))) {
                      const Value *SL = castsOnly(L->getPointerOperand());
                      for (const User *U : SL->users())
                        if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == SL)
                          defsOf(St->getValueOperand(), out, seen);
                      return;
                    }
                    if (const auto *PN = dyn_cast<PHINode>(V)) {
                      for (const Value *In : PN->incoming_values()) defsOf(In, out, seen);
                      return;
                    }
                    out.insert(V);
                  };
              auto onlyDef = [&](const Value *V, const Value *X) {
                std::set<const Value *> d, seen;
                defsOf(V, d, seen);
                return d.size() == 1 && *d.begin() == X;
              };
              auto zeroing = [&](const Function *G) {
                std::set<const Value *> defs, seen;
                for (const Instruction &I : instructions(*G))
                  if (const auto *R = dyn_cast<ReturnInst>(&I); R && R->getReturnValue()) defsOf(R->getReturnValue(), defs, seen);
                if (defs.empty()) return false;
                for (const Value *X : defs) {
                  const auto *XC = dyn_cast<CallBase>(X);
                  if (!XC) return false;
                  std::set<const Value *> sizes;
                  for (const Value *Arg : XC->args())
                    if (Arg->getType()->isIntegerTy()) sizes.insert(resolve(Arg));
                  std::set<const Instruction *> zs;
                  for (const Instruction &I : instructions(*G))
                    if (const auto *MS = dyn_cast<MemSetInst>(&I))
                      if (const auto *V0 = dyn_cast<ConstantInt>(MS->getValue());
                          V0 && V0->isZero() && onlyDef(MS->getRawDest(), X) && sizes.count(resolve(MS->getLength())))
                        zs.insert(MS);
                  if (zs.empty()) return false;
                  // Every path from X to a return passes a memset of X or X's null edge.
                  std::vector<const BasicBlock *> work;
                  std::set<const BasicBlock *> seenB;
                  bool done = false;
                  for (const Instruction *I = XC->getNextNode(); I && !done; I = I->getNextNode()) done = zs.count(I);
                  if (!done) work.push_back(XC->getParent());
                  bool first = true;
                  while (!work.empty()) {
                    const BasicBlock *B = work.back();
                    work.pop_back();
                    if (!first) {
                      if (!seenB.insert(B).second) continue;
                      bool z = false;
                      for (const Instruction &I : *B) z |= zs.count(&I) > 0;
                      if (z) continue;
                    }
                    first = false;
                    const Instruction *T = B->getTerminator();
                    if (isa<ReturnInst>(T)) return false;
                    int skip = -1;
                    if (const auto *BR = dyn_cast<BranchInst>(T); BR && BR->isConditional())
                      if (const auto *IC = dyn_cast<ICmpInst>(BR->getCondition()); IC && IC->isEquality() &&
                                                                                 isa<ConstantPointerNull>(IC->getOperand(1)) &&
                                                                                 onlyDef(IC->getOperand(0), X))
                        skip = IC->getPredicate() == ICmpInst::ICMP_EQ ? 0 : 1;
                    for (unsigned k = 0; k < T->getNumSuccessors(); k++)
                      if ((int)k != skip) work.push_back(T->getSuccessor(k));
                  }
                }
                return true;
              };
              // r1: an object's size, from its allocation: a global's or a
              // local's type; malloc's argument, calloc's product; for a
              // zeroing wrapper, the argument its memset 0 covers (the size
              // the program clears is the size it asked for). An argument
              // is a constant, or a formal of a function never address-taken
              // resolved to its direct callers' constant actuals (the
              // largest). An access past every size it can have is in no such
              // object: dropped, listed with the size's source.
              std::function<bool(const Value *, std::set<uint64_t> &, bool &, int)> constsOf =
                  [&](const Value *V, std::set<uint64_t> &cs, bool &viaFormal, int d) -> bool {
                if (d > 4) return false;
                V = resolve(V);
                if (const auto *C = dyn_cast<ConstantInt>(V)) return cs.insert(C->getZExtValue()), true;
                const auto *A = dyn_cast<Argument>(V);
                if (!A || A->getParent()->hasAddressTaken()) return false;
                viaFormal = true;
                bool any = false;
                for (const User *U : A->getParent()->users()) {
                  const auto *CB = dyn_cast<CallBase>(U);
                  if (!CB || CB->getCalledOperand() != A->getParent() || A->getArgNo() >= CB->arg_size() ||
                      !constsOf(CB->getArgOperand(A->getArgNo()), cs, viaFormal, d + 1))
                    return false;
                  any = true;
                }
                return any;
              };
              // s1 (Fable 2026-10-19): a certified pool's carve is as long as
              // its length, and its length must be the size formal rounded up
              // to the pool's alignment A, (x + A-1) & -A (through -O0 slots
              // and integer casts), or a constant; else the object is unsized
              // and kept.
              struct Ext {
                bool ok = true, none = true;
                uint64_t v = 0, A = 0;
                size_t k = 0; // direct actuals read
                // A round-up of a slot the walk is already reading (`len =
                // (len + A-1) & -A`): applied to the slot's other values.
                const Value *pendSlot = nullptr;
                uint64_t pendA = 0;
                std::string why;
              };
              auto join = [](Ext &a, const Ext &b) {
                a.k += b.k;
                if (b.pendSlot) a.pendSlot = b.pendSlot, a.pendA = std::max(a.pendA, b.pendA);
                if (!a.ok) return;
                if (!b.ok) return (void)(a.ok = false, a.why = b.why);
                if (b.none) return;
                a.v = a.none ? b.v : std::max(a.v, b.v);
                a.none = false;
                if (b.A) a.A = b.A;
              };
              auto fail = [](const std::string &w) {
                Ext e;
                e.ok = false, e.why = w;
                return e;
              };
              using Bind = std::function<Ext(const Argument *)>;
              auto intOf = [&](const Value *V) {
                for (V = castsOnly(V); const auto *C = dyn_cast<CastInst>(V);) {
                  if (!isa<ZExtInst>(C) && !isa<TruncInst>(C)) break;
                  V = castsOnly(C->getOperand(0));
                }
                return V;
              };
              std::function<Ext(const Value *, const Bind &, std::set<const Value *> &, int)> lenOf =
                  [&](const Value *V, const Bind &bind, std::set<const Value *> &onPath, int d) -> Ext {
                if (d > 16) return fail("too deep at " + valueText(V));
                V = intOf(V);
                if (const auto *C = dyn_cast<ConstantInt>(V)) {
                  Ext e;
                  e.none = false, e.v = C->getZExtValue();
                  return e;
                }
                if (const auto *A = dyn_cast<Argument>(V)) return bind(A);
                if (const auto *L = dyn_cast<LoadInst>(V); L && transientSlot(castsOnly(L->getPointerOperand()))) {
                  const Value *SL = castsOnly(L->getPointerOperand());
                  if (!onPath.insert(SL).second) {
                    Ext c; // a cycle: adds nothing unless a round-up is on it
                    c.pendSlot = SL;
                    return c;
                  }
                  Ext e;
                  for (const User *U : SL->users())
                    if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == SL)
                      join(e, lenOf(St->getValueOperand(), bind, onPath, d + 1));
                  onPath.erase(SL);
                  if (e.pendSlot == SL) {
                    // The least fixpoint of S = vals + R(S) with R the round-up
                    // (monotone, idempotent, R(x) >= x): R(max vals).
                    // A plain copy round the cycle (x = x) adds nothing.
                    if (e.ok && !e.none && e.pendA) e.v = (e.v + e.pendA - 1) & ~(e.pendA - 1), e.A = e.pendA;
                    e.pendSlot = nullptr, e.pendA = 0;
                  }
                  return e;
                }
                if (const auto *PN = dyn_cast<PHINode>(V)) {
                  Ext e;
                  for (const Value *In : PN->incoming_values()) join(e, lenOf(In, bind, onPath, d + 1));
                  return e;
                }
                if (const auto *SI = dyn_cast<SelectInst>(V)) {
                  Ext e = lenOf(SI->getTrueValue(), bind, onPath, d + 1);
                  join(e, lenOf(SI->getFalseValue(), bind, onPath, d + 1));
                  return e;
                }
                if (const auto *B = dyn_cast<BinaryOperator>(V); B && B->getOpcode() == Instruction::And)
                  if (const auto *M = dyn_cast<ConstantInt>(B->getOperand(1)); M && M->isNegative() && (-M->getValue()).isPowerOf2()) {
                    const uint64_t A = (-M->getValue()).getZExtValue();
                    // x + c1 - c2 ... with the constants summing to A-1 (-O0
                    // keeps `+ A - 1` as two steps).
                    int64_t sum = 0;
                    const Value *X = intOf(B->getOperand(0));
                    for (int k = 0; k < 4; k++) {
                      const auto *Ad = dyn_cast<BinaryOperator>(X);
                      const auto *K = Ad ? dyn_cast<ConstantInt>(Ad->getOperand(1)) : nullptr;
                      if (!K || (Ad->getOpcode() != Instruction::Add && Ad->getOpcode() != Instruction::Sub)) break;
                      sum += Ad->getOpcode() == Instruction::Add ? K->getSExtValue() : -K->getSExtValue();
                      X = intOf(Ad->getOperand(0));
                    }
                    if (sum == (int64_t)A - 1) {
                      Ext e = lenOf(X, bind, onPath, d + 1);
                      if (e.ok && !e.none) e.v = (e.v + A - 1) & ~(A - 1), e.A = A;
                      if (e.pendSlot) e.pendA = std::max(e.pendA, A);
                      return e;
                    }
                  }
                return fail("length not a round-up of the size formal (" + valueText(V) + ")");
              };
              // A formal of a function no one takes the address of: its direct
              // callers' actuals, the largest.
              std::function<Ext(const Argument *, int)> directBind = [&](const Argument *A, int d) -> Ext {
                const Function *F = A->getParent();
                if (F->hasAddressTaken()) return fail("a formal of " + F->getName().str() + ", address-taken");
                if (d > 6) return fail("too deep at a formal of " + F->getName().str());
                Ext e;
                for (const User *U : F->users()) {
                  const auto *CB = dyn_cast<CallBase>(U);
                  if (!CB || CB->getCalledOperand() != F || A->getArgNo() >= CB->arg_size()) return fail("an address use of " + F->getName().str());
                  std::set<const Value *> op;
                  Ext x = lenOf(CB->getArgOperand(A->getArgNo()), [&](const Argument *B) { return directBind(B, d + 1); }, op, 0);
                  x.k = std::max<size_t>(x.k, 1);
                  join(e, x);
                }
                if (e.ok && e.none) return fail("a formal of " + F->getName().str() + ", which has no caller");
                return e;
              };
              std::map<std::string, std::string> s1Why;   // a kept object's unsized reason
              std::set<const Function *> lenStack;
              // The length of what F returns, its formals bound by bind; the
              // pools its carves come from.
              std::function<Ext(const Function *, const Bind &, std::set<std::string> &, int)> retLen =
                  [&](const Function *F, const Bind &bind, std::set<std::string> &pools, int d) -> Ext {
                if (d > 4) return fail("too deep in " + F->getName().str());
                if (!lenStack.insert(F).second) return Ext{}; // a recursive return adds what the others give
                Ext e;
                std::vector<const Value *> vs;
                std::set<const Value *> seen;
                for (const Instruction &I : instructions(*F))
                  if (const auto *R = dyn_cast<ReturnInst>(&I); R && R->getReturnValue()) vs.push_back(R->getReturnValue());
                while (!vs.empty() && e.ok) {
                  const Value *V = castsOnly(vs.back());
                  vs.pop_back();
                  if (!seen.insert(V).second || isa<ConstantPointerNull>(V)) continue;
                  if (const auto *L = dyn_cast<LoadInst>(V); L && transientSlot(castsOnly(L->getPointerOperand()))) {
                    for (const User *U : castsOnly(L->getPointerOperand())->users())
                      if (const auto *St = dyn_cast<StoreInst>(U); St && castsOnly(St->getPointerOperand()) == castsOnly(L->getPointerOperand()))
                        vs.push_back(St->getValueOperand());
                    continue;
                  }
                  if (const auto *PN = dyn_cast<PHINode>(V)) {
                    for (const Value *In : PN->incoming_values()) vs.push_back(In);
                    continue;
                  }
                  if (const auto *SI = dyn_cast<SelectInst>(V)) {
                    vs.push_back(SI->getTrueValue()), vs.push_back(SI->getFalseValue());
                    continue;
                  }
                  const auto *CI = dyn_cast<Instruction>(V);
                  if (auto pit = CI ? poolCarvePool.find(CI) : poolCarvePool.end(); pit != poolCarvePool.end()) {
                    pools.insert(pit->second);
                    auto zit = poolCarveSizes.find(CI);
                    std::set<const Value *> op;
                    if (zit != poolCarveSizes.end() && zit->second.n) {
                      Ext x = lenOf(zit->second.n, bind, op, 0);
                      if (x.ok && !x.none) x.v *= zit->second.scale;
                      join(e, x);
                    } else if (zit != poolCarveSizes.end() && zit->second.chunk) {
                      // malloc(HDR + n) carved at HDR is n bytes.
                      const CallBase *CC = zit->second.chunk;
                      const auto *Ad = CC->arg_size() ? dyn_cast<BinaryOperator>(intOf(CC->getArgOperand(0))) : nullptr;
                      Ext x = fail("a header carve's chunk size not HDR + n " + snapLoc(CC));
                      if (Ad && Ad->getOpcode() == Instruction::Add)
                        for (unsigned o = 0; o < 2; o++)
                          if (const auto *K = dyn_cast<ConstantInt>(intOf(Ad->getOperand(o))); K && K->getSExtValue() == zit->second.off)
                            x = lenOf(Ad->getOperand(1 - o), bind, op, 0);
                      join(e, x);
                    } else {
                      join(e, fail("a carve of unknown size " + snapLoc(CI)));
                    }
                    continue;
                  }
                  if (CI && poolRefusedCarvePool.count(CI)) {
                    join(e, fail("a refused pool's carve " + snapLoc(CI)));
                    continue;
                  }
                  const auto *CB = dyn_cast<CallBase>(V);
                  const Function *G = CB ? CB->getCalledFunction() : nullptr;
                  if (!G) {
                    join(e, fail("a return no rule sizes " + valueText(V)));
                    continue;
                  }
                  std::set<const Value *> op;
                  if (G->getName() == "malloc") {
                    join(e, lenOf(CB->getArgOperand(0), bind, op, 0));
                    continue;
                  }
                  if (G->isDeclaration()) {
                    join(e, fail("an extern allocation " + G->getName().str()));
                    continue;
                  }
                  join(e, retLen(G, [&, CB](const Argument *B) {
                         std::set<const Value *> op2;
                         return lenOf(CB->getArgOperand(B->getArgNo()), bind, op2, 0);
                       }, pools, d + 1));
                }
                lenStack.erase(F);
                return e;
              };
              auto objSize = [&](const std::string &on, std::string &src) -> int64_t {
                auto it = objSite.find(on);
                if (it == objSite.end()) return -1;
                if (const auto *GV = dyn_cast<GlobalVariable>(it->second)) {
                  src = "its global's type";
                  return (int64_t)GV->getParent()->getDataLayout().getTypeAllocSize(GV->getValueType());
                }
                if (const auto *AI = dyn_cast<AllocaInst>(it->second))
                  if (auto sz = AI->getAllocationSize(AI->getModule()->getDataLayout()); sz && !sz->isScalable()) {
                    src = "its local's type";
                    return (int64_t)sz->getFixedValue();
                  }
                // s1: a carve reached directly, its length's formals bound to
                // their direct callers' actuals.
                if (const auto *CI = dyn_cast<Instruction>(it->second); CI && poolCarvePool.count(CI)) {
                  auto zit = poolCarveSizes.find(CI);
                  std::set<const Value *> op;
                  Ext e = zit == poolCarveSizes.end() || !zit->second.n
                              ? fail("a carve whose length is not its size operand " + snapLoc(CI))
                              : lenOf(zit->second.n, [&](const Argument *B) { return directBind(B, 0); }, op, 0);
                  const std::string P = poolCarvePool[CI];
                  const std::string pv = P + " (Carves.cc: " + poolVerdicts[P] + ")";
                  if (!e.ok || e.none) return s1Why[on] = (e.ok ? std::string("no length") : e.why) + "; pool " + pv, -1;
                  e.v *= zit->second.scale;
                  src = "its size argument (max of " + std::to_string(std::max<size_t>(e.k, 1)) + " direct actuals: " +
                        std::to_string(e.v) + (e.A ? ", rounded to " + std::to_string(e.A) : std::string()) + "); pool " + pv;
                  return (int64_t)e.v;
                }
                const auto *CB = dyn_cast<CallBase>(it->second);
                const Function *G = CB ? CB->getCalledFunction() : nullptr;
                if (!G) return -1;
                std::vector<const Value *> args;
                if (G->getName() == "malloc" || G->getName() == "calloc") {
                  for (const Value *A : CB->args()) args.push_back(A);
                } else if (!G->isDeclaration() && zeroing(G)) {
                  for (const Instruction &I : instructions(*G))
                    if (const auto *MS = dyn_cast<MemSetInst>(&I))
                      if (const auto *A = dyn_cast<Argument>(resolve(MS->getLength())); A && A->getParent() == G)
                        if (const auto *V0 = dyn_cast<ConstantInt>(MS->getValue()); V0 && V0->isZero()) {
                          args = {CB->getArgOperand(A->getArgNo())};
                          break;
                        }
                }
                if (args.empty() && objPools.count(on)) {
                  // s1: a wrapper over certified pools at this call site.
                  std::set<std::string> pools;
                  Ext e = retLen(G, [&](const Argument *B) {
                    std::set<const Value *> op;
                    return lenOf(CB->getArgOperand(B->getArgNo()), [&](const Argument *C2) { return directBind(C2, 0); }, op, 0);
                  }, pools, 0);
                  std::string pv;
                  for (const std::string &P : pools) pv += (pv.empty() ? "" : ", ") + P + " (Carves.cc: " + poolVerdicts[P] + ")";
                  if (!e.ok || e.none) return s1Why[on] = (e.ok ? std::string("no length") : e.why) + "; wrapper " + G->getName().str() + "; pool " + pv, -1;
                  src = "its size argument (" + std::to_string(e.v) + (e.A ? ", rounded to " + std::to_string(e.A) : std::string()) +
                        ") through " + G->getName().str() + "; pool " + pv;
                  return (int64_t)e.v;
                }
                if (args.empty()) return -1;
                uint64_t size = 1;
                bool viaFormal = false;
                std::string vals;
                for (const Value *A : args) {
                  std::set<uint64_t> cs;
                  if (!constsOf(A, cs, viaFormal, 0) || cs.empty()) return -1;
                  size *= *cs.rbegin();
                  for (uint64_t c : cs) vals += (vals.empty() ? "" : ", ") + std::to_string(c);
                }
                src = std::string(viaFormal ? "its direct callers' actuals (" : "a constant argument (") + vals + ")";
                return (int64_t)size;
              };
              std::set<Obj> wo;
              std::set<std::string> wop, zeroAt, dropped, keptObjs;
              if (decline.empty()) {
                objsOf(W->getPointerOperand(), 0, wo, wop);
                if (!wop.empty())
                  decline = "the word's objects are open: " + std::to_string(wop.size()) + " reasons, e.g. " + *wop.begin();
                for (const Obj &o : wo) {
                  std::string src;
                  const int64_t sz = objSize(o.first, src);
                  if (sz >= 0 && o.second + wlen > sz) {
                    dropped.insert(o.first + " +" + std::to_string(o.second) + ": past its size " + std::to_string(sz) +
                                   " (" + src + ")");
                    continue;
                  }
                  keptObjs.insert(o.first + " +" + std::to_string(o.second) +
                                  (sz >= 0 ? ", size " + std::to_string(sz) + " (" + src + ")" : std::string(", size unknown")));
                  if (!decline.empty()) continue; // every object is still checked for its size
                  auto it = objSite.find(o.first);
                  const auto *CB = it == objSite.end() ? nullptr : dyn_cast<CallBase>(it->second);
                  const Function *G = CB ? CB->getCalledFunction() : nullptr;
                  if (G && (G->getName() == "calloc" || (!G->isDeclaration() && zeroing(G)))) zeroAt.insert(o.first);
                  else decline = "an object not zero-allocated: " + o.first + " +" + std::to_string(o.second);
                }
                if (decline.empty() && zeroAt.empty()) decline = "the word has no object";
              }
              // (2) Every store of W keeps the mask from the same word or
              // clears it; no write names W otherwise; no initializer is
              // non-zero over it.
              const size_t kp = K.rfind('+');
              const std::string KS = K.substr(0, kp == std::string::npos ? 0 : kp);
              std::vector<std::string> clears;
              size_t keeps = 0;
              if (decline.empty())
                for (auto &[M, _] : Ctx->Modules)
                  for (const Function &F : *M)
                    for (const Instruction &I : instructions(F)) {
                      const auto *St = dyn_cast<StoreInst>(&I);
                      if (!St || !decline.empty() || fieldKey(St, St->getPointerOperand()) != K) continue;
                      const Value *V = St->getValueOperand();
                      if (!V->getType()->isIntegerTy() || V->getType()->getIntegerBitWidth() != mask.getBitWidth()) {
                        decline = "a store of another width: " + snapLoc(St);
                        break;
                      }
                      const KnownBits KB = computeKnownBits(V, M->getDataLayout());
                      if ((KB.Zero & mask) == mask) {
                        clears.push_back(snapLoc(St));
                        continue;
                      }
                      bool kept = false;
                      if (const auto *O = dyn_cast<BinaryOperator>(V); O && O->getOpcode() == Instruction::Or)
                        for (int k = 0; k < 2 && !kept; k++) {
                          const auto *An = dyn_cast<BinaryOperator>(O->getOperand(k));
                          const auto *C = An && An->getOpcode() == Instruction::And ? dyn_cast<ConstantInt>(An->getOperand(1)) : nullptr;
                          const auto *L2 = C ? dyn_cast<LoadInst>(An->getOperand(0)) : nullptr;
                          kept = L2 && castsOnly(L2->getPointerOperand()) == castsOnly(St->getPointerOperand()) &&
                                 (C->getValue() & mask) == mask &&
                                 (computeKnownBits(O->getOperand(1 - k), M->getDataLayout()).Zero & mask) == mask;
                        }
                      if (kept) keeps++;
                      else decline = "a store that may set the mask: " + snapLoc(St);
                    }
              if (decline.empty())
                if (std::string c = coverOpen(K, wlen); !c.empty()) decline = c;
              if (decline.empty()) {
                // R1: the writes with no named slot, against the word's
                // objects (closed: every object the word can lie in).
                std::set<const Value *> Wsites;
                for (const std::string &z : zeroAt)
                  if (auto it = objSite.find(z); it != objSite.end()) Wsites.insert(it->second);
                  else decline = "the word's object " + z + " has no site to decide unnamed-destination writes against";
                if (decline.empty())
                  if (std::string u = unnamedOpen(K, &Wsites); !u.empty()) decline = u;
              }
              if (decline.empty()) {
                buildInit();
                for (const InitSlot &IS : initNonZero)
                  if (IS.S == KS && IS.off < KO_of(K) + wlen && KO_of(K) < IS.off + IS.len) {
                    decline = "a non-zero initializer over the word: @" + IS.gv;
                    break;
                  }
              }
              SmallString<16> mhex;
              mask.toStringUnsigned(mhex, 16);
              std::string gl;
              for (const std::string &g : guardLocs) gl += (gl.empty() ? "" : ", ") + g;
              const std::string gtext = "guard " + gl + " (mask 0x" + std::string(mhex) + " of " +
                                        (K.empty() ? std::string("an unnamed word") : K) + ")";
              CG_LOG("Container: snapshot holder " << hname << ": guard word " << K << "; the holder's object walks: "
                     << keysUnionWalked.size() << " union fields read by key (" << unionExcluded.size()
                     << " stores another member's, excluded), " << cycleCuts << " cycle cuts (adding nothing; "
                     << cutEmpty.size() << " fields every store of which is cut), " << dropped.size()
                     << " objects past their size, dropped, " << s1Why.size() << " kept unsized; "
                     << elemWalked.size() << " handle arrays read by element, " << codeCallsWalked.size()
                     << " indirect calls through closed code fields followed; " << nodeCount << " nodes walked (budget "
                     << nodeBudget << "), " << budgetCuts << " budget cuts, " << offCycles
                     << " cycles stepping the offset\n");
              for (const std::string &x : dropped)
                o1AssumeLines.push_back("    snapshot holder " + hname + ": dropped from the word's objects: " + x);
              for (const auto &[o, why] : s1Why)
                o1AssumeLines.push_back("    snapshot holder " + hname + ": kept, its size unknown: " + o + ": " + why);
              // (f) per formal, by function name: the field, chain and callers,
              // or why the rule does not apply.
              std::map<std::string, const Fed *> fedByName;
              for (const auto &[F, fd] : fedOf) fedByName[F->getName().str()] = &fd;
              for (const auto &[fn, fd] : fedByName)
                CG_LOG("Container: snapshot holder " << hname << ": formal rule: " << fn << ": "
                       << (fd->text.empty() ? "not applied, " + fd->why : fd->text) << "\n");
              for (const std::string &x : keptObjs) CG_LOG("Container: snapshot holder " << hname << ": kept: " << x << "\n");
              for (const std::string &x : coverLog) CG_LOG("Container: snapshot holder " << hname << ": " << x << "\n");
              std::stable_sort(coverReasons.begin(), coverReasons.end(),
                               [](const CoverReason &a, const CoverReason &b) { return irOrderLess(a.I, b.I); });
              for (const CoverReason &r : coverReasons) {
                std::string ks;
                for (const std::string &k : r.keys) ks += (ks.empty() ? "" : ", ") + k;
                CG_LOG("Container: snapshot holder " << hname << ": cover: unnamed-destination write " << snapLoc(r.I) << ": "
                       << r.why << " (over " << ks << ")\n");
              }
              for (const MemTransferInst *MT : std::set<const MemTransferInst *, IROrder>(kToKCopies.begin(), kToKCopies.end()))
                CG_LOG("Container: snapshot holder " << hname << ": cover: a block copy from the same key, nothing added (R2): "
                                                     << snapLoc(MT) << "\n");
              CG_LOG("Container: snapshot holder " << hname << ": cover: " << coverIcalls.size()
                     << " indirect call sites through closed code fields followed\n");
              CG_LOG("Container: snapshot holder " << hname << ": object walks: " << nodeCount << " nodes, "
                     << format("%.3f", walkSecs) << " s\n");
              // Every reason the word's objects are open, not only the first.
              for (const std::string &x : wop) CG_LOG("Container: snapshot holder " << hname << ": open: " << x << "\n");
              if (decline.empty()) {
                // A certified pool's carve through a zeroing wrapper is an
                // object of its own at the wrapper's call site, resting on
                // the pool's certificate.
                for (const std::string &z : zeroAt)
                  if (auto pit = objPools.find(z); pit != objPools.end())
                    for (const std::string &P : pit->second)
                      o1AssumeLines.push_back("    ASSUMPTION pool " + P + ": " + z +
                                              " is an object of its own, zeroed by its callee (a carve of the certified "
                                              "pool; Carves.cc: " + poolVerdicts[P] + ")");
                std::string zs, cs;
                for (const std::string &z : zeroAt) zs += (zs.empty() ? "" : ", ") + z;
                for (const std::string &c : clears) cs += (cs.empty() ? "" : ", ") + c;
                for (const auto *v : {&hOuts, &eOuts})
                  for (const MemTransferInst *MT : *v) {
                    snapUnreachable.insert(MT);
                    o1AssumeLines.push_back("    ASSUMPTION unreachable by name: restore " + snapLoc(MT) + ": " + gtext + ", " +
                                            std::to_string(keeps + clears.size()) + " named stores each keeping or clearing it (" +
                                            std::to_string(keeps) + " keep; clears: " + (cs.empty() ? "none" : cs) +
                                            "), objects zero-allocated at " + zs);
                  }
                continue;
              }
              o1AssumeLines.push_back("  snapshot holder " + hname + ": " + gtext + ": not unreachable by name (" + decline + ")");
            }
          }
          if (!premiseOpen.empty()) continue;
          // The restores O1 counts as moves within one owner.
          for (const MemTransferInst *MT : hOuts) {
            std::string o, x;
            if (handleLoad(MT->getRawDest(), o, x) && o == owner) snapRestores[MT] = hname;
          }
          for (const MemTransferInst *MT : eOuts)
            if (ownElem(MT->getRawDest(), owner, 0)) snapRestores[MT] = hname;
          SnapshotHolder SH;
          SH.alloc = A;
          SH.elem = T;
          SH.elemPtrs = elemPtrs;
          for (const auto *v : {&eSaves, &eOuts})
            for (const MemTransferInst *MT : *v) SH.elemCopies.insert(MT);
          snapshotHolders.push_back(std::move(SH));
        }
      }
      auto joinSet = [](const std::set<std::string> &S) {
        std::string r;
        for (const std::string &x : S) r += (r.empty() ? "" : "; ") + x;
        return r;
      };
      size_t o1NoElement = 0, o1IntoElement = 0;
      std::map<std::string, size_t> o1Roots; // an open copy's root reason -> copies through it
      std::vector<std::string> o1NameLines;
      std::map<std::string, size_t> o1Pools; // certified pool -> copies resting on its chunks (one premise per pool)
      for (auto &[M, _] : Ctx->Modules)
        for (Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            const auto *MT = dyn_cast<MemTransferInst>(&I);
            if (!MT) continue;
            const std::string K = fieldKey(MT, MT->getRawDest());
            if (K.empty()) {
              // A destination no field names (a pointer loaded from a field,
              // a local, an array): by what it points to (Fable 2026-10-17, a
              // checker soundness fix; before such copies were not checked).
              // An element struct, or the owner's handle array (a load of a
              // handle field): checked as below. A local or a global: no
              // element. Anything else: unclassifiable, listed.
              const Value *Dst = MT->getRawDest()->stripPointerCasts();
              const Value *DB = getUnderlyingObject(Dst);
              if (isa<AllocaInst>(DB) || isa<GlobalVariable>(DB)) continue;
              bool candidate = false;
              if (const auto *DL = dyn_cast<LoadInst>(Dst)) {
                // A load of a handle field (the owner's array), of a link
                // field or of a closed cursor field (an element).
                const std::string HK = fieldKey(DL, DL->getPointerOperand());
                candidate = !HK.empty() && (handle.count(HK) || links.count(HK) ||
                                            (cursorOpen.count(HK) && cursorOpen[HK].empty()));
              }
              StructType *PT = candidate ? nullptr : pointees.get(Dst, Dst->getContext());
              if (PT && PT->hasName()) candidate = embedsElem(stripStructNameSuffix(PT->getName()).drop_front(7), 0);
              else if (!candidate) {
                // By name: the destination's origins.
                const Origins O = originsOf(Dst, 0);
                const std::string at = F.getName().str() + ": " + valueText(MT);
                std::string orig = joinSet(O.leaves);
                for (const auto &[pn, sites] : O.pools)
                  orig += (orig.empty() ? "" : "; ") + std::string("chunks of pool ") + pn + " (" + joinSet(sites) + ")";
                if (!O.elements.empty()) {
                  o1NameLines.push_back("    O1 by name: into an element: " + at + ": elements " + joinSet(O.elements) +
                                          (orig.empty() ? "" : "; other origins " + orig) +
                                          (O.unknown.empty() ? "" : "; unknown via " + joinSet(O.unknown)));
                  o1IntoElement++;
                  candidate = true;
                } else if (!O.unknown.empty()) {
                  for (const std::string &r : O.unknown) o1Roots[r]++;
                  o1Unclassified.push_back(at + ": unknown via " + joinSet(O.unknown) +
                                           (orig.empty() ? "" : "; origins " + orig));
                  continue;
                } else {
                  o1NameLines.push_back("    O1 by name: no element: " + at + ": origins " + orig);
                  o1NoElement++;
                  for (const auto &[pn, sites] : O.pools) o1Pools[pn]++;
                  continue;
                }
              }
              if (!candidate) continue;
              if (snapRestores.count(MT)) {
                snapMoves++;
                continue;
              }
              if (snapUnreachable.count(MT)) {
                snapUnreach++;
                continue;
              }
              if (!body.count(&F)) {
                const size_t mark = eoMark();
                const std::string a = elemOwner(MT->getRawDest(), 0), v = elemOwner(MT->getRawSource(), 0);
                eoSettle(mark, !a.empty() && a == v);
                if (!a.empty() && a == v) {
                  inlineSites.push_back(F.getName().str() + ": " + valueText(MT));
                  continue;
                }
              } else {
                const uint8_t src = get(baseOf(MT->getRawSource())) & ~NUL;
                if (src && !(src & ~(DER | FRS))) continue;
              }
              badCopies.push_back(F.getName().str() + ": " + valueText(MT) + " (destination named by what it points to)");
              continue;
            }
            // The destination range [off, off + len) against the link fields
            // of a container struct embedded at the start, and the owner's
            // handle fields.
            const std::string S = K.substr(0, K.rfind('+'));
            const int64_t off = std::stoll(K.substr(K.rfind('+') + 1));
            const auto *LenC = dyn_cast<ConstantInt>(MT->getLength());
            const int64_t len = LenC ? (int64_t)LenC->getZExtValue() : INT64_MAX / 2;
            std::vector<int64_t> pos;
            if (embedsElem(StringRef(S).drop_front(7), 0))
              for (const std::string &L : links) pos.push_back(std::stoll(L.substr(L.rfind('+') + 1)));
            for (const std::string &H : handle)
              if (H.substr(0, H.rfind('+')) == S) pos.push_back(std::stoll(H.substr(H.rfind('+') + 1)));
            bool covers = false;
            for (int64_t p0 : pos) covers |= p0 >= off && p0 < off + len;
            if (!covers) continue;
            if (snapRestores.count(MT)) {
              snapMoves++;
              continue;
            }
            if (snapUnreachable.count(MT)) {
              snapUnreach++;
              continue;
            }
            if (body.count(&F)) {
              const uint8_t src = get(baseOf(MT->getRawSource())) & ~NUL;
              if (src && !(src & ~(DER | FRS))) continue;
            } else {
              // A copy between two elements of one owner: the link fields it
              // covers are link copies (the rb_replace_node rule), the other
              // bytes ordinary flow (Fable 2026-10-16).
              const size_t mark = eoMark();
              const std::string a = elemOwner(MT->getRawDest(), 0), v = elemOwner(MT->getRawSource(), 0);
              eoSettle(mark, !a.empty() && a == v);
              if (!a.empty() && a == v) {
                inlineSites.push_back(F.getName().str() + ": " + valueText(MT));
                continue;
              }
            }
            badCopies.push_back(F.getName().str() + ": " + valueText(MT));
          }
      if (!badCopies.empty()) {
        std::string l = "an element copied from another value: " + std::to_string(badCopies.size()) + " copies";
        for (const std::string &b : badCopies) l += " [" + b + "]";
        open1.insert(l);
      }
      if (o1IntoElement || o1NoElement || !o1Unclassified.empty()) {
        o1AssumeLines.push_back("  O1 by name: " + std::to_string(o1IntoElement + o1NoElement + o1Unclassified.size()) +
                                " block copies whose destination no field names and whose pointee names no struct: " +
                                std::to_string(o1IntoElement) + " into an element (checked), " +
                                std::to_string(o1NoElement) + " into no element (origins by name), " +
                                std::to_string(o1Unclassified.size()) + " open-unproven (each an ASSUMPTION) through " +
                                std::to_string(o1Roots.size()) + " roots; " + std::to_string(icallClosed.size()) +
                                " indirect call sites closed by their callee's names; elements are the constructors' "
                                "allocations, as the block's insert checks establish (each copy: the rule report)");
        std::vector<std::pair<size_t, std::string>> roots;
        for (const auto &[r, n] : o1Roots) roots.emplace_back(n, r);
        std::sort(roots.begin(), roots.end(), [](const auto &a, const auto &b) { return a.first != b.first ? a.first > b.first : a.second < b.second; });
        for (const auto &[n, r] : roots) o1AssumeLines.push_back("    O1 open root (" + std::to_string(n) + " copies): " + r);
        for (const auto &[pn, n] : o1Pools) {
          o1AssumeLines.push_back("    ASSUMPTION pool " + pn + ": a carve outside the constructors is a chunk apart from "
                                  "every element (the pool's carve certificate), for " + std::to_string(n) + " copies");
          nO1Assume++;
        }
        o1ReportLines.insert(o1ReportLines.end(), o1NameLines.begin(), o1NameLines.end());
        for (const std::string &u : o1Unclassified) {
          o1ReportLines.push_back("    ASSUMPTION a block copy into no element: " + u);
          nO1Assume++;
        }
      }
      // (R3, D1) The byte-cell premise R3's read side rests on, when R3
      // looked at a vector: each copy with an unnamed, open source.
      if (r3Census) {
        CG_LOG("Container: R3 read side: " << (r3NamedOpen + r3ByteRows.size()) << " block copies with open source: "
               << r3NamedOpen << " under another name (name premise), " << r3ByteRows.size()
               << " unnamed (byte-cell ASSUMPTION rows)\n");
        o1AssumeLines.push_back("  R3 read side: a byte copy with an open source carries no code pointer; a pointer copied as "
                                "bytes would be a leak (plan 3.53): " + std::to_string(r3ByteRows.size()) + " copies");
        for (const MemTransferInst *MT : r3ByteRows) {
          o1AssumeLines.push_back("    ASSUMPTION a byte copy with an open source carries no code pointer: " + snapLoc(MT) + ": " +
                                  valueText(MT));
          nO1Assume++;
        }
      }
    }
    std::string o1 = open1.empty() ? "O1 PASS" : "O1 FAIL(open:";
    for (const std::string &K : open1) {
      o1 += " " + K;
      if (const StoreInst *S = firstBad1[K])
        o1 += " [" + S->getFunction()->getName().str() + ": " + valueText(S) + "; value class " +
              std::to_string(get(S->getValueOperand())) + "]";
    }
    if (!open1.empty()) o1 += ")";
    if (!inlineSites.empty()) {
      o1 += " (inline insert: " + std::to_string(inlineSites.size()) + " same-owner stores or copies outside the body:";
      for (size_t i = 0; i < inlineSites.size() && i < 4; i++) o1 += " [" + inlineSites[i] + "]";
      o1 += ")";
    }
    if (declared) {
      // Every failing reason with its count and first site; naming failures
      // fail too (an unnamed access through an owner or element value never
      // passes).
      if (o1Fail.empty() && o1Naming.empty()) {
        o1 = "O1 PASS";
      } else if (o1Fail.empty()) {
        o1 = "O1 FAIL on naming (" + std::to_string(o1Naming.size()) +
             " accesses through owner or element values that no rule names)";
      } else {
        o1 = "O1 FAIL(";
        for (auto &[why, sites] : o1Fail) {
          o1 += (o1.back() == '(' ? "" : "; ") + why;
          if (!sites.empty()) o1 += ": " + std::to_string(sites.size()) + " [" + sites[0] + "]";
        }
        if (!o1Naming.empty()) o1 += "; on naming: " + std::to_string(o1Naming.size());
        o1 += ")";
      }
    }
    // O4: every callee outside the body is a row of this container, a
    // carve row, an allocation or a free (modeled), a prover no-op, a pure
    // row, or does not return; an indirect call is checked as a code field
    // (not built: FAIL).
    std::set<std::string> bad4;
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F)) {
        const auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || isa<DbgInfoIntrinsic>(CB)) continue;
        const Function *G = CB->getCalledFunction();
        // An inline asm is modeled (asmModel), no callee, unless its text calls.
        if (CB->isInlineAsm()) {
          const StringRef AsmText = cast<InlineAsm>(CB->getCalledOperand())->getAsmString();
          if (AsmText.contains("call")) bad4.insert("an asm that calls in " + F->getName().str());
          continue;
        }
        if (!G) {
          const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
          const std::string K = CL ? fieldKey(CL, CL->getPointerOperand()) : "";
          if (code.count(K) && !codeOpen.count(K)) continue; // its targets are in the body
          bad4.insert("an indirect call in " + F->getName().str() +
                      (codeOpen.count(K) ? " (code field " + K + " open: " + codeOpen[K] + ")" : ""));
          continue;
        }
        if (body.count(G) || C.rows.count(G->getName().str()) || carveFns.count(G->getName().str())) continue;
        if (G->isIntrinsic() || CB->doesNotReturn() || G->doesNotReturn()) continue;
        if (Ctx->AllocFuncs.count(G) || G->getName() == "free" || G->getName() == "cfree") continue;
        if (auto sit = Ctx->FuncSummaries.find(G); sit != Ctx->FuncSummaries.end() && sit->second &&
                                                   (sit->second->noop || sit->second->fresh || sit->second->freeArg >= 0))
          continue;
        bad4.insert(G->getName().str());
      }
    std::string o4 = bad4.empty() ? "O4 PASS" : "O4 FAIL(callee:";
    for (const std::string &g : bad4) o4 += " " + g;
    if (!bad4.empty()) o4 += ")";
    // O2: what a lookup returns is null, derived from its owner, or an
    // insert row's result.
    std::set<std::string> bad2;
    // O3: an insert's element goes only into the owner's storage: stores
    // of it into owner handle fields or derived cells, writes through it,
    // compares, a body helper's formal (checked there), or returned.
    std::set<std::string> bad3;
    std::function<void(const Value *, const std::string &, std::set<const Value *> &)> elemUses =
        [&](const Value *E, const std::string &fn, std::set<const Value *> &seen) {
          if (!seen.insert(E).second) return;
          for (const User *U : E->users()) {
            const auto *UI = dyn_cast<Instruction>(U);
            if (!UI || isa<DbgInfoIntrinsic>(UI) || isa<ICmpInst>(UI)) continue;
            if (isa<CastInst>(UI) || isa<PHINode>(UI) || isa<SelectInst>(UI)) { elemUses(UI, fn, seen); continue; }
            // The element as a link word (declared LINKWORD storage, R1's
            // grammar): its ptrtoint with a tag set from a constant or from
            // another word's tag extract, stored into a link word below.
            if (const auto *BO = dyn_cast<BinaryOperator>(UI); BO && wordInts && E->getType()->isIntegerTy()) {
              const Value *O = BO->getOperand(BO->getOperand(0) == E ? 1 : 0);
              auto smallTag = [](const Value *X) {
                const auto *C = dyn_cast<ConstantInt>(X);
                return C && C->getValue().ult(8);
              };
              const auto *OA = dyn_cast<BinaryOperator>(O);
              const bool tag = smallTag(O) || (OA && OA->getOpcode() == Instruction::And &&
                                               (smallTag(OA->getOperand(0)) || smallTag(OA->getOperand(1))));
              const auto op = BO->getOpcode();
              if (tag && (op == Instruction::Or || op == Instruction::Xor || op == Instruction::Add)) {
                elemUses(UI, fn, seen);
                continue;
              }
            }
            if (const auto *G = dyn_cast<GetElementPtrInst>(UI)) {
              if (G->getPointerOperand() == E) continue; // a field of the element
            }
            if (const auto *L = dyn_cast<LoadInst>(UI); L && L->getPointerOperand() == E) continue;
            if (const auto *S = dyn_cast<StoreInst>(UI)) {
              if (S->getPointerOperand() == E) continue; // a write through it
              const Value *B = baseOf(S->getPointerOperand());
              if (transientSlot(B)) {
                for (const User *LU : B->users())
                  if (isa<LoadInst>(LU)) elemUses(LU, fn, seen);
                continue;
              }
              const uint8_t b = get(B) & ~NUL; // a store through null never executes
              // A tagged word only into a declared link word: one the access
              // names, or the word at +0 of a body element (the element
              // pointer itself is the address).
              const bool wordOk =
                  !E->getType()->isIntegerTy() ||
                  (declared && (declWord.count(ckey(S, S->getPointerOperand())) ||
                                (S->getPointerOperand()->stripPointerCasts() == B && premiseElemT &&
                                 declWord.count(stripStructNameSuffix(premiseElemT->getName()).str() + "+0"))));
              if (b && !(b & ~(OWN | DER | FRS)) && wordOk) continue; // into the owner's storage (or a new element)
              bad3.insert(fn + ": stored into " + valueText(S));
              continue;
            }
            if (const auto *CB = dyn_cast<CallBase>(UI)) {
              const Function *G = CB->getCalledFunction();
              // An inline asm, by the graph build's model: the element stored
              // into a slot or written through a raw pointer of the owner's
              // storage, or written and read through (a raw pointer itself).
              if (CB->isInlineAsm()) {
                const AsmModel AM = asmModel(*CB, &CDL);
                auto intoOwner = [&](const Value *P) {
                  const uint8_t b = get(baseOf(P)) & ~NUL;
                  return b && !(b & ~(OWN | DER | FRS));
                };
                for (const AsmModel::Slot &Sl : AM.slots)
                  if (Sl.output)
                    for (const AsmModel::Value_ &In : Sl.stores)
                      if (In.ok && In.val->stripPointerCasts() == E->stripPointerCasts() && !intoOwner(Sl.ptr))
                        bad3.insert(fn + ": stored by an asm into " + valueText(CB));
                // The model's raw-pointer rule writes every value input through
                // every raw pointer input: its own class (Fable 2026-10-15).
                if (AM.memEffects)
                  for (const AsmModel::Value_ &In : AM.valueInputs)
                    if (In.ok && In.val->stripPointerCasts() == E->stripPointerCasts())
                      for (const Value *P : AM.rawPtrs)
                        if (!intoOwner(P))
                          bad3.insert("asm model over-approximation: " + fn + ": written through a raw pointer input by " +
                                      valueText(CB));
                continue;
              }
              if (const auto *MI = dyn_cast<MemIntrinsic>(CB)) {
                // Reading it (a copy's source) moves nothing out; zeroing it
                // is a null store; filling it stores the source's fields, so
                // the source must be the same owner's or fresh (Fable
                // 2026-10-14: per-field decomposition).
                if (MI->getRawDest()->stripPointerCasts() != E->stripPointerCasts() || isa<MemSetInst>(MI)) continue;
                const auto *MT = cast<MemTransferInst>(MI);
                const uint8_t src = get(baseOf(MT->getRawSource())) & ~NUL;
                if (src && !(src & ~(DER | FRS))) continue;
                bad3.insert(fn + ": filled from another value (" + valueText(CB) + ")");
                continue;
              }
              if (G)
                if (auto sit = Ctx->FuncSummaries.find(G); sit != Ctx->FuncSummaries.end() && sit->second && sit->second->noop)
                  continue; // read by a no-op (strcmp)
              if (const CR *RR = rowOf(G); G && RR && body.count(G)) {
                for (unsigned a = 0; a < CB->arg_size() && a < G->arg_size(); a++)
                  if (CB->getArgOperand(a)->stripPointerCasts() == E->stripPointerCasts())
                    elemUses(G->getArg(a), G->getName().str(), seen);
                continue; // a row of the same container takes it
              }
              if (const CR *PR = rowOf(G); PR && PR->role == CR::Pure) continue; // a leaf premise
              if (G && body.count(G) && !rowOf(G)) {
                for (unsigned a = 0; a < CB->arg_size() && a < G->arg_size(); a++)
                  if (CB->getArgOperand(a) == E) elemUses(G->getArg(a), G->getName().str(), seen);
                continue;
              }
              if (!G)
                if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
                  const std::string K = fieldKey(CL, CL->getPointerOperand());
                  if (code.count(K) && !codeOpen.count(K)) {
                    // Through a closed code field: each fed constructor.
                    for (const Function *T : codeTargets[K])
                      for (unsigned a = 0; a < CB->arg_size() && a < T->arg_size(); a++)
                        if (CB->getArgOperand(a)->stripPointerCasts() == E->stripPointerCasts() && !T->isDeclaration())
                          elemUses(T->getArg(a), T->getName().str(), seen);
                    continue;
                  }
                }
              bad3.insert(fn + ": passed to " + (G ? G->getName().str() : std::string("an indirect call")) + " (" +
                          valueText(CB) + ")");
              continue;
            }
            if (isa<ReturnInst>(UI)) continue; // the insert's result
            bad3.insert(fn + ": " + valueText(UI));
          }
        };
    // An ELEM(ret) row's RET read from a closed cursor field (cursorField
    // above) passes O2 "through a closed cursor field" (Fable 2026-10-16, Q-a).
    // The payload reads a value is (through casts, phis, selects and -O0
    // slots): each one's field, and those its base is when the base is a
    // payload value too.
    auto payloadReads = [&](const Value *V0, std::set<std::pair<std::string, const LoadInst *>> &fieldsOut) {
      std::vector<const Value *> wl{V0};
      std::set<const Value *> seen;
      for (size_t k = 0; k < wl.size(); k++) {
        const Value *V = wl[k]->stripPointerCasts();
        if (!seen.insert(V).second || !(get(V) & PAY)) continue;
        if (const auto *PN = dyn_cast<PHINode>(V)) {
          for (const Value *In : PN->incoming_values()) wl.push_back(In);
        } else if (const auto *SL = dyn_cast<SelectInst>(V)) {
          wl.push_back(SL->getTrueValue()), wl.push_back(SL->getFalseValue());
        } else if (const auto *L = dyn_cast<LoadInst>(V)) {
          const Value *B = baseOf(L->getPointerOperand());
          if (transientSlot(B)) {
            for (const User *U : B->users())
              if (const auto *S = dyn_cast<StoreInst>(U); S && S->getPointerOperand()->stripPointerCasts() == B)
                wl.push_back(S->getValueOperand());
          } else {
            fieldsOut.insert({ckey(L, L->getPointerOperand()), L});
            wl.push_back(B); // a payload base: its own payload reads too
          }
        } else {
          fieldsOut.insert({"", nullptr});
        }
      }
    };
    std::set<std::string> cursorUsed;
    for (const auto &[fn, R] : C.rows) {
      auto it = byName.find(fn);
      if (it == byName.end() || !(body.count(it->second) || derefFns.count(it->second))) continue;
      const Function *F = it->second;
      if (R.role == CR::Lookup || R.role == CR::Traverse || (R.role == CR::Remove && R.elem == -1))
        for (const Instruction &I : instructions(*F))
          if (const auto *RI = dyn_cast<ReturnInst>(&I); RI && RI->getReturnValue() &&
                                                         RI->getReturnValue()->getType()->isPointerTy()) {
            const uint8_t m = get(RI->getReturnValue());
            if (!m || (m & ~(NUL | DER | PAY | INS))) {
              bad2.insert(fn + " returns " + valueText(RI->getReturnValue()) + " (" + std::to_string(m) + ")");
              continue;
            }
            // ELEM(ret): what it returns is an element, so a payload read
            // must be a closed cursor field.
            if (!(m & PAY) || R.elem != -1) continue;
            std::set<std::pair<std::string, const LoadInst *>> ks;
            payloadReads(RI->getReturnValue(), ks);
            for (const auto &[K, PL] : ks) {
              if (K.empty()) {
                bad2.insert(fn + " returns " + valueText(RI->getReturnValue()) + " (a payload value it cannot name)");
                continue;
              }
              // Outside an evaluation: the assumptions the read rests on (P3's
              // exclusions) settle here.
              const size_t mark = eoMark();
              const std::string why = cursorRead(K, PL);
              eoSettle(mark, why.empty());
              if (!why.empty())
                bad2.insert(fn + " returns " + valueText(RI->getReturnValue()) + " (read from " + K +
                            ", a cursor field not closed: " + why + ")");
              else {
                cursorUsed.insert(K);
                if (const std::string u = PL ? uncheckedOf(K, PL) : std::string(); !u.empty()) uncheckedCursor.insert(u);
              }
            }
          }
      if (R.role == CR::Insert || (R.role == CR::Lookup && R.create >= 0 && R.elem == -1)) {
        std::set<const Value *> seen;
        if (R.elem >= 0 && (unsigned)R.elem < F->arg_size()) elemUses(F->getArg(R.elem), fn, seen);
        for (int e : R.moreElems)
          if ((unsigned)e < F->arg_size()) elemUses(F->getArg(e), fn, seen);
        if (R.elem == -1)
          for (const Instruction &I : instructions(*F))
            if (const auto *RI = dyn_cast<ReturnInst>(&I); RI && RI->getReturnValue())
              if (const auto *D = dyn_cast<Instruction>(RI->getReturnValue()->stripPointerCasts()))
                elemUses(D, fn, seen);
      }
    }
    // Every fresh block the body makes goes only into the owner's storage
    // (a new element, a key copy), so a store into one is a store into
    // the container. A fresh block stored into a certified pool's handle
    // field is pool storage (a chunk: objalloc_alloc inlined into a
    // constructor at -O3), not an element: the pool's certificate covers
    // its uses, and its carves are the elements (Fable 2026-10-14).
    size_t poolChunks = 0;
    auto poolChunk = [&](const Instruction *I) {
      SmallVector<const Value *, 4> w{I};
      for (size_t k = 0; k < w.size(); k++)
        for (const User *U : w[k]->users()) {
          if (const auto *SI = dyn_cast<StoreInst>(U);
              SI && SI->getValueOperand() == w[k] && poolHandleStores.count(SI))
            return true;
          if (isa<CastInst>(U)) w.push_back(U);
        }
      return false;
    };
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        if (isa<CallBase>(&I) && I.getType()->isPointerTy() && get(&I) == FRS) {
          if (poolChunk(&I)) {
            poolChunks++;
            continue;
          }
          std::set<const Value *> seen;
          elemUses(&I, F->getName().str() + " (a fresh block)", seen);
        }
    std::string o2 = bad2.empty() ? "O2 PASS" : "O2 FAIL(";
    for (const std::string &b : bad2) o2 += (o2.back() == '(' ? "" : "; ") + b;
    if (!bad2.empty()) o2 += ")";
    std::string o3 = bad3.empty() ? "O3 PASS" : "O3 FAIL(";
    for (const std::string &b : bad3) o3 += (o3.back() == '(' ? "" : "; ") + b;
    if (!bad3.empty()) o3 += ")";
    if (poolChunks) o3 += " (" + std::to_string(poolChunks) + " pool chunks allocated inside the body: certified pool storage)";
    if (moves) o1 += " (" + std::to_string(moves) + " element moves within one owner)";
    if (snapMoves)
      o1 += " (" + std::to_string(snapMoves) + " restores out of a snapshot holder: moves within one owner)";
    if (snapUnreach)
      o1 += " (" + std::to_string(snapUnreach) + " restores of a snapshot holder unreachable by name, listed)";
    // O6 (body reads): every pointer field of an element the body reads
    // is one the body writes (a body read of an owner-written field would
    // see the body's object without the owner's writes).
    std::set<std::string> bodyWrites, bad6, o6Cursor;
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F)) {
        const Value *A = nullptr;
        int64_t bytes = 0;
        if (const auto *S = dyn_cast<StoreInst>(&I)) {
          A = S->getPointerOperand();
          bytes = (int64_t)CDL.getTypeStoreSize(S->getValueOperand()->getType());
          if (const std::string K = ckey(S, A); !K.empty()) bodyWrites.insert(K);
        } else if (const auto *MS = dyn_cast<MemSetInst>(&I); MS && declared) {
          A = MS->getDest();
          const auto *Len = dyn_cast<ConstantInt>(MS->getLength());
          bytes = Len ? (int64_t)Len->getZExtValue() : INT64_MAX / 4;
        }
        // Declared storage: every declared slot a wide store or a fill spans.
        StructType *S = nullptr;
        int64_t off = 0;
        if (!declared || !A || !namedSlot(&I, A, CDL, pointees, S, off) || !S->hasName()) continue;
        structCover(S, off, off + bytes, CDL, [&](StructType *ST, int64_t lo, int64_t h) {
          if (!ST->hasName()) return;
          const std::string SN = stripStructNameSuffix(ST->getName()).str();
          for (const std::string &K : links)
            if (const size_t p = K.rfind('+'); K.compare(0, p, SN) == 0)
              if (const int64_t o = std::stoll(K.substr(p + 1)); o >= lo && o < h) bodyWrites.insert(K);
        });
      }
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        if (const auto *L = dyn_cast<LoadInst>(&I); L && L->getType()->isPointerTy()) {
          const uint8_t b = get(baseOf(L->getPointerOperand())) & ~NUL;
          if (!(b & (DER | FRS))) continue;
          const std::string K = ckey(L, L->getPointerOperand());
          if (K.empty() || ownerTypes.count(K.substr(0, K.rfind('+')))) continue;
          if (bodyWrites.count(K)) continue;
          // A body read of a closed cursor field discharges O6 under the
          // listed instance premise (Fable 2026-10-16, Q-e): what it reads
          // is null or an element, whoever wrote it.
          const size_t mark = eoMark();
          const bool closed = cursorOpen.count(K) && cursorRead(K, L).empty();
          eoSettle(mark, closed);
          if (closed) {
            o6Cursor.insert(K);
            cursorUsed.insert(K);
            if (const std::string u = uncheckedOf(K, L); !u.empty()) uncheckedCursor.insert(u);
            continue;
          }
          bad6.insert(F->getName().str() + "." + K);
        }
    std::string o6 = bad6.empty() ? "O6 PASS" : "O6 FAIL(body reads an owner-written field:";
    for (const std::string &b : bad6) o6 += " " + b;
    if (!bad6.empty()) o6 += ")";
    if (bad6.empty() && !o6Cursor.empty()) {
      o6 += " (body reads of closed cursor fields:";
      for (const std::string &K : o6Cursor) o6 += " " + K;
      o6 += ", under the instance premise)";
    }
    C.obligations = {o1, o2, o3, o4, o6};
    const bool holds = sentOk && o1.rfind("O1 PASS", 0) == 0 && o2 == "O2 PASS" && o3.rfind("O3 PASS", 0) == 0 &&
                       o4 == "O4 PASS" && o6.rfind("O6 PASS", 0) == 0 && premiseFail.empty() && derefFail.empty();
    // A report block is checked and reported, never applied (plan 3.55 R3 D1).
    C.verified = holds && !C.report;
    if (C.verified) {
      const size_t ci = &C - &Ctx->Containers[0];
      if (containerBodies.size() <= ci) {
        containerBodies.resize(ci + 1);
        containerElemSources.resize(ci + 1);
        containerInherit.resize(ci + 1);
        containerCtors.resize(ci + 1);
        containerOwnerCtors.resize(ci + 1);
        containerCtorType.resize(ci + 1);
      }
      containerOwnerCtors[ci] = ownerFeeds;
      containerBodies[ci] = body;
      // The element mint's inputs: the body's element values (constructor
      // results: an indirect call through a closed code field), the
      // constructors with the argument the owner is passed at, and the
      // byte offsets the body writes on an element (from the element's
      // start; -1: a write at an offset not constant).
      std::set<int64_t> W;
      std::set<StructType *> bodyElemTypes; // the structs the body steps through on an element
      // Constructors first (the element bases below need them).
      for (const Function *F : body)
        for (const Instruction &I : instructions(*F))
          if (const auto *CB = dyn_cast<CallBase>(&I); CB && !CB->getCalledFunction())
            if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
              const std::string K = fieldKey(CL, CL->getPointerOperand());
              if (code.count(K) && !codeOpen.count(K))
                for (unsigned a = 0; a < CB->arg_size(); a++)
                  if (get(CB->getArgOperand(a)) == OWN)
                    for (const Function *T : codeTargets[K]) containerCtors[ci].emplace(T, a);
            }
      // An element base: in a constructor, its fresh blocks; elsewhere, a
      // constructor call's result (through casts and -O0 slots).
      auto elemBase = [&](const Value *A, const Function *F) {
        if (containerCtors[ci].count(F)) return (get(A) & FRS) != 0;
        A = A->stripPointerCasts();
        if (const auto *L = dyn_cast<LoadInst>(A); L && transientSlot(L->getPointerOperand()->stripPointerCasts())) {
          for (const User *U : L->getPointerOperand()->stripPointerCasts()->users())
            if (const auto *S2 = dyn_cast<StoreInst>(U))
              if (const auto *CB = dyn_cast<CallBase>(S2->getValueOperand()->stripPointerCasts());
                  CB && !CB->getCalledFunction())
                return true;
          return false;
        }
        const auto *CB = dyn_cast<CallBase>(A);
        return CB && !CB->getCalledFunction();
      };
      for (const Function *F : body)
        for (const Instruction &I : instructions(*F)) {
          if (const auto *CB = dyn_cast<CallBase>(&I); CB && !CB->getCalledFunction())
            if (const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts())) {
              const std::string K = fieldKey(CL, CL->getPointerOperand());
              if (code.count(K) && !codeOpen.count(K)) containerElemSources[ci].push_back(CB);
            }
          // A store, or a block write (memcpy/memset: every pointer-aligned
          // offset of its range), through an element.
          const Value *A = nullptr;
          int64_t len = 1;
          if (const auto *S = dyn_cast<StoreInst>(&I)) A = S->getPointerOperand();
          else if (const auto *MI = dyn_cast<MemIntrinsic>(&I)) {
            A = MI->getRawDest();
            const auto *LC = dyn_cast<ConstantInt>(MI->getLength());
            len = LC ? (int64_t)LC->getZExtValue() : -1;
          }
          if (!A) continue;
          A = A->stripPointerCasts();
          int64_t off = 0;
          bool known = len >= 0;
          StructType *stepT = nullptr; // the struct the step on the element base names
          while (const auto *G = dyn_cast<GEPOperator>(A)) {
            APInt Off(64, 0);
            if (G->accumulateConstantOffset(F->getParent()->getDataLayout(), Off)) off += Off.getSExtValue();
            else known = false;
            stepT = dyn_cast<StructType>(G->getSourceElementType());
            A = G->getPointerOperand()->stripPointerCasts();
          }
          if (!elemBase(A, F)) continue;
          if (stepT && stepT->hasName() && !containerCtors[ci].count(F)) bodyElemTypes.insert(stepT);
          if (!known) W.insert(-1);
          else if (len <= 1) W.insert(off);
          else
            for (int64_t w = off & ~int64_t(7); w < off + len; w += 8) W.insert(w);
        }
      containerInherit[ci].assign(W.begin(), W.end());
      // The row objects' layouts: each constructor's element is its fresh
      // block, of the constant size the block's call passes, typed by the
      // struct of that size its typed uses step through; the solver mints
      // one row object per element struct of a constructor fed to the
      // owner (Fable 2026-10-19), never one layout chosen among them. A
      // size not constant, or no struct of that size, refuses the mint.
      std::string sizeFail;
      StructType *elemT = nullptr;
      std::vector<StructType *> ctorTypes;
      // The struct analyzer's embedding table (transitive): base name ->
      // the structs that hold it at offset 0, with one IR type each.
      std::map<std::string, std::set<std::string>> embeds;
      std::map<std::string, StructType *> typeOf;
      Ctx->structAnalyzer.forEachContainer([&](const StructType *St, const Module *, const StructType *Ct, unsigned off) {
        if (off == 0 && St->hasName() && Ct->hasName()) {
          embeds[stripStructNameSuffix(St->getName()).str()].insert(stripStructNameSuffix(Ct->getName()).str());
          typeOf.emplace(stripStructNameSuffix(Ct->getName()).str(), const_cast<StructType *>(Ct));
        }
      });
      const DataLayout &EDL = Ctx->Modules.front().first->getDataLayout();
      for (const auto &[T, a] : containerCtors[ci]) {
        (void)a;
        // A carve on a new chunk (chunk + header: objalloc_alloc's new-chunk
        // path) has a chunk-relative size only; it is the same request as
        // the constructor's other path, so it fails only when no element of
        // this constructor has a constant size.
        std::string chunkRelative;
        bool measured = false;
        for (const Instruction &I : instructions(*T)) {
          // A constructor's element: a fresh call of its own (not another
          // constructor: a derived entry's newfunc calls its base's with the
          // block it allocated; not a certified pool's chunk), or a certified
          // pool carve (objalloc_alloc inlined at -O3), of a constant size.
          uint64_t sz = 0;
          if (const auto *CB = dyn_cast<CallBase>(&I)) {
            if (!CB->getType()->isPointerTy() || !(get(CB) & FRS)) continue;
            if (const Function *G = CB->getCalledFunction(); G && (body.count(G) || containerCtors[ci].count(G)))
              continue;
            if (poolChunk(CB)) continue;
            // Its size: the call's constant integer arguments (one; two
            // multiply, calloc's shape).
            uint64_t prod = 1;
            unsigned consts = 0;
            for (const Value *Arg : CB->args())
              if (const auto *K = dyn_cast<ConstantInt>(Arg); K && K->getBitWidth() >= 32) {
                prod *= K->getZExtValue();
                consts++;
              }
            if (consts == 0 || consts > 2) {
              sizeFail = T->getName().str() + ": " + valueText(CB);
              continue;
            }
            sz = prod;
          } else if (poolCarves.count(&I) && (get(&I) & FRS)) {
            auto zit = poolCarveSizes.find(&I);
            const auto *K = zit == poolCarveSizes.end() ? nullptr : dyn_cast_or_null<ConstantInt>(zit->second.n);
            if (!K) {
              if (zit != poolCarveSizes.end() && zit->second.chunk)
                chunkRelative = T->getName().str() + ": a carve of no constant size " + valueText(&I);
              else
                sizeFail = T->getName().str() + ": a carve of no constant size " + valueText(&I);
              continue;
            }
            sz = K->getZExtValue() * zit->second.scale;
          } else {
            continue;
          }
          // Its type: a struct of that size its derived values step through,
          // else a pointer local the constructor declares (structOfSize).
          StructType *found = structOfSize(&I, sz, T);
          // Last: the one struct of that size that holds a struct the body
          // steps through on an element at offset 0 (the struct analyzer's
          // embedding table).
          if (!found) {
            std::set<std::string> names;
            for (StructType *B : bodyElemTypes) {
              const std::string bn = stripStructNameSuffix(B->getName()).str();
              if (B->isSized() && EDL.getTypeAllocSize(B) == sz) names.insert(bn);
              for (const std::string &cn : embeds[bn])
                if (StructType *CT = typeOf[cn]; CT && CT->isSized() && EDL.getTypeAllocSize(CT) == sz) names.insert(cn);
            }
            if (names.size() == 1) found = typeOf.count(*names.begin()) && typeOf[*names.begin()]
                                                 ? typeOf[*names.begin()]
                                                 : StructType::getTypeByName(T->getContext(), "struct." + *names.begin());
          }
          if (!found) {
            sizeFail = T->getName().str() + ": no struct of " + std::to_string(sz) + " bytes at " + valueText(&I);
            continue;
          }
          measured = true;
          ctorTypes.push_back(found);
          if (auto &CTs = containerCtorType[ci][T]; std::find(CTs.begin(), CTs.end(), found) == CTs.end())
            CTs.push_back(found);
          if (!elemT || EDL.getTypeAllocSize(found) > EDL.getTypeAllocSize(elemT)) elemT = found;
        }
        if (!measured && !chunkRelative.empty() && sizeFail.empty()) sizeFail = chunkRelative;
      }
      // One object per element: every constructor's struct embeds the
      // smallest (the base entry) at offset 0, by the struct analyzer's
      // embedding table (transitive), so their fields at one offset are
      // the same bytes of one object.
      if (elemT && sizeFail.empty()) {
        // The base: a struct the body itself steps through on an element
        // that every constructor's struct is or embeds at offset 0.
        std::string baseName;
        for (StructType *B : bodyElemTypes) {
          const std::string bn = stripStructNameSuffix(B->getName()).str();
          bool all = true;
          for (StructType *T : ctorTypes) {
            const std::string n = stripStructNameSuffix(T->getName()).str();
            all &= n == bn || embeds[bn].count(n);
          }
          if (all) {
            baseName = bn;
            break;
          }
        }
        if (baseName.empty())
          sizeFail = "no struct the body steps through on an element is embedded at offset 0 of every constructor's"
                     " element (struct analyzer)";
      }
      // The report line's constructor types, before a refusal clears them.
      std::vector<std::string> cts; // by name: the map's order follows the heap
      for (const auto &[Fc, Ts] : containerCtorType[ci]) {
        std::string t;
        for (StructType *T : Ts) t += " " + T->getName().str() + " (" + std::to_string(EDL.getTypeAllocSize(T)) + " bytes)";
        cts.push_back(Fc->getName().str() + ":" + t);
      }
      std::sort(cts.begin(), cts.end());
      std::string ctl;
      for (const std::string &c : cts) ctl += (ctl.empty() ? "" : "; ") + c;
      // A body write at no constant element offset cannot be inherited
      // field by field: a container that mints (an ELEM(ret) row or a
      // constructor) is rejected.
      bool mintsHere = !containerCtors[ci].empty();
      for (const auto &[fn, R] : C.rows) mintsHere |= R.elem == -1;
      if (mintsHere && (W.count(-1) || !sizeFail.empty() || (!containerCtors[ci].empty() && !elemT))) {
        C.verified = false;
        C.obligations.push_back(W.count(-1) ? "mint FAIL(a body write into an element at no constant offset)"
                                            : "mint FAIL(element size unknown: " +
                                                  (sizeFail.empty() ? std::string("no constructor element") : sizeFail) + ")");
        containerBodies[ci].clear();
        containerElemSources[ci].clear();
        containerCtors[ci].clear();
        containerInherit[ci].clear();
        containerOwnerCtors[ci].clear();
        containerCtorType[ci].clear();
      }
      std::string ws;
      for (int64_t w : W) ws += " " + std::to_string(w);
      cline("  element mint: " + std::to_string(containerElemSources[ci].size()) + " element sources in the body, " +
            std::to_string(containerCtors[ci].size()) + " constructors (row objects by constructor type: " +
            (ctl.empty() ? std::string("none") : ctl) + "), inherited offsets {" + ws + " }");
      if (C.verified)
        for (const auto &[fn, R] : C.rows)
          if (auto it = byName.find(fn); it != byName.end() && R.ownerDeref < 0) containerRowOf[it->second] = {ci, R};
    }
    for (const std::string &l : sentLines) C.obligations.push_back(l);
    for (const auto &[fn, R] : C.rows) {
      if (R.role != CR::Pure) continue;
      auto it = byName.find(fn);
      if (it == byName.end()) continue;
      bool icall = false;
      for (const Instruction &I : instructions(*it->second))
        if (const auto *CB = dyn_cast<CallBase>(&I); CB && !CB->getCalledFunction() && !CB->isInlineAsm()) icall = true;
      if (icall) C.obligations.push_back("pure over icall: " + fn + " (checked after the solve, below)");
    }
    if (!sentOk) C.obligations.push_back("a sentinel failed: its loads count as another value (O2 FAIL)");
    std::string bl;
    {
      std::vector<std::string> bn;
      for (const Function *F : body) bn.push_back(F->getName().str());
      std::sort(bn.begin(), bn.end());
      for (const std::string &n : bn) bl += (bl.empty() ? "" : " ") + n;
    }
    cline(C.name + " (" + C.provenance + (C.report ? ", report" : "") + "): " + std::to_string(C.rows.size()) +
          " rows, body {" + bl + "}" +
          (missing.empty() ? "" : "; rows without a body here: " + missing) + "; owner types:" +
          [&] { std::string t; for (auto &x : ownerTypes) t += " " + x; return t; }() + "; " + std::to_string(handle.size()) +
          " handle fields, " + std::to_string(links.size()) + " link fields, " + std::to_string(code.size()) +
          " code fields (" + std::to_string(codeTargetCount) + " targets through closed code fields)");
    for (const std::string &o : C.obligations) cline("  " + o);
    // The assumptions a verdict rests on (Fable 2026-10-16: "VERIFIED under n
    // assumptions", each listed).
    for (const std::string &x : o1AssumeLines) cline(x);
    containerReport.insert(containerReport.end(), o1ReportLines.begin(), o1ReportLines.end());
    size_t nAssume = nO1Assume;
    for (const std::string &x : derefLines) cline("  row " + x);
    for (const std::string &x : derefFail) cline("  row FAIL " + x);
    cursorInstance.insert(cursorUsed.begin(), cursorUsed.end());
    std::vector<std::string> cursorLineList;
    for (const auto &[K, x] : elemCursorLines) cursorLineList.push_back(x);
    std::sort(cursorLineList.begin(), cursorLineList.end());
    for (const std::string &x : cursorLineList) cline("  " + x);
    // The instance premise of the fields that ended closed (a provisional
    // closure, read while the field was under way, is no premise).
    for (auto it = cursorInstance.begin(); it != cursorInstance.end();)
      it = cursorOpen.count(*it) && cursorOpen[*it].empty() ? std::next(it) : cursorInstance.erase(it);
    for (const std::string &K : cursorInstance) {
      cline("    ASSUMPTION closed cursor " + K + ": the element stored there is of the same table instance");
      nAssume++;
    }
    for (const std::string &u : uncheckedCursor) { // of the fields that ended closed
      const std::string K = u.substr(0, u.find('\t'));
      if (!cursorOpen.count(K) || !cursorOpen[K].empty()) continue;
      cline("    ASSUMPTION closed cursor " + K + ": a read admitted by its own member's census key without a "
            "settling check (UNCHECKED): " + u.substr(u.find('\t') + 1));
      nAssume++;
    }
    for (const std::string &x : outParamAssumed) {
      cline("    ASSUMPTION element from a caller's out-parameter, assumed an element of the owner: " + x);
      nAssume++;
    }
    for (const std::string &x : holderInstance) {
      cline("    ASSUMPTION closed holder " + x + ": the element stored there is of the same table instance");
      nAssume++;
    }
    for (const std::string &x : holderAssumed) {
      cline("    ASSUMPTION a node read back from a holder, assumed an element: " + x);
      nAssume++;
    }
    for (const std::string &x : p3Assumed) {
      cline("    ASSUMPTION stores of other members excluded by their member name (a read of both schemes): " + x);
      nAssume++;
    }
    if (!localArraysRefused.empty())
      cline("  holders: " + std::to_string(localArraysRefused.size()) +
            " locals pointing to a fresh block are no holder (another pointer stored to them too)");
    if (!derefReadChecked.empty() || !derefReadAssumed.empty()) {
      cline("  deref owner read at a row call, one value with a read of the slot (S6): " +
            std::to_string(derefReadChecked.size()) + " checked, " + std::to_string(derefReadAssumed.size()) +
            " ASSUMPTION");
      for (const std::string &x : derefReadAssumed) {
        cline("    ASSUMPTION deref owner read: " + x);
        nAssume++;
      }
    }
    {
      // S6: the re-reads owner code was identified by (here and in the
      // owner shapes), checked or assumed.
      std::map<const LoadInst *, Reread> rr;
      for (const Value *V : rereadLoads)
        if (const auto *L = dyn_cast<LoadInst>(V))
          if (const Reread r = sameRead(L, 0); r.first) rr.emplace(L, r);
      for (auto &[L, r] : rereadsUsed) rr.emplace(L, r);
      size_t assumed = 0, across = 0;
      for (auto &[L, r] : rr) assumed += r.assumed, across += r.across;
      if (!rr.empty()) {
        cline("  owner re-read from the same slot (S6): " + std::to_string(rr.size() - assumed) +
              " checked (every write between them named, none of the slot's name), " + std::to_string(assumed) +
              " ASSUMPTION; " + std::to_string(across) + " across branches (read at the nearest common dominator)");
        std::vector<std::string> sites;
        for (auto &[L, r] : rr)
          if (r.assumed)
            sites.push_back(L->getFunction()->getName().str() + ": " + valueText(L) + " (first read " + valueText(r.first) +
                            (r.across ? ", across branches)" : ")"));
        std::sort(sites.begin(), sites.end());
        for (const std::string &x : sites) cline("    ASSUMPTION owner re-read from the same slot: " + x);
        nAssume += assumed;
      }
    }
    if (declared) {
      // Declared storage (R3 D2): the slots, what wrote them, what failed.
      auto list = [](const std::set<std::string> &s) {
        std::string r;
        for (const std::string &x : s) r += " " + x;
        return r.empty() ? std::string(" none") : r;
      };
      cline("  storage (" + C.provenance + ", declared): handle" + list(declHandle) + "; link" + list(declLink) +
            "; link word" + list(declWord) + "; unused declared storage" + list(unusedDecl));
      std::string adm;
      for (auto &[k, n] : o1Admit) adm += (adm.empty() ? "" : ", ") + k + " " + std::to_string(n);
      cline("  storage writes admitted: " + (adm.empty() ? std::string("none") : adm));
      if (!unionStorage.empty()) {
        cline("  storage inside a union (a declared slot in the IR's member, which is clang's representative; "
              "counted, not a write of the slot): " + std::to_string(unionStorage["writes"]) + " writes");
        for (const std::string &u : unionSites) cline("    " + u);
      }
      for (const std::string &u : plainFieldSites) cline("    an element pointer kept in a plain field: " + u);
      for (auto &[why, sites] : o1Fail) {
        cline("  storage FAIL " + why + (sites.empty() ? std::string() : ": " + std::to_string(sites.size()) + " sites"));
        for (size_t i = 0; i < sites.size() && i < 8; i++) cline("    " + sites[i]);
      }
      for (const std::string &w : wordLines) cline("  " + w);
      if (premiseOwnerT || premiseElemT) {
        cline("  row premise (1c): owner " +
              (premiseOwnerT ? stripStructNameSuffix(premiseOwnerT->getName()).str() : std::string("none")) +
              ", element " + (premiseElemT ? stripStructNameSuffix(premiseElemT->getName()).str() : std::string("none")) +
              "; " + std::to_string(premiseArgs) + " call-site arguments: " + std::to_string(premiseAgree) + " agree (" +
              std::to_string(premiseByBase) + " named by a base plus a byte offset, " +
              std::to_string(premiseUnionDI.size()) + " through a union member by debug info), " +
              std::to_string(premiseFail.size()) + " disagree (FAIL), " + std::to_string(premiseUnion.size()) +
              " inside a union (members not in the IR: ASSUMPTION), " + std::to_string(premisePast.size()) +
              " a step past the layout of a named base (ASSUMPTION), " + std::to_string(premiseAssume.size()) +
              " named by nothing (ASSUMPTION), " + std::to_string(premiseNull) + " null");
        for (const std::string &s : premiseFail) cline("    premise FAIL: " + s);
        for (const std::string &s : premiseUnionDI) cline("    premise through a union member: " + s);
        for (const std::string &s : premiseUnion) cline("    ASSUMPTION premise, inside a union: " + s);
        for (const std::string &s : premisePast) cline("    ASSUMPTION premise, a step past the layout of " + s);
        for (const std::string &s : premiseAssume) cline("    ASSUMPTION premise: " + s);
        for (const std::string &s : tableDisagree)
          cline("    embedding table disagrees with the IR layout walk: " + s);
      }
      cline("  owner code: " + std::to_string(rowSites) + " row call sites outside the body, " +
            std::to_string(ownerValues.size()) + " owner values (SSA value or GEP shape, per function); implicit inserts " +
            std::to_string(implicitMatched.size()) + " matched, " + std::to_string(implicitUnmatched.size()) +
            " unmatched; " + std::to_string(lookupsByDerivation) + " lookups by derivation");
      for (size_t i = 0; i < implicitMatched.size() && i < 8; i++) cline("    implicit insert matched: " + implicitMatched[i]);
      for (size_t i = 0; i < implicitUnmatched.size() && i < 8; i++)
        cline("    implicit insert UNMATCHED: " + implicitUnmatched[i]);
      // Every listing sorted: one input gives one report text whatever the
      // binary's heap layout (groups and bodies are keyed by pointer).
      for (std::vector<std::string> *L : {&formalNodeSites, &formalObjSites, &cursorAssumed, &linkInvariant,
                                          &traverseJoined})
        std::sort(L->begin(), L->end());
      if (!linkInvariant.empty()) {
        cline("  inlined removes: " + std::to_string(linkInvariant.size()) +
              " nodes assumed elements by their link reads (the link invariant, the remove row's ELEM premise)");
        for (const std::string &x : linkInvariant)
          cline("    ASSUMPTION inlined remove: node assumed an element by its parent word: " + x);
      }
      if (!traverseJoined.empty()) {
        cline("  traverse elements joined to the function's only owner group: " + std::to_string(traverseJoined.size()));
        for (const std::string &x : traverseJoined)
          cline("    ASSUMPTION traverse element joined the function's only owner group: " + x);
      }
      if (!unionSlotActuals.empty()) {
        cline("  slots at a union actual (S5): " + std::to_string(unionSlotAddrs) + " addresses, " +
              std::to_string(unionSlotActuals.size()) + " actuals");
        for (const std::string &x : unionSlotActuals)
          cline("    ASSUMPTION (the premise's) declared slots at a union actual + k: " + x);
      }
      if (!formalNodeSites.empty()) {
        cline("  descents from a node assumed an element (S7): " + std::to_string(formalNodeSites.size()));
        for (const std::string &x : formalNodeSites) cline("    ASSUMPTION descent from a node assumed an element: " + x);
      }
      if (!formalObjSites.empty()) {
        cline("  descents from a formal object's node at +e (Q1): " + std::to_string(formalObjSites.size()));
        for (const std::string &x : formalObjSites)
          cline("    ASSUMPTION descent from a formal object's node at +e, assumed an element: " + x);
      }
      if (!cursorLines.empty()) {
        cline("  cursor fields (S7): " + std::to_string(cursorLines.size()) + "; reads assumed " +
              std::to_string(cursorAssumed.size()));
        for (const std::string &x : cursorLines) cline("    cursor field " + x);
        for (size_t i = 0; i < cursorAssumed.size() && i < 8; i++)
          cline("    ASSUMPTION a node read back from a plain field: " + cursorAssumed[i]);
      }
      if (!o1Naming.empty()) {
        size_t past = 0;
        for (const std::string &n : o1Naming) past += n.find("(a step past the layout of ") != std::string::npos;
        cline("  naming FAIL: " + std::to_string(o1Naming.size()) +
              " accesses through owner or element values that no rule names (" + std::to_string(past) +
              " a step past the layout of a named base)");
        for (size_t i = 0; i < o1Naming.size() && i < 8; i++) cline("    " + o1Naming[i]);
      }
    }
    // Verdicts are per binary: the body's optimization level with each
    // (clang -O0 marks every function optnone).
    size_t optnone = 0;
    for (const Function *F : body) optnone += F->hasOptNone();
    const std::string level = optnone == body.size() ? "the body at -O0"
                              : optnone == 0         ? "the body optimized"
                                                     : "the body partly at -O0";
    cline(std::string("  ") +
          (C.report ? (holds ? "REPORT ONLY: the obligations hold (rows not applied)"
                             : "REPORT ONLY: the obligations fail (rows not applied)")
                    : C.verified ? (nAssume ? "VERIFIED under " + std::to_string(nAssume) + " assumptions (rows applied)"
                                            : std::string("VERIFIED (rows applied)"))
                                 : "REJECTED (rows not applied)") +
          "; " + level);
  }
  if (!Ctx->Containers.empty())
    CG_LOG("Container: anonymous struct fields: " << pointees.anonByEnclosing << " lookups ("
           << pointees.anonByEnclosingAt.size()
           << " distinct instructions) named by the enclosing named struct and byte offset, "
           << pointees.anonUnnamedN << " lookups (" << pointees.anonUnnamedAt.size()
           << " distinct instructions) unnamed (no enclosing named struct on the access's GEP chain)\n");
}

// After the solve: a pure row's indirect calls (Fable 2026-10-14) take the
// solver's resolved targets; no target, or every target pure (no pointer
// store, no block copy, no indirect call of its own), keeps the premise;
// otherwise the premise is broken and the rows applied are reported as
// such (the answers for the container's owners rest on it).
void CallGraphPass::checkContainerPremises(bool stopped) {
  for (size_t ci = 0; ci < Ctx->Containers.size(); ci++) {
    auto &C = Ctx->Containers[ci];
    if (!C.verified) continue;
    for (const auto &[fn, R] : C.rows) {
      if (R.role != GlobalContext::ContainerRow::Pure) continue;
      const Function *F = nullptr;
      for (auto &[M, _] : Ctx->Modules)
        if (const Function *G = M->getFunction(fn); G && !G->isDeclaration()) F = G;
      if (!F) continue;
      for (const Instruction &I : instructions(*F)) {
        const auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->getCalledFunction() || CB->isInlineAsm()) continue;
        std::string ts, bad;
        auto it = Ctx->Callees.find(const_cast<CallBase *>(CB));
        if (it != Ctx->Callees.end())
          for (const Function *T : it->second) {
            ts += (ts.empty() ? "" : " ") + T->getName().str();
            for (const Instruction &J : instructions(*T)) {
              const auto *S = dyn_cast<StoreInst>(&J);
              const auto *JC = dyn_cast<CallBase>(&J);
              if ((S && containsPointerType(S->getValueOperand()->getType())) || isa<MemTransferInst>(&J) ||
                  (JC && !JC->getCalledFunction() && !JC->isInlineAsm()))
                bad = T->getName().str() + ": " + valueText(&J);
            }
          }
        const std::string l = "pure over icall: " + fn + " " + valueText(CB) + ": targets {" +
                              (ts.empty() ? std::string("no target") : ts) + "} " +
                              (bad.empty() ? "PASS" : "FAIL(" + bad + "): the premise is broken; the rows were applied") +
                              (stopped ? " (at a stop: the targets are not final; no number from this run)" : "");
        CG_LOG("Container: " << C.name << ": " << l << "\n");
        if (std::find(containerReport.begin(), containerReport.end(), C.name + ": " + l) == containerReport.end())
          containerReport.push_back(C.name + ": " + l);
      }
    }
  }
}

