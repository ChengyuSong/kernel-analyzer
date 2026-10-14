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
#include <llvm/IR/Dominators.h>

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
  // A field access's key: its IR struct (linker suffix stripped) and offset.
  auto fieldKey = [&](const Instruction *I, const Value *Addr) -> std::string {
    if (isa<AllocaInst>(Addr->stripPointerCasts())) return "";
    StructType *S = nullptr;
    int64_t off = 0;
    if (!accessSlot(I, Addr, I->getModule()->getDataLayout(), S, off) || !S || !S->hasName()) return "";
    return stripStructNameSuffix(S->getName()).str() + "+" + std::to_string(off);
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
  auto closedField = [&](const std::string &K) {
    auto it = fields.find(K);
    return it == fields.end() || it->second.foreign.empty();
  };
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
  auto ptrMembers = [&](StringRef Tag) {
    std::vector<std::pair<uint64_t, std::string>> out;
    auto dit = diStructs.find(Tag.str());
    const DICompositeType *Cc = dit == diStructs.end() ? nullptr : dit->second;
    if (!Cc) return out;
    for (const DINode *E : Cc->getElements()) {
      const auto *M = dyn_cast<DIDerivedType>(E);
      if (!M || M->getTag() != dwarf::DW_TAG_member || M->isStaticMember()) continue;
      const DIType *T = diStrip(M->getBaseType());
      const auto *P = dyn_cast_or_null<DIDerivedType>(T);
      if (!P || P->getTag() != dwarf::DW_TAG_pointer_type) continue;
      const DIType *B = diStrip(P->getBaseType());
      if (const auto *P2 = dyn_cast_or_null<DIDerivedType>(B); P2 && P2->getTag() == dwarf::DW_TAG_pointer_type)
        B = diStrip(P2->getBaseType());
      const auto *S = dyn_cast_or_null<DICompositeType>(B);
      out.push_back({M->getOffsetInBits() / 8,
                     S && S->getTag() == dwarf::DW_TAG_structure_type ? S->getName().str() : std::string()});
    }
    return out;
  };
  for (auto &C : Ctx->Containers) {
    using CR = GlobalContext::ContainerRow;
    C.verified = false;
    C.obligations.clear();
    // The body: the row functions, and the functions only they call
    // (direct calls only, address never taken), to a fixpoint.
    std::set<const Function *> body;
    std::string missing;
    for (const auto &[fn, R] : C.rows) {
      if (R.role == CR::Pure || R.role == CR::Carve) continue;
      auto it = byName.find(fn);
      if (it == byName.end()) missing += (missing.empty() ? "" : ", ") + fn;
      else body.insert(it->second);
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
      if (R.owner < 0) continue;
      auto it = byName.find(fn);
      if (it == byName.end()) continue;
      const DISubprogram *SP = it->second->getSubprogram();
      const DISubroutineType *ST = SP ? SP->getType() : nullptr;
      if (ST && (unsigned)R.owner + 1 < ST->getTypeArray().size())
        if (const StringRef N = ka::diStructName(ST->getTypeArray()[R.owner + 1], true); !N.empty())
          ownerTypes.insert("struct." + N.str());
    }
    // O1: every data pointer field of an owner type the body reads or
    // writes is closed (a field whose loads are called is a code field:
    // O4's).
    std::set<std::string> handle, code, open1;
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
    for (const std::string &K : code) {
      std::set<const Function *> T;
      for (const StoreInst *S : fields[K].allSI) {
        std::set<const Argument *> onStack;
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
      if (auto it = byName.find(fn); it != byName.end() && body.count(it->second) && R.owner >= 0)
        ownerIdx[it->second] = R.owner;
    auto rowOf = [&](const Function *G) -> const CR * {
      auto it = G ? C.rows.find(G->getName().str()) : C.rows.end();
      return it == C.rows.end() ? nullptr : &it->second;
    };
    auto get = [&](const Value *V) -> uint8_t {
      V = V->stripPointerCasts();
      if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) return NUL;
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
    auto transfer = [&](const Instruction &I) -> uint8_t {
      if (poolCarves.count(&I)) return FRS; // a certified pool carve: a fresh block
      if (const auto *L = dyn_cast<LoadInst>(&I)) {
        const Value *B = baseOf(L->getPointerOperand());
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
        const std::string K = fieldKey(L, L->getPointerOperand());
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
        if (b & (INS | OTH | PAY)) m |= OTH;
        return m ? m : (b ? OTH : 0);
      }
      if (isa<GetElementPtrInst>(&I) || isa<CastInst>(&I)) return get(I.getOperand(0));
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
      for (const Function *F : body) {
        auto oit = ownerIdx.find(F);
        for (const Argument &A : F->args())
          if (A.getType()->isPointerTy() && oit != ownerIdx.end() && (int)A.getArgNo() == oit->second) join(&A, OWN);
        // An insert row's ELEM(argN): the element coming in (O3 checks it
        // goes only into the owner's storage), like a new element.
        if (const CR *R = rowOf(F); R && R->role == CR::Insert && R->elem >= 0 && (unsigned)R->elem < F->arg_size())
          join(F->getArg(R->elem), FRS);
        for (const Instruction &I : instructions(*F)) {
          if (I.getType()->isPointerTy()) join(&I, transfer(I));
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
    std::function<std::string(const Value *, int)> ownerShape = [&](const Value *V, int d) -> std::string {
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
      if (const auto *G = dyn_cast<GEPOperator>(V)) {
        APInt Off(64, 0);
        if (!G->accumulateConstantOffset(DL0, Off)) return "";
        const std::string b = ownerShape(G->getPointerOperand(), d + 1);
        return b.empty() ? "" : b + "+" + std::to_string(Off.getSExtValue());
      }
      std::string t;
      raw_string_ostream os(t);
      os << (const void *)V;
      return os.str();
    };
    // Outside the body: the owner a value is an element of (a row's or a
    // constructor's result, through casts, slots stored once and constant
    // steps); "" if none.
    std::function<std::string(const Value *, int)> elemOwner = [&](const Value *V, int d) -> std::string {
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
          return only ? elemOwner(only->getValueOperand(), d + 1) : "";
        }
      if (const auto *G = dyn_cast<GEPOperator>(V)) return elemOwner(G->getPointerOperand(), d + 1);
      const auto *CB = dyn_cast<CallBase>(V);
      const Function *G = CB ? CB->getCalledFunction() : nullptr;
      if (!G) return "";
      if (const CR *R = rowOf(G); R && R->owner >= 0 && (R->role == CR::Lookup || R->role == CR::Insert) &&
                                  R->elem == -1 && (unsigned)R->owner < CB->arg_size())
        return ownerShape(CB->getArgOperand(R->owner), 0);
      if (auto cit = ctorsHere.find(G); cit != ctorsHere.end() && cit->second < CB->arg_size())
        return ownerShape(CB->getArgOperand(cit->second), 0);
      return "";
    };
    std::vector<std::string> inlineSites;
    auto isInlineMove = [&](const StoreInst *S) {
      if (body.count(S->getFunction())) return false;
      const std::string a = elemOwner(baseOf(S->getPointerOperand()), 0), v = elemOwner(S->getValueOperand(), 0);
      if (a.empty() || a != v) return false;
      inlineSites.push_back(S->getFunction()->getName().str() + ": " + valueText(S));
      return true;
    };
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
    size_t copiesInto = 0;
    std::string badCopy;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (const Instruction &I : instructions(F)) {
          const auto *MT = dyn_cast<MemTransferInst>(&I);
          if (!MT) continue;
          const std::string K = fieldKey(MT, MT->getRawDest());
          if (K.empty()) continue;
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
          copiesInto++;
          if (body.count(&F)) {
            const uint8_t src = get(baseOf(MT->getRawSource())) & ~NUL;
            if (src && !(src & ~(DER | FRS))) continue;
          } else {
            const std::string a = elemOwner(MT->getRawDest(), 0), v = elemOwner(MT->getRawSource(), 0);
            if (!a.empty() && a == v) {
              inlineSites.push_back(F.getName().str() + ": " + valueText(MT));
              continue;
            }
          }
          if (badCopy.empty()) badCopy = F.getName().str() + ": " + valueText(MT);
        }
    if (!badCopy.empty()) open1.insert("an element copied from another value [" + badCopy + "]");
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
              if (b && !(b & ~(OWN | DER | FRS))) continue; // into the owner's storage (or a new element)
              bad3.insert(fn + ": stored into " + valueText(S));
              continue;
            }
            if (const auto *CB = dyn_cast<CallBase>(UI)) {
              const Function *G = CB->getCalledFunction();
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
    for (const auto &[fn, R] : C.rows) {
      auto it = byName.find(fn);
      if (it == byName.end() || !body.count(it->second)) continue;
      const Function *F = it->second;
      if (R.role == CR::Lookup || R.role == CR::Traverse)
        for (const Instruction &I : instructions(*F))
          if (const auto *RI = dyn_cast<ReturnInst>(&I); RI && RI->getReturnValue() &&
                                                         RI->getReturnValue()->getType()->isPointerTy()) {
            const uint8_t m = get(RI->getReturnValue());
            if (!m || (m & ~(NUL | DER | PAY | INS)))
              bad2.insert(fn + " returns " + valueText(RI->getReturnValue()) + " (" + std::to_string(m) + ")");
          }
      if (R.role == CR::Insert || (R.role == CR::Lookup && R.create >= 0 && R.elem == -1)) {
        std::set<const Value *> seen;
        if (R.elem >= 0 && (unsigned)R.elem < F->arg_size()) elemUses(F->getArg(R.elem), fn, seen);
        if (R.elem == -1)
          for (const Instruction &I : instructions(*F))
            if (const auto *RI = dyn_cast<ReturnInst>(&I); RI && RI->getReturnValue())
              if (const auto *D = dyn_cast<Instruction>(RI->getReturnValue()->stripPointerCasts()))
                elemUses(D, fn, seen);
      }
    }
    // Every fresh block the body makes goes only into the owner's storage
    // (a new element, a key copy), so a store into one is a store into
    // the container.
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        if (isa<CallBase>(&I) && I.getType()->isPointerTy() && get(&I) == FRS) {
          std::set<const Value *> seen;
          elemUses(&I, F->getName().str() + " (a fresh block)", seen);
        }
    std::string o2 = bad2.empty() ? "O2 PASS" : "O2 FAIL(";
    for (const std::string &b : bad2) o2 += (o2.back() == '(' ? "" : "; ") + b;
    if (!bad2.empty()) o2 += ")";
    std::string o3 = bad3.empty() ? "O3 PASS" : "O3 FAIL(";
    for (const std::string &b : bad3) o3 += (o3.back() == '(' ? "" : "; ") + b;
    if (!bad3.empty()) o3 += ")";
    if (moves) o1 += " (" + std::to_string(moves) + " element moves within one owner)";
    // O6 (body reads): every pointer field of an element the body reads
    // is one the body writes (a body read of an owner-written field would
    // see the body's object without the owner's writes).
    std::set<std::string> bodyWrites, bad6;
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        if (const auto *S = dyn_cast<StoreInst>(&I))
          if (const std::string K = fieldKey(S, S->getPointerOperand()); !K.empty()) bodyWrites.insert(K);
    for (const Function *F : body)
      for (const Instruction &I : instructions(*F))
        if (const auto *L = dyn_cast<LoadInst>(&I); L && L->getType()->isPointerTy()) {
          const uint8_t b = get(baseOf(L->getPointerOperand())) & ~NUL;
          if (!(b & (DER | FRS))) continue;
          const std::string K = fieldKey(L, L->getPointerOperand());
          if (K.empty() || ownerTypes.count(K.substr(0, K.rfind('+')))) continue;
          if (!bodyWrites.count(K)) bad6.insert(F->getName().str() + "." + K);
        }
    std::string o6 = bad6.empty() ? "O6 PASS" : "O6 FAIL(body reads an owner-written field:";
    for (const std::string &b : bad6) o6 += " " + b;
    if (!bad6.empty()) o6 += ")";
    C.obligations = {o1, o2, o3, o4, o6};
    C.verified = sentOk && o1.rfind("O1 PASS", 0) == 0 && o2 == "O2 PASS" && o3 == "O3 PASS" && o4 == "O4 PASS" &&
                 o6 == "O6 PASS";
    if (C.verified) {
      const size_t ci = &C - &Ctx->Containers[0];
      if (containerBodies.size() <= ci) {
        containerBodies.resize(ci + 1);
        containerElemSources.resize(ci + 1);
        containerInherit.resize(ci + 1);
        containerCtors.resize(ci + 1);
      }
      containerBodies[ci] = body;
      // The element mint's inputs: the body's element values (constructor
      // results: an indirect call through a closed code field), the
      // constructors with the argument the owner is passed at, and the
      // byte offsets the body writes on an element (from the element's
      // start; -1: a write at an offset not constant).
      std::set<int64_t> W;
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
          while (const auto *G = dyn_cast<GEPOperator>(A)) {
            APInt Off(64, 0);
            if (G->accumulateConstantOffset(F->getParent()->getDataLayout(), Off)) off += Off.getSExtValue();
            else known = false;
            A = G->getPointerOperand()->stripPointerCasts();
          }
          if (!elemBase(A, F)) continue;
          if (!known) W.insert(-1);
          else if (len <= 1) W.insert(off);
          else
            for (int64_t w = off & ~int64_t(7); w < off + len; w += 8) W.insert(w);
        }
      containerInherit[ci].assign(W.begin(), W.end());
      // A body write at no constant element offset cannot be inherited
      // field by field: a container that mints (an ELEM(ret) row or a
      // constructor) is rejected.
      bool mintsHere = !containerCtors[ci].empty();
      for (const auto &[fn, R] : C.rows) mintsHere |= R.elem == -1;
      if (mintsHere && W.count(-1)) {
        C.verified = false;
        C.obligations.push_back("mint FAIL(a body write into an element at no constant offset)");
        containerBodies[ci].clear();
        containerElemSources[ci].clear();
        containerCtors[ci].clear();
        containerInherit[ci].clear();
      }
      std::string ws;
      for (int64_t w : W) ws += " " + std::to_string(w);
      cline("  element mint: " + std::to_string(containerElemSources[ci].size()) + " element sources in the body, " +
            std::to_string(containerCtors[ci].size()) + " constructors, inherited offsets {" + ws + " }");
      if (C.verified)
        for (const auto &[fn, R] : C.rows)
          if (auto it = byName.find(fn); it != byName.end()) containerRowOf[it->second] = {ci, R};
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
    for (const Function *F : body) bl += (bl.empty() ? "" : " ") + F->getName().str();
    cline(C.name + " (" + C.provenance + "): " + std::to_string(C.rows.size()) + " rows, body {" + bl + "}" +
          (missing.empty() ? "" : "; rows without a body here: " + missing) + "; owner types:" +
          [&] { std::string t; for (auto &x : ownerTypes) t += " " + x; return t; }() + "; " + std::to_string(handle.size()) +
          " handle fields, " + std::to_string(links.size()) + " link fields, " + std::to_string(code.size()) +
          " code fields (" + std::to_string(codeTargetCount) + " targets through closed code fields)");
    for (const std::string &o : C.obligations) cline("  " + o);
    cline(std::string("  ") + (C.verified ? "VERIFIED (rows applied)" : "REJECTED (rows not applied)"));
  }
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

