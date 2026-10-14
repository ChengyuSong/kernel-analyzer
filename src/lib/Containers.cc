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

  struct FieldState {
    size_t fed = 0, nulls = 0, restores = 0, loads = 0;
    std::vector<std::string> foreign;                   // stores of another value (examples)
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
        if (const Value *C = freshOf(V, 0)) {
          fields[K].fed++;
          feeds.push_back({K, C});
        } else if (const auto *VC = dyn_cast<CallBase>(V->stripPointerCasts())) {
          const Function *CF = VC->getCalledFunction();
          calledFeeds[K][CF ? CF->getName().str() : std::string("an indirect call")]++;
          if (fields[K].foreign.size() < 3) fields[K].foreign.push_back(F.getName().str() + ": " + valueText(SI));
          else fields[K].foreign.push_back("");
        } else if (isa<ConstantPointerNull>(V->stripPointerCasts())) {
          fields[K].nulls++;
        } else if (reloadOf(V, K, ownerOf(SI->getPointerOperand()), 0)) {
          fields[K].restores++;
        } else if (fields[K].foreign.size() < 3) {
          fields[K].foreign.push_back(F.getName().str() + ": " + valueText(SI));
        } else {
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
}
