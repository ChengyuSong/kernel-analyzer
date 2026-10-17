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
  // A field access's key: its IR struct (linker suffix stripped) and offset,
  // named by its struct GEP or TBAA tag, an array member at a variable index,
  // or at offset 0 with neither by the address's pointee (one naming rule
  // with the link words, plan 3.55 R3 D3).
  PointeeResolver pointees(Ctx);
  auto fieldKey = [&](const Instruction *I, const Value *Addr) -> std::string {
    if (isa<AllocaInst>(Addr->stripPointerCasts())) return "";
    StructType *S = nullptr;
    int64_t off = 0;
    if (!namedSlot(I, Addr, I->getModule()->getDataLayout(), pointees, S, off) || !S || !S->hasName()) return "";
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
  containerElemType.clear();
  containerOwnerCtors.clear();
  containerCtorType.clear();
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
      if (isa<AllocaInst>(A->stripPointerCasts())) return "";
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
    std::vector<std::string> derefReadChecked;
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
      else derefReadChecked.push_back(site);
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
      size_t stores = 0, others = 0, unkeyed = 0, wholeCopies = 0;
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
        }
      };
      for (auto &[M, _] : Ctx->Modules)
        for (const Function &F : *M)
          for (const Instruction &I : instructions(F)) {
            if (!why.empty()) break;
            if (const auto *S = dyn_cast<StoreInst>(&I)) {
              if (!S->getValueOperand()->getType()->isPointerTy() || fieldKey(S, S->getPointerOperand()) != K) continue;
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
                                              ")"
                                        : "not closed (" + why + ")");
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
            if (badCopy.empty()) badCopy = F.getName().str() + ": " + valueText(MT);
          }
      if (!badCopy.empty()) open1.insert("an element copied from another value [" + badCopy + "]");
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
        containerElemType.resize(ci + 1, nullptr);
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
      // The row object's layout: each constructor's element is its fresh
      // block, of the constant size the block's call passes, typed by the
      // struct of that size its typed uses step through; the row object
      // takes the largest (they share the base entry as a prefix, so two
      // constructors' fields at one offset are the same bytes of one
      // object). A size not constant, or no struct of that size, refuses
      // the mint.
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
          // Its type: a struct of that size its derived values step through.
          StructType *found = nullptr;
          SmallVector<const Value *, 8> w{&I};
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
          if (StructType *&CT = containerCtorType[ci][T]; !CT || EDL.getTypeAllocSize(found) > EDL.getTypeAllocSize(CT))
            CT = found;
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
      containerElemType[ci] = elemT;
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
        containerElemType[ci] = nullptr;
        containerOwnerCtors[ci].clear();
        containerCtorType[ci].clear();
      }
      std::string ws;
      for (int64_t w : W) ws += " " + std::to_string(w);
      cline("  element mint: " + std::to_string(containerElemSources[ci].size()) + " element sources in the body, " +
            std::to_string(containerCtors[ci].size()) + " constructors (row objects laid out as " +
            (elemT ? elemT->getName().str() + ", " + std::to_string(EDL.getTypeAllocSize(elemT)) + " bytes"
                   : std::string("none")) +
            "), inherited offsets {" + ws + " }");
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
    size_t nAssume = 0;
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
      std::sort(derefReadChecked.begin(), derefReadChecked.end());
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
    CG_LOG("Container: anonymous struct fields: " << pointees.anonByEnclosing
           << " named by the enclosing named struct and byte offset, " << pointees.anonUnnamedN
           << " unnamed (no enclosing named struct on the access's GEP chain)\n");
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

