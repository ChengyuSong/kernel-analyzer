/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// Census.cc: measurement-only censuses (add no edges).
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"
#include <llvm/BinaryFormat/Dwarf.h>

static std::map<std::string, size_t> g_sinkEscapeSinks; // sink -> sites
                                   // (tag-bit-only local closures)
// Ground-truth type census (--cfl-gt-type-census): each input line is a
// dynamically OBSERVED dispatch "frame1;frame2;... target" (inline chain
// -> callee). We test our isCompatible rules against reality: a record
// whose frame functions contain indirect callsites but where NO site
// accepts the target is a WITNESSED type-filter unsoundness — a
// runtime-true pair the filter would reject. This cannot prove the
// filter sound (GT covers one config/workload); it can only convict.
void CallGraphPass::runGTTypeCensus(const std::string &path) {
  std::unordered_map<std::string, std::vector<const Function *>> defs;
  for (auto &mp : Ctx->Modules)
    for (Function &F : *mp.first)
      if (!F.isDeclaration() && !F.empty())
        defs[F.getName().str()].push_back(&F);
  std::unordered_map<const Function *, std::vector<const CallBase *>>
      siteCache;
  auto sitesOf =
      [&](const Function *F) -> const std::vector<const CallBase *> & {
    auto [it, ins] = siteCache.emplace(F, std::vector<const CallBase *>{});
    if (ins)
      for (const Instruction &I :
           instructions(*const_cast<Function *>(F)))
        if (const auto *CB = dyn_cast<CallBase>(&I))
          if (!CB->getCalledFunction() && !CB->isInlineAsm() &&
              !isa<Function>(
                  CB->getCalledOperand()->stripPointerCastsAndAliases()))
            it->second.push_back(CB);
    return it->second;
  };
  std::ifstream in(path);
  if (!in) {
    errs() << "GT-TYPE census: cannot open " << path << "\n";
    exit(1);
  }
  std::string line;
  size_t total = 0, ok = 0, viol = 0, nosite = 0, nocaller = 0, notgt = 0;
  while (std::getline(in, line)) {
    if (line.empty())
      continue;
    auto sp = line.rfind(' ');
    if (sp == std::string::npos)
      continue;
    std::string chain = line.substr(0, sp), tgt = line.substr(sp + 1);
    total++;
    auto dIt = defs.find(tgt);
    if (dIt == defs.end()) {
      notgt++;
      continue;
    }
    bool compat = false, anyCaller = false;
    size_t nSites = 0;
    size_t pos = 0;
    while (pos <= chain.size() && !compat) {
      size_t e = chain.find(';', pos);
      std::string frame =
          chain.substr(pos, e == std::string::npos ? std::string::npos
                                                   : e - pos);
      pos = (e == std::string::npos) ? chain.size() + 1 : e + 1;
      auto fIt = defs.find(frame);
      if (fIt == defs.end())
        continue;
      anyCaller = true;
      for (const Function *FF : fIt->second) {
        for (const CallBase *CB : sitesOf(FF)) {
          nSites++;
          for (const Function *TF : dIt->second)
            if (isCompatible(CB, TF)) {
              compat = true;
              break;
            }
          if (compat)
            break;
        }
        if (compat)
          break;
      }
    }
    if (!anyCaller) {
      nocaller++;
      continue;
    }
    if (compat)
      ok++;
    else if (nSites == 0) {
      nosite++;
      errs() << "GT-TYPE NO-ICALL-IN-FRAMES " << line << "\n";
    } else {
      viol++;
      errs() << "GT-TYPE VIOLATION (" << nSites << " sites tried) " << line
             << "\n";
    }
  }
  errs() << "GT-TYPE CENSUS: " << total << " records: " << ok
         << " type-compatible, " << viol << " VIOLATIONS (runtime-true, "
         << "type-rejected everywhere in-frame), " << nosite
         << " no-icall-in-frames (devirt/inlined), " << nocaller
         << " caller-absent, " << notgt << " target-absent\n";
}

// --cfl-census-nexus (task #38): DISCOVER nexus structs instead of
// guessing them. A nexus struct is one whose objects many subsystems
// write pointers into — under FI its single cell transitively couples
// them all (task_struct = the exemplar found via the coupler census).
// Static signal: for every store whose address is a GEP into a named
// struct type, record (type <- writing subsystem); rank by subsystem
// diversity, splitting pointer-valued stores (the coupling carriers)
// from all stores.
void CallGraphPass::runNexusCensus() {
  struct TypeStat {
    uint64_t ptrWriters = 0, allWriters = 0, readers = 0;
    size_t ptrStores = 0;
  };
  std::map<std::string, TypeStat> byType;
  for (auto &mp : Ctx->Modules) {
    const uint8_t sb = subsysBitOf(mp.first);
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      for (Instruction &I : instructions(F)) {
        const Value *addr = nullptr;
        bool isStore = false, ptrVal = false;
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          addr = SI->getPointerOperand();
          isStore = true;
          ptrVal = SI->getValueOperand()->getType()->isPointerTy();
        } else if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          addr = LI->getPointerOperand();
          ptrVal = LI->getType()->isPointerTy();
        } else {
          continue;
        }
        const auto *GO =
            dyn_cast<GEPOperator>(addr->stripPointerCasts());
        const StructType *ST =
            GO ? dyn_cast<StructType>(GO->getSourceElementType()) : nullptr;
        if (!ST || !ST->hasName())
          continue;
        auto &t = byType[sctCanonStructName(ST->getName()).str()];
        if (isStore) {
          t.allWriters |= 1ull << sb;
          if (ptrVal) {
            t.ptrWriters |= 1ull << sb;
            t.ptrStores++;
          }
        } else if (ptrVal) {
          t.readers |= 1ull << sb;
        }
      }
    }
  }
  std::vector<std::pair<int, const std::string *>> rk;
  for (auto &kv : byType)
    rk.emplace_back(__builtin_popcountll(kv.second.ptrWriters), &kv.first);
  std::sort(rk.begin(), rk.end(), std::greater<>());
  errs() << "NexusCensus: " << byType.size() << " struct types with "
         << "field traffic\n";
  for (size_t i = 0; i < std::min<size_t>(30, rk.size()); i++) {
    auto &t = byType[*rk[i].second];
    errs() << "NexusCensus: ptr-writers " << rk[i].first << " subsys, "
           << "readers " << __builtin_popcountll(t.readers)
           << " subsys, " << t.ptrStores << " ptr-stores  "
           << *rk[i].second << "\n";
  }
}


// Trace-payload read-back contract confirmer (task #32, design recorded
// at task #31 close). The sink model (--cfl-sink-instr) seals cluster
// joins at trace-payload cells — sound ONLY if nothing loaded back out
// of a payload cell ever feeds an indirect call. This pass machine-
// checks that contract at every payload accessor callsite:
//   ring_buffer_event_data — THE payload pointer accessor, both the
//     write path (trace_event_buffer_reserve fills fbuffer->entry) and
//     the read path (trace output iterators);
//   perf_trace_buf_alloc — the perf-side raw_data payload buffer.
// The returned pointer is walked as PTR (payload address: GEP/cast
// chains, phi/select); loads through PTR yield VAL (payload content),
// walked through casts/phis/arithmetic — with inttoptr(VAL) laundering
// re-entering as PTR. Verdicts per site:
//   VIOLATION — a tracked value IS an indirect call's called operand.
//     Sealing REFUSES to run (hard error), never silently degrades.
//   ESCAPE — the value leaves the local walk (pointer stored, e.g.
//     fbuffer->entry / iter->ent; passed to a non-intrinsic callee;
//     returned; walk cap). Inventoried by sink name for the documented
//     review — the contract holds for these by review, not by machine.
//   CONFIRMED — every use is a write into the payload, comparison,
//     GEP index / branch condition (the certified benign control
//     channel: data-indexed selection, soundly over-approximated by
//     including all table entries), or other local non-dispatch use.
void CallGraphPass::runSinkConfirmer() {
  // Accessor list shared with the arena planting in visitCallBase — the
  // contract this confirms and the model it gates must key identically.
  auto isPayloadAccessor = isSinkPayloadAccessor;
  enum Kind : char { PTR, VAL };
  size_t sites = 0;
  std::vector<std::string> violations;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      for (Instruction &I : instructions(F)) {
        const auto *Root = dyn_cast<CallBase>(&I);
        if (!Root || Root->isInlineAsm())
          continue;
        const auto *AF = dyn_cast<Function>(
            Root->getCalledOperand()->stripPointerCasts());
        if (!AF || !isPayloadAccessor(AF->getName()))
          continue;
        sites++;
        // Bounded forward walk from the payload pointer.
        SmallVector<std::pair<const Value *, Kind>, 32> wl;
        SmallPtrSet<const Value *, 32> seenP, seenV;
        std::set<std::string> escapes;
        bool violated = false;
        wl.push_back({Root, PTR});
        seenP.insert(Root);
        size_t steps = 0;
        while (!wl.empty()) {
          if (++steps > 768) { // explicit cap, never silent
            escapes.insert("walk-cap");
            break;
          }
          auto [V, k] = wl.pop_back_val();
          auto push = [&](const Value *N2, Kind nk) {
            auto &seen = nk == PTR ? seenP : seenV;
            if (seen.insert(N2).second)
              wl.push_back({N2, nk});
          };
          for (const User *U : V->users()) {
            if (const auto *CB = dyn_cast<CallBase>(U)) {
              if (CB->getCalledOperand()->stripPointerCasts() == V) {
                violated = true; // payload-derived value dispatched
                violations.push_back(
                    (F.getName() + " (" + AF->getName() + " site)").str());
                continue;
              }
              const auto *CF2 = dyn_cast<Function>(
                  CB->getCalledOperand()->stripPointerCasts());
              if (CF2 && CF2->isIntrinsic()) {
                // mem-write INTO the payload is the sink's purpose;
                // memcpy OUT of it exports the bytes — review item.
                if (const auto *MT = dyn_cast<MemTransferInst>(CB)) {
                  if (MT->getRawSource()->stripPointerCasts() == V)
                    escapes.insert("memcpy-out");
                  continue;
                }
                continue; // memset/dbg/lifetime/assume: benign
              }
              escapes.insert(CF2 ? CF2->getName().str()
                                 : std::string("<indirect-arg>"));
              continue;
            }
            if (const auto *LI = dyn_cast<LoadInst>(U)) {
              if (k == PTR || LI->getPointerOperand() == V)
                push(LI, VAL); // content read-back (or read through a
                               // content-derived pointer: conservative)
              continue;
            }
            if (const auto *SI = dyn_cast<StoreInst>(U)) {
              if (SI->getValueOperand() == V)
                escapes.insert(k == PTR ? "ptr-stored" : "val-stored");
              continue; // store INTO tracked memory: benign write
            }
            if (isa<IntToPtrInst>(U)) {
              push(U, PTR); // laundering: content becomes a pointer
              continue;
            }
            if (const auto *G2 = dyn_cast<GEPOperator>(U)) {
              if (G2->getPointerOperand() == V)
                push(U, k); // address arithmetic keeps the kind
              // V as INDEX: data-selected offset — certified benign
              // control channel (all table entries stay included)
              continue;
            }
            if (isa<CastInst>(U)) {
              push(U, k);
              continue;
            }
            if (isa<PHINode>(U) || isa<SelectInst>(U)) {
              push(U, k);
              continue;
            }
            if (isa<BinaryOperator>(U)) {
              push(U, VAL); // arithmetic on content/address stays data
              continue;
            }
            if (isa<ICmpInst>(U) || isa<BranchInst>(U) ||
                isa<SwitchInst>(U))
              continue; // compare/branch: certified benign channel
            if (isa<ReturnInst>(U)) {
              escapes.insert(k == PTR ? "ret-ptr" : "ret-val");
              continue;
            }
            if (const auto *RMW = dyn_cast<AtomicRMWInst>(U)) {
              if (RMW->getPointerOperand() == V)
                push(U, VAL); // old value read back
              else
                escapes.insert("atomic-val");
              continue;
            }
            escapes.insert(std::string("use:") +
                           (isa<Instruction>(U)
                                ? cast<Instruction>(U)->getOpcodeName()
                                : "constexpr"));
          }
        }
        if (violated)
          g_sinkSitesViolated++;
        else if (!escapes.empty()) {
          g_sinkSitesEscaped++;
          for (const std::string &e : escapes)
            g_sinkEscapeSinks[e]++;
        } else {
          g_sinkSitesConfirmed++;
        }
      }
    }
  }
  g_sinkContractChecked = true;
  errs() << "SinkConfirm: " << sites << " payload accessor sites: "
         << g_sinkSitesConfirmed << " CONFIRMED, " << g_sinkSitesEscaped
         << " ESCAPE, " << g_sinkSitesViolated << " VIOLATION\n";
  size_t eShown = 0;
  for (auto &kv : g_sinkEscapeSinks) {
    if (eShown++ >= 40) {
      errs() << "SinkConfirm: ... " << (g_sinkEscapeSinks.size() - 40)
             << " more escape sinks\n";
      break;
    }
    errs() << "SinkConfirm: escape " << kv.first << " at " << kv.second
           << " sites\n";
  }
  for (size_t i = 0; i < std::min<size_t>(20, violations.size()); i++)
    errs() << "SinkConfirm: VIOLATION in " << violations[i] << "\n";
  if (CFLSinkInstr && g_sinkSitesViolated) {
    errs() << "ERROR: --cfl-sink-instr read-back contract VIOLATED at "
           << g_sinkSitesViolated
           << " sites — a payload-derived value feeds an indirect call; "
              "refusing to seal (see SinkConfirm: VIOLATION lines)\n";
    exit(1);
  }
}


// --cfl-census-invoke: MEASUREMENT-ONLY. Tier-1 discovery for the
// INVOKE summary vocabulary (task #28): scan every defined,
// not-yet-summarized function for the registration shapes, then rank
// candidates by constant-Function evidence at their direct callsites —
// the discriminator separating fn-registration APIs from generic
// container stores (opaque pointers make formal types useless).
// Shapes:
//   DIRECT   fptr formal invoked in the body with another formal at
//            call-arg position K  -> INVOKE(argF:fK<-argD) verbatim
//   FIELD    formal stored into a field of another formal (timer/rcu
//            shape: data IS the container; dispatcher supplies K)
//   COSTORE  two formals stored into one local/heap object (kthread
//            create-struct shape; dispatcher elsewhere)
// Adds no edges; emits proposal lines for the proposer/confirmer loop.
void CallGraphPass::runInvokeCensus() {
  struct Cand {
    const Function *F;
    int argF, argD;
    int fk;            // DIRECT only; -1 otherwise
    const char *shape;
    size_t callsites = 0, constFn = 0, nullFn = 0, dynFn = 0;
  };
  std::vector<Cand> cands;
  // (function, argF, argD, shape) dedup across multiple body sites
  std::set<std::tuple<const Function *, int, int, std::string>> seen;
  auto formalIdx = [](const Function &F, const Value *V) -> int {
    V = V->stripPointerCasts();
    for (const auto &A : F.args())
      if (&A == V) return (int)A.getArgNo();
    return -1;
  };
  auto storeBase = [](const Value *P) -> const Value * {
    P = P->stripPointerCasts();
    while (auto *G = dyn_cast<GEPOperator>(P))
      P = G->getPointerOperand()->stripPointerCasts();
    return P;
  };
  size_t nFuncs = 0;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
      if (shouldSkipFunction(&F)) continue;
      if (Ctx->FuncSummaries.count(&F)) continue; // already handled
      if (F.arg_size() < 2) continue;             // need (fn, data)
      nFuncs++;
      // per-object co-store map: base -> formal indices stored into it
      std::map<const Value *, std::set<int>> coStores;
      for (const Instruction &I : instructions(F)) {
        if (const auto *CB = dyn_cast<CallBase>(&I)) {
          if (CB->isInlineAsm()) continue;
          if (const Function *IC = CB->getCalledFunction()) {
            // PASSTHRU: formals forwarded into an already-summarized
            // INVOKE function -> the wrapper inherits the translated
            // atom (composition lift; closes kthread_create_on_cpu /
            // smpboot without hand-seeding)
            auto sit = Ctx->FuncSummaries.find(
                getFuncDef(const_cast<Function *>(IC)));
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(IC);
            if (sit != Ctx->FuncSummaries.end()) {
              for (const auto &A : sit->second->atoms) {
                if (A.kind != GlobalContext::SummaryAtom::Invoke) continue;
                if ((unsigned)A.dst >= CB->arg_size() ||
                    (unsigned)A.src >= CB->arg_size())
                  continue;
                int fIdx = formalIdx(F, CB->getArgOperand(A.dst));
                int dIdx = formalIdx(F, CB->getArgOperand(A.src));
                if (fIdx < 0 || dIdx < 0 || fIdx == dIdx) continue;
                if (seen.insert({&F, fIdx, dIdx, "PASSTHRU"}).second)
                  cands.push_back({&F, fIdx, dIdx, A.aux, "PASSTHRU"});
              }
            }
            continue;
          }
          int fIdx = formalIdx(F, CB->getCalledOperand());
          if (fIdx < 0) continue;
          for (unsigned k = 0; k < CB->arg_size(); k++) {
            int dIdx = formalIdx(F, CB->getArgOperand(k));
            if (dIdx < 0 || dIdx == fIdx) continue;
            if (!containsPointerType(CB->getArgOperand(k)->getType()))
              continue;
            if (seen.insert({&F, fIdx, dIdx, "DIRECT"}).second)
              cands.push_back({&F, fIdx, dIdx, (int)k, "DIRECT"});
          }
        } else if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          int vIdx = formalIdx(F, SI->getValueOperand());
          if (vIdx < 0) continue;
          const Value *base = storeBase(SI->getPointerOperand());
          int bIdx = formalIdx(F, base);
          if (bIdx >= 0 && bIdx != vIdx) {
            if (seen.insert({&F, vIdx, bIdx, "FIELD"}).second)
              cands.push_back({&F, vIdx, bIdx, -1, "FIELD"});
          } else if (isa<AllocaInst>(base) || isa<CallBase>(base) ||
                     isa<GlobalVariable>(base)) {
            coStores[base].insert(vIdx);
          }
        }
      }
      for (auto &[base, idxs] : coStores) {
        if (idxs.size() < 2) continue;
        // report each ordered pair once (fn identity unknown pre-callsite)
        for (int a : idxs)
          for (int b : idxs)
            if (a != b && seen.insert({&F, a, b, "COSTORE"}).second)
              cands.push_back({&F, a, b, -1, "COSTORE"});
      }
    }
  }
  // callsite evidence sweep: constant Function at argF position
  std::map<const Function *, std::vector<Cand *>> byFunc;
  for (auto &c : cands) byFunc[getFuncDef(const_cast<Function *>(c.F))]
                            .push_back(&c);
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.isDeclaration()) continue;
      for (const Instruction &I : instructions(F)) {
        const auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->isInlineAsm()) continue;
        const Function *CF = CB->getCalledFunction();
        if (!CF) continue;
        auto it = byFunc.find(getFuncDef(const_cast<Function *>(CF)));
        if (it == byFunc.end()) continue;
        for (Cand *c : it->second) {
          if ((unsigned)c->argF >= CB->arg_size()) continue;
          c->callsites++;
          const Value *fv = CB->getArgOperand(c->argF)->stripPointerCasts();
          if (isa<Function>(fv)) c->constFn++;
          else if (isa<ConstantPointerNull>(fv)) c->nullFn++;
          else c->dynFn++;
        }
      }
    }
  }
  std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
    return a.constFn != b.constFn ? a.constFn > b.constFn
                                  : a.callsites > b.callsites;
  });
  size_t withEvidence = 0, printed = 0;
  for (const auto &c : cands)
    if (c.constFn > 0) withEvidence++;
  errs() << "InvokeCensus: scanned " << nFuncs << " defined functions, "
         << cands.size() << " shape candidates, " << withEvidence
         << " with constant-Function callsite evidence\n";
  for (const auto &c : cands) {
    if (c.constFn == 0 || printed >= 200) break;
    printed++;
    errs() << "InvokeCensus: " << c.shape << " " << c.F->getName()
           << " fn=arg" << c.argF << " data=arg" << c.argD;
    if (c.fk >= 0) errs() << " f" << c.fk;
    errs() << " callsites=" << c.callsites << " constFn=" << c.constFn
           << " null=" << c.nullFn << " dyn=" << c.dynFn;
    if (c.fk >= 0)
      errs() << "  proposal: " << c.F->getName() << " INVOKE(arg" << c.argF
             << ":f" << c.fk << "<-arg" << c.argD << ")";
    errs() << "\n";
  }
  if (withEvidence > printed)
    errs() << "InvokeCensus: ... +" << (withEvidence - printed)
           << " more with evidence (raise the cap to see them)\n";
}

// --cfl-construct-census (plan 3.34 instrument 2): the constructs every
// soup traced so far came from, counted before the solve. Syntactic, so
// the counts are candidates: each kind's examples name the function or
// site to model (a summary, a clone, a key).
void CallGraphPass::runConstructCensus() {
  struct Kind {
    const char *name;
    size_t n = 0, covered = 0;
    std::vector<std::string> ex;
    void add(const std::string &e, bool cov) {
      n++;
      covered += cov;
      if (!cov && ex.size() < 10) ex.push_back(e);
    }
  };
  Kind wrappers{"allocator wrapper (returns an allocator's result)"},
      pools{"pool allocator (returns a variable offset into a loaded or allocated block)"},
      containers{"generic container (void* parameter stored into a field of another parameter)"},
      method1{"method call p->f(p) (one level)"}, methodN{"method call p->x->f(p) (two or more levels)"},
      fptrCalls{"other indirect call"}, idTests{"method-identity test (h->slot ==/!= function)"},
      unions{"union type with a pointer member"}, varargs{"varargs function with a body"},
      byteCopies{"struct copy through a byte buffer (memcpy between a struct and a non-struct)"};
  auto loc = [](const Instruction *I) {
    std::string s = I->getFunction()->getName().str();
    if (const DILocation *L = I->getDebugLoc())
      s += " " + L->getFilename().str() + ":" + std::to_string(L->getLine());
    return s;
  };
  auto summarized = [&](const Function *F) { return Ctx->FuncSummaries.count(F) > 0; };
  // A value that is an allocator result (through casts and phis/selects):
  // a call of an allocator, or of a wrapper found so far.
  std::set<const Function *> wrapperSet;
  std::function<bool(const Value *, int)> fromAlloc = [&](const Value *V, int d) -> bool {
    V = V->stripPointerCasts();
    if (const auto *CB = dyn_cast<CallBase>(V))
      if (const Function *C = CB->getCalledFunction())
        return Ctx->AllocFuncs.count(const_cast<Function *>(C)) > 0 || wrapperSet.count(C) > 0;
    if (d > 4) return false;
    if (const auto *P = dyn_cast<PHINode>(V)) {
      bool any = false;
      for (const Value *In : P->incoming_values())
        if (!isa<ConstantPointerNull>(In)) { if (!fromAlloc(In, d + 1)) return false; any = true; }
      return any;
    }
    return false;
  };
  // The values a value can be: through casts, phis, constant GEPs (for a
  // base) and, at -O0, loads of a non-escaping local slot (its stores).
  std::function<void(const Value *, int, std::vector<const Value *> &)> defs =
      [&](const Value *V, int d, std::vector<const Value *> &out) {
        V = V->stripPointerCasts();
        if (d > 6) { out.push_back(V); return; }
        if (const auto *P = dyn_cast<PHINode>(V)) {
          for (const Value *In : P->incoming_values()) defs(In, d + 1, out);
          return;
        }
        if (const auto *L = dyn_cast<LoadInst>(V))
          if (const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
            std::vector<const Value *> stored;
            bool ok = true;
            for (const User *U : S->users()) {
              if (isa<LoadInst>(U)) continue;
              const auto *SI = dyn_cast<StoreInst>(U);
              if (!SI || SI->getPointerOperand() != S) { ok = false; break; }
              stored.push_back(SI->getValueOperand());
            }
            if (ok) {
              for (const Value *X : stored) defs(X, d + 1, out);
              return;
            }
          }
        out.push_back(V);
      };
  // A block base: an allocator result, a load (a free list or a header
  // field), through constant GEPs (past a header).
  auto blockBase = [&](const Value *B) {
    std::vector<const Value *> ds;
    defs(B, 0, ds);
    for (const Value *X : ds) {
      while (const auto *G = dyn_cast<GEPOperator>(X)) {
        if (!G->hasAllConstantIndices()) break;
        X = G->getPointerOperand()->stripPointerCasts();
      }
      std::vector<const Value *> d2;
      defs(X, 0, d2);
      for (const Value *Y : d2)
        if (isa<LoadInst>(Y) || fromAlloc(Y, 0)) return true;
    }
    return false;
  };
  auto isVoidPtrDI = [](const DIType *T) {
    const auto *D = dyn_cast_or_null<DIDerivedType>(T);
    return D && D->getTag() == dwarf::DW_TAG_pointer_type && !D->getBaseType();
  };
  // Wrappers to a fixpoint: every non-null return is an allocation result,
  // or a constant offset past one (a header before the payload).
  for (bool grew = true; grew;) {
    grew = false;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (F.isDeclaration() || !F.getReturnType()->isPointerTy() || wrapperSet.count(&F) ||
            Ctx->AllocFuncs.count(&F))
          continue;
        bool anyRet = false, all = true;
        for (const BasicBlock &BB : F)
          if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
            if (const Value *RV = RI->getReturnValue()) {
              std::vector<const Value *> ds;
              defs(RV, 0, ds);
              for (const Value *X : ds) {
                if (isa<ConstantPointerNull>(X)) continue;
                anyRet = true;
                while (const auto *G = dyn_cast<GEPOperator>(X)) {
                  if (!G->hasAllConstantIndices()) break;
                  X = G->getPointerOperand()->stripPointerCasts();
                }
                std::vector<const Value *> d2;
                defs(X, 0, d2);
                for (const Value *Y : d2) all &= fromAlloc(Y, 0);
              }
            }
        if (anyRet && all) { wrapperSet.insert(&F); grew = true; }
      }
  }
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M) {
      if (F.isDeclaration()) continue;
      if (F.isVarArg()) varargs.add(F.getName().str(), summarized(&F));
      if (wrapperSet.count(&F)) wrappers.add(F.getName().str(), summarized(&F));
      // Wrappers and pools: by what F returns.
      if (F.getReturnType()->isPointerTy()) {
        bool anyRet = false, allAlloc = true, interior = false;
        for (const BasicBlock &BB : F)
          if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
            if (const Value *RV = RI->getReturnValue()) {
              std::vector<const Value *> ds;
              defs(RV, 0, ds);
              for (const Value *X : ds) {
                if (isa<ConstantPointerNull>(X)) continue;
                anyRet = true;
                allAlloc &= fromAlloc(X, 0);
                if (const auto *G = dyn_cast<GEPOperator>(X))
                  if (!G->hasAllConstantIndices() && blockBase(G->getPointerOperand()))
                    interior = true;
              }
            }
        const bool alloc = Ctx->AllocFuncs.count(&F) > 0;
        (void)allAlloc;
        if (anyRet && interior) pools.add(F.getName().str(), summarized(&F) || alloc);
      }
      // Generic containers: a void* formal stored into a field reached
      // from another formal.
      if (const DISubprogram *SP = F.getSubprogram())
        if (const DISubroutineType *ST = SP->getType()) {
          auto types = ST->getTypeArray();
          for (Instruction &I : instructions(F)) {
            const auto *SI = dyn_cast<StoreInst>(&I);
            if (!SI) continue;
            const auto *A = dyn_cast<Argument>(SI->getValueOperand()->stripPointerCasts());
            if (!A || A->getArgNo() + 1 >= types.size() || !isVoidPtrDI(types[A->getArgNo() + 1]))
              continue;
            const Value *P = SI->getPointerOperand()->stripPointerCasts();
            if (const auto *G = dyn_cast<GEPOperator>(P)) P = G->getPointerOperand()->stripPointerCasts();
            if (const auto *L = dyn_cast<LoadInst>(P)) P = L->getPointerOperand()->stripPointerCasts();
            if (isa<Argument>(P) || isa<LoadInst>(P)) {
              containers.add(F.getName().str() + " arg" + std::to_string(A->getArgNo()), summarized(&F));
              break;
            }
          }
        }
      for (Instruction &I : instructions(F)) {
        if (const auto *CB = dyn_cast<CallBase>(&I)) {
          if (CB->isInlineAsm()) continue;
          if (!CB->getCalledFunction() &&
              !isa<Function>(CB->getCalledOperand()->stripPointerCasts())) {
            std::vector<std::pair<const Value *, const Value *>> path;
            const int k = dispatchReceiver(CB, &path);
            if (k < 0) fptrCalls.add(loc(&I), false);
            else if (path.size() == 1) method1.add(loc(&I), true);
            else methodN.add(loc(&I), true);
            continue;
          }
          if (const Function *C = CB->getCalledFunction())
            if ((C->getName().starts_with("llvm.memcpy") || C->getName().starts_with("llvm.memmove") ||
                 C->getName() == "memcpy" || C->getName() == "memmove") && CB->arg_size() >= 2) {
              auto structy = [&](const Value *V) {
                V = V->stripPointerCasts();
                if (const auto *AI = dyn_cast<AllocaInst>(V)) return AI->getAllocatedType()->isStructTy();
                if (const auto *G = dyn_cast<GEPOperator>(V)) return G->getResultElementType()->isStructTy() ||
                                                                   G->getSourceElementType()->isStructTy();
                if (const auto *GV = dyn_cast<GlobalVariable>(V)) return GV->getValueType()->isStructTy();
                return false;
              };
              if (structy(CB->getArgOperand(0)) != structy(CB->getArgOperand(1)))
                byteCopies.add(loc(&I), false);
            }
        }
        if (const auto *C = dyn_cast<ICmpInst>(&I))
          if (C->isEquality())
            for (unsigned i = 0; i < 2; i++)
              if (isa<Function>(C->getOperand(i)->stripPointerCasts()) &&
                  isa<LoadInst>(C->getOperand(1 - i)->stripPointerCasts())) {
                idTests.add(loc(&I), true);
                break;
              }
      }
    }
    // Unions with a pointer member (debug info).
    DebugInfoFinder DIF;
    DIF.processModule(*M);
    std::set<std::string> seenU;
    for (const DIType *T : DIF.types()) {
      const auto *CT = dyn_cast<DICompositeType>(T);
      if (!CT || CT->getTag() != dwarf::DW_TAG_union_type) continue;
      unsigned ptrs = 0;
      for (const DINode *E : CT->getElements())
        if (const auto *Mb = dyn_cast<DIDerivedType>(E))
          if (const auto *B = dyn_cast_or_null<DIDerivedType>(Mb->getBaseType()))
            ptrs += B->getTag() == dwarf::DW_TAG_pointer_type;
      if (!ptrs) continue;
      const std::string nm = CT->getName().empty()
                                 ? ("anonymous at " + CT->getFilename().str() + ":" + std::to_string(CT->getLine()))
                                 : CT->getName().str();
      if (seenU.insert(nm).second) unions.add(nm + " (" + std::to_string(ptrs) + " pointer members)", false);
    }
    (void)DL;
  }
  errs() << "CONSTRUCT CENSUS (counts before the solve; 'covered' = a summary or the engine handles it)\n";
  for (Kind *K : {&wrappers, &pools, &containers, &method1, &methodN, &fptrCalls, &idTests, &unions,
                  &varargs, &byteCopies}) {
    errs() << "  " << K->name << ": " << K->n << " (" << K->covered << " covered)\n";
    for (const std::string &e : K->ex) errs() << "      " << e << "\n";
  }
  errs() << "  carves (one past an array, used as another type): counted per solve as "
            "'carved regions' in the cell report\n";
}
