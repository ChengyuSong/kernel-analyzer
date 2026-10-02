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

// --cfl-census-fields (task #29): MEASUREMENT-ONLY census of the
// family-2/3 store-side registration channels. A channel is a
// (struct,byte-offset) field key with constant-Function STORES on the
// registration side and field-LOAD-fed icalls on the dispatch side
// (INIT_WORK/timer/hrtimer/notifier shape: the fn is not a call
// parameter, it is written into a container the dispatcher reads
// back). Also counts paired sibling stores ((fn,data) written into
// the same object in the same function — the correlation a
// same-origin binding could exploit) and ops-struct pointer stores
// (family 3). Adds no edges.
void CallGraphPass::runFieldChannelCensus() {
  struct Chan {
    size_t fnStores = 0, dynStores = 0, opsStores = 0, icallLoads = 0;
    size_t paired = 0;
    std::set<std::string> fnSample;
    std::string loadSample;
  };
  std::map<std::string, Chan> chans;
  // family-3: "<opsFieldKey> ->fn <fnFieldKey>" -> (dispatchSites,
  // receiver-passing sites)
  std::map<std::string, std::pair<size_t, size_t>> twoLevel;
  std::map<const Value *, size_t> opsGlobalFanout; // ops global -> stores
  auto fieldKey = [&](const Value *P, const DataLayout &DL,
                      bool &varIdx) -> std::pair<std::string, const Value *> {
    APInt Off(64, 0);
    std::string SName;
    varIdx = false;
    P = P->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(P)) {
      if (!G->accumulateConstantOffset(DL, Off))
        varIdx = true;
      if (SName.empty())
        if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
          if (ST->hasName())
            SName = stripStructNameSuffix(ST->getStructName()).str();
      P = G->getPointerOperand()->stripPointerCasts();
    }
    std::string Key = (SName.empty() ? std::string("?") : SName) + "+" +
                      (varIdx ? std::string("var")
                              : std::to_string(Off.getSExtValue()));
    return {Key, P};
  };
  auto isOpsGlobal = [](const Value *V) {
    const auto *GV = dyn_cast<GlobalVariable>(V);
    if (!GV || !GV->hasInitializer()) return false;
    const auto *CS = dyn_cast<ConstantStruct>(GV->getInitializer());
    if (!CS) return false;
    for (const Use &Op : CS->operands())
      if (isa<Function>(Op->stripPointerCasts())) return true;
    return false;
  };
  size_t totalFnStores = 0, totalIcallLoads = 0;
  for (auto &mp : Ctx->Modules) {
    const DataLayout &DL = mp.first->getDataLayout();
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
      if (shouldSkipFunction(&F)) continue;
      // per-base sibling stores within this function: fn-offset keys
      // and data-ptr stores keyed by base object
      std::map<const Value *, std::vector<std::string>> baseFnKeys;
      std::map<const Value *, size_t> baseDataStores;
      for (const Instruction &I : instructions(F)) {
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          const Value *V = SI->getValueOperand()->stripPointerCasts();
          bool varIdx = false;
          auto [Key, Base] = fieldKey(SI->getPointerOperand(), DL, varIdx);
          if (const auto *Fn = dyn_cast<Function>(V)) {
            Chan &C = chans[Key];
            C.fnStores++;
            totalFnStores++;
            if (C.fnSample.size() < 4) C.fnSample.insert(Fn->getName().str());
            baseFnKeys[Base].push_back(Key);
          } else if (isOpsGlobal(V)) {
            chans[Key].opsStores++;
            opsGlobalFanout[V]++;
          } else if (containsPointerType(V->getType())) {
            baseDataStores[Base]++;
            // dynamic fn store? count under the key only if the value
            // could be a function — unknowable under opaque ptrs; the
            // dyn tally lives on channels that ALSO see constant fns
            if (chans.count(Key)) chans[Key].dynStores++;
          }
        } else if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          const CallBase *fedCB = nullptr;
          for (const User *U : LI->users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (CB && !CB->isInlineAsm() &&
                CB->getCalledOperand()->stripPointerCasts() == LI)
              fedCB = CB;
          }
          if (!fedCB) continue;
          bool varIdx = false;
          auto [Key, Base] = fieldKey(LI->getPointerOperand(), DL, varIdx);
          Chan &C = chans[Key];
          C.icallLoads++;
          totalIcallLoads++;
          if (C.loadSample.empty())
            C.loadSample = F.getName().str();
          // family-3 two-level dispatch: the fn load's base is ITSELF
          // a loaded pointer (obj->ops then ops->fn). Record the outer
          // (ops-field) key and whether the icall passes the receiver
          // (the inner load's base object) as an argument.
          if (const auto *L1 = dyn_cast<LoadInst>(Base)) {
            bool v2 = false;
            auto [OKey, OBase] = fieldKey(L1->getPointerOperand(), DL, v2);
            bool recv = false;
            for (const Use &A2 : fedCB->args())
              if (A2->stripPointerCasts() == OBase) recv = true;
            auto &T = twoLevel[OKey + " ->fn " + Key];
            T.first++;
            if (recv) T.second++;
          }
        }
      }
      for (auto &[Base, Keys] : baseFnKeys)
        if (baseDataStores.count(Base))
          for (const std::string &K : Keys) chans[K].paired++;
    }
  }
  // Rank two-sided channels (registration AND dispatch observed).
  std::vector<std::pair<const std::string *, const Chan *>> ranked;
  size_t oneSidedStores = 0, oneSidedLoads = 0;
  for (auto &[K, C] : chans) {
    if (C.fnStores && C.icallLoads) ranked.push_back({&K, &C});
    else if (C.fnStores) oneSidedStores++;
    else if (C.icallLoads) oneSidedLoads++;
  }
  std::sort(ranked.begin(), ranked.end(), [](auto &A, auto &B) {
    return A.second->fnStores * A.second->icallLoads >
           B.second->fnStores * B.second->icallLoads;
  });
  errs() << "FieldChannels: " << chans.size() << " field keys; "
         << ranked.size() << " two-sided channels (" << oneSidedStores
         << " store-only, " << oneSidedLoads << " load-only); "
         << totalFnStores << " constant-fn stores, " << totalIcallLoads
         << " field-load icalls total\n";
  size_t shown = 0;
  for (auto &[K, C] : ranked) {
    if (shown++ >= 40) break;
    errs() << "FieldChannels: " << *K << " fnStores=" << C->fnStores
           << " paired=" << C->paired << " dynStores=" << C->dynStores
           << " opsStores=" << C->opsStores
           << " icallLoads=" << C->icallLoads << " dispatch@"
           << C->loadSample << " fns:";
    for (const auto &N : C->fnSample) errs() << " " << N;
    errs() << "\n";
  }
  // family-3 report: two-level dispatch channels + ops-global fan-out
  std::vector<std::pair<size_t, const std::string *>> tlRank;
  size_t recvTotal = 0, tlTotal = 0;
  for (auto &[K, V] : twoLevel) {
    tlRank.emplace_back(V.first, &K);
    tlTotal += V.first;
    recvTotal += V.second;
  }
  std::sort(tlRank.begin(), tlRank.end(), std::greater<>());
  errs() << "OpsChannels: " << twoLevel.size()
         << " two-level dispatch channels, " << tlTotal << " sites, "
         << recvTotal << " pass the receiver; " << opsGlobalFanout.size()
         << " distinct ops globals stored\n";
  for (size_t i = 0; i < std::min<size_t>(25, tlRank.size()); i++) {
    auto &V = twoLevel[*tlRank[i].second];
    errs() << "OpsChannels: " << *tlRank[i].second << " sites=" << V.first
           << " recv=" << V.second << "\n";
  }
  std::vector<std::pair<size_t, const Value *>> ogRank;
  for (auto &[G, N] : opsGlobalFanout) ogRank.emplace_back(N, G);
  std::sort(ogRank.begin(), ogRank.end(), std::greater<>());
  for (size_t i = 0; i < std::min<size_t>(10, ogRank.size()); i++)
    errs() << "OpsChannels: opsGlobal " << ogRank[i].second->getName()
           << " stored at " << ogRank[i].first << " sites\n";
}


// --cfl-census-tracepoint (task #35): size the tracepoint keyed-channel
// design. The prize (pin-measured): 964 __traceiter_* callers carry
// 1,504,648 pairs = 17.9% of the 8.39M kernel answer set, because
// tracepoint_add_func's generic tp->funcs store pools every
// tracepoint's (probe, data) registrations into one channel. The model
// keys the channel by the @__tracepoint_* global — this census splits
// the registration sites by how the key is named there:
//   CONST  — tp argument IS a @__tracepoint_* global (the inlined
//            register_trace_<name> wrappers): directly keyable, the
//            static_call (#14) primitive shape.
//   LOAD   — tp loaded from memory (trace_event_reg's call->tp path):
//            needs the trace_event_call static-initializer pair
//            correlation (.tp co-resident with .probe/.perf_probe —
//            the #28 pair-atom shape).
//   FORMAL — tp is the enclosing function's parameter: in-family
//            plumbing (tracepoint_add_func etc.), not a channel entry.
// Dispatch side: every __traceiter_* body must name its key global at
// the funcs-head load (constexpr GEP on @__tracepoint_*) — keyless
// icalls would break the model, so they are counted loudly.
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

void CallGraphPass::runTracepointCensus() {
  auto isRegFn = isTracepointRegFn;
  size_t nConst = 0, nConstPair = 0, nLoad = 0, nFormal = 0, nOther = 0;
  std::map<std::string, size_t> loadEnclosing, formalEnclosing,
      otherEnclosing;
  boost::unordered_flat_set<const GlobalVariable *> constKeys;
  boost::unordered_flat_set<const Function *> constProbes;
  size_t nTraceiter = 0, nTraceiterKeyless = 0, nIcallKeyed = 0,
         nIcallKeyless = 0;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) {
      if (F.empty())
        continue;
      const bool isTraceiter = F.getName().starts_with("__traceiter_");
      const GlobalVariable *fnKey = nullptr;
      if (isTraceiter) {
        nTraceiter++;
        for (Instruction &I : instructions(F)) {
          const auto *LI = dyn_cast<LoadInst>(&I);
          if (!LI)
            continue;
          const Value *P = LI->getPointerOperand();
          if (const auto *CE = dyn_cast<ConstantExpr>(P))
            if (CE->getOpcode() == Instruction::GetElementPtr)
              P = CE->getOperand(0);
          if (const auto *GV =
                  dyn_cast<GlobalVariable>(P->stripPointerCasts()))
            if (GV->getName().starts_with("__tracepoint_")) {
              fnKey = GV;
              break;
            }
        }
        if (!fnKey)
          nTraceiterKeyless++;
      }
      for (Instruction &I : instructions(F)) {
        const auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || CB->isInlineAsm())
          continue;
        const auto *CF = dyn_cast<Function>(
            CB->getCalledOperand()->stripPointerCasts());
        if (!CF) {
          if (isTraceiter) {
            if (fnKey)
              nIcallKeyed++;
            else
              nIcallKeyless++;
          }
          continue;
        }
        if (!isRegFn(CF->getName()) || CB->arg_size() < 2)
          continue;
        const Value *tp = CB->getArgOperand(0)->stripPointerCasts();
        if (const auto *GV = dyn_cast<GlobalVariable>(tp)) {
          if (GV->getName().starts_with("__tracepoint_")) {
            nConst++;
            constKeys.insert(GV);
            if (const auto *PF = dyn_cast<Function>(
                    CB->getArgOperand(1)->stripPointerCasts())) {
              nConstPair++;
              constProbes.insert(PF);
            }
          } else {
            nOther++;
            otherEnclosing[(F.getName() + " (gv " + GV->getName() + ")")
                               .str()]++;
          }
        } else if (isa<LoadInst>(tp)) {
          nLoad++;
          loadEnclosing[F.getName().str()]++;
        } else if (isa<Argument>(tp)) {
          nFormal++;
          formalEnclosing[F.getName().str()]++;
        } else {
          nOther++;
          otherEnclosing[
              (F.getName() + " (" +
               (isa<Instruction>(tp) ? cast<Instruction>(tp)->getOpcodeName()
                                     : "non-inst") +
               ")").str()]++;
        }
      }
    }
  }
  errs() << "TracepointCensus: register-family sites "
         << (nConst + nLoad + nFormal + nOther) << " = CONST " << nConst
         << " (" << nConstPair << " fully-static pairs, "
         << constKeys.size() << " distinct keys, " << constProbes.size()
         << " distinct probes) / LOAD " << nLoad << " / FORMAL " << nFormal
         << " / OTHER " << nOther << "\n";
  errs() << "TracepointCensus: dispatch __traceiter fns " << nTraceiter
         << " (" << nTraceiterKeyless << " KEYLESS), icalls keyed "
         << nIcallKeyed << " / keyless " << nIcallKeyless << "\n";
  auto dumpTop = [](const char *tag,
                    const std::map<std::string, size_t> &m) {
    std::vector<std::pair<size_t, const std::string *>> v;
    for (auto &kv : m)
      v.emplace_back(kv.second, &kv.first);
    std::sort(v.begin(), v.end(), std::greater<>());
    for (size_t i = 0; i < std::min<size_t>(10, v.size()); i++)
      errs() << "TracepointCensus: " << tag << " x" << v[i].first << " "
             << *v[i].second << "\n";
  };
  dumpTop("load-site", loadEnclosing);
  dumpTop("formal-site", formalEnclosing);
  dumpTop("other-site", otherEnclosing);
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
