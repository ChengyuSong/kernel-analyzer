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

// Summaries.cc: transfer summaries: func_summaries.txt, atoms at call sites, chain pairs, provers and confirmers.
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

static size_t g_freshPromoted = 0, g_freshRejRet = 0, g_freshRejEscape = 0,
              g_freshRejSide = 0, g_freshInit = 0, g_escapeSamples = 0,
              g_freshHelperComposed = 0, g_freshCpy = 0, g_freshAlias = 0;
static std::map<std::string, size_t> g_escapeBuckets;
// Stores (and handle-field reads) of promoted wrappers exempted by a pool
// certificate (plan 3.55 (a)): the confirmer and the solver read the same
// certificate.
static std::set<const llvm::Instruction *> g_poolCertExempt;
static std::map<std::string, size_t> g_escapeCallees;
void CallGraphPass::confirmFreshWrappers() {
  static GlobalContext::FuncSummary pureFresh; // stable address for the map
  pureFresh.fresh = true;
  // A promoted wrapper keeps its body (BODY): its own calls stay in the
  // call graph (png_create_info_struct's memset) and its icalls resolve;
  // the call site's result is still the fresh per-site object.
  pureFresh.body = true;
  auto isNoopIntrinsic = [](const Function *IF) {
    if (!IF->isIntrinsic()) return false;
    StringRef n = IF->getName();
    return n.starts_with("llvm.dbg") || n.starts_with("llvm.lifetime") ||
           n.starts_with("llvm.assume") || n.starts_with("llvm.expect") ||
           n.starts_with("llvm.memset") || n.starts_with("llvm.experimental");
  };
  // Init-helper analysis (step B v2, the dominant call-escape bucket):
  // a helper is INIT-ONLY in pointer param j if param j is used solely
  // as a store base (through GEP/bitcast chains, plus null checks), and
  // every stored value is one of: the helper's own formal m (recorded
  // as a mapping), a non-pointer, null, or a param-j-derived pointer
  // (self-linkage, e.g. INIT_LIST_HEAD). No other pointer side effects
  // anywhere in the helper, all other ptr params unused for stores,
  // void-or-unused result. The wrapper then composes the helper's
  // stores through the callsite into its own ST atoms — one level of
  // summary composition, still zero graph duplication.
  struct InitInfo {
    bool valid = false;
    int objParam = -1;
    SmallVector<int, 4> srcFormals; // helper formal indices stored into obj
    SmallVector<const GlobalValue *, 4> srcGlobals; // globals stored into obj
    bool selfStore = false;         // obj-interior stored into obj
  };
  static std::map<const Function *, InitInfo> initCache;
  std::function<const InitInfo &(const Function *)> initOnlyInfoRef;
  initOnlyInfoRef = [&](const Function *C) -> const InitInfo & {
    auto it = initCache.find(C);
    if (it != initCache.end()) return it->second;
    InitInfo &inf = initCache[C];
    if (C->isDeclaration() || C->isVarArg()) return inf;
    if (!C->getReturnType()->isVoidTy()) return inf; // keep v1 strict
    // classify each pointer param's use graph
    int obj = -1;
    bool bad = false;
    SmallPtrSet<const Value *, 16> objGraph;
    SmallVector<int, 4> srcs;
    SmallVector<const GlobalValue *, 4> gsrcs;
    SmallPtrSet<const Instruction *, 4> nestedInit;
    bool self = false;
    for (const Argument &A2 : C->args()) {
      if (!A2.getType()->isPointerTy()) continue;
      // walk this param's derived-pointer graph
      SmallVector<const Value *, 8> w2{&A2};
      SmallPtrSet<const Value *, 16> g2;
      bool storedInto = false, escapes = false;
      SmallVector<int, 4> mySrcs;
      SmallVector<const GlobalValue *, 4> myGsrcs;
      SmallPtrSet<const Instruction *, 4> myNested;
      bool mySelf = false;
      while (!w2.empty() && !escapes) {
        const Value *v2 = w2.pop_back_val();
        if (!g2.insert(v2).second) continue;
        for (const User *U2 : v2->users()) {
          if (isa<ICmpInst>(U2)) continue;
          if (isa<GetElementPtrInst>(U2) || isa<BitCastInst>(U2)) {
            w2.push_back(cast<Value>(U2));
            continue;
          }
          if (const auto *SI2 = dyn_cast<StoreInst>(U2)) {
            if (SI2->getValueOperand() == v2) {
              // param-derived ptr stored: self-linkage iff the target
              // is also param-derived; a DIRECT formal stored into a
              // sibling param's memory is the init itself (recorded by
              // the sibling's walk as an Argument-source store-into);
              // any other target is an escape.
              const Value *tb = SI2->getPointerOperand()->stripPointerCasts();
              while (const auto *G3 = dyn_cast<GetElementPtrInst>(tb))
                tb = G3->getPointerOperand()->stripPointerCasts();
              if (g2.count(tb) || tb == &A2) { mySelf = true; storedInto = true; continue; }
              if (v2 == &A2) {
                if (const auto *TA = dyn_cast<Argument>(tb)) {
                  if (TA->getParent() == C && TA != &A2)
                    continue; // sibling records this as its init store
                }
              }
              escapes = true;
              break;
            }
            // store INTO param memory
            storedInto = true;
            const Value *sv2 = SI2->getValueOperand()->stripPointerCasts();
            if (!containsPointerType(sv2->getType())) continue;
            if (isa<ConstantPointerNull>(sv2)) continue;
            if (g2.count(sv2)) { mySelf = true; continue; }
            if (const auto *SA = dyn_cast<Argument>(sv2)) {
              if (SA->getParent() == C) { mySrcs.push_back((int)SA->getArgNo()); continue; }
            }
            if (const auto *SG = dyn_cast<GlobalValue>(sv2)) {
              myGsrcs.push_back(SG); // ops tables etc.
              continue;
            }
            escapes = true; // derived value: reject helper
            break;
          }
          if (const auto *NC = dyn_cast<CallBase>(U2)) {
            // nested init helper on this param (vma_init ->
            // vma_numab_state_init shape): recurse. The cache entry is
            // default-invalid while in flight, so cycles reject
            // naturally.
            const Function *C2 = NC->getCalledFunction();
            bool okNested = false;
            if (C2 && NC->getCalledOperand()->stripPointerCasts() != v2 &&
                NC->getType()->isVoidTy()) {
              const InitInfo &ni = initOnlyInfoRef(C2);
              bool pOk = ni.valid && ni.objParam < (int)NC->arg_size() &&
                         NC->getArgOperand(ni.objParam)
                                 ->stripPointerCasts() == v2;
              if (pOk)
                for (unsigned ai2 = 0; ai2 < NC->arg_size(); ai2++)
                  if ((int)ai2 != ni.objParam &&
                      NC->getArgOperand(ai2)->stripPointerCasts() == v2)
                    pOk = false;
              if (pOk) {
                okNested = true;
                for (int m3 : ni.srcFormals) {
                  if (m3 >= (int)NC->arg_size()) { okNested = false; break; }
                  const Value *av2 =
                      NC->getArgOperand(m3)->stripPointerCasts();
                  if (!containsPointerType(av2->getType())) continue;
                  if (isa<ConstantPointerNull>(av2)) continue;
                  if (g2.count(av2)) { mySelf = true; continue; }
                  if (const auto *NA = dyn_cast<Argument>(av2)) {
                    if (NA->getParent() == C) {
                      mySrcs.push_back((int)NA->getArgNo());
                      continue;
                    }
                  }
                  if (const auto *NG = dyn_cast<GlobalValue>(av2)) {
                    myGsrcs.push_back(NG);
                    continue;
                  }
                  okNested = false;
                  break;
                }
                if (okNested) {
                  for (const GlobalValue *NG2 : ni.srcGlobals)
                    myGsrcs.push_back(NG2);
                  if (ni.selfStore) mySelf = true;
                  storedInto = true;
                  myNested.insert(NC);
                }
              }
            }
            if (!okNested) { escapes = true; break; }
            continue;
          }
          escapes = true;
          break;
        }
      }
      if (escapes) { bad = true; break; }
      if (storedInto) {
        if (obj >= 0) { bad = true; break; } // one stored-into param only
        obj = (int)A2.getArgNo();
        objGraph = g2;
        srcs = mySrcs;
        gsrcs = myGsrcs;
        for (const Instruction *NI2 : myNested) nestedInit.insert(NI2);
        self = mySelf;
      }
    }
    if (bad || obj < 0) return inf;
    // no other pointer side effects in the helper body
    for (auto II2 = inst_begin(*C), IE2 = inst_end(*C); II2 != IE2; ++II2) {
      const Instruction *I3 = &*II2;
      if (const auto *SI3 = dyn_cast<StoreInst>(I3)) {
        const Value *pb3 = SI3->getPointerOperand()->stripPointerCasts();
        while (const auto *G4 = dyn_cast<GetElementPtrInst>(pb3))
          pb3 = G4->getPointerOperand()->stripPointerCasts();
        if (!objGraph.count(pb3) &&
            !(isa<Argument>(pb3) &&
              cast<Argument>(pb3)->getArgNo() == (unsigned)obj)) {
          if (containsPointerType(SI3->getValueOperand()->getType()))
            return inf;
        }
        continue;
      }
      if (const auto *CB3 = dyn_cast<CallBase>(I3)) {
        if (nestedInit.count(I3)) continue; // composed nested init
        const Function *CF3 = CB3->getCalledFunction();
        if (CF3 && isNoopIntrinsic(CF3)) continue;
        return inf; // any real call: reject helper (v1)
      }
      if (isa<PtrToIntInst>(I3) || isa<AtomicRMWInst>(I3) ||
          isa<AtomicCmpXchgInst>(I3) || isa<LoadInst>(I3))
        ; // loads are fine (reads don't move pointers outward)
    }
    inf.valid = true;
    inf.objParam = obj;
    inf.srcFormals = srcs;
    inf.srcGlobals = gsrcs;
    inf.selfStore = self;
    return inf;
  };
  auto &initOnlyInfo = initOnlyInfoRef;
  // O0 shape (2026-09-16): formals and call results are spilled into
  // local slots and reloaded. A slot whose only users are loads, stores
  // INTO it and debug/lifetime markers never escapes; a load from it
  // reads the stores that REACH it — the last store before it in its
  // block, else the last store of each predecessor path (the mem2reg
  // answer, computed on demand). Without this every O0 wrapper failed
  // R1 at its first reload (cflow/binutils: xrealloc, bfd_malloc).
  auto isSpillSlot = [](const Value *v) -> const AllocaInst * {
    return spillSlotOf(v);
  };
  auto reachingSlotStores = [](const LoadInst *L, const AllocaInst *AI,
                               SmallVectorImpl<const StoreInst *> &out) {
    reachingSlotStoresOf(L, AI, out);
  };
  // Plan 3.55 (a), certificate-bound: the pool's own bookkeeping is not an
  // escape. Only where the PoolCarve certificate names the field (a
  // certified pool's handle field, poolFieldAccess) and the value derives
  // from that pool's chunk: a read of one of its handle fields, through
  // casts, address steps and spill slots (objalloc_create: `chunk =
  // ret->chunks; ret->current_ptr = (char *)chunk + HDR`).
  std::function<bool(const Value *, const std::string &, int)> poolDerived =
      [&](const Value *x, const std::string &P, int d) -> bool {
    x = x->stripPointerCasts();
    if (d > 8) return false;
    if (const auto *L = dyn_cast<LoadInst>(x)) {
      if (auto it = poolFieldAccess.find(L); it != poolFieldAccess.end()) return it->second == P;
      if (const AllocaInst *AI = isSpillSlot(L->getPointerOperand())) {
        SmallVector<const StoreInst *, 4> defs;
        reachingSlotStores(L, AI, defs);
        if (defs.empty()) return false;
        for (const StoreInst *D : defs)
          if (!poolDerived(D->getValueOperand(), P, d + 1)) return false;
        return true;
      }
      return false;
    }
    if (const auto *G = dyn_cast<GEPOperator>(x)) return poolDerived(G->getPointerOperand(), P, d + 1);
    return false;
  };
  // Every use of a handle-field read stays in the pool P: compares, writes
  // into P's handle fields through it (the chunk's header), and stores of it
  // (or a step of it) into P's handle fields. Those stores are returned.
  auto poolUsesOnly = [&](const LoadInst *L0, const std::string &P,
                          SmallVectorImpl<const Instruction *> &stores) -> bool {
    SmallVector<const Value *, 8> w{L0};
    SmallPtrSet<const Value *, 16> seen;
    while (!w.empty()) {
      const Value *x = w.pop_back_val();
      if (!seen.insert(x).second) continue;
      for (const User *U : x->users()) {
        if (isa<ICmpInst>(U) || isa<DbgInfoIntrinsic>(U)) continue;
        if (isa<CastInst>(U) || isa<GetElementPtrInst>(U)) { w.push_back(U); continue; }
        if (const auto *S = dyn_cast<StoreInst>(U)) {
          auto it = poolFieldAccess.find(S);
          if (it != poolFieldAccess.end() && it->second == P) { stores.push_back(S); continue; }
          if (S->getValueOperand() == x)
            if (const AllocaInst *AI = isSpillSlot(S->getPointerOperand())) {
              for (const User *AU : AI->users())
                if (const auto *RL = dyn_cast<LoadInst>(AU)) {
                  SmallVector<const StoreInst *, 4> defs;
                  reachingSlotStores(RL, AI, defs);
                  if (llvm::is_contained(defs, S)) w.push_back(RL);
                }
              continue;
            }
          return false;
        }
        return false;
      }
    }
    return true;
  };
  // A wrapper's summary as a summary-file line (ST, CPY, ALIAS sorted).
  auto freshLine = [](StringRef name, ArrayRef<int> st, ArrayRef<int> cpy,
                      ArrayRef<int> alias) {
    std::string ln = name.str() + " FRESH";
    for (int an : st) ln += " ST(*ret<-arg" + std::to_string(an) + ")";
    for (int cj : cpy) ln += " CPY(ret<-arg" + std::to_string(cj) + ")";
    for (int aj : alias) ln += " ALIAS(ret=arg" + std::to_string(aj) + ")";
    return ln + " BODY";
  };
  // Hand rows of the shape the engine emits (FRESH, ST(*ret<-argN),
  // CPY(ret<-argN), ALIAS(ret=argN), BODY) on functions with a body, as
  // lines. After the fixpoint each is checked with its own row hidden
  // and the others in place; a row the engine confirms with the same
  // line is reported as redundant given the other rows (a set of such
  // rows is removable when the engine reconfirms them all without it).
  // The check promotes nothing.
  std::map<const Function *, std::string> handRows;
  for (auto &[HF, HS] : Ctx->FuncSummaries) {
    if (HF->isDeclaration() || HF->empty() ||
        !HF->getReturnType()->isPointerTy())
      continue;
    if (!HS->fresh || !HS->body || HS->none || HS->noop || HS->pool ||
        HS->freeArg >= 0 || !HS->labels.empty())
      continue;
    SmallVector<int, 4> st, cpy, alias;
    bool shape = true;
    for (const auto &A : HS->atoms) {
      using SA = GlobalContext::SummaryAtom;
      bool plain = A.dst == -1 && A.src >= 0 && !A.gsrc && !A.gdst &&
                   !A.gsrc2 && A.dstByteOff == 0 && A.srcByteOff == 0;
      if (A.kind == SA::Fresh) continue;
      if (A.kind == SA::Store && plain) st.push_back(A.src);
      else if (A.kind == SA::Cpy && plain) cpy.push_back(A.src);
      else if (A.kind == SA::Alias && plain) alias.push_back(A.src);
      else { shape = false; break; }
    }
    if (!shape) continue;
    for (auto *v : {&st, &cpy, &alias}) {
      std::sort(v->begin(), v->end());
      v->erase(std::unique(v->begin(), v->end()), v->end());
    }
    handRows[HF] = freshLine(HF->getName(), st, cpy, alias);
  }
  // Hides a hand row for the check of its own function; restores it on
  // every exit from the loop body.
  struct HiddenRow {
    GlobalContext *C = nullptr;
    const Function *F = nullptr;
    const GlobalContext::FuncSummary *S = nullptr;
    bool alloc = false;
    void hide(GlobalContext *Cx, const Function *Fn) {
      C = Cx; F = Fn; S = Cx->FuncSummaries.at(Fn);
      alloc = Cx->AllocFuncs.erase(Fn);
      Cx->FuncSummaries.erase(Fn);
    }
    ~HiddenRow() {
      if (!C) return;
      C->FuncSummaries[F] = S;
      if (alloc) C->AllocFuncs.insert(F);
    }
  };
  size_t redundantRows = 0;
  size_t round = 0;
  // Phases. Lfp: rounds promote wrappers over confirmed allocators until
  // none is added (least fixpoint). Then the recursive candidates (members
  // of a cycle of direct calls among unconfirmed pointer-returning
  // functions: _objalloc_alloc calls itself) get the greatest fixpoint
  // (plan 3.53 rule 3, Fable 2026-10-12): the set is assumed fresh
  // (`assumed`: its calls are fresh sources), Probe rounds check each
  // member under that assumption and drop the failures until the set is
  // stable, and a GfpPromote round promotes the survivors; Lfp then runs
  // again over them. Check: the redundancy report, last.
  enum Phase { Lfp, Probe, GfpPromote, Check } phase = Lfp;
  std::unordered_set<const Function *> assumed, passed;
  bool gfpDone = false;
  bool changed = true;
  // Counters as of the fixpoint: probe and check rounds leave them unchanged.
  size_t *cs[] = {&g_freshPromoted, &g_freshRejRet, &g_freshRejEscape,
                  &g_freshRejSide, &g_freshInit, &g_escapeSamples,
                  &g_freshHelperComposed, &g_freshCpy, &g_freshAlias};
  size_t sv[9];
  std::map<std::string, size_t> svBuckets, svCallees;
  auto saveCounters = [&]() {
    for (unsigned i = 0; i < 9; i++) sv[i] = *cs[i];
    svBuckets = g_escapeBuckets;
    svCallees = g_escapeCallees;
  };
  auto restoreCounters = [&]() {
    for (unsigned i = 0; i < 9; i++) *cs[i] = sv[i];
    g_escapeBuckets = svBuckets;
    g_escapeCallees = svCallees;
  };
  // Unconfirmed pointer-returning functions with a body that lie on a
  // cycle of direct calls among themselves (Tarjan).
  auto recursiveCandidates = [&]() {
    auto eligible = [&](const Function *G) {
      return G && !G->isDeclaration() && !G->empty() && G->getReturnType()->isPointerTy() &&
             !Ctx->AllocFuncs.count(G) && !Ctx->ContainerFuncs.count(G) && !Ctx->FuncSummaries.count(G);
    };
    auto callees = [&](const Function *G, SmallVectorImpl<const Function *> &out) {
      for (const Instruction &I : instructions(*G))
        if (const auto *CB = dyn_cast<CallBase>(&I))
          if (const Function *CF = CB->getCalledFunction()) {
            const Function *D = CF->isDeclaration() ? getFuncDef(const_cast<Function *>(CF)) : CF;
            if (eligible(D)) out.push_back(D);
          }
    };
    std::unordered_set<const Function *> out;
    std::unordered_map<const Function *, unsigned> index, low;
    std::unordered_set<const Function *> onStack;
    std::vector<const Function *> stack;
    unsigned next = 0;
    std::function<void(const Function *)> strong = [&](const Function *V) {
      index[V] = low[V] = next++;
      stack.push_back(V);
      onStack.insert(V);
      SmallVector<const Function *, 8> succ;
      callees(V, succ);
      bool self = false;
      for (const Function *W : succ) {
        self |= W == V;
        if (!index.count(W)) {
          strong(W);
          low[V] = std::min(low[V], low[W]);
        } else if (onStack.count(W)) {
          low[V] = std::min(low[V], index[W]);
        }
      }
      if (low[V] != index[V]) return;
      std::vector<const Function *> scc;
      const Function *W;
      do {
        W = stack.back();
        stack.pop_back();
        onStack.erase(W);
        scc.push_back(W);
      } while (W != V);
      if (scc.size() > 1 || self) out.insert(scc.begin(), scc.end());
    };
    for (auto &mp : Ctx->Modules)
      for (Function &G : *mp.first)
        if (eligible(&G) && !index.count(&G)) strong(&G);
    return out;
  };
  size_t gfpRounds = 0, gfpPromoted = 0;
  bool first = true;
  while (true) {
    if (first) {
      first = false;
    } else if (phase == Lfp) {
      if (!changed) {
        assumed = gfpDone ? std::unordered_set<const Function *>() : recursiveCandidates();
        phase = assumed.empty() ? Check : Probe;
        saveCounters();
      }
    } else if (phase == Probe) {
      restoreCounters();
      if (passed.size() == assumed.size()) {
        phase = GfpPromote;
      } else if (passed.empty()) {
        assumed.clear();
        gfpDone = true;
        phase = Check;
      } else {
        assumed = passed;
      }
    } else if (phase == GfpPromote) {
      assumed.clear();
      gfpDone = !changed; // nothing promoted: no further greatest fixpoint
      phase = Lfp;
      changed = true;
    } else {
      break; // the check ran
    }
    const bool checking = phase == Check, probing = phase == Probe;
    const bool quiet = checking || probing;
    if (phase == Lfp || phase == GfpPromote) round++;
    if (probing) {
      passed.clear();
      gfpRounds++;
    }
    changed = false;
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        HiddenRow hidden;
        if (checking) {
          if (!handRows.count(&F)) continue;
          hidden.hide(Ctx, &F);
          // A recursive row is checked at its greatest fixpoint: its own
          // calls are assumed fresh while it is checked.
          assumed.clear();
          assumed.insert(&F);
        } else if ((probing || phase == GfpPromote) && !assumed.count(&F)) {
          continue;
        }
        if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
        if (!F.getReturnType()->isPointerTy()) continue;
        if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
          continue;
        if (Ctx->FuncSummaries.count(&F)) continue;
        // Fresh sources: allocator callees (file FRESH, promoted, or
        // hardcoded). A callee whose summary also carries CPY(ret<-argK)
        // (the realloc/strdup shape) is a fresh source that COPIES: the
        // wrapper inherits the copy from whichever of its own formals
        // reaches the callee's argK (resolved after R3). A callee with
        // any other atom (init stores, invoke) is not composed here.
        SmallVector<std::pair<const CallBase *, int>, 4> cpySrcs;
        // A callee whose result also ALIASes its argK (realloc: FRESH
        // covers realloc(NULL, n), the alias carries the old object): the
        // wrapper aliases whichever of its own formals reaches argK (plan
        // 3.53 follow-up 2: the realloc-wrapper shape).
        SmallVector<std::pair<const CallBase *, int>, 4> aliasSrcs;
        auto calleeFresh = [&](const CallBase *CB) {
          const Function *CF = CB->getCalledFunction();
          if (CF && !assumed.empty() &&
              assumed.count(CF->isDeclaration() ? getFuncDef(const_cast<Function *>(CF)) : CF))
            return true; // inside the assumed-fresh set (greatest fixpoint)
          if (!CF || !Ctx->AllocFuncs.count(CF)) return false;
          auto sit = Ctx->FuncSummaries.find(CF);
          if (sit == Ctx->FuncSummaries.end())
            sit = Ctx->FuncSummaries.find(
                getFuncDef(const_cast<Function *>(CF)));
          if (sit == Ctx->FuncSummaries.end()) return true; // hardcoded
          for (const auto &A : sit->second->atoms) {
            if (A.kind == GlobalContext::SummaryAtom::Fresh) continue;
            if (A.kind == GlobalContext::SummaryAtom::Cpy && A.dst == -1 &&
                A.src >= 0) {
              cpySrcs.push_back({CB, A.src});
              continue;
            }
            if (A.kind == GlobalContext::SummaryAtom::Alias && A.dst == -1 &&
                A.src >= 0 && A.srcByteOff == 0) {
              aliasSrcs.push_back({CB, A.src});
              continue;
            }
            return false;
          }
          return true;
        };
        // R1: trace returns to fresh sources.
        SmallPtrSet<const Value *, 16> onRetPath;
        SmallVector<const Value *, 8> work;
        bool ok = true;
        const Value *r1bad = nullptr; // first non-fresh return source
        for (auto &BB : F)
          if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
            if (RI->getReturnValue()) work.push_back(RI->getReturnValue());
        if (work.empty()) continue; // no pointer actually returned
        while (!work.empty() && ok) {
          const Value *v = work.pop_back_val();
          if (!onRetPath.insert(v).second) continue;
          if (isa<ConstantPointerNull>(v) || isa<UndefValue>(v)) continue;
          // A carve of a certified pool is a fresh object (rule 3).
          if (const auto *CI = dyn_cast<Instruction>(v); CI && poolCarves.count(CI)) continue;
          if (const auto *CE = dyn_cast<ConstantExpr>(v)) {
            if (CE->getOpcode() == Instruction::IntToPtr) continue; // ERR_PTR
            ok = false;
            continue;
          }
          if (const auto *CB = dyn_cast<CallBase>(v)) {
            if (!calleeFresh(CB)) { ok = false; r1bad = v; }
            continue;
          }
          if (const auto *PN = dyn_cast<PHINode>(v)) {
            for (const Value *iv : PN->incoming_values()) work.push_back(iv);
            continue;
          }
          if (const auto *Sel = dyn_cast<SelectInst>(v)) {
            work.push_back(Sel->getTrueValue());
            work.push_back(Sel->getFalseValue());
            continue;
          }
          if (const auto *Cast = dyn_cast<CastInst>(v)) {
            if (Cast->getOpcode() == Instruction::BitCast ||
                Cast->getOpcode() == Instruction::AddrSpaceCast) {
              work.push_back(Cast->getOperand(0));
              continue;
            }
          }
          if (const auto *L = dyn_cast<LoadInst>(v)) {
            // O0 reload of a spill slot: the stores that reach it.
            if (const AllocaInst *AI = isSpillSlot(L->getPointerOperand())) {
              SmallVector<const StoreInst *, 4> defs;
              reachingSlotStores(L, AI, defs);
              if (defs.empty()) { ok = false; continue; } // uninitialised
              for (const StoreInst *D : defs)
                work.push_back(D->getValueOperand());
              continue;
            }
          }
          ok = false; // GEP, load, argument, anything else: not pure fresh
          r1bad = v;
        }
        if (!ok) {
          g_freshRejRet++;
          static size_t r1Samples = 0;
          if ((!quiet || !CFLTraceFunc.empty()) && (r1Samples++ < 20 || !CFLTraceFunc.empty()) && r1bad) {
            // With --cfl-trace-func every R1 rejection is logged (a
            // wrapper that should have been promoted is debugged here).
            std::string t; raw_string_ostream os(t); os << *r1bad;
            CG_LOG("ConfirmFresh R1: " << F.getName() << " returns "
                   << StringRef(os.str()).ltrim().substr(0, 80) << "\n");
          }
          continue;
        }
        // R2/B: classify every use of the fresh object graph. Allowed:
        // the return path, null checks, and — the STEP-B extension —
        // GEP chains off the fresh pointer whose leaves are stores of
        // FORMAL ARGUMENTS (or non-pointer values) into the object:
        // the alloc-init shape, expressible as ST(*ret <- argI) atoms
        // applied per callsite (an infinite clone with no graph
        // duplication). Anything else remains an escape.
        SmallPtrSet<const Value *, 16> freshGraph; // fresh ptr + GEPs
        SmallPtrSet<const Instruction *, 8> initStores;
        SmallVector<const Instruction *, 4> certExempt; // pool bookkeeping (plan 3.55 (a))
        SmallPtrSet<const Instruction *, 4> initCalls; // composed helpers
        SmallVector<int, 4> initArgs;
        SmallVector<const GlobalValue *, 4> initGlobals;
        unsigned subAllocs = 0;
        bool selfStore = false;
        bool escaped = false, untracedInit = false;
        const char *rejWhy = nullptr; // escape-anatomy bucket
        {
          SmallVector<const Value *, 8> gwork;
          for (const Value *v : onRetPath)
            if (isa<CallBase>(v) || (isa<Instruction>(v) && poolCarves.count(cast<Instruction>(v))))
              gwork.push_back(v);
          SmallPtrSet<const Value *, 16> seen;
          while (!gwork.empty() && !escaped) {
            const Value *v = gwork.pop_back_val();
            if (!seen.insert(v).second) continue;
            freshGraph.insert(v);
            for (const User *U : v->users()) {
              const Value *uv = cast<Value>(U);
              if (isa<ICmpInst>(U) || isa<ReturnInst>(U)) continue;
              if (onRetPath.count(uv)) {
                // A return-path value (cast, phi, reload) is the fresh
                // pointer too: its OTHER users must be classified — at
                // O0 the cast is also spilled into a slot; at O2 a
                // return-path phi stored elsewhere would be an escape
                // that skipping it here silently missed.
                gwork.push_back(uv);
                continue;
              }
              if (isa<GetElementPtrInst>(U) || isa<BitCastInst>(U)) {
                gwork.push_back(uv);
                continue;
              }
              // A read of a certified pool's handle field of the object
              // whose value stays in that pool (plan 3.55 (a)).
              if (const auto *LU = dyn_cast<LoadInst>(U); LU && LU->getPointerOperand() == v) {
                SmallVector<const Instruction *, 4> ps;
                auto it = poolFieldAccess.find(LU);
                if (it != poolFieldAccess.end() && poolUsesOnly(LU, it->second, ps)) {
                  certExempt.push_back(LU);
                  for (const Instruction *PS : ps) {
                    initStores.insert(PS);
                    certExempt.push_back(PS);
                  }
                  continue;
                }
              }
              if (const auto *SI = dyn_cast<StoreInst>(U)) {
                // The pool's own bump (p + n stored back into H) moves
                // no object: the next carve is another.
                if (poolBookkeeping.count(SI)) continue;
                // store INTO the fresh graph is init; storing the fresh
                // pointer ITSELF somewhere else is an escape — bucket
                // it by where it lands.
                if (SI->getValueOperand() == v) {
                  if (const AllocaInst *AI =
                          isSpillSlot(SI->getPointerOperand())) {
                    // O0 spill of the fresh pointer: the reloads this
                    // store reaches ARE the pointer — classify their
                    // uses with the same rules.
                    for (const User *LU : AI->users())
                      if (const auto *L2 = dyn_cast<LoadInst>(LU)) {
                        SmallVector<const StoreInst *, 4> defs;
                        reachingSlotStores(L2, AI, defs);
                        if (llvm::is_contained(defs, SI)) gwork.push_back(L2);
                      }
                    continue;
                  }
                  const Value *pb =
                      SI->getPointerOperand()->stripPointerCasts();
                  while (const auto *G2 = dyn_cast<GetElementPtrInst>(pb))
                    pb = G2->getPointerOperand()->stripPointerCasts();
                  if (seen.count(pb) || freshGraph.count(pb)) {
                    // self-linkage (INIT_LIST_HEAD): object interior
                    // stored into the object itself
                    initStores.insert(SI);
                    selfStore = true;
                    continue;
                  }
                  if (const auto *PA = dyn_cast<Argument>(pb))
                    rejWhy = PA->getParent() == &F ? "outparam-store"
                                                   : "store-foreign-arg";
                  else if (isa<GlobalVariable>(pb))
                    rejWhy = "global-store";
                  else if (isa<LoadInst>(pb))
                    rejWhy = "store-into-loaded"; // list linkage shape
                  else
                    rejWhy = "store-other";
                  escaped = true;
                  break;
                }
                const Value *sv =
                    SI->getValueOperand()->stripPointerCasts();
                if (!containsPointerType(sv->getType())) {
                  initStores.insert(SI);
                  continue;
                }
                // O0: the stored value is a reload of a spilled formal
                // (`list->free_data = fun`). Resolve through the slot;
                // every reaching value must classify as an init source.
                if (const auto *SL = dyn_cast<LoadInst>(sv)) {
                  if (const AllocaInst *SAI =
                          isSpillSlot(SL->getPointerOperand())) {
                    SmallVector<const StoreInst *, 4> defs;
                    reachingSlotStores(SL, SAI, defs);
                    bool allOk = !defs.empty();
                    SmallVector<int, 2> args2;
                    SmallVector<const GlobalValue *, 2> globs2;
                    for (const StoreInst *D : defs) {
                      const Value *dv = D->getValueOperand()->stripPointerCasts();
                      if (isa<ConstantPointerNull>(dv)) continue;
                      if (const auto *DA = dyn_cast<Argument>(dv)) {
                        if (DA->getParent() == &F) { args2.push_back((int)DA->getArgNo()); continue; }
                      }
                      if (const auto *DG = dyn_cast<GlobalValue>(dv)) { globs2.push_back(DG); continue; }
                      allOk = false;
                      break;
                    }
                    if (allOk) {
                      initStores.insert(SI);
                      initArgs.append(args2.begin(), args2.end());
                      initGlobals.append(globs2.begin(), globs2.end());
                      continue;
                    }
                  }
                }
                if (const auto *A2 = dyn_cast<Argument>(sv)) {
                  if (A2->getParent() == &F) {
                    initStores.insert(SI);
                    initArgs.push_back((int)A2->getArgNo());
                    continue;
                  }
                }
                if (isa<ConstantPointerNull>(sv)) {
                  initStores.insert(SI);
                  continue;
                }
                if (const auto *GVs = dyn_cast<GlobalValue>(sv)) {
                  initStores.insert(SI); // ops table / named fn into fresh
                  initGlobals.push_back(GVs);
                  continue;
                }
                if (const auto *SubCB = dyn_cast<CallBase>(sv)) {
                  // second allocation stored into the object
                  // (vm_area_alloc's vma_lock): FreshSub atom, provided
                  // the sub-result's other uses are only null checks
                  // and error-path frees
                  const Function *SubF = SubCB->getCalledFunction();
                  if (SubF && Ctx->AllocFuncs.count(SubF)) {
                    bool subOk = true;
                    for (const User *SU : SubCB->users()) {
                      if (SU == SI || isa<ICmpInst>(SU)) continue;
                      if (const auto *FC = dyn_cast<CallBase>(SU)) {
                        const Function *FF = FC->getCalledFunction();
                        if (FF && isFreeFn(FF->getName())) continue;
                      }
                      subOk = false;
                      break;
                    }
                    if (subOk) {
                      initStores.insert(SI);
                      subAllocs++;
                      continue;
                    }
                  }
                }
                // Into a certified pool's handle field, a value derived
                // from that pool's chunk (plan 3.55 (a)).
                if (auto it = poolFieldAccess.find(SI);
                    it != poolFieldAccess.end() && poolDerived(sv, it->second, 0)) {
                  initStores.insert(SI);
                  certExempt.push_back(SI);
                  continue;
                }
                untracedInit = true; // ptr from load/call: reject
                rejWhy = isa<GlobalValue>(sv)   ? "init-from-global"
                         : isa<LoadInst>(sv)    ? "init-from-load"
                         : isa<CallBase>(sv)    ? "init-from-call"
                         : isa<PHINode>(sv)     ? "init-from-phi"
                                                : "init-other";
                break;
              }
              if (const auto *CB2 = dyn_cast<CallBase>(U)) {
                const Function *EC = CB2->getCalledFunction();
                if (EC && (EC->getName().starts_with("llvm.memset") ||
                           EC->getName().starts_with("llvm.lifetime") ||
                           EC->getName().starts_with("llvm.dbg"))) {
                  continue; // zeroing/markers: no pointer content moved
                }
                if (const auto *MT = dyn_cast<MemTransferInst>(CB2)) {
                  // Bytes copied INTO the fresh object (xmemdup shape):
                  // a residue-preserving copy from the source's pointee
                  // — CPY(ret<-argJ) once the source traces to formal J
                  // (checked after R3 with the callee-CPY sources).
                  // The fresh pointer as SOURCE stays an escape.
                  if (MT->getRawDest()->stripPointerCasts() == v &&
                      !isa<GetElementPtrInst>(v)) { // whole object, offset 0
                    cpySrcs.push_back({CB2, 1});
                    initCalls.insert(CB2);
                    continue;
                  }
                }
                // Curated benign-init callees: lock/waitqueue/completion
                // initializers store no program function pointers at
                // init time (lockdep names/keys are rodata metadata).
                // LEDGERed via the promotion log; extend deliberately.
                static const char *kBenignInit[] = {
                    "__raw_spin_lock_init", "lockdep_init_map_type",
                    "__init_waitqueue_head", "__mutex_init",
                    "init_completion", "__init_swait_queue_head",
                    "__init_rwsem", "seqcount_init", "__seqcount_init"};
                bool benign = false;
                if (EC)
                  for (const char *bn : kBenignInit)
                    if (EC->getName() == bn) { benign = true; break; }
                if (benign) {
                  initCalls.insert(CB2);
                  continue;
                }
                if (EC && isFreeFn(EC->getName())) {
                  // fresh freed on an error path: the object dies; the
                  // summary's fresh-object over-approximation is sound
                  initCalls.insert(CB2);
                  continue;
                }
                bool composed = false;
                if (EC && CB2->getCalledOperand()->stripPointerCasts() != v) {
                  const InitInfo &inf = initOnlyInfo(EC);
                  bool posOk = inf.valid &&
                               inf.objParam < (int)CB2->arg_size() &&
                               CB2->getArgOperand(inf.objParam)
                                       ->stripPointerCasts() == v;
                  if (posOk)
                    for (unsigned ai = 0; ai < CB2->arg_size(); ai++)
                      if ((int)ai != inf.objParam &&
                          CB2->getArgOperand(ai)->stripPointerCasts() == v)
                        posOk = false; // fresh escapes via a second slot
                  if (posOk) {
                    bool mapOk = true;
                    SmallVector<int, 4> mapped;
                    for (int m2 : inf.srcFormals) {
                      if (m2 >= (int)CB2->arg_size()) { mapOk = false; break; }
                      const Value *av =
                          CB2->getArgOperand(m2)->stripPointerCasts();
                      if (!containsPointerType(av->getType())) continue;
                      if (isa<ConstantPointerNull>(av)) continue;
                      if (const auto *AA = dyn_cast<Argument>(av)) {
                        if (AA->getParent() == &F) {
                          mapped.push_back((int)AA->getArgNo());
                          continue;
                        }
                      }
                      mapOk = false;
                      break;
                    }
                    if (mapOk) {
                      for (int g3 : mapped) initArgs.push_back(g3);
                      for (const GlobalValue *G5 : inf.srcGlobals)
                        initGlobals.push_back(G5);
                      if (inf.selfStore) selfStore = true;
                      initCalls.insert(CB2);
                      composed = true;
                      g_freshHelperComposed++;
                    }
                  }
                }
                if (!composed) {
                  rejWhy = EC ? "call-escape" : "icall-escape";
                  if (EC) g_escapeCallees[EC->getName().str()]++;
                  escaped = true;
                  break;
                }
                continue;
              }
              if (isa<PHINode>(U) || isa<SelectInst>(U)) {
                rejWhy = "phi-route";
                escaped = true;
                break;
              }
              if (isa<PtrToIntInst>(U)) rejWhy = "ptrtoint";
              else rejWhy = "other-use";
              escaped = true;
              break;
            }
          }
        }
        if (escaped || untracedInit) {
          g_freshRejEscape++;
          g_escapeBuckets[rejWhy ? rejWhy : "unknown"]++;
          if ((!quiet || !CFLTraceFunc.empty()) && g_escapeSamples < 40 && rejWhy) {
            g_escapeSamples++;
            CG_LOG("ConfirmFresh ESCAPE: " << F.getName() << " ["
                   << rejWhy << "]\n");
          }
          continue;
        }
        // R3: no pointer side effects elsewhere (classified init stores
        // are exempt — they become atoms).
        const Instruction *r3bad = nullptr;
        for (auto II = inst_begin(F), IE = inst_end(F); II != IE && ok;
             ++II) {
          const Instruction *I2 = &*II;
          if (poolBookkeeping.count(I2)) continue; // a certified pool's own state
          if (const auto *SI = dyn_cast<StoreInst>(I2)) {
            if (initStores.count(I2)) continue;
            // A store into a non-escaping local slot moves nothing out
            // of the function; the reload's uses are judged above.
            if (isSpillSlot(SI->getPointerOperand())) continue;
            if (containsPointerType(SI->getValueOperand()->getType())) {
              ok = false;
              r3bad = I2;
            }
            continue;
          }
          if (const auto *CB = dyn_cast<CallBase>(I2)) {
            if (initCalls.count(I2)) continue; // composed init helper
            const Function *CF = CB->getCalledFunction();
            if (CF && (isNoopIntrinsic(CF) || Ctx->AllocFuncs.count(CF) ||
                       isFreeFn(CF->getName())))
              continue;
            // A call that does not return (noreturn on the call or the
            // callee, the block ending in unreachable: bpf_error,
            // __assert_fail, png_error): no execution through it returns
            // the result, and its effects (a longjmp included) stay in the
            // kept body (BODY).
            if (CB->doesNotReturn() && isa_and_nonnull<UnreachableInst>(CB->getNextNonDebugInstruction()))
              continue;
            if (CF && !assumed.empty() &&
                assumed.count(CF->isDeclaration() ? getFuncDef(const_cast<Function *>(CF)) : CF))
              continue; // inside the assumed-fresh set

            if (CF) { // NOOP-summarized callee (strlen in xstrdup):
              auto nit = Ctx->FuncSummaries.find(CF); // transfers nothing
              if (nit != Ctx->FuncSummaries.end() && nit->second->noop)
                continue;
            }
            bool ptrInvolved =
                containsPointerType(CB->getType()) && !onRetPath.count(CB);
            for (const Value *a2 : CB->args())
              if (containsPointerType(a2->getType())) ptrInvolved = true;
            if (!CF || ptrInvolved) { ok = false; r3bad = I2; }
            continue;
          }
          if (isa<PtrToIntInst>(I2) || isa<AtomicRMWInst>(I2) ||
              isa<AtomicCmpXchgInst>(I2)) {
            ok = false;
            r3bad = I2;
          }
        }
        if (!ok) {
          g_freshRejSide++;
          if (!CFLTraceFunc.empty() && r3bad) {
            std::string t; raw_string_ostream os(t); os << *r3bad;
            CG_LOG("ConfirmFresh R3: " << F.getName() << " side effect "
                   << StringRef(os.str()).ltrim().substr(0, 80) << "\n");
          }
          continue;
        }
        // Inherit CPY(ret<-argK) from a copying fresh callee: the actual
        // at argK must be one of F's own formals (through spill reloads
        // and casts) or null (realloc(NULL, n) is malloc). Anything else
        // — a local object, a global, a loaded pointer, a call result in
        // a loop — is not composable and rejects the wrapper.
        // The formals of F that reach argument K of call CCB (through
        // spill reloads and casts; null is allowed: realloc(NULL, n) is
        // malloc). Anything else is not composable.
        auto formalsAt = [&](const CallBase *CCB, int K, SmallVectorImpl<int> &out) {
          if (K >= (int)CCB->arg_size()) return false;
          SmallVector<const Value *, 4> tw{CCB->getArgOperand(K)->stripPointerCasts()};
          SmallPtrSet<const Value *, 8> tseen;
          while (!tw.empty()) {
            const Value *tv = tw.pop_back_val();
            if (!tseen.insert(tv).second) continue;
            if (const auto *TA = dyn_cast<Argument>(tv)) {
              if (TA->getParent() != &F) return false;
              out.push_back((int)TA->getArgNo());
              continue;
            }
            if (isa<ConstantPointerNull>(tv)) continue;
            if (const auto *TL = dyn_cast<LoadInst>(tv)) {
              if (const AllocaInst *AI = isSpillSlot(TL->getPointerOperand())) {
                SmallVector<const StoreInst *, 4> defs;
                reachingSlotStores(TL, AI, defs);
                if (defs.empty()) return false;
                for (const StoreInst *D : defs)
                  tw.push_back(D->getValueOperand()->stripPointerCasts());
                continue;
              }
            }
            if (const auto *TC = dyn_cast<CastInst>(tv)) {
              tw.push_back(TC->getOperand(0));
              continue;
            }
            return false;
          }
          return true;
        };
        SmallVector<int, 4> cpyArgs, aliasArgs;
        bool cpyOk = true;
        for (auto &[CCB, K] : cpySrcs)
          if (!formalsAt(CCB, K, cpyArgs)) { cpyOk = false; break; }
        if (!cpyOk) {
          g_freshRejEscape++;
          g_escapeBuckets["cpy-src-untraced"]++;
          continue;
        }
        bool aliasOk = true;
        for (auto &[CCB, K] : aliasSrcs)
          if (!formalsAt(CCB, K, aliasArgs)) { aliasOk = false; break; }
        if (!aliasOk) {
          g_freshRejEscape++;
          g_escapeBuckets["alias-src-untraced"]++;
          continue;
        }
        std::sort(aliasArgs.begin(), aliasArgs.end());
        aliasArgs.erase(std::unique(aliasArgs.begin(), aliasArgs.end()), aliasArgs.end());
        std::sort(cpyArgs.begin(), cpyArgs.end());
        cpyArgs.erase(std::unique(cpyArgs.begin(), cpyArgs.end()),
                      cpyArgs.end());
        if (checking) {
          // A hand row the engine confirms with the same line: reported,
          // not promoted (the row stays in force).
          std::sort(initArgs.begin(), initArgs.end());
          initArgs.erase(std::unique(initArgs.begin(), initArgs.end()),
                         initArgs.end());
          if (initGlobals.empty() && !selfStore && subAllocs == 0 &&
              freshLine(F.getName(), initArgs, cpyArgs, aliasArgs) ==
                  handRows[&F]) {
            redundantRows++;
            CG_LOG("ConfirmFresh: REDUNDANT hand row " << handRows[&F]
                   << " (the engine confirms it given the other rows)\n");
          }
          continue;
        }
        if (probing) {
          passed.insert(&F); // fresh under the assumption
          continue;
        }
        // Promote. Pure fresh -> shared static summary; alloc-init ->
        // generated {FRESH, ST(*ret <- argI)...} summary (owned by Ctx).
        Ctx->AllocFuncs.insert(&F);
        if (initArgs.empty() && initGlobals.empty() && !selfStore &&
            subAllocs == 0 && cpyArgs.empty() && aliasArgs.empty()) {
          Ctx->FuncSummaries[&F] = &pureFresh;
        } else {
          Ctx->OwnedSummaries.emplace_back();
          GlobalContext::FuncSummary &S = Ctx->OwnedSummaries.back();
          S.fresh = true;
          S.body = true;
          std::sort(initArgs.begin(), initArgs.end());
          initArgs.erase(std::unique(initArgs.begin(), initArgs.end()),
                         initArgs.end());
          for (int an : initArgs) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::Store;
            A.dst = -1; // *ret
            A.src = an;
            S.atoms.push_back(A);
          }
          if (selfStore) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::Store;
            A.dst = -1;
            A.src = -1; // object interior stored into itself
            S.atoms.push_back(A);
          }
          for (unsigned si2 = 0; si2 < subAllocs; si2++) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::FreshSub;
            A.dst = -1; // sub-object into *ret
            S.atoms.push_back(A);
          }
          {
            std::sort(initGlobals.begin(), initGlobals.end());
            initGlobals.erase(
                std::unique(initGlobals.begin(), initGlobals.end()),
                initGlobals.end());
            for (const GlobalValue *G5 : initGlobals) {
              GlobalContext::SummaryAtom A{};
              A.kind = GlobalContext::SummaryAtom::Store;
              A.dst = -1; // *ret
              A.gsrc = G5;
              S.atoms.push_back(A);
            }
          }
          for (int cj : cpyArgs) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::Cpy;
            A.dst = -1; // *ret <- *argcj, residue-complete at apply
            A.src = cj;
            S.atoms.push_back(A);
          }
          for (int aj : aliasArgs) {
            GlobalContext::SummaryAtom A{};
            A.kind = GlobalContext::SummaryAtom::Alias;
            A.dst = -1; // ret = argaj (the realloc'd object)
            A.src = aj;
            S.atoms.push_back(A);
          }
          if (!aliasArgs.empty()) g_freshAlias++;
          Ctx->FuncSummaries[&F] = &S;
          if (!cpyArgs.empty()) g_freshCpy++;
          else if (aliasArgs.empty()) g_freshInit++;
        }
        g_freshPromoted++;
        if (phase == Lfp || phase == GfpPromote) g_poolCertExempt.insert(certExempt.begin(), certExempt.end());
        if (phase == GfpPromote) gfpPromoted++;
        changed = true;
        if (g_freshPromoted <= 20)
          CG_LOG("ConfirmFresh: promoted " << F.getName()
                 << (initArgs.empty() ? "" : " [alloc-init]")
                 << (cpyArgs.empty() ? "" : " [copy]")
                 << (aliasArgs.empty() ? "" : " [realloc]") << " (round "
                 << round << ")\n");
        {
          // The promotion as a summary-file line (harvestable: a library
          // run's output becomes its interface summary).
          std::string ln = freshLine(F.getName(), initArgs, cpyArgs, aliasArgs);
          if (selfStore) ln += " # +self-store";
          if (subAllocs) ln += " # +" + std::to_string(subAllocs) + " sub-alloc";
          CG_LOG("ConfirmFresh: LINE " << ln << "\n");
        }
      }
    }
  }
  restoreCounters();
  if (gfpRounds)
    CG_LOG("ConfirmFresh: recursive candidates: " << gfpRounds << " probe rounds, " << gfpPromoted
           << " promoted at the greatest fixpoint\n");
  CG_LOG("ConfirmFresh: " << redundantRows << " of " << handRows.size()
         << " hand FRESH rows the engine confirms with the same line, "
         << "given the other rows\n");
  CG_LOG("ConfirmFresh: " << g_freshPromoted << " wrappers promoted ("
         << g_freshInit << " alloc-init with ST atoms, " << g_freshCpy
         << " copying with CPY atoms, " << g_freshAlias
         << " realloc wrappers with ALIAS atoms) in " << round
         << " rounds; " << g_freshHelperComposed << " init-helper calls "
         << "composed; rejected " << g_freshRejRet << " ret-not-fresh, "
         << g_freshRejEscape << " escapes, " << g_freshRejSide
         << " ptr-side-effects; " << g_poolCertExempt.size()
         << " handle-field reads and stores exempted by a pool certificate (the pool's own bookkeeping)\n");
  for (auto &eb : g_escapeBuckets)
    CG_LOG("ConfirmFresh escape-bucket[" << eb.first << "]: " << eb.second
           << "\n");
  {
    std::vector<std::pair<size_t, std::string>> ce;
    for (auto &kv : g_escapeCallees) ce.emplace_back(kv.second, kv.first);
    std::sort(ce.begin(), ce.end(), std::greater<>());
    size_t shown = 0;
    for (auto &kv : ce) {
      if (shown++ >= 25) break;
      CG_LOG("ConfirmFresh escape-callee x" << kv.first << " " << kv.second
             << "\n");
    }
  }
}

// --func-summaries: parse the transfer-summary file. Line format:
//   <name>[*] ATOM [ATOM...]   ('*' suffix = prefix match; '#' comments)
// Atoms: FRESH | NONE | CPY(ret<-argN) | CPY(argM<-argN) |
//        ALIAS(ret=argN) | ST(*argC<-argV) | LD(ret<-*argC)
// Ordered, first match wins (NONE entries carve exclusions out of a
// following prefix rule, mirroring the legacy isAllocFn ordering).
// Parse errors are FATAL: a silently dropped summary is a silent
// soundness/precision change.
void loadFuncSummaries(GlobalContext *Ctx, const std::string &path) {
  std::ifstream in(path);
  if (!in) {
    errs() << "FuncSummary: cannot open " << path << "\n";
    assert(false && "--func-summaries file unreadable");
    return;
  }
  // The summary file is part of the trusted semantic specification
  // (authoritative over hardcoded models when loaded) — pin its
  // content hash in every log so answer pins are attributable to a
  // specific spec version (design-review clarification #4).
  if (auto mb = MemoryBuffer::getFile(path)) {
    llvm::SHA256 H;
    H.update((*mb)->getBuffer());
    auto D = H.final();
    CG_LOG("FuncSummary: spec sha256=" << llvm::toHex(D, true) << " ("
           << (*mb)->getBufferSize() << " bytes) " << path << "\n");
  }
  auto parseRef = [](StringRef tok, int &out) -> bool {
    if (tok == "ret") { out = -1; return true; }
    if (tok.consume_front("arg")) {
      unsigned v;
      if (!tok.getAsInteger(10, v)) { out = (int)v; return true; }
    }
    return false;
  };
  // "argN@K" / "ret@K": deref-side ref with a byte offset (field cell)
  auto parseDerefRef = [&](StringRef tok, int &out, int &byteOff) -> bool {
    byteOff = 0;
    auto [base, offs] = tok.split('@');
    if (offs == "X") {
      byteOff = -1; // wildcard offset (fx self-loop at apply)
    } else if (!offs.empty()) {
      unsigned v;
      if (offs.getAsInteger(10, v)) return false;
      byteOff = (int)v;
    }
    return parseRef(base, out);
  };
  // **argN@outer (inner 0) or **argN@inner@outer; outer may be X.
  auto parse2Ref = [&](StringRef tok, int &out, int &inner, int &outer) -> bool {
    inner = 0;
    auto [base, offs] = tok.split('@');
    auto [first, second] = offs.split('@');
    if (!second.empty()) {
      unsigned v;
      if (first.getAsInteger(10, v)) return false;
      inner = (int)v;
      return parseDerefRef((base + "@" + second).str(), out, outer);
    }
    return parseDerefRef(tok, out, outer);
  };
  std::string line;
  size_t lineNo = 0, nFresh = 0, nCpy = 0, nAlias = 0, nSt = 0, nLd = 0,
         nNone = 0, nInv = 0, nChR = 0, nChC = 0, nNoop = 0, nChGated = 0;
  // '@scope extern' / '@scope all': entries that follow apply only to
  // functions without a body / to every function (default). Derived
  // libc blocks are extern-only: a program that defines a same-named
  // function (the kernel's sort, sem_init, strlcpy; tcpdump's strlcpy)
  // gets its body analyzed, not the libc model.
  bool scopeExtern = false;
  // `@container NAME` ... `@container end`: rows of one container (plan
  // 3.55): `<function> ROLE(lookup|insert|traverse|remove|carve|pure)
  // [OWNER(argN)] [ELEM(argN|ret)] [CREATE(argN)] [POOL(argN)]
  // [KEY(argN) FIELD(T+off)]`; not transfer atoms.
  GlobalContext::ContainerSpec *curContainer = nullptr;
  auto badRow = [&](StringRef why) {
    errs() << "FuncSummary: " << path << ":" << lineNo << ": container row: " << why << "\n";
    assert(false && "malformed container row in func_summaries.txt");
  };
  while (std::getline(in, line)) {
    lineNo++;
    StringRef L = StringRef(line).trim();
    if (L.empty() || L.starts_with("#")) continue;
    if (L.starts_with("@")) {
      StringRef d = L.drop_front(1).trim();
      if (d == "scope extern") { scopeExtern = true; continue; }
      if (d == "scope all") { scopeExtern = false; continue; }
      if (d.consume_front("container ")) {
        d = d.trim();
        if (d == "end") {
          if (!curContainer) badRow("@container end without a block");
          curContainer = nullptr;
          continue;
        }
        if (curContainer || d.empty()) badRow("nested or unnamed @container");
        Ctx->Containers.emplace_back();
        curContainer = &Ctx->Containers.back();
        curContainer->name = d.str();
        continue;
      }
      errs() << "FuncSummary: " << path << ":" << lineNo
             << ": unknown directive '" << L << "'\n";
      assert(false && "unknown func_summaries directive");
      continue;
    }
    SmallVector<StringRef, 6> toks;
    L.split(toks, ' ', -1, false);
    if (curContainer) {
      GlobalContext::ContainerRow R;
      R.line = lineNo;
      bool role = false;
      auto argOf = [&](StringRef t, int &out) {
        if (!parseRef(t, out)) badRow(("bad reference '" + t + "'").str());
      };
      for (size_t i = 1; i < toks.size(); i++) {
        StringRef t = toks[i].trim();
        if (t.empty()) continue;
        if (!t.consume_back(")")) badRow(("bad token '" + t + "'").str());
        auto [k, v] = t.split('(');
        if (k == "ROLE") {
          using CR = GlobalContext::ContainerRow;
          role = true;
          if (v == "lookup") R.role = CR::Lookup;
          else if (v == "insert") R.role = CR::Insert;
          else if (v == "traverse") R.role = CR::Traverse;
          else if (v == "remove") R.role = CR::Remove;
          else if (v == "carve") R.role = CR::Carve;
          else if (v == "pure") R.role = CR::Pure;
          else badRow(("unknown role '" + v + "'").str());
        } else if (k == "OWNER") argOf(v, R.owner);
        else if (k == "ELEM") argOf(v, R.elem);
        else if (k == "CREATE") argOf(v, R.create);
        else if (k == "POOL") argOf(v, R.pool);
        else if (k == "KEY") argOf(v, R.key);
        else if (k == "FIELD") R.field = v.str();
        else badRow(("unknown key '" + k + "'").str());
      }
      using CR = GlobalContext::ContainerRow;
      if (!role) badRow("no ROLE");
      if ((R.role == CR::Lookup || R.role == CR::Insert || R.role == CR::Traverse || R.role == CR::Remove) &&
          R.owner < 0)
        badRow("a lookup/insert/traverse/remove row needs OWNER(argN)");
      if (R.role == CR::Insert && R.elem == -2) badRow("an insert row needs ELEM");
      if (R.role == CR::Carve && R.pool < 0) badRow("a carve row needs POOL(argN)");
      if (!curContainer->rows.emplace(toks[0].str(), R).second) badRow("a function twice in one container");
      continue;
    }
    GlobalContext::FuncSummary S;
    S.externOnly = scopeExtern;
    bool hasChainAtom = false;
    bool bad = toks.size() < 2;
    for (size_t i = 1; i < toks.size() && !bad; i++) {
      StringRef t = toks[i].trim();
      if (t.empty()) continue;
      GlobalContext::SummaryAtom A{};
      // AS(argN@K:T): a label atom (plan 3.46). On ST/LD, ":T" after the
      // container ref says argN points to a T (the access is at K inside
      // it): the atom plus AS(argN@0:T).
      if (t.consume_front("AS(") && t.consume_back(")")) {
        auto [r, ty] = t.split(':');
        int arg = -1, off = 0;
        bad = ty.empty() || !parseDerefRef(r, arg, off) || arg < 0 || off < 0;
        if (!bad) S.labels.push_back({arg, off, nullptr, ty.str()});
        continue;
      }
      std::string typedTok;
      if ((t.starts_with("ST(*") || t.starts_with("LD(")) && t.contains(':')) {
        const bool st = t.starts_with("ST(*");
        auto [lhs, rhs] = t.split("<-");
        StringRef cont = st ? lhs : rhs;
        auto [ref, ty] = cont.split(':');
        if (ty.empty() || ty.contains(')') == st) { bad = true; continue; }
        const StringRef tyName = st ? ty : ty.drop_back(1);
        StringRef base = ref;
        if (st) base.consume_front("ST(*");
        else base.consume_front("*");
        int arg = -1, off0 = 0;
        if (!parseDerefRef(base, arg, off0) || arg < 0) { bad = true; continue; }
        S.labels.push_back({arg, 0, nullptr, tyName.str()});
        typedTok = st ? (ref + "<-" + rhs).str() : (lhs + "<-" + ref + ")").str();
        t = typedTok;
      }
      if (t == "FRESH") {
        A.kind = GlobalContext::SummaryAtom::Fresh;
        S.fresh = true;
        nFresh++;
      } else if (t == "NONE") {
        S.none = true;
        nNone++;
        continue;
      } else if (t == "BODY") {
        S.body = true; // keep analyzing the body (a FRESH wrapper's own calls)
        continue;
      } else if (t == "POOL") {
        S.pool = true;
        continue;
      } else if (t.consume_front("SIZE(") && t.consume_back(")")) {
        SmallVector<StringRef, 2> fs;
        t.split(fs, '*');
        for (StringRef f : fs) {
          unsigned n = 0;
          if (!f.consume_front("arg") || f.getAsInteger(10, n) || fs.size() > 2) { bad = true; break; }
          S.sizeArgs.push_back(n);
        }
        continue;
      } else if (t.consume_front("FREE(arg") && t.consume_back(")")) {
        int n = -1;
        if (t.getAsInteger(10, n) || n < 0) { bad = true; continue; }
        S.freeArg = n;
        continue;
      } else if (t == "NOOP") {
        S.noop = true;
        nNoop++;
        continue;
      } else if (t == "EMPTY") {
        // Proven pointer-transfer-free with a body that must stay
        // walked (in-body dispatch/asm survives): callsite wiring cut,
        // zero atoms, no body-skip — the file form of the adopted
        // EMPTY-ATOM class.
        nNoop++;
        continue;
      } else if (t.consume_front("CPY(") && t.consume_back(")")) {
        auto [d, s] = t.split("<-");
        A.kind = GlobalContext::SummaryAtom::Cpy;
        bad = !parseRef(d, A.dst) || !parseRef(s, A.src) || A.src < 0;
        nCpy++;
      } else if (t.consume_front("ALIAS(") && t.consume_back(")")) {
        // Both "ALIAS(ret=argN)" (legacy) and "ALIAS(ret<-argN[@K])"
        // (generator) forms; @K = interior alias (ret = argN + K).
        auto [d, s] = t.contains("<-") ? t.split("<-") : t.split("=");
        A.kind = GlobalContext::SummaryAtom::Alias;
        bad = !parseRef(d, A.dst) ||
              !parseDerefRef(s, A.src, A.srcByteOff) || A.src < 0;
        nAlias++;
      } else if (t.consume_front("ST(*") && t.consume_back(")")) {
        // ST(*argC@K<-argV) or ST(*ret@K<-argV): the latter initialises
        // a field of the fresh result (what the confirmer's alloc-init
        // atoms say; hash_initialize's hasher/comparator slots).
        auto [c, v] = t.split("<-");
        A.kind = GlobalContext::SummaryAtom::Store;
        bad = !parseDerefRef(c, A.dst, A.dstByteOff) ||
              !parseDerefRef(v, A.src, A.srcByteOff);
        nSt++;
      } else if (t.consume_front("MVX(*") && t.consume_back(")")) {
        auto [c, v] = t.split("<-*");
        A.kind = GlobalContext::SummaryAtom::MoveX;
        bad = !parseDerefRef(c, A.dst, A.dstByteOff) ||
              !parseDerefRef(v, A.src, A.srcByteOff) || A.dst < 0 ||
              A.src < 0;
        nSt++;
      } else if (t.consume_front("MV(*") && t.consume_back(")")) {
        auto [c, v] = t.split("<-*");
        A.kind = GlobalContext::SummaryAtom::Move;
        bad = !parseDerefRef(c, A.dst, A.dstByteOff) ||
              !parseDerefRef(v, A.src, A.srcByteOff) || A.dst < 0 ||
              A.src < 0;
        nSt++;
      } else if (t.consume_front("FRESHSUB(*") && t.consume_back(")")) {
        // FRESHSUB(*argN): a fresh per-callsite object stored into *argN
        // (the lazily created container of linked_list_append).
        int off0 = 0;
        A.kind = GlobalContext::SummaryAtom::FreshSub;
        bad = !parseDerefRef(t, A.dst, off0) || A.dst < 0;
        nFresh++;
      } else if (t.consume_front("ST2(**") && t.consume_back(")")) {
        // ST2(**argN@off<-argV[@K]): value into field off of the object
        // the pointer in *argN@0 points to (exact, no wildcard).
        // ST2(**argN@inner@outer<-argV): the pointer in *argN@inner, then
        // field or element `outer` of what it points to (X: any element;
        // GList::append's data[length]).
        auto [c, v] = t.split("<-");
        A.kind = GlobalContext::SummaryAtom::Store2;
        A.exact2 = true;
        bad = !parse2Ref(c, A.dst, A.innerOff, A.dstByteOff) ||
              !parseDerefRef(v, A.src, A.srcByteOff) || A.dst < 0 || A.src < 0;
        nSt++;
      } else if (t.consume_front("LD2(ret<-**") && t.consume_back(")")) {
        // LD2(ret<-**argN@off) and LD2(ret<-**argN@inner@outer)
        // (GList::get: data[i] = LD2(ret<-**arg0@data@X)).
        A.kind = GlobalContext::SummaryAtom::Load2;
        A.exact2 = true;
        A.dst = -1;
        bad = !parse2Ref(t, A.src, A.innerOff, A.srcByteOff) || A.src < 0;
        nLd++;
      } else if (t.consume_front("DISPATCH(") && t.consume_back(")")) {
        // DISPATCH(fnref:fK<-valref[@siteFn]); ref = argN | *argN@off |
        // **argN@off. The indirect call(s) inside siteFn (default: the
        // summarized callee) take their callee from fnref and formal K
        // from valref; the site keeps its identity for the answer.
        A.kind = GlobalContext::SummaryAtom::Dispatch;
        auto parseLvl = [&](StringRef r, int &idx, int &off, int &lvl) {
          lvl = 0;
          while (r.consume_front("*")) lvl++;
          return parseDerefRef(r, idx, off) && idx >= 0 && lvl <= 2;
        };
        auto [fnp, rest2] = t.split(':');
        bad = !parseLvl(fnp, A.dst, A.dstByteOff, A.fnLevel);
        auto [fk, rest3] = rest2.split("<-");
        StringRef vp = rest3;
        const size_t at = rest3.rfind('@');
        if (at != StringRef::npos) {
          StringRef tail = rest3.substr(at + 1);
          unsigned tmpv;
          if (tail != "X" && tail.getAsInteger(10, tmpv)) { // a name
            A.siteFn = tail.str();
            vp = rest3.substr(0, at);
          }
        }
        bad = bad || !parseLvl(vp, A.src, A.srcByteOff, A.valLevel);
        unsigned fkv = 0;
        StringRef fks = fk;
        bad = bad || !fks.consume_front("f") || fks.getAsInteger(10, fkv);
        A.aux = (int)fkv;
        nInv++;
      } else if (t.consume_front("INVOKE(") && t.consume_back(")")) {
        auto [fnp, rest2] = t.split(":");
        A.kind = GlobalContext::SummaryAtom::Invoke;
        bad = !parseRef(fnp, A.dst) || A.dst < 0;
        if (!bad && rest2 == "ret") {
          // ret-transparency only: INVOKE(argF:ret). Args stay pooled
          // (no completeness claim); constant-fn callsites bind the
          // invoked fn's return to THIS callsite value instead of the
          // pooled HOF return (the ret-pooling hub channel).
          A.src = -1;
          A.aux = -1;
          A.off = 1;
        } else if (!bad) {
          auto [fk, dp] = rest2.split("<-");
          if (dp.consume_back(":ret"))
            A.off = 1; // data binding + ret-transparency
          // argD, or argD@X: the callback receives an INTERIOR pointer
          // into the data argument (qsort's comparator over the base
          // array) — bound with the wildcard shift.
          bad = !parseDerefRef(dp, A.src, A.srcByteOff) || A.src < 0;
          unsigned fkv = 0;
          if (!bad) {
            StringRef fks = fk;
            bad = !fks.consume_front("f") || fks.getAsInteger(10, fkv);
            A.aux = (int)fkv;
          }
        }
        nInv++;
      } else if (t.consume_front("CHAINREG(") && t.consume_back(")")) {
        // CHAINREG(argK,*argB+OFF,fS): key at argK; callback at byte
        // OFF inside the block global at argB; block -> formal fS
        SmallVector<StringRef, 3> ps;
        t.split(ps, ',');
        A.kind = GlobalContext::SummaryAtom::ChainReg;
        hasChainAtom = true;
        bad = ps.size() != 3;
        if (!bad) {
          StringRef k = ps[0];
          if (k.consume_front("@")) {
            A.gsym = k.str(); // global-keyed variant (wrapper lift)
            bad = A.gsym.empty();
          } else {
            bad = !parseRef(k, A.dst) || A.dst < 0;
          }
        }
        if (!bad) {
          StringRef b = ps[1];
          bad = !b.consume_front("*");
          auto [ba, boff] = b.split('+');
          unsigned offv = 0, fkv = 0;
          bad = bad || !parseRef(ba, A.src) || A.src < 0 ||
                boff.getAsInteger(10, offv);
          StringRef fs = ps[2];
          bad = bad || !fs.consume_front("f") || fs.getAsInteger(10, fkv);
          A.off = (int)offv;
          A.fk = (int)fkv;
        }
        nChR++;
      } else if (t.consume_front("CHAINCALL(") && t.consume_back(")")) {
        // CHAINCALL(argK:fN<-argV) or CHAINCALL(@sym:fN<-argV): key at
        // argK / the named global; dispatch value argV -> each
        // registered callback's formal fN
        auto [kp, rest2] = t.split(':');
        auto [fkp, vp] = rest2.split("<-");
        A.kind = GlobalContext::SummaryAtom::ChainCall;
        hasChainAtom = true;
        unsigned fkv = 0;
        StringRef fks = fkp;
        if (kp.consume_front("@")) {
          A.gsym = kp.str();
          A.dst = -1;
          bad = A.gsym.empty();
        } else {
          bad = !parseRef(kp, A.dst) || A.dst < 0;
        }
        bad = bad || !parseRef(vp, A.src) || A.src < 0 ||
              !fks.consume_front("f") || fks.getAsInteger(10, fkv);
        A.fk = (int)fkv;
        nChC++;
      } else if (t.consume_front("ST2(**") && t.consume_back(")")) {
        auto [c, v] = t.split("<-");
        A.kind = GlobalContext::SummaryAtom::Store2;
        bad = !parseDerefRef(c, A.dst, A.dstByteOff) ||
              !parseDerefRef(v, A.src, A.srcByteOff) || A.dst < 0;
        nSt++;
      } else if (t.consume_front("MV2(**") && t.consume_back(")")) {
        auto [c, v] = t.split("<-*");
        A.kind = GlobalContext::SummaryAtom::Move2;
        bad = !parseDerefRef(c, A.dst, A.dstByteOff) ||
              !parseDerefRef(v, A.src, A.srcByteOff) || A.dst < 0 ||
              A.src < 0;
        nSt++;
      } else if (t.consume_front("LD2(") && t.consume_back(")")) {
        auto [d, c] = t.split("<-**");
        A.kind = GlobalContext::SummaryAtom::Load2;
        bad = !parseRef(d, A.dst) ||
              !parseDerefRef(c, A.src, A.srcByteOff) || A.src < 0;
        nLd++;
      } else if (t.consume_front("LDX(") && t.consume_back(")")) {
        auto [d, c] = t.split("<-*");
        A.kind = GlobalContext::SummaryAtom::LoadX;
        bad = !parseRef(d, A.dst) ||
              !parseDerefRef(c, A.src, A.srcByteOff) || A.src < 0;
        nLd++;
      } else if (t.consume_front("LD(") && t.consume_back(")")) {
        auto [d, c] = t.split("<-*");
        A.kind = GlobalContext::SummaryAtom::Load;
        bad = !parseRef(d, A.dst) ||
              !parseDerefRef(c, A.src, A.srcByteOff) || A.src < 0;
        nLd++;
      } else {
        bad = true;
      }
      if (!bad && !S.none) S.atoms.push_back(A);
    }
    if (S.noop && (!S.atoms.empty() || S.none || S.fresh))
      bad = true; // NOOP is standalone: it owns the whole callsite
    if (bad) {
      errs() << "FuncSummary: parse error at " << path << ":" << lineNo
             << ": '" << line << "'\n";
      assert(false && "malformed func-summaries line");
      continue;
    }
    // Chain-channel lines (CHAINREG/CHAINCALL) are consumed only under
    // --cfl-propose-chain-summaries. Skipping the WHOLE spec keeps the
    // function on normal pooled wiring; dropping only the atom would
    // leave an empty spec, which handleCall treats as transfer-free and
    // would sever the registration without a channel replacing it.
    if (hasChainAtom && !CFLProposeChainSummaries) {
      nChGated++;
      continue;
    }
    Ctx->SummarySpecs.emplace_back(toks[0].str(), std::move(S));
  }
  if (curContainer) badRow("unterminated @container block");
  for (const auto &C : Ctx->Containers)
    CG_LOG("FuncSummary: container " << C.name << ": " << C.rows.size() << " rows (" << C.provenance << ")\n");
  CG_LOG("FuncSummary: loaded " << Ctx->SummarySpecs.size() << " specs from "
         << path << " (" << nFresh << " FRESH, " << nCpy << " CPY, "
         << nAlias << " ALIAS, " << nSt << " ST, " << nLd << " LD, "
         << nInv << " INVOKE, " << nChR << " CHAINREG, " << nChC
         << " CHAINCALL, " << nNone << " NONE, " << nNoop << " NOOP; "
         << nChGated << " chain-bearing specs GATED off: pass "
         << "--cfl-propose-chain-summaries to consume them)\n");
}

// First-match-wins spec lookup ('*' suffix = prefix).
const GlobalContext::FuncSummary *
summaryForName(GlobalContext *Ctx, StringRef name, bool hasBody) {
  for (const auto &sp : Ctx->SummarySpecs) {
    // An extern-only spec does not match a function that has a body;
    // matching continues (a later '@scope all' rule may still apply).
    if (hasBody && sp.second.externOnly) {
      StringRef p0(sp.first);
      bool h0 = p0.consume_back("*") ? name.starts_with(p0) : name == sp.first;
      if (h0)
        CG_LOG("FuncSummary: extern-only spec '" << sp.first
               << "' skipped for defined function " << name << "\n");
      continue;
    }
    StringRef pat(sp.first);
    bool glob = StringRef(sp.first).ends_with("*");
    bool hit = pat.consume_back("*") ? name.starts_with(pat) : name == pat;
    if (hit) {
      // Glob-expansion LEDGER: every name a glob classifies is one
      // census line — glob overreach (vmalloc* catching vmalloc_init)
      // silently mis-models whole bodies, so the expansion must be
      // auditable from any verbose log, not rediscovered by bisection.
      if (glob && name != StringRef(sp.first).drop_back())
        CG_LOG("FuncSummary glob '" << sp.first << "' classified "
               << name << (sp.second.none ? " (NONE)"
                           : sp.second.fresh ? " (FRESH)" : "") << "\n");
      return sp.second.none ? nullptr : &sp.second;
    }
  }
  return nullptr;
}

// Byte offsets of direct Function constants inside a static initializer
// (nested structs/arrays; pointers to other globals are NOT followed).
void walkInitFnOffsets(const Constant *C, uint64_t base,
                              const DataLayout &DL,
                              std::set<int64_t> &out) {
  if (const auto *CSt = dyn_cast<ConstantStruct>(C)) {
    const StructLayout *SL = DL.getStructLayout(CSt->getType());
    for (unsigned e = 0; e < CSt->getNumOperands(); e++)
      walkInitFnOffsets(CSt->getOperand(e), base + SL->getElementOffset(e),
                        DL, out);
  } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
    uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
    for (unsigned e = 0; e < CA->getNumOperands(); e++)
      walkInitFnOffsets(CA->getOperand(e), base + e * es, DL, out);
  } else if (isa<Function>(C->stripPointerCasts())) {
    out.insert((int64_t)base);
  }
}

// (byte offset -> Function) slots of a static initializer — the
// value-identified form of walkInitFnOffsets. Type-AGNOSTIC by
// construction: literal and named struct constants walk identically
// (the literal-table gap, docs/regfield-literal-table-gap.md — a
// table's identity must never depend on its type's spelling).
void walkInitFnSlots(const Constant *C, uint64_t base,
                            const DataLayout &DL,
                            std::map<uint64_t, const Function *> &out) {
  if (const auto *CSt = dyn_cast<ConstantStruct>(C)) {
    const StructLayout *SL = DL.getStructLayout(CSt->getType());
    for (unsigned e = 0; e < CSt->getNumOperands(); e++)
      walkInitFnSlots(CSt->getOperand(e), base + SL->getElementOffset(e),
                      DL, out);
  } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
    uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
    for (unsigned e = 0; e < CA->getNumOperands(); e++)
      walkInitFnSlots(CA->getOperand(e), base + e * es, DL, out);
  } else if (const auto *Fn = dyn_cast<Function>(C->stripPointerCasts())) {
    out[base] = Fn;
  }
}

// File-entry decay validator (always on when a summary file is loaded).
// The checked-in file must hold only version-portable semantics, but
// names/keys/offsets silently decay as the kernel moves (6.18 renamed
// scsi_register_driver -> __scsi_register_driver; pci_driver shifted
// -16 bytes). A decayed entry never errors — it just stops matching
// (sound, silently loses the model) — so decay must be a report line.
// Offset validation is PARTIAL by nature: it catches offsets landing on
// non-fn slots (alignment breaks), not fn-slot permutation — the chain
// prover's supplement policy is the mitigation for the latter.
void checkFileSummaries(GlobalContext *Ctx) {
  boost::unordered_flat_set<StringRef> fnNames, gvNames;
  for (auto &mp : Ctx->Modules) {
    for (Function &F : *mp.first) fnNames.insert(F.getName());
    for (GlobalVariable &G : mp.first->globals()) gvNames.insert(G.getName());
    for (GlobalAlias &A : mp.first->aliases()) {
      fnNames.insert(A.getName());
      gvNames.insert(A.getName());
    }
  }
  size_t unmatched = 0, badKeys = 0, staleOffs = 0;
  struct ChainCheck { int blkArg; std::set<int64_t> offs; };
  boost::unordered_flat_map<StringRef, ChainCheck> chainSpecs;
  for (const auto &sp : Ctx->SummarySpecs) {
    StringRef pat(sp.first);
    bool matched;
    if (pat.ends_with("*")) {
      StringRef p = pat.drop_back();
      matched = false;
      for (StringRef n : fnNames)
        if (n.starts_with(p)) { matched = true; break; }
    } else {
      matched = fnNames.count(pat) != 0;
    }
    if (!matched) {
      unmatched++;
      CG_LOG("SummaryCheck: UNMATCHED '" << sp.first
             << "' — dormant in this corpus (other-config/other-codebase "
                "coverage, or renamed upstream)\n");
    }
    for (const auto &A : sp.second.atoms) {
      if (!A.gsym.empty() && !gvNames.count(StringRef(A.gsym)) &&
          !fnNames.count(StringRef(A.gsym))) {
        badKeys++;
        CG_LOG("SummaryCheck: BAD-KEY '@" << A.gsym << "' in '"
               << sp.first << "' — key symbol absent from corpus "
                              "(dormant config? — sites fall back "
                              "pooled, sound)\n");
      }
      if (A.kind == GlobalContext::SummaryAtom::ChainReg && A.off >= 0 &&
          !pat.ends_with("*") && matched) {
        auto &CC = chainSpecs[pat];
        CC.blkArg = A.src;
        CC.offs.insert(A.off);
      }
    }
  }
  if (!chainSpecs.empty()) {
    boost::unordered_flat_map<StringRef, std::pair<unsigned, std::set<int64_t>>>
        seen; // name -> (conforming sites, fn-bearing offsets)
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration()) continue;
        for (inst_iterator ii = inst_begin(F), ie = inst_end(F); ii != ie;
             ++ii) {
          const auto *CB = dyn_cast<CallBase>(&*ii);
          if (!CB) continue;
          const Function *CF = CB->getCalledFunction();
          if (!CF) continue;
          auto it = chainSpecs.find(CF->getName());
          if (it == chainSpecs.end() ||
              (unsigned)it->second.blkArg >= CB->arg_size())
            continue;
          const auto *GV = dyn_cast<GlobalVariable>(
              CB->getArgOperand(it->second.blkArg)->stripPointerCasts());
          if (!GV || !GV->hasInitializer()) continue;
          auto &rec = seen[it->first];
          rec.first++;
          walkInitFnOffsets(GV->getInitializer(), 0,
                            GV->getParent()->getDataLayout(), rec.second);
        }
      }
    }
    for (auto &[name, CC] : chainSpecs) {
      auto sit = seen.find(name);
      if (sit == seen.end() || sit->second.first == 0) continue;
      for (int64_t o : CC.offs)
        if (!sit->second.second.count(o)) {
          staleOffs++;
          CG_LOG("SummaryCheck: STALE-OFFSET '" << name << "' CHAINREG off "
                 << o << " is fn-bearing in 0/" << sit->second.first
                 << " conforming callsites — layout drift\n");
        }
    }
  }
  // Absolute counts are a DORMANCY census (the file deliberately covers
  // other configs/codebases); DECAY is the cross-version diff — comm
  // the UNMATCHED/BAD-KEY lines of two kernels' logs: an entry live at
  // one vintage and dormant at the next is the renamed/removed set.
  if (unmatched || badKeys || staleOffs)
    errs() << "[WARN] SummaryCheck: " << unmatched
           << " entries dormant in this corpus, " << badKeys
           << " unresolvable @keys, " << staleOffs
           << " CHAINREG offsets not fn-bearing — see SummaryCheck lines "
              "(--verbose=2); diff against another vintage's lines to "
              "isolate decay\n";
  else
    CG_LOG("SummaryCheck: all " << Ctx->SummarySpecs.size()
           << " file entries resolve in this corpus\n");
}

static size_t g_sumDispatch = 0;
size_t g_sumCpy = 0, g_sumAlias = 0, g_sumSt = 0, g_sumLd = 0,
              g_sumSkipped = 0, g_sumFreshSub = 0, g_sumInvoke = 0,
              g_sumInvokeDyn = 0, g_chainReg = 0, g_chainRegDyn = 0,
              g_chainCall = 0, g_chainCallDyn = 0, g_chainLate = 0,
              g_sumLabels = 0;
// Returns true when an Invoke atom's fn operand is not a constant
// function at this callsite — the caller must fall back to the pooled
// arg/ret wiring for soundness (LEDGERed).
// Chain keys must be canonical across TUs: external-linkage heads have
// per-TU declaration copies; map through Gobjs/ExtGobjs by GUID.
const GlobalValue *CallGraphPass::canonChainKey(const GlobalValue *G) {
  if (!G || G->hasLocalLinkage()) return G;
  auto git = Ctx->Gobjs.find(G->getGUID());
  if (git != Ctx->Gobjs.end() && git->second) return git->second;
  auto eit = Ctx->ExtGobjs.find(G->getGUID());
  if (eit != Ctx->ExtGobjs.end() && eit->second) return eit->second;
  return G;
}

// Deref cell at a byte offset within *base — mirrors runtime
// store/load field handling under fs (field-ptr node + matched
// f-edges); at FI (or offset 0) the plain top cell.
// Named cells: the shape of a summary atom's write into
// summaryDerefCell(base, byteOff) — one pointer, or unknown extent at a
// wildcard offset — and the part of the offset that cell does not carry
// (field-insensitive cells are the base's own).
uint64_t CallGraphPass::summaryWriteSize(int byteOff) const {
  return byteOff < 0 ? 0
                     : Ctx->Modules.front().first->getDataLayout()
                           .getPointerSize();
}

int64_t CallGraphPass::summaryCellOffset(int byteOff) const {
  return (byteOff > 0 && !Graph.fieldSensitive()) ? byteOff : 0;
}

NodeIndex CallGraphPass::summaryDerefCell(NodeIndex base, int byteOff) {
  NodeIndex canon = getCanonicalNode(base);
  if (byteOff < 0 && Graph.fieldSensitive()) {
    // wildcard offset (@X): base cell + fx self-loop — the same
    // fallback the walked body uses for variable-offset GEP access
    addFieldWildcardLoop(canon, "summary-wildcard");
    return getRepDerefNode(canon);
  }
  if (byteOff <= 0 || !Graph.fieldSensitive())
    return getRepDerefNode(canon);
  NodeIndex f = getFieldPtrNode(canon, (int64_t)byteOff);
  addFieldEdgesExact(canon, getCanonicalNode(f), (int64_t)byteOff);
  return getRepDerefNode(getCanonicalNode(f));
}

// Two-level cell: deref(contents-of(cell(base@off1))), second level
// wildcard — the deref-of-deref chain a walked load-then-store builds.
// The cell node's plane IS the loaded pointers' value set, so its
// deref covers the pointed-to cells; the fx loop absorbs the unknown
// second-level offset/shift (FI: plain chain).
NodeIndex CallGraphPass::summaryDeref2Cell(NodeIndex base, int byteOff) {
  NodeIndex cellA = summaryDerefCell(base, byteOff);
  NodeIndex canonCell = getCanonicalNode(cellA);
  if (Graph.fieldSensitive())
    addFieldWildcardLoop(canonCell, "summary-2lvl");
  return getRepDerefNode(canonCell);
}

// Value-side interior ref "argN@K": the summarized callee produced a
// pointer INTO the actual at byte K (seq_buf_init's s->seq.buffer =
// s->buffer shape). Under field mode this is the actual's field-ptr
// node (origin preserved, shift K); under FI it collapses to the base
// — exactly what a walked GEP would do.
NodeIndex CallGraphPass::summaryFieldPtr(NodeIndex base, int byteOff) {
  NodeIndex canon = getCanonicalNode(base);
  if (byteOff < 0 && Graph.fieldSensitive()) {
    addFieldWildcardLoop(canon, "summary-wildcard");
    return canon;
  }
  if (byteOff <= 0 || !Graph.fieldSensitive())
    return canon;
  NodeIndex f = getFieldPtrNode(canon, (int64_t)byteOff);
  addFieldEdgesExact(canon, getCanonicalNode(f), (int64_t)byteOff);
  return getCanonicalNode(f);
}

// Resolve a chain-key symbol name to its defining GlobalValue:
// Gobjs -> ExtGobjs -> one-time unique-local-name scan (static chain
// heads are in no global map and invisible from caller TUs).
static const GlobalValue *resolveChainKeySym(GlobalContext *Ctx,
                                             const CallBase *CS,
                                             const std::string &sym) {
  const uint64_t g = llvm::GlobalValue::getGUID(sym);
  auto git = Ctx->Gobjs.find(g);
  if (git != Ctx->Gobjs.end() && git->second) return git->second;
  auto eit = Ctx->ExtGobjs.find(g);
  if (eit != Ctx->ExtGobjs.end() && eit->second) return eit->second;
  static std::unordered_map<std::string, const GlobalValue *> localByName;
  static bool scanned = false;
  if (!scanned) {
    scanned = true;
    for (auto &mp2 : Ctx->Modules)
      for (const GlobalVariable &GV2 : mp2.first->globals()) {
        if (!GV2.hasLocalLinkage() || !GV2.hasName()) continue;
        auto [it2, ins2] = localByName.emplace(GV2.getName().str(), &GV2);
        if (!ins2) it2->second = nullptr; // ambiguous
      }
  }
  auto lit = localByName.find(sym);
  if (lit != localByName.end() && lit->second) return lit->second;
  return CS->getModule()->getNamedValue(sym);
}

bool CallGraphPass::applySummaryAtoms(const CallBase *CS,
                                      const GlobalContext::FuncSummary &S,
                                      bool *retBound, const Function *SF) {
  // Label atoms (plan 3.46): a typed step of T from argN + K into a node
  // of its own; nothing transfers.
  for (const auto &LA : S.labels) {
    if (LA.arg < 0 || (unsigned)LA.arg >= CS->arg_size()) continue;
    const llvm::StructType *Ty = LA.ty;
    if (!Ty) {
      static std::map<std::string, const llvm::StructType *> byName;
      auto [it, ins] = byName.try_emplace(LA.tyName, nullptr);
      if (ins) {
        for (auto &[Mod, MName] : Ctx->Modules)
          for (llvm::StructType *ST : Mod->getIdentifiedStructTypes())
            if (ST->hasName() && !ST->isOpaque() &&
                stripStructNameSuffix(ST->getName()) == LA.tyName) {
              it->second = ST;
              break;
            }
        if (!it->second)
          errs() << "FuncSummary: label type " << LA.tyName
                 << " names no struct of the corpus (AS atom ignored)\n";
      }
      Ty = it->second;
      if (!Ty) continue;
    }
    NodeIndex a = getRepNodeForValue(CS->getArgOperand(LA.arg));
    if (a == AndersNodeFactory::InvalidIndex) continue;
    NodeIndex base = summaryFieldPtr(a, LA.off);
    NodeIndex sink = getCanonicalNode(NF.createValueNode());
    addFieldEdgesExact(getCanonicalNode(base), sink, 0, 0, false, Ty);
    g_sumLabels++;
  }
  if (S.noop)
    return false; // NOOP owns the callsite: nothing transfers
  bool needPooled = false;
  auto nodeForGlobal = [&](const llvm::GlobalValue *G) -> NodeIndex {
    // Resolve to the DEFINING instance (mirror getFuncDef): atoms may
    // carry the adopting TU's DECLARATION pointer, whose node routes
    // through the extern-symbol machinery — depositing there smeared
    // via the extern hub (5.18 phy_ethtool family, +27k pool pairs).
    if (G->isDeclaration() && G->hasName()) {
      auto git = Ctx->Gobjs.find(G->getGUID());
      if (git != Ctx->Gobjs.end()) G = git->second;
    }
    NodeIndex n = getRepNodeForValue(G);
    if (n == AndersNodeFactory::InvalidIndex)
      n = getCanonicalNode(
          NF.createValueNode(const_cast<llvm::GlobalValue *>(G)));
    return n;
  };
  auto nodeForRef = [&](int ref, bool create) -> NodeIndex {
    const Value *v =
        ref < 0 ? (const Value *)CS
                : ((unsigned)ref < CS->arg_size() ? CS->getArgOperand(ref)
                                                  : nullptr);
    if (!v) { g_sumSkipped++; return AndersNodeFactory::InvalidIndex; }
    NodeIndex n = getRepNodeForValue(v);
    if (n == AndersNodeFactory::InvalidIndex && create)
      n = getCanonicalNode(NF.createValueNode(v));
    if (n == AndersNodeFactory::InvalidIndex) g_sumSkipped++;
    return n;
  };
  // Named cells: an atom writing through formal `ref` (or global `g`)
  // at byte `off` writes field `off` of the struct that formal points
  // to, which the call site's untyped actual does not show.
  struct WritePos {
    CallGraphPass &P;
    bool Old;
    WritePos(CallGraphPass &P_, const Function *F, int ref,
             const GlobalValue *g, int off)
        : P(P_), Old(P_.cellWriteHasPos) {
      if (!P.namedPlanes() || off < 0)
        return;
      llvm::StructType *St = nullptr;
      if (g) {
        if (const auto *GV = dyn_cast<GlobalVariable>(g)) {
          Type *T = GV->getValueType();
          while (T->isArrayTy()) T = T->getArrayElementType();
          St = dyn_cast<llvm::StructType>(T);
          if (St && (St->isLiteral() || !St->hasName())) St = nullptr;
        }
      } else if (F && ref >= 0) {
        St = P.formalStruct(F, (unsigned)ref);
      }
      if (!St || (uint64_t)off >= P.curDL->getTypeAllocSize(St))
        return;
      P.cellWritePos = ka::AccessNames::Position();
      P.cellWritePos.S = St;
      P.cellWritePos.off = off;
      P.cellWriteWhere = "summary:" + (F ? F->getName().str() : std::string("?"));
      P.cellWriteHasPos = true;
    }
    ~WritePos() { P.cellWriteHasPos = Old; }
  };
  for (const auto &A : S.atoms) {
    switch (A.kind) {
    case GlobalContext::SummaryAtom::Fresh:
      break; // AllocFuncs path owns object creation
    case GlobalContext::SummaryAtom::Cpy: {
      NodeIndex d = nodeForRef(A.dst, true), s = nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          s == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(getRepDerefNode(getCanonicalNode(s)),
                        getRepDerefNode(getCanonicalNode(d)));
      // Residue-complete copy under field mode: CPY is memcpy
      // semantics — a byte copy preserves offsets, so EVERY residue
      // plane must relay, not just residue 0 (the deref edge above).
      // Same layout-free encoding as the llvm.memcpy small-copy path,
      // but NOT gated on --cfl-residue-copies: that flag bounds fact
      // volume over ALL unknown-layout memcpys; summary atoms are a
      // small hand-vetted struct-dup population, and skipping their
      // residues DROPS dynamically-true flows — fib_rules_ops kmemdup
      // lost 15/20 GT-true pairs at P=13, surviving field = offset
      // 104 ≡ 0 (mod 13) by residue accident (found via the 5.18 GT
      // target_absent shift 2026-08-18; invisible to t_kmemdup, whose
      // source fields are runtime stores).
      if (CFLCells) {
        // The cell solver copies cell by cell (arrays as one element).
        byteCopies.emplace_back(getCanonicalNode(s), getCanonicalNode(d),
                                (int64_t)-1, CS);
      } else if (flowsTo() && Graph.fieldSensitive() && exactFieldLabels()) {
        // Exact addresses: no residue set to relay; a byte copy of
        // unknown extent is the range wildcard on both sides.
        addFieldWildcardLoop(getCanonicalNode(s), "cpy-unknown-extent");
        addFieldWildcardLoop(getCanonicalNode(d), "cpy-unknown-extent");
      } else if (flowsTo() && Graph.fieldSensitive()) {
        const unsigned P = Graph.numFieldBuckets();
        NodeIndex sParent = getCanonicalNode(s);
        NodeIndex dParent = getCanonicalNode(d);
        for (unsigned r = 1; r < P; r++) {
          NodeIndex sF = getFieldPtrNode(sParent, (int64_t)r);
          NodeIndex dF = getFieldPtrNode(dParent, (int64_t)r);
          Graph.addField(sParent, getCanonicalNode(sF), (int)r);
          Graph.addField(dParent, getCanonicalNode(dF), (int)r);
          addAssignmentEdge(getRepDerefNode(getCanonicalNode(sF)),
                            getRepDerefNode(getCanonicalNode(dF)));
        }
      }
      g_sumCpy++;
      break;
    }
    case GlobalContext::SummaryAtom::Alias: {
      NodeIndex d = nodeForRef(A.dst, true);
      NodeIndex s = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, false);
      if (d == AndersNodeFactory::InvalidIndex ||
          s == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(summaryFieldPtr(s, A.srcByteOff),
                        getCanonicalNode(d));
      g_sumAlias++;
      break;
    }
    case GlobalContext::SummaryAtom::Store: {
      NodeIndex c = A.gdst ? nodeForGlobal(A.gdst) : nodeForRef(A.dst, true);
      NodeIndex v = A.gsrc    ? getRepNodeForValue(A.gsrc)
                    : A.gsrc2 ? nodeForGlobal(A.gsrc2)
                              : nodeForRef(A.src, false);
      if (A.gsrc && v == AndersNodeFactory::InvalidIndex)
        v = getCanonicalNode(NF.createValueNode(A.gsrc));
      if (c == AndersNodeFactory::InvalidIndex ||
          v == AndersNodeFactory::InvalidIndex)
        break;
      CellWriteSize ws(*this, summaryWriteSize(A.dstByteOff),
                       summaryCellOffset(A.dstByteOff));
      WritePos wp(*this, SF, A.dst, A.gdst, A.dstByteOff);
      addAssignmentEdge(A.gsrc ? getCanonicalNode(v)
                               : summaryFieldPtr(v, A.srcByteOff),
                        summaryDerefCell(c, A.dstByteOff));
      g_sumSt++;
      break;
    }
    case GlobalContext::SummaryAtom::Move: {
      NodeIndex d = A.gdst ? nodeForGlobal(A.gdst) : nodeForRef(A.dst, true);
      NodeIndex c = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      CellWriteSize ws(*this, summaryWriteSize(A.dstByteOff),
                       summaryCellOffset(A.dstByteOff), /*IsValue=*/true);
      WritePos wp(*this, SF, A.dst, A.gdst, A.dstByteOff);
      addAssignmentEdge(summaryDerefCell(c, A.srcByteOff),
                        summaryDerefCell(d, A.dstByteOff));
      g_sumSt++;
      break;
    }
    case GlobalContext::SummaryAtom::Invoke: {
      // pair-correlated dispatch: bind data to the registered fn's
      // formal directly and re-attribute the invocation to this
      // registration site (Callees export edge). The pooled container
      // path drains because the summarized registration no longer
      // feeds it. A.off==1 adds RET-TRANSPARENCY: the callsite value
      // receives (only) the invoked fn's return — severs the
      // ret-pooling hub channel (fwnode devcon family, task #31).
      if ((unsigned)A.dst >= CS->arg_size() ||
          (A.src >= 0 && (unsigned)A.src >= CS->arg_size())) {
        g_sumSkipped++;
        break;
      }
      const Value *fv = CS->getArgOperand(A.dst)->stripPointerCasts();
      if (isa<ConstantPointerNull>(fv))
        break; // null fn: never invoked, nothing to bind
      const auto *RF = dyn_cast<Function>(fv);
      if (!RF) {
        // dynamic fn: cannot bind statically — signal pooled fallback
        // (ret included: the pooled return edge stays)
        g_sumInvokeDyn++;
        needPooled = true;
        break;
      }
      Function *DF = getFuncDef(const_cast<Function *>(RF));
      if (A.src >= 0 && (unsigned)A.aux < DF->arg_size()) {
        NodeIndex dn = nodeForRef(A.src, false);
        NodeIndex fn2 = getRepNodeForValue(DF->getArg(A.aux));
        if (fn2 == AndersNodeFactory::InvalidIndex)
          fn2 = getCanonicalNode(NF.createValueNode(DF->getArg(A.aux)));
        if (dn != AndersNodeFactory::InvalidIndex) {
          // argD@X / argD@K: the formal receives an interior pointer.
          const NodeIndex src2 = A.srcByteOff != 0
                                     ? summaryFieldPtr(dn, A.srcByteOff)
                                     : getCanonicalNode(dn);
          addAssignmentEdge(src2, getCanonicalNode(fn2));
          g_sumInvoke++;
        }
      }
      if (A.off == 1) {
        if (containsPointerType(DF->getReturnType())) {
          NodeIndex rn = NF.getReturnNodeFor(DF);
          if (rn == AndersNodeFactory::InvalidIndex ||
              rn == NF.getUniversalPtrNode())
            rn = NF.createReturnNode(DF);
          NodeIndex cn = nodeForRef(-1, true);
          if (cn != AndersNodeFactory::InvalidIndex)
            addAssignmentEdge(getCanonicalNode(rn), getCanonicalNode(cn));
        }
        if (retBound)
          *retBound = true; // suppress the pooled HOF return edge
        if (A.src < 0)
          needPooled = true; // pure-ret: no claim about the args
        g_sumInvokeRet++;
      }
      Ctx->Callees[CS].insert(DF); // re-attributed callgraph edge
      break;
    }
    case GlobalContext::SummaryAtom::ChainReg: {
      if ((unsigned)A.src >= CS->arg_size() ||
          (A.dst >= 0 && (unsigned)A.dst >= CS->arg_size())) {
        g_sumSkipped++;
        break;
      }
      if (chainFinalized) { g_chainLate++; needPooled = true; break; }
      const GlobalValue *key = nullptr;
      if (A.gsrc) {
        key = A.gsrc; // derived (composition lift): already canonical
      } else if (!A.gsym.empty()) {
        key = resolveChainKeySym(Ctx, CS, A.gsym);
        if (key && key->isDeclaration())
          key = canonChainKey(key);
      } else if (A.dst >= 0) {
        key = canonChainKey(dyn_cast<GlobalValue>(
            CS->getArgOperand(A.dst)->stripPointerCasts()));
      }
      const auto *blk = dyn_cast<GlobalVariable>(
          CS->getArgOperand(A.src)->stripPointerCasts());
      Function *fn = nullptr;
      if (blk && blk->hasInitializer()) {
        // walk the constant initializer to the fn at byte offset A.off
        const DataLayout &DL = blk->getParent()->getDataLayout();
        const Constant *C = blk->getInitializer();
        uint64_t off = (uint64_t)A.off;
        while (C) {
          if (const auto *CSt = dyn_cast<ConstantStruct>(C)) {
            const StructLayout *SL = DL.getStructLayout(CSt->getType());
            unsigned e = SL->getElementContainingOffset(off);
            off -= SL->getElementOffset(e);
            C = CSt->getOperand(e);
          } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
            uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
            if (!es) { C = nullptr; break; }
            C = CA->getOperand(off / es);
            off %= es;
          } else {
            break;
          }
        }
        if (C && off == 0)
          fn = const_cast<Function *>(
              dyn_cast<Function>(C->stripPointerCasts()));
      }
      if (!key || !blk || !fn) {
        // dynamic key/block or runtime-installed callback: keep the
        // container fed (pooled) — sound, LEDGERed
        g_chainRegDyn++;
        needPooled = true;
        break;
      }
      chainRegs.push_back({key, blk, getFuncDef(fn), A.fk, CS});
      g_chainReg++;
      break;
    }
    case GlobalContext::SummaryAtom::ChainCall: {
      if ((A.gsym.empty() && (unsigned)A.dst >= CS->arg_size()) ||
          (unsigned)A.src >= CS->arg_size()) { g_sumSkipped++; break; }
      if (chainFinalized) { g_chainLate++; needPooled = true; break; }
      const GlobalValue *key =
          !A.gsym.empty()
              ? resolveChainKeySym(Ctx, CS, A.gsym)
              : canonChainKey(dyn_cast<GlobalValue>(
                    CS->getArgOperand(A.dst)->stripPointerCasts()));
      if (!key) { g_chainCallDyn++; needPooled = true; break; }
      if (!chainDispatches.empty() && chainDispatches.back().cs == CS &&
          chainDispatches.back().key == key) {
        chainDispatches.back().binds.push_back({A.fk, A.src});
      } else {
        ChainDispatchRec r{CS, key, {}};
        r.binds.push_back({A.fk, A.src});
        chainDispatches.push_back(std::move(r));
        g_chainCall++;
      }
      // The dispatch site ALWAYS keeps pooled wiring: pooled-fallback
      // registrations and manual chain links flow through the body,
      // and its icall must still resolve them (the paired subset is
      // additional). Draining here severed t_chain2's fallback reg.
      needPooled = true;
      break;
    }
    case GlobalContext::SummaryAtom::FreshSub: {
      NodeIndex d = nodeForRef(A.dst, true);
      if (d == AndersNodeFactory::InvalidIndex) break;
      NodeIndex subVal = getCanonicalNode(NF.createValueNode());
      NodeIndex subObj = NF.createOpaqueObjectNode(nullptr, true);
      // Provenance tag: anonymous minted objects otherwise print as
      // "<synthetic>" in weld blame / traces — the x20 15-subsys
      // unattributable bucket (2026-08-25).
      {
        const Function *TF = CS->getCalledFunction();
        std::string tag =
            "freshsub:" + (TF ? TF->getName().str() : std::string("<icall>")) +
            "@" + CS->getFunction()->getName().str();
        g_opaqueProvenance[subVal] = tag;
        g_opaqueProvenance[subObj] = tag;
      }
      Graph.addDeref(subVal, subObj);
      addAllocSite(subVal, subVal); // origin identity for the mint loop
      {
        CellWriteSize ws(*this, Ctx->Modules.front().first->getDataLayout()
                                    .getPointerSize());
        WritePos wp(*this, SF, A.dst, nullptr, 0);
        addAssignmentEdge(subVal, getRepDerefNode(getCanonicalNode(d)));
      }
      g_sumFreshSub++;
      break;
    }
    case GlobalContext::SummaryAtom::Load: {
      NodeIndex d = nodeForRef(A.dst, true);
      NodeIndex c = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(summaryDerefCell(c, A.srcByteOff),
                        getCanonicalNode(d));
      g_sumLd++;
      break;
    }
    case GlobalContext::SummaryAtom::Store2: {
      NodeIndex c = A.gdst ? nodeForGlobal(A.gdst) : nodeForRef(A.dst, true);
      NodeIndex v = A.gsrc2 ? nodeForGlobal(A.gsrc2)
                            : nodeForRef(A.src, false);
      if (c == AndersNodeFactory::InvalidIndex ||
          v == AndersNodeFactory::InvalidIndex)
        break;
      // File ST2: the pointer in *c@0, then field dstByteOff of what it
      // points to (exact); generated Store2 keeps its wildcard level 2.
      CellWriteSize ws(*this, summaryWriteSize(A.dstByteOff));
      addAssignmentEdge(summaryFieldPtr(v, A.srcByteOff),
                        A.exact2 ? summaryDerefCell(summaryDerefCell(c, A.innerOff),
                                                    A.dstByteOff)
                                 : summaryDeref2Cell(c, A.dstByteOff));
      g_sumSt++;
      break;
    }
    case GlobalContext::SummaryAtom::Dispatch: {
      auto refNode = [&](int idx, int lvl, int off) -> NodeIndex {
        NodeIndex b = nodeForRef(idx, false);
        if (b == AndersNodeFactory::InvalidIndex) return b;
        if (lvl == 0) return getCanonicalNode(b);
        if (lvl == 1) return summaryDerefCell(b, off);
        return summaryDerefCell(summaryDerefCell(b, 0), off);
      };
      const NodeIndex fnv = refNode(A.dst, A.fnLevel, A.dstByteOff);
      const NodeIndex valv = refNode(A.src, A.valLevel, A.srcByteOff);
      if (fnv == AndersNodeFactory::InvalidIndex) { g_sumSkipped++; break; }
      Function *siteF = nullptr;
      if (!A.siteFn.empty()) {
        siteF = CS->getModule()->getFunction(A.siteFn);
      } else if (const Function *TF = CS->getCalledFunction()) {
        siteF = const_cast<Function *>(TF);
      }
      if (siteF) siteF = getFuncDef(siteF);
      if (!siteF || siteF->isDeclaration()) { g_sumSkipped++; break; }
      for (auto II = inst_begin(*siteF), IE = inst_end(*siteF); II != IE; ++II) {
        auto *IC = dyn_cast<CallBase>(&*II);
        if (!IC || IC->isInlineAsm() || IC->getCalledFunction()) continue;
        Value *fop = IC->getCalledOperand()->stripPointerCastsAndAliases();
        if (isa<Function>(fop)) continue;
        NodeIndex icf = getRepNodeForValue(fop);
        if (icf == AndersNodeFactory::InvalidIndex)
          icf = getCanonicalNode(NF.createValueNode(fop));
        addAssignmentEdge(fnv, getCanonicalNode(icf)); // cell -> operand: a load
        if (valv != AndersNodeFactory::InvalidIndex &&
            (unsigned)A.aux < IC->arg_size()) {
          Value *av = IC->getArgOperand(A.aux)->stripPointerCasts();
          NodeIndex ica = getRepNodeForValue(av);
          if (ica == AndersNodeFactory::InvalidIndex)
            ica = getCanonicalNode(NF.createValueNode(av));
          addAssignmentEdge(valv, getCanonicalNode(ica));
        }
        Ctx->IndirectCallInsts.insert(IC);
        g_sumDispatch++;
      }
      break;
    }
    case GlobalContext::SummaryAtom::Move2: {
      NodeIndex d = A.gdst ? nodeForGlobal(A.gdst) : nodeForRef(A.dst, true);
      NodeIndex c = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      CellWriteSize ws(*this, summaryWriteSize(A.dstByteOff), 0,
                       /*IsValue=*/true);
      addAssignmentEdge(summaryDerefCell(c, A.srcByteOff),
                        summaryDeref2Cell(d, A.dstByteOff));
      g_sumSt++;
      break;
    }
    case GlobalContext::SummaryAtom::Load2: {
      NodeIndex d = nodeForRef(A.dst, true);
      NodeIndex c = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(A.exact2 ? summaryDerefCell(summaryDerefCell(c, A.innerOff),
                                                    A.srcByteOff)
                                 : summaryDeref2Cell(c, A.srcByteOff),
                        getCanonicalNode(d));
      g_sumLd++;
      break;
    }
    case GlobalContext::SummaryAtom::MoveX: {
      // interior-of-loaded stored into a cell: the stored VALUE is the
      // loaded value plus an unknown delta. The wildcard belongs to
      // that value (a fresh node with the fx self-loop, as LoadX does
      // for its result), NOT to the destination parent: a wildcard on
      // the parent makes every field of the destination object
      // offset-insensitive, fusing all its pointer fields regardless
      // of type (nm-new: pe_ILF_save_relocs's `vars->reltab +=
      // vars->relcount` collapsed the caller's pe_ILF_vars struct, and
      // its bfd* and bfd_in_memory* fields became one cell).
      NodeIndex d = A.gdst ? nodeForGlobal(A.gdst) : nodeForRef(A.dst, true);
      NodeIndex c = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      NodeIndex v = NF.createValueNode();
      g_opaqueProvenance[v] = "mvx-value";
      addAssignmentEdge(summaryDerefCell(c, A.srcByteOff), v);
      if (Graph.fieldSensitive())
        addFieldWildcardLoop(v, "summary-mvx");
      CellWriteSize ws(*this, summaryWriteSize(A.dstByteOff),
                       summaryCellOffset(A.dstByteOff));
      WritePos wp(*this, SF, A.dst, A.gdst, A.dstByteOff);
      addAssignmentEdge(v, summaryDerefCell(d, A.dstByteOff));
      g_sumSt++;
      break;
    }
    case GlobalContext::SummaryAtom::LoadX: {
      // interior-of-loaded: result = loaded value + unknown delta —
      // LD, then wildcard the RESULT's shift (fx self-loop; FI no-op)
      NodeIndex d = nodeForRef(A.dst, true);
      NodeIndex c = A.gsrc2 ? nodeForGlobal(A.gsrc2) : nodeForRef(A.src, true);
      if (d == AndersNodeFactory::InvalidIndex ||
          c == AndersNodeFactory::InvalidIndex)
        break;
      addAssignmentEdge(summaryDerefCell(c, A.srcByteOff),
                        getCanonicalNode(d));
      if (Graph.fieldSensitive())
        addFieldWildcardLoop(getCanonicalNode(d), "summary-ldx");
      g_sumLd++;
      break;
    }
    }
  }
  return needPooled;
}

// --cfl-confirm-invoke (task #28 tier 2): auto-confirm INVOKE summaries
// where the proof is LOCAL, under the #17 completeness discipline — a
// summary replaces callsite arg/ret wiring, so every pointer formal
// must be fully accounted by the atoms or provably benign; anything
// else rejects to the LEDGER.
//   DIRECT   the fn formal is invoked synchronously in the body with
//            other formals as arguments -> INVOKE atoms verbatim.
//   PASSTHRU formals are forwarded into an already-summarized INVOKE
//            callee -> the wrapper inherits translated atoms (+FRESH
//            when it returns the callee's fresh result). Fixpoint over
//            wrapper chains.
// Deferred shapes (FIELD/COSTORE) are NOT auto-confirmed: their
// dispatcher lives elsewhere; the census reports them for review.
static size_t g_invConfirmed = 0, g_invConfirmedPass = 0, g_invRejEscape = 0,
              g_invRejPtrRet = 0, g_invRejNoBinding = 0, g_invRejShape = 0,
              g_invConfirmedChain = 0;
void CallGraphPass::confirmInvokeSummaries() {
  // Benign transitive use of a pointer chain rooted at a formal:
  // address arithmetic and non-pointer reads/writes lose no pointer
  // flow when callsite wiring is dropped. PHIs/selects reject (v1).
  std::function<bool(const Value *)> benignChain = [&](const Value *V) {
    for (const User *U : V->users()) {
      if (isa<GEPOperator>(U) || isa<CastInst>(U)) {
        if (!benignChain(U)) return false;
      } else if (const auto *LI = dyn_cast<LoadInst>(U)) {
        if (containsPointerType(LI->getType())) return false;
      } else if (const auto *SI = dyn_cast<StoreInst>(U)) {
        if (SI->getValueOperand() == V) return false; // chain ptr escapes
        if (containsPointerType(SI->getValueOperand()->getType()))
          return false; // pointer written through the chain
      } else if (const auto *RMW = dyn_cast<AtomicRMWInst>(U)) {
        if (containsPointerType(RMW->getValOperand()->getType()))
          return false;
      } else if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(U)) {
        if (containsPointerType(CX->getNewValOperand()->getType()))
          return false;
      } else if (isa<ICmpInst>(U)) {
        // ok
      } else {
        return false;
      }
    }
    return true;
  };
  auto isNoopIntrinsic = [](const Function *IF) {
    if (!IF || !IF->isIntrinsic()) return false;
    switch (IF->getIntrinsicID()) {
    case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
    case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
    case Intrinsic::assume: case Intrinsic::expect:
      return true;
    default: return false;
    }
  };
  size_t rounds = 0;
  bool changed = true;
  SmallPtrSet<const Function *, 16> rejected; // don't re-check/re-count
  while (changed && rounds++ < 16) {
    changed = false;
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
        if (F.isVarArg()) continue;
        if (shouldSkipFunction(&F)) continue;
        if (Ctx->FuncSummaries.count(&F)) continue;
        if (rejected.count(&F)) continue;
        if (F.arg_size() < 1) continue; // chain wrappers are single-arg
        auto formalIdx = [&](const Value *V) -> int {
          V = V->stripPointerCasts();
          for (const auto &A : F.args())
            if (&A == V) return (int)A.getArgNo();
          return -1;
        };
        // Locate the dispatch sites: icalls on ONE fn formal (DIRECT)
        // and/or calls into summarized-INVOKE callees (PASSTHRU).
        int fnFormal = -1;
        bool multiFn = false;
        SmallPtrSet<const CallBase *, 4> fnIcalls, passCalls,
            chainPassCalls;
        for (const Instruction &I : instructions(F)) {
          const auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || CB->isInlineAsm()) continue;
          if (const Function *IC = CB->getCalledFunction()) {
            auto sit = Ctx->FuncSummaries.find(
                getFuncDef(const_cast<Function *>(IC)));
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(IC);
            if (sit == Ctx->FuncSummaries.end()) continue;
            bool onlyInvFresh = true;
            for (const auto &A : sit->second->atoms) {
              if (A.kind == GlobalContext::SummaryAtom::Invoke) {
                if ((unsigned)A.dst < CB->arg_size() &&
                    formalIdx(CB->getArgOperand(A.dst)) >= 0)
                  passCalls.insert(CB);
              } else if (A.kind == GlobalContext::SummaryAtom::ChainReg) {
                // wrapper forwards its block formal into a CHAINREG
                // callee whose key is CONSTANT here -> liftable
                if ((unsigned)A.src < CB->arg_size() &&
                    formalIdx(CB->getArgOperand(A.src)) >= 0 &&
                    (A.gsrc || !A.gsym.empty() ||
                     (A.dst >= 0 && (unsigned)A.dst < CB->arg_size() &&
                      isa<GlobalValue>(CB->getArgOperand(A.dst)
                                           ->stripPointerCasts()))))
                  chainPassCalls.insert(CB);
              } else if (A.kind != GlobalContext::SummaryAtom::Fresh) {
                onlyInvFresh = false; // CPY/ST/... translation: v1 out
              }
            }
            if (!onlyInvFresh) {
              passCalls.erase(CB); // CPY/ST etc.: v1 out
              chainPassCalls.erase(CB);
            }
            continue;
          }
          int fi = formalIdx(CB->getCalledOperand());
          if (fi < 0) continue;
          if (fnFormal != -1 && fnFormal != fi) multiFn = true;
          fnFormal = fi;
          fnIcalls.insert(CB);
        }
        if (fnIcalls.empty() && passCalls.empty() && chainPassCalls.empty())
          continue;
        const int shapes = (!fnIcalls.empty()) + (!passCalls.empty()) +
                           (!chainPassCalls.empty());
        if (multiFn || shapes > 1) {
          g_invRejShape++;
          rejected.insert(&F);
          continue; // mixed/multi shapes: review territory (v1)
        }
        // Completeness sweep over every pointer formal.
        bool ok = true;
        const char *why = nullptr;
        std::set<std::pair<int, int>> bindings; // (callee formal k, data idx)
        bool wantFresh = false;
        for (const auto &Arg : F.args()) {
          if (!containsPointerType(Arg.getType())) continue;
          int ai = (int)Arg.getArgNo();
          for (const User *U : Arg.users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (CB && fnIcalls.count(CB)) {
              if (CB->getCalledOperand()->stripPointerCasts() == &Arg)
                continue; // the fn slot itself
              bool foundArg = false;
              for (unsigned k = 0; k < CB->arg_size(); k++)
                if (CB->getArgOperand(k)->stripPointerCasts() == &Arg) {
                  bindings.insert({(int)k, ai});
                  foundArg = true;
                }
              if (!foundArg) { ok = false; why = "esc-call"; }
              continue;
            }
            if (CB && (passCalls.count(CB) || chainPassCalls.count(CB)))
              continue; // callee summary is authoritative
            if (CB) {
              const Function *IC = CB->getCalledFunction();
              if (IC && (isNoopIntrinsic(IC) || isFreeFn(IC->getName())))
                continue;
              ok = false; why = "esc-call"; break;
            }
            if (isa<ICmpInst>(U)) continue;
            if (isa<GEPOperator>(U) || isa<CastInst>(U) ||
                isa<LoadInst>(U) || isa<StoreInst>(U) ||
                isa<AtomicRMWInst>(U) || isa<AtomicCmpXchgInst>(U)) {
              // treat as chain rooted here: store OF the formal rejects
              if (const auto *SI = dyn_cast<StoreInst>(U)) {
                if (SI->getValueOperand()->stripPointerCasts() == &Arg) {
                  ok = false; why = "esc-store"; break;
                }
                if (containsPointerType(SI->getValueOperand()->getType())) {
                  ok = false; why = "esc-store"; break;
                }
                continue;
              }
              if (const auto *LI = dyn_cast<LoadInst>(U)) {
                if (containsPointerType(LI->getType())) {
                  ok = false; why = "esc-load"; break;
                }
                continue;
              }
              if (!benignChain(U)) { ok = false; why = "esc-chain"; break; }
              continue;
            }
            ok = false; why = "esc-other"; break;
          }
          if (!ok) break;
        }
        // Return accounting.
        const CallBase *retPass = nullptr;
        if (ok && containsPointerType(F.getReturnType())) {
          if (!fnIcalls.empty() || !chainPassCalls.empty()) {
            ok = false; why = "ptr-ret"; // chain regs return int
          } else {
            for (const Instruction &I : instructions(F)) {
              const auto *RI = dyn_cast<ReturnInst>(&I);
              if (!RI) continue;
              const Value *RV = RI->getReturnValue()->stripPointerCasts();
              if (isa<ConstantPointerNull>(RV)) continue;
              const auto *RC = dyn_cast<CallBase>(RV);
              if (RC && passCalls.count(RC)) { retPass = RC; continue; }
              ok = false; why = "ptr-ret"; break;
            }
          }
        }
        if (!ok) {
          if (why && (!strcmp(why, "ptr-ret"))) g_invRejPtrRet++;
          else g_invRejEscape++;
          CG_LOG("ConfirmInvoke: REVIEW " << F.getName() << " ("
                 << (fnIcalls.empty() ? "PASSTHRU" : "DIRECT") << ", "
                 << (why ? why : "?") << ")\n");
          rejected.insert(&F);
          continue;
        }
        // Build atoms.
        GlobalContext::FuncSummary S;
        if (!chainPassCalls.empty()) {
          for (const CallBase *CB : chainPassCalls) {
            const Function *IC = getFuncDef(
                const_cast<Function *>(CB->getCalledFunction()));
            auto sit = Ctx->FuncSummaries.find(IC);
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(CB->getCalledFunction());
            for (const auto &A : sit->second->atoms) {
              if (A.kind != GlobalContext::SummaryAtom::ChainReg) continue;
              int wb = (unsigned)A.src < CB->arg_size()
                           ? formalIdx(CB->getArgOperand(A.src))
                           : -1;
              if (wb < 0) continue;
              const GlobalValue *key = nullptr;
              if (A.gsrc) key = A.gsrc;
              else if (!A.gsym.empty())
                key = canonChainKey(
                    CB->getModule()->getNamedValue(A.gsym));
              else if (A.dst >= 0 && (unsigned)A.dst < CB->arg_size())
                key = canonChainKey(dyn_cast<GlobalValue>(
                    CB->getArgOperand(A.dst)->stripPointerCasts()));
              if (!key) continue;
              GlobalContext::SummaryAtom NA;
              NA.kind = GlobalContext::SummaryAtom::ChainReg;
              NA.dst = -1;
              NA.src = wb;
              NA.off = A.off;
              NA.fk = A.fk;
              NA.gsrc = key;
              S.atoms.push_back(std::move(NA));
            }
          }
          if (!S.atoms.empty()) {
            Ctx->OwnedSummaries.push_back(std::move(S));
            Ctx->FuncSummaries[&F] = &Ctx->OwnedSummaries.back();
            g_invConfirmedChain++;
            changed = true;
            std::string line = F.getName().str();
            for (const auto &A : Ctx->OwnedSummaries.back().atoms)
              line += " CHAINREG(@" + A.gsrc->getName().str() + ",*arg" +
                      std::to_string(A.src) + "+" + std::to_string(A.off) +
                      ",f" + std::to_string(A.fk) + ")";
            errs() << "ConfirmInvoke: CONFIRMED CHAINLIFT " << line << "\n";
          } else {
            g_invRejNoBinding++;
            rejected.insert(&F);
          }
          continue;
        }
        if (!fnIcalls.empty()) {
          for (auto [k, d] : bindings)
            S.atoms.push_back({GlobalContext::SummaryAtom::Invoke,
                               fnFormal, d, k});
        } else {
          for (const CallBase *CB : passCalls) {
            const Function *IC = getFuncDef(
                const_cast<Function *>(CB->getCalledFunction()));
            auto sit = Ctx->FuncSummaries.find(IC);
            if (sit == Ctx->FuncSummaries.end())
              sit = Ctx->FuncSummaries.find(CB->getCalledFunction());
            for (const auto &A : sit->second->atoms) {
              if (A.kind != GlobalContext::SummaryAtom::Invoke) continue;
              if ((unsigned)A.dst >= CB->arg_size() ||
                  (unsigned)A.src >= CB->arg_size())
                continue;
              int wf = formalIdx(CB->getArgOperand(A.dst));
              int wd = formalIdx(CB->getArgOperand(A.src));
              if (wf < 0 || wd < 0 || wf == wd) continue;
              S.atoms.push_back({GlobalContext::SummaryAtom::Invoke,
                                 wf, wd, A.aux});
            }
            if (retPass == CB && sit->second->fresh) wantFresh = true;
          }
        }
        if (S.atoms.empty()) {
          if (!fnIcalls.empty()) { g_invRejNoBinding++; rejected.insert(&F); }
          continue; // PASSTHRU may translate in a later round
        }
        S.fresh = wantFresh;
        Ctx->OwnedSummaries.push_back(std::move(S));
        Ctx->FuncSummaries[&F] = &Ctx->OwnedSummaries.back();
        if (wantFresh) Ctx->AllocFuncs.insert(&F);
        if (!fnIcalls.empty()) g_invConfirmed++; else g_invConfirmedPass++;
        changed = true;
        // file-format proposal line for review adoption
        std::string line = F.getName().str();
        for (const auto &A : Ctx->OwnedSummaries.back().atoms) {
          line += " INVOKE(arg" + std::to_string(A.dst) + ":f" +
                  std::to_string(A.aux) + "<-arg" + std::to_string(A.src) +
                  ")";
        }
        if (wantFresh) line += " FRESH";
        errs() << "ConfirmInvoke: CONFIRMED "
               << (fnIcalls.empty() ? "PASSTHRU " : "DIRECT ") << line
               << "\n";
      }
    }
  }
  CG_LOG("ConfirmInvoke LEDGER: " << g_invConfirmed << " DIRECT + "
         << g_invConfirmedPass << " PASSTHRU + " << g_invConfirmedChain
         << " CHAINLIFT confirmed ("
         << rounds << " rounds); rejected " << g_invRejEscape
         << " escape, " << g_invRejPtrRet << " ptr-ret, "
         << g_invRejNoBinding << " no-binding, " << g_invRejShape
         << " mixed-shape\n");
}

// Wire the keyed pair-channels: for each chain-head key, the cross
// product of registrations and dispatch sites — the callback becomes a
// callee OF THE DISPATCH SITE (real invocation attribution), its self
// formal receives the registration's block global, and each dispatch
// binding wires that site's value operand to the callback's formal.
// Registrations whose key has NO dispatch site fall back to pooled
// wiring (the container channel keeps them; nothing is severed).
void CallGraphPass::finalizeChainPairs() {
  chainFinalized = true;
  if (chainRegs.empty() && chainDispatches.empty()) return;
  if (perTUSolve()) {
    errs() << "finalizeChainPairs: keyed pair-channels create cross-module "
              "edges after the last module; per-TU compositional mode "
              "cannot compose them. Rerun with --cfl-compositional=false.\n";
    exit(1);
  }
  std::map<const GlobalValue *, std::vector<size_t>> byKeyR, byKeyD;
  for (size_t i = 0; i < chainRegs.size(); i++)
    byKeyR[chainRegs[i].key].push_back(i);
  for (size_t i = 0; i < chainDispatches.size(); i++)
    byKeyD[chainDispatches[i].key].push_back(i);
  size_t pairs = 0, orphanRegs = 0, orphanDispatch = 0;
  auto formalNode = [&](Function *F, int k) -> NodeIndex {
    if (k < 0 || (unsigned)k >= F->arg_size())
      return AndersNodeFactory::InvalidIndex;
    NodeIndex n = getRepNodeForValue(F->getArg(k));
    if (n == AndersNodeFactory::InvalidIndex)
      n = NF.createValueNode(F->getArg(k));
    return getCanonicalNode(n);
  };
  for (auto &[key, regs] : byKeyR) {
    auto dIt = byKeyD.find(key);
    if (dIt == byKeyD.end()) {
      // no dispatch in corpus for this key: keep the pooled channel
      for (size_t ri : regs) {
        const ChainRegRec &r = chainRegs[ri];
        Function *CF = r.cs->getCalledFunction()
                           ? getFuncDef(r.cs->getCalledFunction())
                           : nullptr;
        if (CF && !CF->isDeclaration()) wireCallArgs(r.cs, CF);
        orphanRegs++;
      }
      continue;
    }
    for (size_t ri : regs) {
      const ChainRegRec &r = chainRegs[ri];
      NodeIndex blkNode = getRepNodeForValue(r.blk);
      if (blkNode == AndersNodeFactory::InvalidIndex)
        blkNode = NF.createValueNode(r.blk);
      NodeIndex selfN = formalNode(r.fn, r.selfFk);
      if (selfN != AndersNodeFactory::InvalidIndex)
        addAssignmentEdge(getCanonicalNode(blkNode), selfN);
      for (size_t di : dIt->second) {
        const ChainDispatchRec &d = chainDispatches[di];
        Ctx->Callees[d.cs].insert(r.fn);
        for (auto [fk, ai] : d.binds) {
          if ((unsigned)ai >= d.cs->arg_size()) continue;
          NodeIndex vN = getRepNodeForValue(d.cs->getArgOperand(ai));
          if (vN == AndersNodeFactory::InvalidIndex) continue;
          NodeIndex fN = formalNode(r.fn, fk);
          if (fN != AndersNodeFactory::InvalidIndex)
            addAssignmentEdge(getCanonicalNode(vN), fN);
        }
        pairs++;
      }
    }
  }
  for (auto &[key, ds] : byKeyD)
    if (!byKeyR.count(key)) orphanDispatch += ds.size();
  CG_LOG("ChainPairs LEDGER: " << chainRegs.size() << " const registrations"
         << " x " << chainDispatches.size() << " dispatch sites over "
         << byKeyR.size() << " keys -> " << pairs << " wired pairs; "
         << orphanRegs << " regs pooled (no dispatch), " << orphanDispatch
         << " dispatch sites without const regs; dyn fallbacks "
         << g_chainRegDyn << " reg / " << g_chainCallDyn << " call, "
         << g_chainLate << " post-finalize\n");
}

// An INVOKE-bearing FRESH summary keeps its body analyzed: the body IS
// the pooled container channel (create-struct stores -> dispatcher) that
// dynamic-fn registration callsites still feed. Constant-fn callsites
// don't wire actuals into it (drained by design), so the body carries
// Summary provers (NOOP + transfer atoms) as a PRE-PASS: pure IR
// proofs, no analysis state — run after file summaries attach and
// BEFORE any graph construction so --cfl-adopt-proposed-summaries can
// install the proofs for THIS corpus (atom byte offsets are layout-
// specific: a 5.18-proven ST(*arg0@4096<-arg0) is wrong on 6.x — the
// shared func_summaries.txt stays layout-free/hand-audited; adoption
// is per-run, re-proven on the corpus being analyzed).
// The typed-access evidence of a body (plan 3.46): for each struct GEP
// whose base is argN + K, the struct whose member step the cell solver
// would take from the object's start (the first struct level with a
// nonzero member offset; a field-0 level adds no edge, and a nonzero
// first index is an untyped byte offset under --cfl-cells). The base
// resolves through casts, constant GEPs and non-escaping O0 slots that
// hold one value.
static std::vector<GlobalContext::FuncSummary::LabelAtom>
bodyLabels(const Function &F, const DataLayout &DL) {
  boost::unordered_flat_map<const Value *, int> argIdx;
  int ai = 0;
  for (const Argument &A : F.args()) argIdx[&A] = ai++;
  std::function<bool(const Value *, int, int &, int64_t &)> argOf =
      [&](const Value *V, int depth, int &arg, int64_t &off) -> bool {
    if (depth == 0) return false;
    V = V->stripPointerCasts();
    if (auto it = argIdx.find(V); it != argIdx.end()) {
      arg = it->second;
      off = 0;
      return true;
    }
    if (const auto *G = dyn_cast<GEPOperator>(V)) {
      APInt O(64, 0);
      if (!G->accumulateConstantOffset(DL, O)) return false;
      if (!argOf(G->getPointerOperand(), depth - 1, arg, off)) return false;
      off += O.getSExtValue();
      return true;
    }
    if (const auto *L = dyn_cast<LoadInst>(V)) {
      const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
      if (!AI) return false;
      const Value *only = nullptr;
      for (const User *U : AI->users()) {
        if (const auto *L2 = dyn_cast<LoadInst>(U)) {
          if (L2->getPointerOperand() == AI) continue;
          return false;
        }
        if (const auto *S2 = dyn_cast<StoreInst>(U)) {
          if (S2->getPointerOperand() != AI || S2->getValueOperand() == AI) return false;
          if (only && only != S2->getValueOperand()) return false;
          only = S2->getValueOperand();
          continue;
        }
        if (const auto *II = dyn_cast<IntrinsicInst>(U))
          if (II->isLifetimeStartOrEnd() || isa<DbgInfoIntrinsic>(II)) continue;
        return false;
      }
      return only && argOf(only, depth - 1, arg, off);
    }
    return false;
  };
  std::vector<GlobalContext::FuncSummary::LabelAtom> out;
  std::set<std::tuple<int, int64_t, const StructType *>> seen;
  for (const auto &BB : F)
    for (const auto &I : BB) {
      const auto *G = dyn_cast<GetElementPtrInst>(&I);
      if (!G || G->getNumIndices() < 2) continue;
      const auto *F0 = dyn_cast<ConstantInt>(G->idx_begin()->get());
      if (!F0 || !F0->isZero()) continue;
      int64_t acc = 0;
      const StructType *T = nullptr;
      bool first = true;
      for (auto GTI = gep_type_begin(G), E = gep_type_end(G); GTI != E; ++GTI) {
        if (first) { first = false; continue; } // the pointer level (0)
        const auto *CI = dyn_cast<ConstantInt>(GTI.getOperand());
        if (!CI) break;
        if (StructType *ST = GTI.getStructTypeOrNull()) {
          const int64_t eo = (int64_t)DL.getStructLayout(ST)->getElementOffset(CI->getZExtValue());
          if (eo != 0) {
            if (ST->hasName() && !ST->isLiteral()) T = ST;
            break;
          }
        } else {
          acc += CI->getSExtValue() * (int64_t)DL.getTypeAllocSize(GTI.getIndexedType());
        }
      }
      if (!T) continue;
      int arg = -1;
      int64_t off = 0;
      if (!argOf(G->getPointerOperand(), 8, arg, off) || off + acc < 0) continue;
      if (seen.insert({arg, off + acc, T}).second)
        out.push_back({arg, (int)(off + acc), T});
    }
  return out;
}

// Do a body's label atoms carry all the naming evidence it gives the
// objects its arguments reach (plan 3.46)? Not when it steps through a
// pointer loaded from argument memory (a second level: AS cannot name
// it), indexes an argument pointer by a variable (a walk or stride:
// element sizes), copies or sets argument memory (effective type), or
// passes an argument pointer to a function with a body (whose evidence
// a skipped body would also skip). *why names the first such access.
static bool labelsCover(const Function &F, std::string &why) {
  boost::unordered_flat_set<const Value *> arg1, deep; // argN + K / loaded from it
  for (const Argument &A : F.args())
    if (A.getType()->isPointerTy()) arg1.insert(&A);
  auto isSlot = [](const Value *P) -> const AllocaInst * {
    const auto *AI = dyn_cast<AllocaInst>(P->stripPointerCasts());
    if (!AI) return nullptr;
    for (const User *U : AI->users()) {
      if (const auto *L = dyn_cast<LoadInst>(U); L && L->getPointerOperand() == AI) continue;
      if (const auto *S = dyn_cast<StoreInst>(U);
          S && S->getPointerOperand() == AI && S->getValueOperand() != AI)
        continue;
      if (const auto *II = dyn_cast<IntrinsicInst>(U);
          II && (II->isLifetimeStartOrEnd() || isa<DbgInfoIntrinsic>(II)))
        continue;
      return nullptr;
    }
    return AI;
  };
  boost::unordered_flat_set<const AllocaInst *> slot1, slotDeep;
  for (bool changed = true; changed;) {
    changed = false;
    auto mark = [&](boost::unordered_flat_set<const Value *> &S, const Value *V) {
      changed |= S.insert(V).second;
    };
    for (const auto &BB : F)
      for (const auto &I : BB) {
        auto in1 = [&](const Value *V) { return arg1.count(V->stripPointerCasts()) > 0; };
        auto inD = [&](const Value *V) { return deep.count(V->stripPointerCasts()) > 0; };
        if (const auto *S = dyn_cast<StoreInst>(&I)) {
          if (const AllocaInst *AI = isSlot(S->getPointerOperand())) {
            if (in1(S->getValueOperand())) changed |= slot1.insert(AI).second;
            if (inD(S->getValueOperand())) changed |= slotDeep.insert(AI).second;
          }
        } else if (const auto *L = dyn_cast<LoadInst>(&I)) {
          if (const AllocaInst *AI = isSlot(L->getPointerOperand())) {
            if (slot1.count(AI)) mark(arg1, L);
            if (slotDeep.count(AI)) mark(deep, L);
          } else if (L->getType()->isPointerTy() &&
                     (in1(L->getPointerOperand()) || inD(L->getPointerOperand()))) {
            mark(deep, L);
          }
        } else if (isa<GetElementPtrInst>(I) || isa<CastInst>(I) || isa<PHINode>(I) ||
                   isa<SelectInst>(I) || isa<FreezeInst>(I)) {
          for (const Value *Op : I.operands()) {
            if (in1(Op)) mark(arg1, &I);
            if (inD(Op)) mark(deep, &I);
          }
        }
      }
  }
  auto any = [&](const Value *V) {
    V = V->stripPointerCasts();
    return arg1.count(V) || deep.count(V);
  };
  for (const auto &BB : F)
    for (const auto &I : BB) {
      if (const auto *G = dyn_cast<GetElementPtrInst>(&I)) {
        const Value *B = G->getPointerOperand()->stripPointerCasts();
        if (deep.count(B)) { why = "step through a loaded pointer"; return false; }
        if (arg1.count(B) && !G->hasAllConstantIndices()) {
          why = "variable index on an argument pointer";
          return false;
        }
      } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
        if (isa<DbgInfoIntrinsic>(CB)) continue;
        bool passes = false;
        for (const Value *A : CB->args()) passes |= any(A);
        if (!passes) continue;
        if (isa<MemIntrinsic>(CB)) { why = "memory intrinsic on argument memory"; return false; }
        const Function *CF = CB->getCalledFunction();
        if (!CF || !CF->isDeclaration()) {
          why = "argument pointer passed to " + (CF ? CF->getName().str() : std::string("an icall"));
          return false;
        }
      }
    }
  return true;
}

void CallGraphPass::runSummaryProvers(Module *M) {
  curDL = &M->getDataLayout();
  // Engine check of drafted label atoms (plan 3.46): a file entry that
  // replaces a body defined here must carry the body's naming evidence.
  // MISSING: a typed step of the body the entry does not state; EXTRA: a
  // stated label the body does not show; UNCOVERED: evidence no label
  // can state (the entry loses it under --cfl-cells).
  if (CFLCells) {
    size_t nOk = 0, nBad = 0;
    for (auto &[F, Sp] : Ctx->FuncSummaries) {
      const GlobalContext::FuncSummary &S = *Sp;
      if (F->isDeclaration() || S.none || S.body || S.fresh) continue;
      if (!S.noop && S.atoms.empty()) continue;
      std::set<std::tuple<int, int, std::string>> body, drafted;
      for (const auto &LA : bodyLabels(*F, *curDL))
        body.insert({LA.arg, LA.off, stripStructNameSuffix(LA.ty->getName()).str()});
      for (const auto &LA : S.labels)
        drafted.insert({LA.arg, LA.off,
                        LA.ty ? stripStructNameSuffix(LA.ty->getName()).str() : LA.tyName});
      std::string why, line;
      const bool cover = labelsCover(*F, why);
      for (const auto &[a, o, t] : body)
        if (!drafted.count({a, o, t}))
          line += " MISSING AS(arg" + std::to_string(a) + "@" + std::to_string(o) + ":" + t + ")";
      for (const auto &[a, o, t] : drafted)
        if (!body.count({a, o, t}))
          line += " EXTRA AS(arg" + std::to_string(a) + "@" + std::to_string(o) + ":" + t + ")";
      if (!cover) line += " UNCOVERED [" + why + "]";
      if (line.empty()) { nOk++; continue; }
      nBad++;
      CG_LOG("LabelCheck: " << F->getName() << line << "\n");
    }
    CG_LOG("LabelCheck: " << nOk << " body-replacing file entries carry their bodies' "
           << "naming evidence, " << nBad << " do not (see above)\n");
  }
  struct PAtom { // 0=ST 1=MV 2=LD(ret) 3=ALIAS(ret) 4=CPY
    int kind; int a1; int a2; int64_t o1; int64_t o2;
    const GlobalValue *g1 = nullptr; // dst/container-side global
    const GlobalValue *g2 = nullptr; // src/value-side global
  };
  boost::unordered_flat_map<const Function *, SmallVector<PAtom, 6>> props;
  boost::unordered_flat_set<const Function *> permRefused;
  boost::unordered_flat_map<std::string, uint64_t> aRefuse;
  // Existing file entries usable for composition: pure
  // Cpy/Alias/Store/Load/Move atom sets (no FRESH/INVOKE/CHAIN
  // — those are callsite-contextual or allocator-owned).
  auto fileAtoms = [&](const Function *CF,
                 SmallVectorImpl<PAtom> &out) -> bool {
    auto sit = Ctx->FuncSummaries.find(CF);
    if (sit == Ctx->FuncSummaries.end()) return false;
    const auto &S = *sit->second;
    if (S.noop || S.none || S.fresh || S.atoms.empty()) return false;
    for (const auto &A : S.atoms) {
      switch (A.kind) {
      case GlobalContext::SummaryAtom::Store:
        if (A.dst < 0 && !A.gdst) return false;
        if (A.src < 0 && !A.gsrc && !A.gsrc2) return false;
        out.push_back({0, A.dst, A.src, A.dstByteOff, A.srcByteOff,
                 A.gdst, A.gsrc ? A.gsrc : A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Move:
        if (A.dst < 0 && !A.gdst) return false;
        if (A.src < 0 && !A.gsrc2) return false;
        out.push_back({1, A.dst, A.src, A.dstByteOff, A.srcByteOff,
                 A.gdst, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Load:
        if (A.dst != -1 || (A.src < 0 && !A.gsrc2)) return false;
        out.push_back({2, 0, A.src, 0, A.srcByteOff, nullptr, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::LoadX:
        if (A.dst != -1 || (A.src < 0 && !A.gsrc2)) return false;
        out.push_back({5, 0, A.src, 0, A.srcByteOff, nullptr, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Store2:
        if (A.dst < 0 && !A.gdst) return false;
        out.push_back({7, A.dst, A.src, A.dstByteOff, A.srcByteOff,
                       A.gdst, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Move2:
        if ((A.dst < 0 && !A.gdst) || (A.src < 0 && !A.gsrc2)) return false;
        out.push_back({8, A.dst, A.src, A.dstByteOff, A.srcByteOff,
                       A.gdst, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Load2:
        if (A.dst != -1 || (A.src < 0 && !A.gsrc2)) return false;
        out.push_back({9, 0, A.src, 0, A.srcByteOff, nullptr, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::MoveX:
        if (A.dst < 0 && !A.gdst) return false;
        if (A.src < 0 && !A.gsrc2) return false;
        out.push_back({6, A.dst, A.src, A.dstByteOff, A.srcByteOff,
                       A.gdst, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Alias:
        if (A.dst != -1 || (A.src < 0 && !A.gsrc2)) return false;
        out.push_back({3, 0, A.src, 0, A.srcByteOff, nullptr, A.gsrc2});
        break;
      case GlobalContext::SummaryAtom::Cpy:
        if (A.dst < 0 || A.src < 0) return false; // ret-CPY: skip
        out.push_back({4, A.dst, A.src, 0, 0});
        break;
      default:
        return false;
      }
    }
    return true;
  };
  auto calleeAtoms = [&](const Function *CF,
                   SmallVectorImpl<PAtom> &out) -> int {
    // 1 = atoms available, 0 = not (yet), -1 = permanently not
    CF = getFuncDef(const_cast<Function *>(CF));
    auto pit = props.find(CF);
    if (pit != props.end()) {
      out.append(pit->second.begin(), pit->second.end());
      return 1;
    }
    if (fileAtoms(CF, out)) return 1;
    if (permRefused.count(CF) || CF->isDeclaration()) return -1;
    return 0;
  };
      boost::unordered_flat_set<const Function *> ok;
      boost::unordered_flat_map<std::string, uint64_t> refuseHist;
      auto calleeSafe = [&](const Function *CF) {
        if (!CF) return false;
        CF = getFuncDef(const_cast<Function *>(CF));
        auto sit = Ctx->FuncSummaries.find(CF);
        if (sit != Ctx->FuncSummaries.end() && sit->second->noop)
          return true;
        return ok.count(CF) != 0;
      };
      // A local slot that never escapes (users: loads, stores INTO it,
      // debug/lifetime markers) — the O0 spill of a formal. A store into
      // it moves nothing out of the function; whatever the stored value
      // carries is judged again where the reload is used (a reload from
      // a slot fed by a formal stays "may carry" in mayCarryLocal).
      auto nonEscapingLocalSlot = [](const Value *base) -> bool {
        const auto *AI = dyn_cast<AllocaInst>(base);
        if (!AI) return false;
        for (const User *U : AI->users()) {
          if (isa<LoadInst>(U)) continue;
          if (const auto *SI2 = dyn_cast<StoreInst>(U)) {
            if (SI2->getPointerOperand() == AI &&
                SI2->getValueOperand() != AI)
              continue;
            return false;
          }
          if (const auto *II2 = dyn_cast<IntrinsicInst>(U)) {
            switch (II2->getIntrinsicID()) {
            case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
            case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
              continue;
            default: break;
            }
          }
          return false;
        }
        return true;
      };
      // ANSWER-SITE callees: a direct call the analysis reclassifies
      // as a resolution site (static_call trampolines dispatch through
      // their __SCK__ key). Body-skip would erase the SITE, not just
      // data flow — rule A must never bless these (km caught it: 9
      // __SCT__cond_resched/might_resched sites lost all targets).
      auto isAnswerSiteCallee = [&](const Function *CF) -> bool {
        return CFLStaticCall && CF && CF->isDeclaration() &&
               CF->getName().starts_with("__SCT__");
      };
      // Rule C: local launder walk — identical to mayCarryPtrProvenance
      // except int returns of NOOP-safe callees are CLEAN (the NOOP
      // claim/proof covers "ret is a count, not a laundered pointer";
      // the fd-chain hazard that forced conservative-yes there is a
      // provenance-witnessed return, which NOOP refuses by rule).
      // Zero-provenance asm write predicate (mirrors handleInlineAsm's
      // §2 j-loop exactly): an indirect-output slot gets store edges
      // ONLY from ptr-typed or provenance-witnessed direct inputs. No
      // such input => the main model emits nothing for the slot =>
      // skipping the body drops nothing. (__raw_save_flags pushf/pop:
      // zero inputs.) %gs/%fs excluded: percpu materialization paths
      // have their own model.
      auto asmInputsProvenanceFree = [&](const CallBase *ACB) -> bool {
        const auto *IA2 = cast<InlineAsm>(ACB->getCalledOperand());
        StringRef AS = IA2->getAsmString();
        if (AS.contains("%gs:") || AS.contains("%fs:")) return false;
        auto ACs = InlineAsm::ParseConstraints(IA2->getConstraintString());
        unsigned ai2 = 0;
        for (auto &CI : ACs) {
          if (CI.Type == InlineAsm::isClobber
#if LLVM_VERSION_MAJOR >= 15
              || CI.Type == InlineAsm::isLabel
#endif
          )
            continue;
          if (!CI.hasArg()) continue;
          if (ai2 >= ACB->arg_size()) return false;
          const unsigned idx = ai2++;
          if (CI.Type != InlineAsm::isInput || CI.isIndirect) continue;
          const Value *A2 = ACB->getArgOperand(idx);
          if (isa<PtrToIntOperator>(A2)) return false;
          if (A2->getType()->isPointerTy()) return false;
          if (curDL && isPtrWidthInt(A2->getType(), *curDL)) {
            bool declined = false;
            if (mayCarryPtrProvenance(A2, 8, declined) || declined)
              return false;
          }
        }
        return true;
      };
      // Flags-local pattern: an int loaded from a LOCAL alloca whose
      // only writers are clean-int stores or zero-provenance asm slots
      // (local_irq_save/restore) carries nothing. Cache per alloca;
      // in-progress = dirty (cycle-safe).
      boost::unordered_flat_map<const AllocaInst *, int> allocaCleanCache;
      std::function<bool(const Value *, unsigned)> mayCarryLocal;
      std::function<bool(const AllocaInst *)> allocaIntClean =
          [&](const AllocaInst *AI) -> bool {
        auto [it2, fresh] = allocaCleanCache.try_emplace(AI, -1);
        if (!fresh) return it2->second == 1;
        bool clean = true;
        SmallVector<const User *, 16> wl(AI->users().begin(),
                                         AI->users().end());
        SmallPtrSet<const User *, 32> seen;
        while (!wl.empty() && clean) {
          const User *U = wl.pop_back_val();
          if (!seen.insert(U).second) continue;
          if (isa<LoadInst>(U)) continue;
          if (const auto *SI2 = dyn_cast<StoreInst>(U)) {
            const Value *SV = SI2->getValueOperand();
            if (SV == AI || getUnderlyingObject(SV) == AI ||
                SV->getType()->isPointerTy() || mayCarryLocal(SV, 6))
              clean = false;
            continue;
          }
          if (isa<GetElementPtrInst>(U) || isa<BitCastInst>(U) ||
              isa<PHINode>(U) || isa<SelectInst>(U)) {
            for (const User *UU : U->users()) wl.push_back(UU);
            continue;
          }
          if (const auto *UC = dyn_cast<CallBase>(U)) {
            if (const auto *II2 = dyn_cast<IntrinsicInst>(UC)) {
              switch (II2->getIntrinsicID()) {
              case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
              case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
                continue;
              default: break;
              }
            }
            if (UC->isInlineAsm() && UC->getCalledOperand() != AI &&
                asmInputsProvenanceFree(UC))
              continue; // slot read/write of a zero-provenance asm
            clean = false;
            continue;
          }
          clean = false;
        }
        allocaCleanCache[AI] = clean ? 1 : 0;
        return clean;
      };
      mayCarryLocal =
          [&](const Value *V, unsigned depth) -> bool {
        if (depth == 0) return true;
        if (isa<PtrToIntInst>(V)) return true;
        if (const auto *C = dyn_cast<Constant>(V)) {
          if (isa<ConstantInt>(C) || isa<ConstantData>(C)) return false;
          return constantHasPtrToInt(C, 6);
        }
        if (const auto *LI2 = dyn_cast<LoadInst>(V)) {
          const auto *AI = dyn_cast<AllocaInst>(
              getUnderlyingObject(LI2->getPointerOperand()));
          return !(AI && allocaIntClean(AI));
        }
        if (isa<Argument>(V)) return true;
        if (const auto *RC = dyn_cast<CallBase>(V)) {
          if (RC->isInlineAsm()) return true;
          const Function *CF2 = dyn_cast<Function>(
              RC->getCalledOperand()->stripPointerCastsAndAliases());
          return !(CF2 && calleeSafe(CF2));
        }
        if (const auto *I = dyn_cast<Instruction>(V)) {
          if (isa<BinaryOperator>(I) || isa<CastInst>(I) ||
              isa<PHINode>(I) || isa<SelectInst>(I) || isa<FreezeInst>(I)) {
            for (const Use &U : I->operands())
              if ((U->getType()->isIntegerTy() ||
                   U->getType()->isPointerTy()) &&
                  mayCarryLocal(U.get(), depth - 1))
                return true;
            return false;
          }
        }
        return false;
      };
      // Rules A/B: a callsite transfers nothing OF THE CALLER's args
      // if every operand is caller-arg-independent — no matter what
      // the callee does internally (its body and its other callsites
      // are analyzed regardless). Unlocks printk/WARN/debug helpers
      // as callees without summarizing them.
      //   narrowConstants: the NOOP applier SKIPS the proposer's body
      //   (g_noopBodies), so this callsite's edges vanish on adoption
      //   — ptr constants must then be provenance-free content (string
      //   literals, non-ptr scalar arrays). Atom-summarized bodies
      //   stay walked, so any Constant keeps its edges: broad is fine.
      auto ptrConstProvenanceFree = [&](const Value *V) -> bool {
        const auto *GV =
            dyn_cast<GlobalVariable>(V->stripPointerCastsAndAliases());
        if (!GV || !GV->isConstant() || !GV->hasInitializer()) return false;
        const Constant *Init = GV->getInitializer();
        if (isa<ConstantAggregateZero>(Init)) return true;
        const auto *CDS = dyn_cast<ConstantDataSequential>(Init);
        return CDS && !CDS->getElementType()->isPointerTy() &&
               !(curDL && isPtrWidthInt(CDS->getElementType(), *curDL));
      };
      auto callsiteArgIrrelevant = [&](const CallBase *CB,
                                       bool narrowConstants) -> bool {
        for (const Value *Arg : CB->args()) {
          if (const auto *II3 =
                  dyn_cast<IntrinsicInst>(Arg->stripPointerCasts())) {
            auto iid = II3->getIntrinsicID();
            if (iid == Intrinsic::returnaddress ||
                iid == Intrinsic::frameaddress)
              continue; // factless in the main model: nothing to lose
          }
          if (const auto *C = dyn_cast<Constant>(Arg)) {
            if (!narrowConstants || !C->getType()->isPointerTy() ||
                isa<ConstantPointerNull>(C) || ptrConstProvenanceFree(C))
              continue;
            return false;
          }
          Type *T = Arg->getType();
          if (T->isPointerTy()) return false;
          if (curDL && isPtrWidthInt(T, *curDL) && mayCarryLocal(Arg, 8))
            return false;
        }
        return true;
      };
      // Asm is transfer-free iff our own handleInlineAsm model would
      // emit no edges for it: no non-immediate pointer inputs, no
      // %gs/%fs segment access (immediates become accessed there), no
      // indirect pointer-capable outputs, no pointer-capable result.
      // Covers jump-label asm goto, WARN/ud2, barriers, rdtsc.
      auto asmTransferFree = [&](const CallBase *CB) {
        // Results need no check: a produced value only matters if it
        // ESCAPES, and the store/return/unsafe-callee rules catch
        // every escape. Only inputs the asm could write through (or
        // launder out-of-band) refuse.
        const auto *IA = cast<InlineAsm>(CB->getCalledOperand());
        auto Cs = InlineAsm::ParseConstraints(IA->getConstraintString());
        // May the asm WRITE memory? (mirrors handleInlineAsm 2b)
        bool memClobber = false, anyIndirectOut = false;
        for (auto &CI : Cs) {
          if (CI.Type == InlineAsm::isClobber) {
            for (const std::string &Code : CI.Codes)
              if (StringRef(Code).contains("memory")) memClobber = true;
          } else if (CI.Type == InlineAsm::isOutput && CI.isIndirect) {
            anyIndirectOut = true;
          }
        }
        const bool mayWrite = memClobber || anyIndirectOut;
        unsigned argIdx = 0;
        for (auto &CI : Cs) {
          if (CI.Type == InlineAsm::isClobber
#if LLVM_VERSION_MAJOR >= 15
              || CI.Type == InlineAsm::isLabel
#endif
          )
            continue;
          if (!CI.hasArg()) continue;
          if (argIdx >= CB->arg_size()) return false;
          const unsigned aIdx = argIdx++;
          const Value *Arg = CB->getArgOperand(aIdx);
          if (Arg->getType()->isPointerTy()) {
            if (CI.isIndirect) {
              // Memory operand. INPUT slots only produce values —
              // escapes are governed downstream; allow. OUTPUT slots
              // (asm writes) are transfer-free iff the slot cannot
              // hold pointer content (handleInlineAsm's ptr/width
              // slot gate) — covers percpu counter inc/add.
              if (CI.Type == InlineAsm::isInput)
                continue;
              Type *ET = CB->getParamElementType(aIdx);
              if (ET && !containsPointerType(ET) &&
                  !(curDL && isPtrWidthInt(ET->getScalarType(), *curDL)))
                continue;
              // Width-int slot (=*rm i64): the main model's store
              // edges are input-driven; with no provenance-capable
              // inputs it emits nothing (__raw_save_flags).
              if (ET && !containsPointerType(ET) &&
                  asmInputsProvenanceFree(CB))
                continue;
              return false;
            }
            // Register/address ptr input: reads through it produce a
            // VALUE (escape-checked downstream); refusal needed only
            // if the asm may WRITE through it.
            if (mayWrite) return false;
          } else if (curDL && isPtrWidthInt(Arg->getType(), *curDL)) {
            if (mayCarryLocal(Arg, 8))
              return false;
          }
        }
        return true;
      };
      auto eligible = [&](const Function &F, std::string &why) {
        for (const auto &BB : F) {
          for (const auto &I : BB) {
            if (const auto *CB = dyn_cast<CallBase>(&I)) {
              if (CB->isInlineAsm()) {
                if (asmTransferFree(CB)) continue;
                { std::string t; raw_string_ostream os(t); os << I;
                  why = "asm " + os.str(); } return false;
              }
              if (const auto *II = dyn_cast<IntrinsicInst>(CB)) {
                switch (II->getIntrinsicID()) {
                case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
                case Intrinsic::dbg_label:
                case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
                case Intrinsic::assume: case Intrinsic::expect:
                case Intrinsic::prefetch: case Intrinsic::donothing:
                case Intrinsic::trap: case Intrinsic::ubsantrap:
                case Intrinsic::vastart: case Intrinsic::vaend:
                case Intrinsic::memset:
                case Intrinsic::vacopy:
                case Intrinsic::stacksave: case Intrinsic::stackrestore:
                // returnaddress/frameaddress: handleCall emits nothing
                // for intrinsics and no other path models these — the
                // result node is factless, so every edge from it in a
                // walked body is vacuous. Skip-exact.
                case Intrinsic::returnaddress: case Intrinsic::frameaddress:
                  continue;
                default: {
                  // pure intrinsics: no pointer-capable args, non-ptr
                  // result — math/bit ops (ctpop, bswap, fshl, umax...)
                  bool pure = !II->getType()->isPointerTy();
                  for (const Value *Arg : II->args())
                    pure &= !Arg->getType()->isPointerTy();
                  if (pure) continue;
                  why = "intrinsic"; return false;
                }
                }
              }
              const Function *CF = dyn_cast<Function>(
                  CB->getCalledOperand()->stripPointerCastsAndAliases());
              if (!CF) { why = "icall"; return false; }
              if (!calleeSafe(CF)) {
                // Rule A/B: unsafe callee, but the site passes nothing
                // of the caller — narrow constants: this body is
                // SKIPPED once the NOOP entry is adopted.
                if (!isAnswerSiteCallee(CF) &&
                    callsiteArgIrrelevant(CB, /*narrowConstants=*/true))
                  continue;
                why = ("callee " + CF->getName()).str(); return false;
              }
              continue;
            }
            if (const auto *SI = dyn_cast<StoreInst>(&I)) {
              const Value *V = SI->getValueOperand();
              if (const auto *II3 =
                      dyn_cast<IntrinsicInst>(V->stripPointerCasts())) {
                auto iid = II3->getIntrinsicID();
                if (iid == Intrinsic::returnaddress ||
                    iid == Intrinsic::frameaddress)
                  continue; // storing a factless value: vacuous edge
              }
              if (V->getType()->isPointerTy()) {
                // Variadic idiom: spilling ptr args into a LOCAL
                // alloca (va area) that never escapes the safe set.
                const Value *base = getUnderlyingObject(
                    SI->getPointerOperand());
                bool localOk = false;
                if (const auto *AI = dyn_cast<AllocaInst>(base)) {
                  localOk = true;
                  SmallVector<const User *, 16> wl(AI->users().begin(),
                                                   AI->users().end());
                  SmallPtrSet<const User *, 32> seen;
                  while (!wl.empty() && localOk) {
                    const User *U = wl.pop_back_val();
                    if (!seen.insert(U).second) continue;
                    if (isa<LoadInst>(U) || isa<StoreInst>(U)) continue;
                    if (isa<GetElementPtrInst>(U) || isa<BitCastInst>(U) ||
                        isa<PHINode>(U) || isa<SelectInst>(U)) {
                      for (const User *UU : U->users()) wl.push_back(UU);
                      continue;
                    }
                    if (const auto *UC = dyn_cast<CallBase>(U)) {
                      if (const auto *II2 = dyn_cast<IntrinsicInst>(UC)) {
                        switch (II2->getIntrinsicID()) {
                        case Intrinsic::vastart: case Intrinsic::vaend:
                        case Intrinsic::vacopy:
                        case Intrinsic::lifetime_start:
                        case Intrinsic::lifetime_end:
                        case Intrinsic::memset:
                          continue;
                        default: break;
                        }
                      }
                      const Function *UF = dyn_cast<Function>(
                          UC->getCalledOperand()->stripPointerCastsAndAliases());
                      if (UF && calleeSafe(UF)) continue;
                    }
                    localOk = false;
                  }
                }
                if (!localOk) {
                  std::string t; raw_string_ostream os(t); os << I;
                  why = "ptr-store " + os.str(); return false;
                }
                continue;
              }
              if (curDL && isPtrWidthInt(V->getType(), *curDL)) {
                // O0 spill of an integer formal into a local slot:
                // nothing leaves the function through this store.
                if (nonEscapingLocalSlot(SI->getPointerOperand())) continue;
                if (mayCarryLocal(V, 8)) {
                  // Self-slot update (s->count++, s->len += n): dirty
                  // contributors that are loads from the SAME pointer
                  // the store writes back through are cell self-loops
                  // in the walked body — vacuous, skip-exact.
                  std::function<bool(const Value *, unsigned)> selfOk =
                      [&](const Value *V2, unsigned depth) -> bool {
                    if (!mayCarryLocal(V2, 8)) return true;
                    if (depth == 0) return false;
                    if (const auto *L2 = dyn_cast<LoadInst>(V2))
                      return L2->getPointerOperand() ==
                             SI->getPointerOperand();
                    if (const auto *I2 = dyn_cast<Instruction>(V2)) {
                      if (isa<BinaryOperator>(I2) || isa<CastInst>(I2) ||
                          isa<PHINode>(I2) || isa<SelectInst>(I2) ||
                          isa<FreezeInst>(I2)) {
                        for (const Use &U : I2->operands())
                          if ((U->getType()->isIntegerTy() ||
                               U->getType()->isPointerTy()) &&
                              !selfOk(U.get(), depth - 1))
                            return false;
                        return true;
                      }
                    }
                    return false;
                  };
                  if (!selfOk(V, 8)) {
                    std::string t; raw_string_ostream os(t); os << I;
                    why = "int-launder-store " + os.str(); return false;
                  }
                }
              }
              continue;
            }
            if (isa<AtomicRMWInst>(&I) || isa<AtomicCmpXchgInst>(&I)) {
              why = "atomic"; return false;
            }
            if (isa<IndirectBrInst>(&I)) { why = "indirectbr"; return false; }
            if (const auto *RI = dyn_cast<ReturnInst>(&I)) {
              const Value *RV = RI->getReturnValue();
              if (RV) {
                if (RV->getType()->isPointerTy()) { why = "ret-ptr"; return false; }
                if (curDL && isPtrWidthInt(RV->getType(), *curDL)) {
                  if (mayCarryLocal(RV, 8)) {
                    why = "ret-launder"; return false;
                  }
                }
              }
            }
          }
        }
        return true;
      };
      bool changed = true;
      size_t rounds = 0;
      while (changed && rounds++ < 20) {
        changed = false;
        for (auto &[mod, mname] : Ctx->Modules) {
          for (const Function &F : *mod) {
            if (F.isDeclaration() || ok.count(&F)) continue;
            const Function *canon = getFuncDef(const_cast<Function *>(&F));
            if (canon != &F || ok.count(canon)) continue;
            auto sit = Ctx->FuncSummaries.find(canon);
            if (sit != Ctx->FuncSummaries.end()) continue; // already covered
            std::string why;
            if (eligible(F, why)) { ok.insert(canon); changed = true; }
            else if (rounds == 1) {
              refuseHist[why.substr(0, why.find(' '))]++;
              CG_LOG("NoopProp: REFUSED " << F.getName() << " [" << why
                     << "]\n");
            }
          }
        }
      }
      // File-entry redundancy census (post-fixpoint: proposed
      // callees fully resolved; one-at-a-time deletion semantics —
      // other file entries stay in the safe set). REDUNDANT = the
      // prover re-derives this NOOP per-run, the hand entry can go
      // (given propose/adopt stays on); CORE = the audit is
      // load-bearing (prover refuses). Report-only.
      {
        size_t nRed = 0, nCore = 0;
        for (auto &[mod, mname] : Ctx->Modules) {
          for (const Function &F : *mod) {
            if (F.isDeclaration()) continue;
            const Function *canon = getFuncDef(const_cast<Function *>(&F));
            if (canon != &F) continue;
            auto sit = Ctx->FuncSummaries.find(canon);
            if (sit == Ctx->FuncSummaries.end() || !sit->second->noop)
              continue;
            std::string why;
            if (eligible(F, why)) {
              CG_LOG("NoopProp: FILE-REDUNDANT " << F.getName() << "\n");
              nRed++;
            } else {
              CG_LOG("NoopProp: FILE-CORE " << F.getName() << " ["
                     << why.substr(0, why.find(' ')) << "]\n");
              nCore++;
            }
          }
        }
        if (nRed + nCore)
          CG_LOG("NoopProp: file NOOP entries with definitions here: "
                 << nRed << " redundant (prover re-derives) / " << nCore
                 << " core (audit load-bearing)\n");
      }
      for (const Function *F : ok)
        CG_LOG("NoopProp: OK " << F->getName() << "\n");
      std::string hist;
      for (auto &kv : refuseHist)
        hist += kv.first + "=" + std::to_string(kv.second) + " ";
      CG_LOG("NoopProp: " << ok.size() << " proposed (" << rounds
             << " rounds); first-round refusals: " << hist << "\n");

      // ---- v2: transfer-atom generator (ST/LD/MV/ALIAS @byte-off) ----
      // v2.1: COMPOSITION — a summarized callee's atoms translate
      // through the call site into caller-frame effects; callee ret
      // atoms (LD/ALIAS) resolve call results in the caller. Outer
      // fixpoint alternates with the NOOP set; refusal anywhere
      // uncertain, retryable only when blocked on an unproposed
      // callee (chains converge like the NOOP fixpoint).
      if ((CFLProposeAtomSummaries || CFLAdoptProposedSummaries) && curDL) {
        size_t nOk = 0;
        auto tryFn = [&](const Function &F, bool &retryable,
                         std::string &why) -> bool {
          retryable = false;
          if (F.arg_size() > 8) { why = "many-args"; return false; }
          size_t nInst = 0;
          for (const auto &BB : F) nInst += BB.size();
          if (nInst > 600) { why = "too-big"; return false; }
          boost::unordered_flat_map<const Value *, int> argIdx;
          int ai = 0;
          for (const Argument &A : F.args()) argIdx[&A] = ai++;
          // kind: 0=ARGP(arg+off) 1=LOADARG(*arg@off) 2=NULLISH
          //       3=GLOBALP(&g+off) 4=LOADGLOBAL(*g@off)
          struct Src { uint8_t kind; int arg; int64_t off;
                       const GlobalValue *gv = nullptr; };
          boost::unordered_flat_map<const Value *, SmallVector<Src, 4>> memo;
          boost::unordered_flat_set<const Value *> inProg;
          bool blockedOnCallee = false;
          // An O0 local slot (a spilled parameter or local variable): an
          // alloca used only by loads from it, stores into it (never of
          // its own address) and lifetime/debug markers. Its address
          // never escapes, so a store into it is a frame-local effect
          // (no atom), and a load from it yields what was stored into it
          // (all stores: flow-insensitive, as the main model is).
          boost::unordered_flat_map<const AllocaInst *, bool> slotMemo;
          auto isSlot = [&](const Value *V) -> const AllocaInst * {
            const auto *AI = dyn_cast<AllocaInst>(V);
            if (!AI) return nullptr;
            auto [it, ins] = slotMemo.try_emplace(AI, true);
            if (ins)
              for (const User *U : AI->users()) {
                if (const auto *L = dyn_cast<LoadInst>(U)) {
                  if (L->getPointerOperand() == AI) continue;
                } else if (const auto *S = dyn_cast<StoreInst>(U)) {
                  if (S->getPointerOperand() == AI && S->getValueOperand() != AI)
                    continue;
                } else if (const auto *II = dyn_cast<IntrinsicInst>(U)) {
                  if (II->isLifetimeStartOrEnd() || isa<DbgInfoIntrinsic>(II))
                    continue;
                }
                it->second = false;
                break;
              }
            return it->second ? AI : nullptr;
          };
          std::function<bool(const Value *, SmallVectorImpl<Src> &)> rez =
              [&](const Value *V, SmallVectorImpl<Src> &out) -> bool {
            V = V->stripPointerCasts();
            auto mit = memo.find(V);
            if (mit != memo.end()) {
              out.append(mit->second.begin(), mit->second.end());
              return true;
            }
            if (!inProg.insert(V).second) return false;
            SmallVector<Src, 4> r;
            bool okr = false;
            if (auto it2 = argIdx.find(V); it2 != argIdx.end()) {
              r.push_back({0, it2->second, 0}); okr = true;
            } else if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V)) {
              r.push_back({2, 0, 0}); okr = true;
            } else if (const auto *G2 = dyn_cast<GlobalValue>(
                           V->stripPointerCastsAndAliases())) {
              // Global container/address ref (v2.2b): pointer identity,
              // adopted-only (never serialized — internal linkage is
              // name-ambiguous across TUs). Record the DEFINING
              // instance (declarations route through the extern hub).
              if (G2->isDeclaration() && G2->hasName()) {
                auto git2 = Ctx->Gobjs.find(G2->getGUID());
                if (git2 != Ctx->Gobjs.end()) G2 = git2->second;
              }
              r.push_back({3, 0, 0, G2}); okr = true;
            } else if (const auto *G = dyn_cast<GEPOperator>(V)) {
              APInt Off(64, 0);
              if (G->accumulateConstantOffset(*curDL, Off)) {
                SmallVector<Src, 4> b;
                if (rez(G->getPointerOperand(), b)) {
                  okr = true;
                  for (auto sv : b) {
                    if (sv.kind == 0 || sv.kind == 3)
                      sv.off += Off.getSExtValue();
                    else if (sv.kind == 1 || sv.kind == 4) okr = false;
                    r.push_back(sv);
                  }
                }
              }
            } else if (const auto *PN = dyn_cast<PHINode>(V)) {
              okr = true;
              for (const Value *IV : PN->incoming_values()) {
                SmallVector<Src, 4> b;
                if (!rez(IV, b)) { okr = false; break; }
                r.append(b.begin(), b.end());
              }
            } else if (const auto *SI2 = dyn_cast<SelectInst>(V)) {
              SmallVector<Src, 4> b;
              okr = rez(SI2->getTrueValue(), b) &&
                    rez(SI2->getFalseValue(), b);
              r = b;
            } else if (const auto *LI = dyn_cast<LoadInst>(V);
                       LI && isSlot(LI->getPointerOperand())) {
              okr = true;
              for (const User *U : LI->getPointerOperand()->users())
                if (const auto *S = dyn_cast<StoreInst>(U)) {
                  SmallVector<Src, 4> b;
                  if (!rez(S->getValueOperand(), b)) { okr = false; break; }
                  r.append(b.begin(), b.end());
                }
            } else if (const auto *LI = dyn_cast<LoadInst>(V)) {
              SmallVector<Src, 4> b;
              if (rez(LI->getPointerOperand(), b)) {
                okr = true;
                for (auto sv : b) {
                  if (sv.kind == 0) r.push_back({1, sv.arg, sv.off});
                  else if (sv.kind == 3)
                    r.push_back({4, 0, sv.off, sv.gv});
                  else if (sv.kind == 2) continue;
                  else { okr = false; break; }
                }
              }
            } else if (const auto *RC = dyn_cast<CallBase>(V)) {
              if (const auto *II3 = dyn_cast<IntrinsicInst>(RC)) {
                auto iid = II3->getIntrinsicID();
                if (iid == Intrinsic::returnaddress ||
                    iid == Intrinsic::frameaddress) {
                  // factless in the main model — contributes nothing
                  r.push_back({2, 0, 0});
                  inProg.erase(V);
                  memo[V] = r;
                  out.append(r.begin(), r.end());
                  return true;
                }
              }
              // Composition: callee ret atoms define the result.
              const Function *CF = dyn_cast<Function>(
                  RC->getCalledOperand()->stripPointerCastsAndAliases());
              if (CF && !RC->isInlineAsm()) {
                SmallVector<PAtom, 6> cas;
                int st = calleeAtoms(CF, cas);
                if (st == 0) blockedOnCallee = true;
                else if (st == 1) {
                  okr = true;
                  bool anyRet = false;
                  for (const auto &A : cas) {
                    if (A.kind == 3) { // ALIAS(ret<-argN[@off] | @g@off)
                      anyRet = true;
                      if (A.o2 < 0) { okr = false; break; } // wildcard
                      if (A.g2) { r.push_back({3, 0, A.o2, A.g2}); continue; }
                      SmallVector<Src, 4> b;
                      if ((unsigned)A.a2 >= RC->arg_size() ||
                          !rez(RC->getArgOperand(A.a2), b)) { okr = false; break; }
                      for (auto sv : b) {
                        if (sv.kind == 0 || sv.kind == 3) sv.off += A.o2;
                        else if ((sv.kind == 1 || sv.kind == 4) && A.o2) {
                          okr = false; break;
                        }
                        r.push_back(sv);
                      }
                    } else if (A.kind == 2) { // LD(ret<-*argC@off | *@g@off)
                      anyRet = true;
                      if (A.o2 < 0) { okr = false; break; } // wildcard
                      if (A.g2) { r.push_back({4, 0, A.o2, A.g2}); continue; }
                      SmallVector<Src, 4> b;
                      if ((unsigned)A.a2 >= RC->arg_size() ||
                          !rez(RC->getArgOperand(A.a2), b)) { okr = false; break; }
                      for (auto sv : b) {
                        if (sv.kind == 0)
                          r.push_back({1, sv.arg, sv.off + A.o2});
                        else if (sv.kind == 3)
                          r.push_back({4, 0, sv.off + A.o2, sv.gv});
                        else if (sv.kind == 2) continue;
                        else { okr = false; break; }
                      }
                    }
                  }
                  if (!anyRet) okr = false; // ret unmodeled by atoms
                }
              }
            }
            inProg.erase(V);
            if (!okr || r.size() > 4) return false;
            memo[V] = r;
            out.append(r.begin(), r.end());
            return true;
          };
          // Int-domain slot sources: a ptr-width int that fails the
          // launder check may still be a MODELABLE slot copy — walk
          // through int arithmetic; every dirty leaf must resolve via
          // rez (loads from arg cells -> LOADARG => MV atoms; laundered
          // args/call rets via their own atoms). Clean contributors
          // vanish. Anything else refuses.
          std::function<bool(const Value *, unsigned,
                             SmallVectorImpl<Src> &)>
              collectIntSrcs = [&](const Value *V, unsigned depth,
                                   SmallVectorImpl<Src> &out) -> bool {
            if (!mayCarryLocal(V, 8)) return true; // clean: no facts
            if (depth == 0) return false;
            if (V->getType()->isPointerTy() || isa<LoadInst>(V) ||
                isa<CallBase>(V))
              return rez(V, out);
            if (const auto *I2 = dyn_cast<Instruction>(V)) {
              if (isa<BinaryOperator>(I2) || isa<CastInst>(I2) ||
                  isa<PHINode>(I2) || isa<SelectInst>(I2) ||
                  isa<FreezeInst>(I2)) {
                for (const Use &U : I2->operands())
                  if ((U->getType()->isIntegerTy() ||
                       U->getType()->isPointerTy()) &&
                      !collectIntSrcs(U.get(), depth - 1, out))
                    return false;
                return true;
              }
            }
            return false;
          };
          std::set<std::string> atomStrs;
          SmallVector<PAtom, 6> atoms;
          auto refStr = [](const Src &x) -> std::string {
            std::string r = x.kind == 0 || x.kind == 1
                                ? "arg" + std::to_string(x.arg)
                                : "@" + x.gv->getName().str();
            if (x.off) r += "@" + std::to_string(x.off);
            return r;
          };
          auto emitStore = [&](const SmallVectorImpl<Src> &Ts,
                               const SmallVectorImpl<Src> &Vs,
                               std::string &ewhy) -> bool {
            for (auto &t : Ts) {
              if ((t.kind != 0 && t.kind != 3) || t.off < 0) {
                ewhy = "store-target"; return false;
              }
              if (t.kind == 3 && !CFLAtomsGlobalStores) {
                // QUARANTINE (2026-08-22): ST(*@g<-...) adoption at
                // 5.18 welded ethtool_phy_ops' cell cluster into the
                // pool (+27,741 pairs, 98% one setter's atom;
                // mechanism not yet pinned — bisect2 attribution
                // exact). Read-side @g atoms are clean (+12 residue).
                ewhy = "global-store-quarantine"; return false;
              }
              const bool tArg = t.kind == 0;
              for (auto &v : Vs) {
                if (v.kind == 2) continue;
                if (v.off < 0) { ewhy = "interior-store"; return false; }
                if (v.kind == 0 || v.kind == 3) { // value = address
                  std::string a = "ST(*" + refStr(t) + "<-" + refStr(v) + ")";
                  if (atomStrs.insert(a).second)
                    atoms.push_back({0, tArg ? t.arg : -1,
                                     v.kind == 0 ? v.arg : -1, t.off, v.off,
                                     tArg ? nullptr : t.gv,
                                     v.kind == 0 ? nullptr : v.gv});
                } else { // kind 1/4: value = loaded cell -> MV
                  if (v.kind == 1 && tArg && v.arg == t.arg && v.off == t.off)
                    continue; // self-move: cell self-loop, vacuous
                  if (v.kind == 4 && !tArg && v.gv == t.gv && v.off == t.off)
                    continue;
                  std::string a = "MV(*" + refStr(t) + "<-*" + refStr(v) + ")";
                  if (atomStrs.insert(a).second)
                    atoms.push_back({1, tArg ? t.arg : -1,
                                     v.kind == 1 ? v.arg : -1, t.off, v.off,
                                     tArg ? nullptr : t.gv,
                                     v.kind == 1 ? nullptr : v.gv});
                }
              }
            }
            return true;
          };
          for (const auto &BB : F) {
            for (const auto &I : BB) {
              if (const auto *CB = dyn_cast<CallBase>(&I)) {
                if (CB->isInlineAsm()) {
                  if (asmTransferFree(CB)) continue;
                  why = "asm"; return false;
                }
                if (const auto *II = dyn_cast<IntrinsicInst>(CB)) {
                  switch (II->getIntrinsicID()) {
                  case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
                  case Intrinsic::dbg_label:
                  case Intrinsic::lifetime_start: case Intrinsic::lifetime_end:
                  case Intrinsic::assume: case Intrinsic::expect:
                  case Intrinsic::prefetch: case Intrinsic::donothing:
                  case Intrinsic::trap: case Intrinsic::ubsantrap:
                  case Intrinsic::vaend: case Intrinsic::memset:
                  case Intrinsic::stacksave: case Intrinsic::stackrestore:
                  case Intrinsic::returnaddress: case Intrinsic::frameaddress:
                    continue;
                  case Intrinsic::vastart: case Intrinsic::vacopy:
                    // va_start/va_copy fill a local va_list with
                    // CALLER tail args the local solve cannot see:
                    // va_arg loads then read cells this interpreter
                    // tracks as empty, so stores of that content
                    // vanish instead of becoming atoms
                    // (sqlite3_config lost the sqlite3_mem_methods
                    // install). Attribute-or-refuse: refuse. (Must
                    // follow the benign list's `continue`, see the
                    // solved pass's note on the 24af384 fall-through.)
                    why = "varargs"; return false;
                  default: {
                    bool pure = !II->getType()->isPointerTy();
                    for (const Value *Arg : II->args())
                      pure &= !Arg->getType()->isPointerTy();
                    if (pure) continue;
                    why = "intrinsic"; return false;
                  }
                  }
                }
                const Function *CF = dyn_cast<Function>(
                    CB->getCalledOperand()->stripPointerCastsAndAliases());
                if (!CF) { why = "icall"; return false; }
                if (calleeSafe(CF)) continue; // NOOP: consumes, no effects
                // Rules A/B (broad): atom-summarized bodies stay
                // walked, so a site passing only constants and clean
                // scalars keeps all its edges — irrelevant to F's
                // transfer function regardless of the callee. Answer
                // sites (__SCT__ dispatch) are never irrelevant.
                if (!isAnswerSiteCallee(CF) &&
                    callsiteArgIrrelevant(CB, /*narrowConstants=*/false))
                  continue;
                SmallVector<PAtom, 6> cas;
                int st = calleeAtoms(CF, cas);
                if (st != 1) {
                  if (st == 0) retryable = true;
                  why = "compose"; return false;
                }
                // Translate callee EFFECT atoms into caller frame.
                for (const auto &A : cas) {
                  if (A.kind == 2 || A.kind == 3 || A.kind == 5 ||
                      A.kind == 9)
                    continue; // ret-only
                  if (A.kind >= 6 || A.o1 < 0 || A.o2 < 0) {
                    // MVX/2-level/wildcard atoms: solved-
                    why = "compose"; return false; // pass territory
                  }
                  if ((!A.g1 &&
                       (A.a1 < 0 || (unsigned)A.a1 >= CB->arg_size())) ||
                      (!A.g2 &&
                       (A.a2 < 0 || (unsigned)A.a2 >= CB->arg_size()))) {
                    why = "compose"; return false;
                  }
                  SmallVector<Src, 4> Cs, Xs;
                  if (A.g1) Cs.push_back({3, 0, 0, A.g1});
                  else if (!rez(CB->getArgOperand(A.a1), Cs)) {
                    why = "compose"; return false;
                  }
                  if (A.g2) Xs.push_back({3, 0, 0, A.g2});
                  else if (!rez(CB->getArgOperand(A.a2), Xs)) {
                    why = "compose"; return false;
                  }
                  if (A.kind == 0) { // callee ST: value = arg a2[@o2] | @g2@o2
                    SmallVector<Src, 4> Ts2, Xs2;
                    for (auto t : Cs) {
                      if (t.kind == 2) continue;
                      if (t.kind != 0 && t.kind != 3) {
                        why = "compose"; return false;
                      }
                      t.off += A.o1;
                      Ts2.push_back(t);
                    }
                    for (auto v : Xs) {
                      if (v.kind == 0 || v.kind == 3) v.off += A.o2;
                      else if ((v.kind == 1 || v.kind == 4) && A.o2) {
                        why = "compose"; return false;
                      }
                      Xs2.push_back(v);
                    }
                    std::string ewhy;
                    if (!emitStore(Ts2, Xs2, ewhy)) { why = ewhy; return false; }
                  } else if (A.kind == 1) { // callee MV
                    for (auto t : Cs) {
                      if (t.kind == 2) continue;
                      if (t.kind != 0 && t.kind != 3) {
                        why = "compose"; return false;
                      }
                      for (auto v : Xs) {
                        if (v.kind == 2) continue;
                        SmallVector<Src, 4> T1{
                            {t.kind, t.arg, t.off + A.o1, t.gv}};
                        SmallVector<Src, 4> V1;
                        if (v.kind == 0)
                          V1.push_back({1, v.arg, v.off + A.o2});
                        else if (v.kind == 3)
                          V1.push_back({4, 0, v.off + A.o2, v.gv});
                        else { why = "compose"; return false; }
                        std::string ewhy;
                        if (!emitStore(T1, V1, ewhy)) { why = ewhy; return false; }
                      }
                    }
                  } else if (A.kind == 4) { // callee CPY: whole cells
                    for (auto t : Cs)
                      for (auto v : Xs) {
                        if (t.kind == 2 || v.kind == 2) continue;
                        if (t.kind != 0 || v.kind != 0 || t.off || v.off) {
                          why = "compose"; return false;
                        }
                        std::string a = "CPY(arg" + std::to_string(t.arg) +
                            "<-arg" + std::to_string(v.arg) + ")";
                        if (atomStrs.insert(a).second)
                          atoms.push_back({4, t.arg, v.arg, 0, 0});
                      }
                  }
                }
                continue;
              }
              if (const auto *SI3 = dyn_cast<StoreInst>(&I)) {
                const Value *Val = SI3->getValueOperand();
                if (isSlot(SI3->getPointerOperand())) continue; // frame-local
                SmallVector<Src, 4> Ts;
                if (!rez(SI3->getPointerOperand(), Ts)) {
                  why = blockedOnCallee ? (retryable = true, "compose")
                                        : "store-target";
                  return false;
                }
                if (!Val->getType()->isPointerTy()) {
                  if (isPtrWidthInt(Val->getType(), *curDL) &&
                      mayCarryLocal(Val, 8)) {
                    SmallVector<Src, 4> Is;
                    std::string ewhy;
                    if (collectIntSrcs(Val, 8, Is) &&
                        emitStore(Ts, Is, ewhy))
                      continue; // modeled as MV/ST slot-copy atoms
                    retryable = true; // callee may become safe later
                    why = "int-launder-store"; return false;
                  }
                  continue;
                }
                SmallVector<Src, 4> Vs;
                if (!rez(Val, Vs)) {
                  why = blockedOnCallee ? (retryable = true, "compose")
                                        : "store-value";
                  return false;
                }
                std::string ewhy;
                if (!emitStore(Ts, Vs, ewhy)) { why = ewhy; return false; }
                continue;
              }
              if (isa<AtomicRMWInst>(&I) || isa<AtomicCmpXchgInst>(&I)) {
                why = "atomic"; return false;
              }
              if (isa<IndirectBrInst>(&I)) { why = "indirectbr"; return false; }
              if (const auto *RI = dyn_cast<ReturnInst>(&I)) {
                const Value *RV = RI->getReturnValue();
                if (!RV) continue;
                if (!RV->getType()->isPointerTy()) {
                  if (isPtrWidthInt(RV->getType(), *curDL) &&
                      mayCarryLocal(RV, 8)) {
                    SmallVector<Src, 4> Is;
                    bool okc = collectIntSrcs(RV, 8, Is);
                    for (auto &v : Is) {
                      if (!okc) break;
                      if (v.kind == 2) continue;
                      if (v.kind == 3 && v.off >= 0) {
                        std::string a = "ALIAS(ret<-" + refStr(v) + ")";
                        if (atomStrs.insert(a).second)
                          atoms.push_back({3, 0, -1, 0, v.off, nullptr, v.gv});
                      } else if (v.kind == 4 && v.off >= 0) {
                        std::string a = "LD(ret<-*" + refStr(v) + ")";
                        if (atomStrs.insert(a).second)
                          atoms.push_back({2, 0, -1, 0, v.off, nullptr, v.gv});
                      } else if (v.kind == 0 && v.off >= 0) {
                        std::string a = "ALIAS(ret<-arg" +
                            std::to_string(v.arg) +
                            (v.off ? "@" + std::to_string(v.off) : "") + ")";
                        if (atomStrs.insert(a).second)
                          atoms.push_back({3, 0, v.arg, 0, v.off});
                      } else if (v.kind == 1 && v.off >= 0) {
                        std::string a = "LD(ret<-*arg" +
                            std::to_string(v.arg) +
                            (v.off ? "@" + std::to_string(v.off) : "") + ")";
                        if (atomStrs.insert(a).second)
                          atoms.push_back({2, 0, v.arg, 0, v.off});
                      } else
                        okc = false;
                    }
                    if (okc) continue;
                    retryable = true; // callee may become safe later
                    why = "ret-launder"; return false;
                  }
                  continue;
                }
                SmallVector<Src, 4> Rs;
                if (!rez(RV, Rs)) {
                  why = blockedOnCallee ? (retryable = true, "compose")
                                        : "ret";
                  return false;
                }
                for (auto &v : Rs) {
                  if (v.kind == 2) continue;
                  if (v.kind == 3 && v.off >= 0) {
                    std::string a = "ALIAS(ret<-" + refStr(v) + ")";
                    if (atomStrs.insert(a).second)
                      atoms.push_back({3, 0, -1, 0, v.off, nullptr, v.gv});
                  } else if (v.kind == 4 && v.off >= 0) {
                    std::string a = "LD(ret<-*" + refStr(v) + ")";
                    if (atomStrs.insert(a).second)
                      atoms.push_back({2, 0, -1, 0, v.off, nullptr, v.gv});
                  } else if (v.kind == 0 && v.off >= 0) {
                    std::string a = "ALIAS(ret<-arg" + std::to_string(v.arg) +
                        (v.off ? "@" + std::to_string(v.off) : "") + ")";
                    if (atomStrs.insert(a).second)
                      atoms.push_back({3, 0, v.arg, 0, v.off});
                  } else if (v.kind == 1 && v.off >= 0) {
                    std::string a = "LD(ret<-*arg" + std::to_string(v.arg) +
                        (v.off ? "@" + std::to_string(v.off) : "") + ")";
                    if (atomStrs.insert(a).second)
                      atoms.push_back({2, 0, v.arg, 0, v.off});
                  } else { why = "ret-interior"; return false; }
                }
              }
            }
          }
          if (atomStrs.empty() || atomStrs.size() > 6) {
            why = atomStrs.empty() ? "no-atoms" : "too-many-atoms";
            return false;
          }
          std::string line;
          for (auto &a : atomStrs) line += " " + a;
          CG_LOG("AtomProp: OK " << F.getName() << line << "\n");
          props[&F] = atoms;
          nOk++;
          return true;
        };
        bool achanged = true;
        size_t around = 0;
        while (achanged && around++ < 20) {
          achanged = false;
          for (auto &[mod, mname] : Ctx->Modules) {
            for (const Function &F : *mod) {
              if (F.isDeclaration()) continue;
              const Function *canon = getFuncDef(const_cast<Function *>(&F));
              if (canon != &F || ok.count(canon) || props.count(canon) ||
                  permRefused.count(canon))
                continue;
              if (Ctx->FuncSummaries.count(canon)) continue;
              bool retryable = false;
              std::string why;
              if (tryFn(F, retryable, why)) {
                achanged = true;
              } else if (!retryable) {
                permRefused.insert(canon);
                if (around == 1) {
                  aRefuse[why]++;
                  CG_LOG("AtomProp: REFUSED " << F.getName() << " ["
                         << why << "]\n");
                }
              } else if (around == 1) {
                aRefuse["compose-pending"]++;
                CG_LOG("AtomProp: PENDING " << F.getName() << " ["
                       << why << "]\n");
              }
            }
          }
        }
        std::string ah;
        for (auto &kv : aRefuse)
          ah += kv.first + "=" + std::to_string(kv.second) + " ";
        CG_LOG("AtomProp: " << nOk << " proposed (" << around
               << " rounds); first-round refusals: " << ah << "\n");
      }

      // ---- Stage A: solver-based summary census ----
      // (--cfl-propose-solved-summaries) Function-local abstract solve
      // over the atom-grammar's value vocabulary; atoms extracted from
      // the solved state. Complexity that stays local no longer
      // refuses — only true interface escapes do. KEY INVARIANT:
      // solved-class summaries keep BODIES WALKED (never g_noopBodies),
      // so only FORMAL-ROOTED values (ARGP/LOADARG/formal-deep) are
      // starved by adoption and need atom relay or escape refusal;
      // global/external-derived flows survive via the walked body.
      // Zero-atom successes -> okEmpty (EMPTY-ATOM summaries: callsite
      // wiring cut, body kept — in-body registrations survive).
      boost::unordered_flat_set<const Function *> okEmpty;
      // Under --cfl-cells a scalar narrower than a pointer is data: its
      // loads and stores carry no pointer (plan 3.42), as in the graph.
      auto narrowData = [&](Type *T) {
        return (T->isIntegerTy() || T->isFloatingPointTy()) &&
               curDL->getTypeSizeInBits(T) < curDL->getPointerSizeInBits();
      };
      if (CFLProposeSolvedSummaries && curDL) {
        // LV kinds: 0 ARGP(a,off) 1 LOADARG(a,off) 2 NULL 3 GLOBALP(g,off)
        //           4 LOADGLOBAL(g,off) 5 LOCAL(id,off) 6 OPAQUE-EXT
        //           7 OPAQUE-IF (formal-derived, must not escape/land)
        //           8 INTERIOR-OF-LOADED: loaded from cell (a/g, off)
        //             plus unknown delta — ret-expressible as LDX
        //           9 TWO-LEVEL: loaded through *(cell(a/g, off)),
        //             2nd level wildcard — LD2/ST2/MV2 territory
        //           off == -1: wildcard offset
        struct LV {
          uint8_t k; int a; int64_t off; const GlobalValue *g;
          bool operator==(const LV &o) const {
            return k == o.k && a == o.a && off == o.off && g == o.g;
          }
        };
        using LVSet = llvm::SmallVector<LV, 4>;
        auto addLV = [](LVSet &sset, const LV &v) -> bool {
          for (auto &e : sset)
            if (e == v) return false;
          // Offset widening: >3 distinct offsets on the same base
          // (pointer-advance loops: s++) widen to the wildcard @X —
          // sound (fx-loop superset) and keeps loops convergent.
          if (v.k == 0 || v.k == 1 || v.k == 3 || v.k == 4 || v.k == 5 ||
              v.k == 8 || v.k == 9) {
            unsigned sameBase = 0;
            bool haveWild = false;
            for (auto &e : sset)
              if (e.k == v.k && e.a == v.a && e.g == v.g) {
                sameBase++;
                haveWild |= e.off < 0;
              }
            if (haveWild) return false; // wildcard subsumes
            if (sameBase >= 3) {
              sset.erase(std::remove_if(sset.begin(), sset.end(),
                                        [&](const LV &e) {
                                          return e.k == v.k && e.a == v.a &&
                                                 e.g == v.g;
                                        }),
                         sset.end());
              sset.push_back({v.k, v.a, -1, v.g});
              return true;
            }
          }
          if (sset.size() >= 8) { // width cap: collapse, keep worst kind
            uint8_t worst = 6;
            for (auto &e : sset)
              if (e.k == 7 || e.k == 0 || e.k == 1) worst = 7;
            if (v.k == 7 || v.k == 0 || v.k == 1) worst = 7;
            for (auto &e : sset)
              if (e.k == worst) return false;
            sset.clear();
            sset.push_back({worst, 0, 0, nullptr});
            return true;
          }
          sset.push_back(v);
          return true;
        };
        boost::unordered_flat_map<std::string, uint64_t> sRefuse;
        boost::unordered_flat_set<const Function *> sPerm;
        size_t nSolved = 0, nEmpty = 0;
        auto trySolve = [&](const Function &F, bool &retryable,
                            std::string &why) -> bool {
          retryable = false;
          if (F.arg_size() > 10) { why = "many-args"; return false; }
          size_t nInst = 0;
          for (const auto &BB : F) nInst += BB.size();
          if (nInst > 2048) { why = "too-big"; return false; }
          boost::unordered_flat_map<const Value *, int> argIdx;
          int ai = 0;
          for (const Argument &A : F.args()) argIdx[&A] = ai++;
          std::map<const Value *, LVSet> env;
          std::map<std::tuple<int, int, const GlobalValue *, int64_t>, LVSet>
              cells;
          int nextLocal = 0;
          boost::unordered_flat_map<const Value *, int> localId;
          bool changed = true;
          std::string fail;
          bool escRetry = false;
          auto evalV = [&](const Value *V) -> LVSet {
            V = V->stripPointerCasts();
            if (auto it2 = argIdx.find(V); it2 != argIdx.end()) {
              // Sub-pointer-width scalar formals (i32 sizes/flags,
              // bools, floats) cannot carry pointer identity — clean.
              Type *AT = V->getType();
              if (!AT->isPointerTy() && !isPtrWidthInt(AT, *curDL))
                return {};
              return {LV{0, it2->second, 0, nullptr}};
            }
            if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
              return {LV{2, 0, 0, nullptr}};
            if (const auto *G2 =
                    dyn_cast<GlobalValue>(V->stripPointerCastsAndAliases())) {
              if (G2->isDeclaration() && G2->hasName()) {
                auto git2 = Ctx->Gobjs.find(G2->getGUID());
                if (git2 != Ctx->Gobjs.end()) G2 = git2->second;
              }
              return {LV{3, 0, 0, G2}};
            }
            if (!isa<Instruction>(V)) {
              if (const auto *G = dyn_cast<GEPOperator>(V)) {
                APInt Off(64, 0);
                if (G->accumulateConstantOffset(*curDL, Off))
                  if (const auto *G3 = dyn_cast<GlobalValue>(
                          G->getPointerOperand()
                              ->stripPointerCastsAndAliases())) {
                    if (G3->isDeclaration() && G3->hasName()) {
                      auto git3 = Ctx->Gobjs.find(G3->getGUID());
                      if (git3 != Ctx->Gobjs.end()) G3 = git3->second;
                    }
                    return {LV{3, 0, Off.getSExtValue(), G3}};
                  }
                return {LV{6, 0, 0, nullptr}};
              }
              if (const auto *C = dyn_cast<Constant>(V)) {
                // An integer constant derived from a pointer (`h->start =
                // (u64)secondary_startup_64`) carries it: the global for a
                // plain ptrtoint, an unknown value for folded arithmetic.
                // Not an empty value: an empty value made the store vanish
                // from an adopted OK-EMPTY summary.
                if (!C->getType()->isPointerTy() && constantHasPtrToInt(C, 6)) {
                  const auto *CE = dyn_cast<ConstantExpr>(C);
                  if (CE && CE->getOpcode() == Instruction::PtrToInt)
                    if (const auto *G4 =
                            dyn_cast<GlobalValue>(CE->getOperand(0)->stripPointerCastsAndAliases())) {
                      if (G4->isDeclaration() && G4->hasName())
                        if (auto git4 = Ctx->Gobjs.find(G4->getGUID()); git4 != Ctx->Gobjs.end()) G4 = git4->second;
                      return {LV{3, 0, 0, G4}};
                    }
                  return {LV{6, 0, 0, nullptr}};
                }
                if (!C->getType()->isPointerTy()) return {};
                return {LV{6, 0, 0, nullptr}};
              }
            }
            auto eIt = env.find(V);
            if (eIt != env.end()) return eIt->second;
            return {};
          };
          auto mergeInto = [&](LVSet &dst, const LVSet &src) -> bool {
            bool ch = false;
            for (const LV &v : src) ch |= addLV(dst, v);
            return ch;
          };
          auto setEnv = [&](const Value *V, const LVSet &lv) {
            changed |= mergeInto(env[V], lv);
          };
          auto cellKey = [&](const LV &base)
              -> std::optional<
                  std::tuple<int, int, const GlobalValue *, int64_t>> {
            if (base.k == 0)
              return std::make_tuple(0, base.a, nullptr, base.off);
            if (base.k == 3)
              return std::make_tuple(3, 0, base.g, base.off);
            if (base.k == 5)
              return std::make_tuple(5, base.a, nullptr, base.off);
            if (base.k == 1 || base.k == 8) // level-2: *(cell(base,off))
              return std::make_tuple(9, base.g ? -1 : base.a, base.g,
                                     base.off);
            return std::nullopt;
          };
          // Sensitive = starved-by-adoption content: formal-rooted only.
          auto lvSensitive = [&](const LV &v) {
            return v.k == 0 || v.k == 1 || v.k == 7 ||
                   ((v.k == 8 || v.k == 9) && !v.g);
          };
          auto lvsSensitive = [&](const LVSet &sset) {
            for (const LV &v : sset)
              if (lvSensitive(v)) return true;
            return false;
          };
          std::function<bool(int, int)> localSensitive =
              [&](int lid, int depth) -> bool {
            if (depth > 4) return true;
            for (auto &kv : cells) {
              if (std::get<0>(kv.first) != 5 || std::get<1>(kv.first) != lid)
                continue;
              for (const LV &v : kv.second) {
                if (lvSensitive(v)) return true;
                if (v.k == 5 && localSensitive(v.a, depth + 1)) return true;
              }
            }
            return false;
          };
          auto anySensitive = [&](const LVSet &sset) -> bool {
            if (lvsSensitive(sset)) return true;
            for (const LV &v : sset)
              if (v.k == 5 && localSensitive(v.a, 0)) return true;
            return false;
          };
          // Content of the cell at (base, off). A wildcard-offset write
          // (memcpy, a variable index, an unmodeled callee) lands in the
          // base's @X cell and may sit at ANY offset, so an exact-offset
          // read sees that cell too.
          auto readCell = [&](LVSet &r, const LV &v) {
            auto ck = cellKey(v);
            if (!ck) return;
            auto cIt = cells.find(*ck);
            if (cIt != cells.end())
              for (const LV &c : cIt->second) r.push_back(c);
            if (v.off < 0) return;
            LV w = v;
            w.off = -1;
            auto wIt = cells.find(*cellKey(w));
            if (wIt != cells.end())
              for (const LV &c : wIt->second) r.push_back(c);
          };
          // An unmodeled callee (declaration without a summary, in-body
          // icall, inline asm, unknown intrinsic) may write any external
          // value anywhere in a local object it reaches through its
          // pointer arguments, including locals whose addresses are stored
          // there. Without this a slot filled by posix_memalign(&p, ...)
          // reads back empty, and a fresh object handed to the caller
          // through a formal (`*s = p`, ffmpeg avio_open_dyn_buf at -O3)
          // vanished from an OK-EMPTY summary whose adoption then cut the
          // only wiring that carried it (fuzz-observed dyn_buf_write lost
          // at aviobuf.c:163). With the clobber the hand-off is OPAQUE-EXT
          // into a formal and the summary is refused (ext-into-formal).
          auto clobberLocals = [&](const CallBase *CB) {
            SmallVector<int, 4> work;
            boost::unordered_flat_set<int> seen;
            for (const Value *Arg : CB->args())
              for (const LV &v : evalV(Arg))
                if (v.k == 5 && seen.insert(v.a).second) work.push_back(v.a);
            while (!work.empty()) {
              int id = work.pop_back_val();
              for (auto &kv : cells)
                if (std::get<0>(kv.first) == 5 && std::get<1>(kv.first) == id)
                  for (const LV &c : kv.second)
                    if (c.k == 5 && seen.insert(c.a).second)
                      work.push_back(c.a);
              changed |= mergeInto(cells[*cellKey(LV{5, id, -1, nullptr})],
                                   LVSet{LV{6, 0, 0, nullptr}});
            }
          };
          for (unsigned round = 0; changed && fail.empty(); round++) {
            if (round > 64) { fail = "no-fixpoint"; break; }
            changed = false;
            for (const auto &BB : F) {
              for (const auto &I : BB) {
                if (!fail.empty()) break;
                if (const auto *AI = dyn_cast<AllocaInst>(&I)) {
                  auto [lit, lins] = localId.try_emplace(AI, nextLocal);
                  if (lins) nextLocal++;
                  setEnv(AI, {LV{5, lit->second, 0, nullptr}});
                } else if (const auto *G = dyn_cast<GEPOperator>(&I)) {
                  LVSet b = evalV(G->getPointerOperand()), r;
                  APInt Off(64, 0);
                  const bool cst = G->accumulateConstantOffset(*curDL, Off);
                  for (LV v : b) {
                    if (v.k == 0 || v.k == 3 || v.k == 5) {
                      if (v.off >= 0 && cst) v.off += Off.getSExtValue();
                      else v.off = -1;
                    } else if (v.k == 2) {
                      continue;
                    } else if (v.k == 1) {
                      v = LV{8, v.a, v.off, nullptr}; // interior of loaded
                    } else if (v.k == 4) {
                      v = LV{8, -1, v.off, v.g};
                    } else if (v.k == 8 || v.k == 9) {
                      // deeper interior: same base (wildcards absorb)
                    } else if (v.k == 7) {
                      v = LV{7, 0, 0, nullptr};
                    } else if (v.k == 6) {
                      v = LV{6, 0, 0, nullptr};
                    }
                    r.push_back(v);
                  }
                  LVSet dd;
                  mergeInto(dd, r);
                  setEnv(&I, dd);
                } else if (const auto *LI = dyn_cast<LoadInst>(&I);
                           LI && CFLCells && narrowData(LI->getType())) {
                  setEnv(&I, LVSet()); // data (plan 3.42): no pointer
                } else if (const auto *LI = dyn_cast<LoadInst>(&I)) {
                  LVSet b = evalV(LI->getPointerOperand()), r;
                  for (const LV &v : b) {
                    if (v.k == 2) continue;
                    if (v.k == 0) {
                      if (v.off < 0) {
                        r.push_back({1, v.a, -1, nullptr}); // LOADARG@X
                        readCell(r, v);
                        continue;
                      }
                      r.push_back({1, v.a, v.off, nullptr});
                      readCell(r, v);
                    } else if (v.k == 3) {
                      if (v.off < 0) { r.push_back({6, 0, 0, nullptr}); continue; }
                      r.push_back({4, 0, v.off, v.g});
                      readCell(r, v);
                    } else if (v.k == 5) {
                      if (v.off < 0) {
                        r.push_back({localSensitive(v.a, 0) ? (uint8_t)7
                                                            : (uint8_t)6,
                                     0, 0, nullptr});
                        continue;
                      }
                      readCell(r, v);
                    } else if (v.k == 1 || v.k == 8) {
                      r.push_back({9, v.g ? -1 : v.a, v.off, v.g});
                      readCell(r, v);
                    } else if (v.k == 7 || (v.k == 9 && !v.g)) {
                      r.push_back({7, 0, 0, nullptr}); // 3-level: deep
                    } else {
                      r.push_back({6, 0, 0, nullptr});
                    }
                  }
                  LVSet dd;
                  mergeInto(dd, r);
                  setEnv(&I, dd);
                } else if (const auto *SI2 = dyn_cast<StoreInst>(&I);
                           SI2 && CFLCells &&
                           narrowData(SI2->getValueOperand()->getType())) {
                  continue; // data (plan 3.42): writes no pointer
                } else if (const auto *SI2 = dyn_cast<StoreInst>(&I)) {
                  LVSet val = evalV(SI2->getValueOperand());
                  LVSet ptr = evalV(SI2->getPointerOperand());
                  for (const LV &pb : ptr) {
                    if (pb.k == 2) continue;
                    auto ck = cellKey(pb);
                    if (!ck) {
                      // write through loaded/opaque pointer: refuse
                      // only if the value carries starved content
                      if (anySensitive(val)) { fail = "deep-store"; break; }
                      continue;
                    }
                    // pb.off < 0: wildcard cell — extraction emits @X
                    changed |= mergeInto(cells[*ck], val);
                  }
                } else if (const auto *PN = dyn_cast<PHINode>(&I)) {
                  LVSet r;
                  for (const Value *iv : PN->incoming_values())
                    mergeInto(r, evalV(iv));
                  setEnv(&I, r);
                } else if (const auto *SEL = dyn_cast<SelectInst>(&I)) {
                  LVSet r = evalV(SEL->getTrueValue());
                  mergeInto(r, evalV(SEL->getFalseValue()));
                  setEnv(&I, r);
                } else if (isa<CastInst>(&I) || isa<FreezeInst>(&I)) {
                  setEnv(&I, evalV(cast<Instruction>(&I)->getOperand(0)));
                } else if (const auto *BO = dyn_cast<BinaryOperator>(&I)) {
                  // int arith over provenance-carrying values: keep the
                  // identities, lose the offset (laundering-safe)
                  LVSet r;
                  for (unsigned oi = 0; oi < 2; oi++)
                    for (LV v : evalV(BO->getOperand(oi))) {
                      if (v.k == 0 || v.k == 3 || v.k == 5 || v.k == 8)
                        v.off = -1;
                      r.push_back(v);
                    }
                  LVSet dd;
                  mergeInto(dd, r);
                  setEnv(&I, dd);
                } else if (isa<AtomicRMWInst>(&I) ||
                           isa<AtomicCmpXchgInst>(&I)) {
                  fail = "atomic";
                } else if (isa<IndirectBrInst>(&I)) {
                  fail = "indirectbr";
                } else if (const auto *CB = dyn_cast<CallBase>(&I)) {
                  if (CB->isInlineAsm()) {
                    // Body-kept summaries: the asm stays modeled in the
                    // walked body — the interface question is only
                    // whether STARVED (formal-rooted) content moves
                    // through it invisibly to the atoms.
                    const auto *IA3 =
                        cast<InlineAsm>(CB->getCalledOperand());
                    auto ACs =
                        InlineAsm::ParseConstraints(IA3->getConstraintString());
                    bool memClob = false, anyIndOut = false;
                    for (auto &CI : ACs) {
                      if (CI.Type == InlineAsm::isClobber) {
                        for (const std::string &Code : CI.Codes)
                          if (StringRef(Code).contains("memory"))
                            memClob = true;
                      } else if (CI.Type == InlineAsm::isOutput &&
                                 CI.isIndirect)
                        anyIndOut = true;
                    }
                    const bool mayWrite = memClob || anyIndOut;
                    bool sensIn = false;
                    unsigned ai3 = 0;
                    for (auto &CI : ACs) {
                      if (CI.Type == InlineAsm::isClobber
#if LLVM_VERSION_MAJOR >= 15
                          || CI.Type == InlineAsm::isLabel
#endif
                      )
                        continue;
                      if (!CI.hasArg()) continue;
                      if (ai3 >= CB->arg_size()) { fail = "asm"; break; }
                      const Value *Arg = CB->getArgOperand(ai3++);
                      LVSet av = evalV(Arg);
                      const bool sens = anySensitive(av);
                      if (CI.isIndirect) {
                        if (CI.Type == InlineAsm::isOutput && sens) {
                          // asm writes external content into interface
                          // memory: not atom-expressible
                          fail = "asm-slot";
                          break;
                        }
                        if (sens) sensIn = true; // read slot of our data
                      } else if (sens) {
                        if (mayWrite) { fail = "asm-arg"; break; }
                        sensIn = true;
                      }
                    }
                    if (!fail.empty()) break;
                    if (mayWrite) clobberLocals(CB);
                    if (CB->getType()->isPointerTy() ||
                        isPtrWidthInt(CB->getType(), *curDL))
                      setEnv(&I, {LV{sensIn ? (uint8_t)7 : (uint8_t)6, 0, 0,
                                     nullptr}});
                    continue;
                  }
                  if (const auto *II = dyn_cast<IntrinsicInst>(CB)) {
                    switch (II->getIntrinsicID()) {
                    case Intrinsic::dbg_declare: case Intrinsic::dbg_value:
                    case Intrinsic::dbg_label:
                    case Intrinsic::lifetime_start:
                    case Intrinsic::lifetime_end:
                    case Intrinsic::assume: case Intrinsic::expect:
                    case Intrinsic::prefetch: case Intrinsic::donothing:
                    case Intrinsic::trap: case Intrinsic::ubsantrap:
                    case Intrinsic::vaend: case Intrinsic::memset:
                    case Intrinsic::stacksave: case Intrinsic::stackrestore:
                    case Intrinsic::returnaddress:
                    case Intrinsic::frameaddress:
                      continue;
                    case Intrinsic::vastart: case Intrinsic::vacopy:
                      // Same varargs blindness as the atom pass: the
                      // local solve never sees caller tail args, so
                      // an "effect-complete" solved summary would
                      // under-claim (sqlite3_config solved OK-EMPTY
                      // while its body installs sqlite3_mem_methods
                      // via va_arg + memcpy). Refuse. (Must follow the
                      // benign list's `continue` — 24af384 placed it
                      // inside the fall-through chain and refused every
                      // function with a dbg/lifetime intrinsic.)
                      fail = "varargs";
                      break;
                    default: {
                      if (isa<MemTransferInst>(II)) {
                        // memcpy/memmove as a wildcard cell transfer:
                        // dst@X ∪= *src@X (CPY over unknown layout —
                        // the fx-loop application covers any offset
                        // pairing; FI = plain cell copy). Refuse only
                        // when an endpoint is unlocatable AND starved
                        // content would move through it.
                        const auto *MT = cast<MemTransferInst>(II);
                        LVSet d2 = evalV(MT->getRawDest());
                        LVSet s2 = evalV(MT->getRawSource());
                        LVSet vals;
                        for (const LV &v : s2) {
                          if (v.k == 2) continue;
                          if (v.k == 0)
                            vals.push_back({1, v.a, -1, nullptr});
                          else if (v.k == 3)
                            vals.push_back({4, 0, -1, v.g});
                          else if (v.k == 5) {
                            for (auto &kv2 : cells)
                              if (std::get<0>(kv2.first) == 5 &&
                                  std::get<1>(kv2.first) == v.a)
                                for (const LV &c2 : kv2.second)
                                  vals.push_back(c2);
                          } else if (v.k == 1 || v.k == 7 ||
                                     (v.k == 8 && !v.g)) {
                            vals.push_back({7, 0, 0, nullptr});
                          } else {
                            vals.push_back({6, 0, 0, nullptr});
                          }
                        }
                        bool bad2 = false;
                        for (const LV &t0 : d2) {
                          if (t0.k == 2) continue;
                          LV t = t0;
                          t.off = -1; // whole-range wildcard
                          auto ck = cellKey(t);
                          if (!ck) {
                            if (lvsSensitive(vals)) { bad2 = true; break; }
                            continue;
                          }
                          changed |= mergeInto(cells[*ck], vals);
                        }
                        if (bad2) { fail = "memcpy"; break; }
                        continue;
                      }
                      bool pure = !II->getType()->isPointerTy();
                      for (const Value *Arg : II->args())
                        pure &= !Arg->getType()->isPointerTy();
                      if (pure) continue;
                      for (const Value *Arg : II->args())
                        if (anySensitive(evalV(Arg))) {
                          fail = "intrinsic";
                          break;
                        }
                      if (!fail.empty()) break;
                      clobberLocals(CB);
                      if (CB->getType()->isPointerTy())
                        setEnv(&I, {LV{6, 0, 0, nullptr}});
                      continue;
                    }
                    }
                    continue;
                  }
                  const Function *CF = dyn_cast<Function>(
                      CB->getCalledOperand()->stripPointerCastsAndAliases());
                  if (!CF) {
                    // In-body icall: solved-class summaries keep the
                    // BODY WALKED, so the site survives and resolves
                    // identically — refusal is needed only when
                    // formal-derived content feeds the dispatch (its
                    // fptr or args), i.e. real caller-dependent
                    // dispatch. printk-class console icalls read the
                    // registry, not caller args: formal-independent.
                    bool sens = anySensitive(evalV(CB->getCalledOperand()));
                    for (const Value *Arg : CB->args())
                      if (!sens && anySensitive(evalV(Arg))) sens = true;
                    if (sens) { fail = "icall"; break; }
                    clobberLocals(CB);
                    if (CB->getType()->isPointerTy())
                      setEnv(&I, {LV{6, 0, 0, nullptr}});
                    continue;
                  }
                  // Answer-site callees (__SCT__): body kept => the
                  // site survives; treat as a normal unsummarized
                  // callee (escape check below).
                  const Function *CFc =
                      getFuncDef(const_cast<Function *>(CF));
                  const bool safeNoop = calleeSafe(CFc) || okEmpty.count(CFc);
                  SmallVector<PAtom, 6> cas;
                  int st = safeNoop ? 1 : calleeAtoms(CFc, cas);
                  // The atom generator's permRefused is NOT permanence
                  // here: the solved pass may still summarize that
                  // callee in a later round. Permanent-unavailable =
                  // declaration or solved-pass sPerm only.
                  if (st == -1 && !CFc->isDeclaration() && !sPerm.count(CFc))
                    st = 0;
                  if (st != 1) {
                    bool sens = false;
                    for (const Value *Arg : CB->args())
                      if (anySensitive(evalV(Arg))) { sens = true; break; }
                    if (sens) {
                      if (st == 0) escRetry = true;
                      fail = ("escape " + CFc->getName()).str();
                      break;
                    }
                    clobberLocals(CB);
                    if (CB->getType()->isPointerTy())
                      setEnv(&I, {LV{6, 0, 0, nullptr}});
                    continue;
                  }
                  // summarized callee: apply its atoms on our LVs
                  bool cok = true;
                  LVSet retLVs;
                  bool anyRet = false;
                  auto resolveRef = [&](int argi,
                                        const GlobalValue *g2) -> LVSet {
                    if (g2) return {LV{3, 0, 0, g2}};
                    if (argi < 0 || (unsigned)argi >= CB->arg_size())
                      return {LV{6, 0, 0, nullptr}};
                    return evalV(CB->getArgOperand(argi));
                  };
                  auto loadOf = [&](const LV &v, int64_t o2) -> LVSet {
                    if (v.k == 0) {
                      if (v.off < 0) return {LV{1, v.a, -1, nullptr}};
                      return {LV{1, v.a, o2 < 0 ? -1 : v.off + o2,
                                 nullptr}};
                    }
                    if (v.k == 3) {
                      if (v.off < 0) return {LV{4, 0, -1, v.g}};
                      return {LV{4, 0, o2 < 0 ? -1 : v.off + o2, v.g}};
                    }
                    if (v.k == 1 || v.k == 8)
                      return {LV{9, v.g ? -1 : v.a, v.off, v.g}};
                    if (v.k == 5) {
                      // wildcard base or wildcard atom offset: any cell
                      if (v.off < 0 || o2 < 0)
                        return {LV{localSensitive(v.a, 0) ? (uint8_t)7
                                                          : (uint8_t)6,
                                   0, 0, nullptr}};
                      LVSet r2;
                      readCell(r2, LV{5, v.a, v.off + o2, nullptr});
                      return r2;
                    }
                    if (v.k == 2) return {};
                    return {LV{v.k == 1 || v.k == 7 || (v.k == 8 && !v.g)
                                   ? (uint8_t)7
                                   : (uint8_t)6,
                               0, 0, nullptr}};
                  };
                  for (const PAtom &A : cas) {
                    if (!cok) break;
                    if (A.kind == 0 || A.kind == 1) {
                      LVSet Cs = resolveRef(A.a1, A.g1);
                      LVSet Vs0 = resolveRef(A.a2, A.g2);
                      for (LV t : Cs) {
                        if (t.k == 2) continue;
                        t.off = (t.off < 0 || A.o1 < 0) ? -1 : t.off + A.o1;
                        auto ck = cellKey(t);
                        LVSet vals;
                        if (A.kind == 0) {
                          for (LV v : Vs0) {
                            if (v.k == 0 || v.k == 3 || v.k == 5)
                              v.off = (v.off < 0 || A.o2 < 0)
                                          ? -1
                                          : v.off + A.o2;
                            else if (A.o2 && v.k != 2 && v.k != 6 &&
                                     v.k != 7)
                              v.off = -1;
                            vals.push_back(v);
                          }
                        } else {
                          for (const LV &v : Vs0) {
                            LVSet lr = loadOf(v, A.o2);
                            for (const LV &x : lr) vals.push_back(x);
                          }
                        }
                        if (!ck) {
                          bool sens = lvsSensitive(vals);
                          for (const LV &v : vals)
                            if (v.k == 5 && localSensitive(v.a, 0))
                              sens = true;
                          if (sens) { cok = false; break; }
                          continue;
                        }
                        changed |= mergeInto(cells[*ck], vals);
                      }
                    } else if (A.kind == 7 || A.kind == 8) { // ST2/MV2
                      LVSet Cs = resolveRef(A.a1, A.g1);
                      LVSet Vs0 = resolveRef(A.a2, A.g2);
                      auto comb2 = [&](int64_t a3, int64_t b3) -> int64_t {
                        return (a3 < 0 || b3 < 0) ? -1 : a3 + b3;
                      };
                      for (const LV &t0 : Cs) {
                        if (t0.k == 2) continue;
                        // target = level-2 cell of *(t0-cell@o1)
                        LV base{0, 0, 0, nullptr};
                        if (t0.k == 0)
                          base = LV{1, t0.a, comb2(t0.off, A.o1), nullptr};
                        else if (t0.k == 3)
                          base = LV{1, -1, comb2(t0.off, A.o1), t0.g};
                        else { cok = false; break; }
                        auto ck = cellKey(base);
                        LVSet vals;
                        for (const LV &v : Vs0) {
                          if (v.k == 2) continue;
                          if (A.kind == 7) { // ST2: value = address
                            LV w = v;
                            if (w.k == 0 || w.k == 3 || w.k == 5)
                              w.off = comb2(w.off, A.o2);
                            vals.push_back(w);
                          } else { // MV2: value = *src@o2
                            for (const LV &x : loadOf(v, A.o2))
                              vals.push_back(x);
                          }
                        }
                        if (!ck) {
                          if (lvsSensitive(vals)) { cok = false; break; }
                          continue;
                        }
                        changed |= mergeInto(cells[*ck], vals);
                      }
                    } else if (A.kind == 9) { // LD2 ret
                      anyRet = true;
                      for (const LV &v : resolveRef(A.a2, A.g2)) {
                        auto comb9 = [&](int64_t a3, int64_t b3) -> int64_t {
                          return (a3 < 0 || b3 < 0) ? -1 : a3 + b3;
                        };
                        if (v.k == 0)
                          retLVs.push_back({9, v.a, comb9(v.off, A.o2),
                                            nullptr});
                        else if (v.k == 3)
                          retLVs.push_back({9, -1, comb9(v.off, A.o2), v.g});
                        else if (v.k == 2)
                          continue;
                        else
                          retLVs.push_back({7, 0, 0, nullptr});
                      }
                    } else if (A.kind == 6) { // MVX: k8 value into cell
                      LVSet Cs = resolveRef(A.a1, A.g1);
                      LVSet Vs0 = resolveRef(A.a2, A.g2);
                      auto comb6 = [&](int64_t a3, int64_t b3) -> int64_t {
                        return (a3 < 0 || b3 < 0) ? -1 : a3 + b3;
                      };
                      for (LV t : Cs) {
                        if (t.k == 2) continue;
                        t.off = comb6(t.off, A.o1);
                        auto ck = cellKey(t);
                        LVSet vals;
                        for (const LV &v : Vs0) {
                          if (v.k == 0)
                            vals.push_back({8, v.a, comb6(v.off, A.o2),
                                            nullptr});
                          else if (v.k == 3)
                            vals.push_back({8, -1, comb6(v.off, A.o2), v.g});
                          else if (v.k == 2)
                            continue;
                          else
                            vals.push_back({7, 0, 0, nullptr});
                        }
                        if (!ck) {
                          if (lvsSensitive(vals)) { cok = false; break; }
                          continue;
                        }
                        changed |= mergeInto(cells[*ck], vals);
                      }
                    } else if (A.kind == 4) {
                      cok = false; // CPY compose: Stage A refusal
                    } else if (A.kind == 5) { // LDX: interior of loaded
                      anyRet = true;
                      for (const LV &v : resolveRef(A.a2, A.g2)) {
                        auto comb = [&](int64_t a3, int64_t b3) -> int64_t {
                          return (a3 < 0 || b3 < 0) ? -1 : a3 + b3;
                        };
                        if (v.k == 0)
                          retLVs.push_back({8, v.a, comb(v.off, A.o2),
                                            nullptr});
                        else if (v.k == 3)
                          retLVs.push_back({8, -1, comb(v.off, A.o2), v.g});
                        else if (v.k == 2)
                          continue;
                        else
                          retLVs.push_back({7, 0, 0, nullptr});
                      }
                    } else if (A.kind == 2 || A.kind == 3) {
                      anyRet = true;
                      for (const LV &v : resolveRef(A.a2, A.g2)) {
                        if (A.kind == 3) {
                          LV w = v;
                          if (w.k == 0 || w.k == 3 || w.k == 5)
                            w.off = (w.off < 0 || A.o2 < 0)
                                        ? -1
                                        : w.off + A.o2;
                          retLVs.push_back(w);
                        } else {
                          for (const LV &x : loadOf(v, A.o2))
                            retLVs.push_back(x);
                        }
                      }
                    }
                  }
                  if (!cok) { fail = "compose"; break; }
                  if (CB->getType()->isPointerTy()) {
                    LVSet dd;
                    if (anyRet) mergeInto(dd, retLVs);
                    else dd.push_back({6, 0, 0, nullptr});
                    setEnv(&I, dd);
                  }
                }
              }
              if (!fail.empty()) break;
            }
          }
          if (!fail.empty()) {
            retryable = escRetry && StringRef(fail).starts_with("escape");
            why = fail;
            return false;
          }
          // ---- extraction ----
          std::set<std::string> atomStrs;
          SmallVector<PAtom, 12> atoms;
          auto refStr = [](int a2, const GlobalValue *g2, int64_t off,
                           bool deref) -> std::string {
            std::string r = deref ? "*" : "";
            if (g2)
              r += "@" + (g2->hasName() ? g2->getName().str()
                                        : std::string("<g>"));
            else
              r += "arg" + std::to_string(a2);
            if (off > 0) r += "@" + std::to_string(off);
            else if (off < 0) r += "@X";
            return r;
          };
          std::string exWhy;
          auto extractCells = [&]() -> bool {
            for (auto &kv : cells) {
              auto [kind, idx2, gv, off] = kv.first;
              if (kind == 5) continue; // locals policed via escapes
              if ((kind == 3 || (kind == 9 && gv)) &&
                  !CFLAtomsGlobalStores) {
                bool starved = lvsSensitive(kv.second);
                for (const LV &v : kv.second)
                  if (v.k == 5 && localSensitive(v.a, 0)) starved = true;
                if (starved) { exWhy = "global-store-quarantine"; return false; }
                continue; // non-starved: body covers global cells
              }
              if (kind == 9) {
                // level-2 cells: **base@off — ST2/MV2 atoms; global-
                // level-2 with non-starved content is body-covered
                for (const LV &v : kv.second) {
                  if (v.k == 2) continue;
                  const bool gbase = gv != nullptr;
                  if (gbase && (v.k == 3 || v.k == 4 || v.k == 6)) continue;
                  if (v.k == 6) { exWhy = "ext-into-formal"; return false; }
                  PAtom A{};
                  A.o1 = off;
                  if (!gbase) A.a1 = idx2, A.g1 = nullptr;
                  else A.a1 = -1, A.g1 = gv;
                  A.kind = v.k == 0 || v.k == 3 ? 7 : 8; // ST2 : MV2
                  if (v.k == 0 || v.k == 1) {
                    A.a2 = v.a; A.o2 = v.off;
                  } else if (v.k == 3 || v.k == 4) {
                    A.a2 = -1; A.g2 = v.g; A.o2 = v.off;
                  } else if (v.k == 8) {
                    A.kind = 8; // treat interior-of-loaded as its cell
                    if (v.g) { A.a2 = -1; A.g2 = v.g; }
                    else A.a2 = v.a;
                    A.o2 = v.off;
                  } else if (v.k == 5) {
                    if (localSensitive(v.a, 0)) { exWhy = "local-escape"; return false; }
                    continue;
                  } else {
                    exWhy = "deep-val"; return false;
                  }
                  std::string t2 = "**" + refStr(A.a1, A.g1, off, false)
                                        .substr(0);
                  std::string a3 =
                      (A.kind == 7 ? std::string("ST2(") : std::string("MV2(")) +
                      t2 + "<-" + refStr(A.a2, A.g2, A.o2, A.kind == 8) + ")";
                  if (atomStrs.insert(a3).second) atoms.push_back(A);
                }
                continue;
              }
              // off < 0: wildcard cell — @X atoms below (fx loop at
              // apply, same as the body's var-GEP fallback)
              for (const LV &v : kv.second) {
                if (v.k == 2) continue;
                // GLOBAL-based cells: body-walked stores land in the
                // real shared global cell — external/global-derived
                // content is covered. FORMAL-based cells are the
                // CALLER's memory: under adoption the body's store
                // hits the EMPTY formal's deref cell, so EVERY
                // non-null content must be atom-relayed or refused.
                if (kind == 3 && (v.k == 3 || v.k == 4 || v.k == 6))
                  continue;
                if (v.k == 6) { exWhy = "ext-into-formal"; return false; }
                PAtom A{};
                A.o1 = off;
                if (kind == 0) A.a1 = idx2, A.g1 = nullptr;
                else A.a1 = -1, A.g1 = gv;
                std::string tstr = refStr(A.a1, A.g1, off, true);
                if (v.k == 0) {
                  A.kind = 0; A.a2 = v.a; A.o2 = v.off;
                } else if (v.k == 1) {
                  A.kind = 1; A.a2 = v.a; A.o2 = v.off;
                } else if (v.k == 3) {
                  A.kind = 0; A.a2 = -1; A.g2 = v.g; A.o2 = v.off;
                } else if (v.k == 4) {
                  A.kind = 1; A.a2 = -1; A.g2 = v.g; A.o2 = v.off;
                } else if (v.k == 5) {
                  if (localSensitive(v.a, 0)) { exWhy = "local-escape"; return false; }
                  continue; // dead local object: no interface content
                } else if (v.k == 8) {
                  A.kind = 6; // MVX: interior-of-loaded into a cell
                  if (v.g) { A.a2 = -1; A.g2 = v.g; }
                  else A.a2 = v.a;
                  A.o2 = v.off;
                } else if (v.k == 9) {
                  exWhy = "deep-val"; return false;
                } else {
                  exWhy = v.k == 7 ? "formal-deep" : "wildcard-val";
                  return false;
                }
                std::string a3 =
                    (A.kind == 0   ? std::string("ST(")
                     : A.kind == 6 ? std::string("MVX(")
                                   : std::string("MV(")) +
                    tstr + "<-" + refStr(A.a2, A.g2, A.o2, A.kind != 0) +
                    ")";
                if (atomStrs.insert(a3).second) atoms.push_back(A);
              }
            }
            return true;
          };
          if (!extractCells()) { why = exWhy; return false; }
          for (const auto &BB : F) {
            const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator());
            if (!RI || !RI->getReturnValue()) continue;
            const Value *RV = RI->getReturnValue();
            if (!RV->getType()->isPointerTy() &&
                !(isPtrWidthInt(RV->getType(), *curDL)))
              continue;
            for (const LV &v : evalV(RV)) {
              if (v.k == 2) continue;
              if (v.k == 6) { why = "ret-ext"; return false; }
              PAtom A{};
              if (v.k == 0) {
                A.kind = 3; A.a2 = v.a; A.o2 = v.off; // off -1 = @X
              } else if (v.k == 1) {
                A.kind = 2; A.a2 = v.a; A.o2 = v.off;
              } else if (v.k == 3) {
                A.kind = 3; A.a2 = -1; A.g2 = v.g; A.o2 = v.off;
              } else if (v.k == 4) {
                A.kind = 2; A.a2 = -1; A.g2 = v.g; A.o2 = v.off;
              } else if (v.k == 8) {
                A.kind = 5;
                if (v.g) { A.a2 = -1; A.g2 = v.g; }
                else A.a2 = v.a;
                A.o2 = v.off;
              } else if (v.k == 9) {
                A.kind = 9;
                if (v.g) { A.a2 = -1; A.g2 = v.g; }
                else A.a2 = v.a;
                A.o2 = v.off;
              } else {
                why = v.k == 5 ? "ret-local" : "ret-deep";
                return false;
              }
              std::string a3 =
                  std::string(A.kind == 3   ? "ALIAS(ret<-"
                              : A.kind == 5 ? "LDX(ret<-"
                              : A.kind == 9 ? "LD2(ret<-*"
                                            : "LD(ret<-") +
                  refStr(A.a2, A.g2, A.o2, A.kind != 3) + ")";
              if (atomStrs.insert(a3).second) atoms.push_back(A);
            }
          }
          if (atoms.size() > 16) { why = "too-many-atoms"; return false; }
          if (atoms.empty()) {
            okEmpty.insert(&F);
            nEmpty++;
            CG_LOG("SolvedProp: OK-EMPTY " << F.getName() << "\n");
          } else {
            SmallVector<PAtom, 6> pv(atoms.begin(), atoms.end());
            props[&F] = pv;
            nSolved++;
            std::string line;
            for (auto &a3 : atomStrs) line += " " + a3;
            CG_LOG("SolvedProp: OK " << F.getName() << line << "\n");
          }
          return true;
        };
        bool schanged = true;
        size_t sround = 0;
        while (schanged && sround++ < 20) {
          schanged = false;
          for (auto &[mod, mname] : Ctx->Modules) {
            for (const Function &F : *mod) {
              if (F.isDeclaration()) continue;
              const Function *canon = getFuncDef(const_cast<Function *>(&F));
              if (canon != &F || ok.count(canon) || okEmpty.count(canon) ||
                  props.count(canon) || sPerm.count(canon))
                continue;
              if (Ctx->FuncSummaries.count(canon)) continue;
              bool retryable = false;
              std::string why;
              if (trySolve(F, retryable, why)) {
                schanged = true;
              } else if (!retryable) {
                sPerm.insert(canon);
                if (sround == 1)
                  sRefuse[why.substr(0, why.find(' '))]++;
                CG_LOG("SolvedProp: REFUSED " << F.getName() << " ["
                       << why << (sround == 1 ? "" : " late") << "]\n");
              } else if (sround == 1) {
                sRefuse["escape-pending"]++;
                CG_LOG("SolvedProp: PENDING " << F.getName() << " ["
                       << why << "]\n");
              }
            }
          }
        }
        // Late passes to TRUE quiescence (the main loop can converge
        // prematurely across module boundaries), then the stuck report
        // with the blockers that ACTUALLY held.
        for (bool late = true; late;) {
          late = false;
          for (auto &[mod, mname] : Ctx->Modules) {
            for (const Function &F : *mod) {
              if (F.isDeclaration()) continue;
              const Function *canon = getFuncDef(const_cast<Function *>(&F));
              if (canon != &F || ok.count(canon) || okEmpty.count(canon) ||
                  props.count(canon) || sPerm.count(canon))
                continue;
              if (Ctx->FuncSummaries.count(canon)) continue;
              bool retryable = false;
              std::string why;
              if (trySolve(F, retryable, why)) late = true;
            }
          }
        }
        for (auto &[mod, mname] : Ctx->Modules) {
          for (const Function &F : *mod) {
            if (F.isDeclaration()) continue;
            const Function *canon = getFuncDef(const_cast<Function *>(&F));
            if (canon != &F || ok.count(canon) || okEmpty.count(canon) ||
                props.count(canon) || sPerm.count(canon))
              continue;
            if (Ctx->FuncSummaries.count(canon)) continue;
            bool retryable = false;
            std::string why;
            if (!trySolve(F, retryable, why))
              CG_LOG("SolvedProp: STUCK " << F.getName() << " [" << why
                     << "]\n");
          }
        }
        std::string sh;
        for (auto &kv : sRefuse)
          sh += kv.first + "=" + std::to_string(kv.second) + " ";
        CG_LOG("SolvedProp: " << nSolved << " atom + " << nEmpty
               << " empty summaries (" << sround
               << " rounds); first-round refusals: " << sh << "\n");
      }
  if (CFLAdoptProposedSummaries) {
    if (FuncSummaryFile.empty()) {
      errs() << "--cfl-adopt-proposed-summaries requires --func-summaries "
                "(authoritative mode owns the body-skip lists)\n";
      assert(false && "adopt-proposed without func-summaries");
    }
    size_t nNoop = 0, nAtom = 0, nEmptyAd = 0;
    auto adoptSkip = [&](const Function *F) -> bool {
      if (CFLAdoptSkip.empty()) return false;
      StringRef spec(CFLAdoptSkip);
      while (!spec.empty()) {
        auto [head, rest] = spec.split(',');
        if (!head.empty() && F->getName() == head) {
          CG_LOG("SummaryAdopt: SKIPPED " << F->getName()
                 << " (--cfl-adopt-skip)\n");
          return true;
        }
        spec = rest;
      }
      return false;
    };
    // Solved-class zero-atom fns: EMPTY-ATOM summaries — callsite
    // wiring cut, body KEPT (never g_noopBodies: their proofs allow
    // formal-independent icalls/asm which body-skip would erase).
    size_t nLabels = 0, nUncovered = 0;
    for (const Function *F : okEmpty) {
      if (adoptSkip(F)) continue;
      GlobalContext::FuncSummary S;
      if (CFLCells) {
        std::string why;
        if (!labelsCover(*F, why)) {
          CG_LOG("SummaryAdopt: KEPT " << F->getName() << " [evidence beyond labels: " << why << "]\n");
          nUncovered++;
          continue;
        }
        S.labels = bodyLabels(*F, *curDL);
        nLabels += S.labels.size();
      }
      Ctx->OwnedSummaries.push_back(std::move(S));
      Ctx->FuncSummaries[F] = &Ctx->OwnedSummaries.back();
      nEmptyAd++;
    }
    for (const Function *F : ok) {
      if (adoptSkip(F)) continue;
      GlobalContext::FuncSummary S;
      S.noop = true;
      // Under --cfl-cells a skipped body still names the objects it
      // touches: its typed accesses label them (djpeg O3: without them
      // gray_rgb565_convert's row buffers stayed unlabeled i8[], 1,026
      // cells unified by name instead of 74). Label atoms carry them;
      // a body with evidence they cannot carry stays walked.
      if (CFLCells) {
        std::string why;
        if (!labelsCover(*F, why)) {
          CG_LOG("SummaryAdopt: KEPT " << F->getName() << " [evidence beyond labels: " << why << "]\n");
          nUncovered++;
          continue;
        }
        S.labels = bodyLabels(*F, *curDL);
        nLabels += S.labels.size();
      }
      Ctx->OwnedSummaries.push_back(std::move(S));
      Ctx->FuncSummaries[F] = &Ctx->OwnedSummaries.back();
      g_noopBodies.insert(F);
      nNoop++;
    }
    size_t nInexact = 0;
    for (auto &[F, pas] : props) {
      if (adoptSkip(F)) continue;
      // Under --cfl-cells an atom with a wildcard offset (@X), MVX/LDX,
      // or a two-level atom the prover proposes (no exact inner offset)
      // applies as a field-any loop: every cell of the object, where the
      // walked body copies position by position. Refused: the body
      // stays walked (plan 3.37 item 2).
      if (CFLCells) {
        // An interior value pointer (ST/ALIAS of argN@K, K > 0) loses
        // the provenance the walked body gives it: &p->zSpace (a typed
        // step into a byte array, plan 3.43) becomes a byte offset, and
        // a walk from it leaves the array. Refused as well.
        const PAtom *bad = nullptr;
        for (const PAtom &A : pas)
          if (A.o1 < 0 || A.o2 < 0 || A.kind == 5 || A.kind == 6 ||
              A.kind == 7 || A.kind == 8 || A.kind == 9 ||
              ((A.kind == 0 || A.kind == 3) && A.o2 > 0)) {
            bad = &A;
            break;
          }
        if (bad) {
          CG_LOG("SummaryAdopt: REFUSED " << F->getName()
                 << " [inexact under cells: atom kind " << bad->kind
                 << (bad->o1 < 0 || bad->o2 < 0 ? ", wildcard offset"
                     : bad->o2 > 0 ? ", interior value pointer" : "")
                 << "]\n");
          nInexact++;
          continue;
        }
      }
      GlobalContext::FuncSummary S;
      if (CFLCells) {
        std::string why;
        if (!labelsCover(*F, why)) {
          CG_LOG("SummaryAdopt: KEPT " << F->getName() << " [evidence beyond labels: " << why << "]\n");
          nUncovered++;
          continue;
        }
        S.labels = bodyLabels(*F, *curDL);
        nLabels += S.labels.size();
      }
      for (const PAtom &A : pas) {
        GlobalContext::SummaryAtom SA{};
        switch (A.kind) {
        case 0: SA.kind = GlobalContext::SummaryAtom::Store; SA.dst = A.a1;
                SA.src = A.a2; SA.dstByteOff = (int)A.o1;
                SA.srcByteOff = (int)A.o2; SA.gdst = A.g1; SA.gsrc2 = A.g2;
                break;
        case 1: SA.kind = GlobalContext::SummaryAtom::Move; SA.dst = A.a1;
                SA.src = A.a2; SA.dstByteOff = (int)A.o1;
                SA.srcByteOff = (int)A.o2; SA.gdst = A.g1; SA.gsrc2 = A.g2;
                break;
        case 2: SA.kind = GlobalContext::SummaryAtom::Load; SA.dst = -1;
                SA.src = A.a2; SA.srcByteOff = (int)A.o2; SA.gsrc2 = A.g2;
                break;
        case 5: SA.kind = GlobalContext::SummaryAtom::LoadX; SA.dst = -1;
                SA.src = A.a2; SA.srcByteOff = (int)A.o2; SA.gsrc2 = A.g2;
                break;
        case 6: SA.kind = GlobalContext::SummaryAtom::MoveX; SA.dst = A.a1;
                SA.src = A.a2; SA.dstByteOff = (int)A.o1;
                SA.srcByteOff = (int)A.o2; SA.gdst = A.g1; SA.gsrc2 = A.g2;
                break;
        case 7: SA.kind = GlobalContext::SummaryAtom::Store2; SA.dst = A.a1;
                SA.src = A.a2; SA.dstByteOff = (int)A.o1;
                SA.srcByteOff = (int)A.o2; SA.gdst = A.g1; SA.gsrc2 = A.g2;
                break;
        case 8: SA.kind = GlobalContext::SummaryAtom::Move2; SA.dst = A.a1;
                SA.src = A.a2; SA.dstByteOff = (int)A.o1;
                SA.srcByteOff = (int)A.o2; SA.gdst = A.g1; SA.gsrc2 = A.g2;
                break;
        case 9: SA.kind = GlobalContext::SummaryAtom::Load2; SA.dst = -1;
                SA.src = A.a2; SA.srcByteOff = (int)A.o2; SA.gsrc2 = A.g2;
                break;
        case 3: SA.kind = GlobalContext::SummaryAtom::Alias; SA.dst = -1;
                SA.src = A.a2; SA.srcByteOff = (int)A.o2; SA.gsrc2 = A.g2;
                break;
        case 4: SA.kind = GlobalContext::SummaryAtom::Cpy; SA.dst = A.a1;
                SA.src = A.a2; break;
        default: assert(false && "unknown proposed atom kind");
        }
        S.atoms.push_back(SA);
      }
      Ctx->OwnedSummaries.push_back(std::move(S));
      Ctx->FuncSummaries[F] = &Ctx->OwnedSummaries.back();
      adoptedAtomBodies.insert(F);
      nAtom++;
    }
    CG_LOG("SummaryAdopt: " << nNoop << " noop + " << nAtom
           << " atom + " << nEmptyAd
           << " empty summaries adopted (per-corpus proofs); " << nInexact
           << " refused as inexact under cells; " << nLabels
           << " label atoms (typed accesses of replaced bodies), " << nUncovered
           << " bodies kept (naming evidence beyond labels)\n");
  }

  // --cfl-propose-chain-summaries (docs/kernel-id-keys.md §7): derive
  // driver-core CHAINREG/CHAINCALL channels from the key-constant-frame
  // rule. REG wrapper = stores a bus_type global's address into a
  // formal-rooted field AND passes that same formal (or an interior GEP
  // of it) to driver_register/bus_add_driver. CALL wrapper = same
  // constant store + device_add/device_register on the formal. Slot
  // offsets = union of fn-bearing byte offsets across all conforming
  // callsites' static-initializer blocks (layout-correct per corpus by
  // construction; non-conforming callsites fall back pooled inside the
  // ChainReg atom application — sound). Bindings are conservative: REG
  // f9 (no self-bind; a wrong bind would be unsound), CALL f0
  // (additive over-approximation; dispatch keeps pooled wiring).
  if (CFLProposeChainSummaries) {
    struct ChainWrap {
      const GlobalValue *bus = nullptr;
      int blkArg = -1;          // formal carrying the driver block
      std::set<int64_t> offs;   // fn-bearing byte offsets (union)
      unsigned sites = 0, dynSites = 0;
      std::string refuse;       // non-empty = census-only
    };
    struct CallWrap {
      const GlobalValue *bus = nullptr;
      int devArg = -1;          // formal carrying the device
      std::string refuse;
    };
    std::map<const Function *, ChainWrap> regWraps;
    std::map<const Function *, CallWrap> callWraps;
    boost::unordered_flat_map<std::string, const Function *> regByName;

    auto busGlobal = [&](const Value *V) -> const GlobalValue * {
      const auto *G = dyn_cast<GlobalValue>(V->stripPointerCasts());
      if (!G) return nullptr;
      const auto *ST = dyn_cast<StructType>(G->getValueType());
      if (!ST || !ST->hasName()) return nullptr;
      StringRef n = ST->getStructName();
      if (n != "struct.bus_type" && !n.starts_with("struct.bus_type."))
        return nullptr;
      return G;
    };
    auto rootFormal = [](const Value *V, const Function &F) -> int {
      V = V->stripPointerCasts();
      while (const auto *G = dyn_cast<GEPOperator>(V))
        V = G->getPointerOperand()->stripPointerCasts();
      if (const auto *A2 = dyn_cast<Argument>(V))
        if (A2->getParent() == &F) return (int)A2->getArgNo();
      return -1;
    };

    // Pass 1: qualify wrappers.
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
        const GlobalValue *bus = nullptr;
        int busArg = -1;
        bool busConflict = false, fnStore = false;
        int regArg = -1, devArg = -1;
        for (inst_iterator ii = inst_begin(F), ie = inst_end(F); ii != ie;
             ++ii) {
          if (const auto *SI = dyn_cast<StoreInst>(&*ii)) {
            if (const GlobalValue *B = busGlobal(SI->getValueOperand())) {
              int a = rootFormal(SI->getPointerOperand(), F);
              if (a >= 0) {
                if (bus && (bus != B || busArg != a)) busConflict = true;
                bus = B; busArg = a;
              }
            } else if (isa<Function>(
                           SI->getValueOperand()->stripPointerCasts())) {
              if (rootFormal(SI->getPointerOperand(), F) >= 0)
                fnStore = true; // shim installer (usb-style): refuse
            }
          } else if (const auto *CB = dyn_cast<CallBase>(&*ii)) {
            const Function *CF = CB->getCalledFunction();
            if (!CF || CB->arg_size() < 1) continue;
            StringRef cn = CF->getName();
            if (cn == "driver_register" || cn == "bus_add_driver")
              regArg = rootFormal(CB->getArgOperand(0), F);
            else if (cn == "device_add" || cn == "device_register")
              devArg = rootFormal(CB->getArgOperand(0), F);
          }
        }
        if (!bus || busArg < 0) continue;
        std::string refuse;
        if (busConflict) refuse = "bus-conflict";
        else if (bus->hasInternalLinkage()) refuse = "internal-key";
        else if (fnStore) refuse = "fn-shim-store";
        if (regArg == busArg) {
          ChainWrap W; W.bus = bus; W.blkArg = busArg; W.refuse = refuse;
          regWraps[&F] = W;
          regByName[F.getName().str()] = &F;
        }
        if (devArg == busArg) {
          CallWrap W; W.bus = bus; W.devArg = busArg; W.refuse = refuse;
          callWraps[&F] = W;
        }
      }
    }

    // Pass 2: collect fn-bearing offsets from conforming callsites
    // (walkInitFnOffsets shared with the file-entry validator).
    for (auto &mp : Ctx->Modules) {
      for (Function &F : *mp.first) {
        if (F.isDeclaration()) continue;
        for (inst_iterator ii = inst_begin(F), ie = inst_end(F); ii != ie;
             ++ii) {
          const auto *CB = dyn_cast<CallBase>(&*ii);
          if (!CB) continue;
          const Function *CF = CB->getCalledFunction();
          if (!CF) continue;
          auto nit = regByName.find(CF->getName().str());
          if (nit == regByName.end()) continue;
          ChainWrap &W = regWraps[nit->second];
          if ((unsigned)W.blkArg >= CB->arg_size()) continue;
          W.sites++;
          const auto *GV = dyn_cast<GlobalVariable>(
              CB->getArgOperand(W.blkArg)->stripPointerCasts());
          if (!GV || !GV->hasInitializer()) { W.dynSites++; continue; }
          walkInitFnOffsets(GV->getInitializer(), 0,
                            GV->getParent()->getDataLayout(), W.offs);
        }
      }
    }

    // Pass 3: report + adopt. File entries are never overridden — they
    // are the correctness reference (MATCH/MISMATCH per wrapper).
    size_t nReg = 0, nCall = 0, nMatch = 0, nRefused = 0;
    auto fileHasChain = [&](const Function *F) -> const
        GlobalContext::FuncSummary * {
      auto it = Ctx->FuncSummaries.find(F);
      return it == Ctx->FuncSummaries.end() ? nullptr : it->second;
    };
    for (auto &[F, W] : regWraps) {
      std::string line;
      for (int64_t o : W.offs)
        line += " CHAINREG(@" + W.bus->getName().str() + ",*arg" +
                std::to_string(W.blkArg) + "+" + std::to_string(o) + ",f9)";
      if (const auto *S = fileHasChain(F)) {
        bool anyChain = false, sameKey = true;
        std::set<int64_t> fileOffs;
        for (const auto &A : S->atoms)
          if (A.kind == GlobalContext::SummaryAtom::ChainReg) {
            anyChain = true;
            fileOffs.insert(A.off);
            if (A.gsym != W.bus->getName().str()) sameKey = false;
          }
        if (anyChain) {
          bool cover = true; // derived must cover every file offset
          for (int64_t o : fileOffs) cover &= W.offs.count(o) > 0;
          CG_LOG("ChainProp: "
                 << (W.offs.empty()
                         ? "MATCH-KEY-ONLY " // wrapper+key derived; no
                                             // conforming sites in corpus
                         : sameKey && cover ? "MATCH-FILE "
                                            : "MISMATCH-FILE ")
                 << F->getName() << " derived" << line << " (file has "
                 << fileOffs.size() << " offs)\n");
          nMatch++;
          // SUPPLEMENT policy REVERTED (2026-08-25, 5.18 gate
          // +32,575): a ChainReg atom whose offset is NULL in a
          // callsite's initializer trips the runtime-installed-
          // callback soundness net (needPooled) — supplemental
          // suspend/resume/shutdown offsets are null in MOST drivers,
          // so most pci/platform registration callsites fell back
          // pooled, UN-severing the driver structs (their err_handler
          // / pm-ops contents re-welded into the giant: 16 fns x
          // 2,294 pool callers). Stale file offsets at other vintages
          // are HARMLESS (additive channel; ahci caller set identical
          // pin-vs-stale at 6.18). Proper v1 fix: per-callsite
          // initializer walk (register every fn-bearing offset of
          // THIS block; no global offset union, no null-slot misses).
          continue; // file atoms authoritative, unsupplemented
        }
      }
      if (!W.refuse.empty()) {
        CG_LOG("ChainProp: REFUSED " << F->getName() << " [" << W.refuse
               << "]" << line << "\n");
        nRefused++;
        continue;
      }
      if (W.offs.empty()) {
        CG_LOG("ChainProp: NO-SITES " << F->getName() << " (sites="
               << W.sites << " dyn=" << W.dynSites << ")\n");
        continue;
      }
      CG_LOG("ChainProp: REG " << F->getName() << line << " (sites="
             << W.sites << " dyn=" << W.dynSites << ")\n");
      nReg++;
      if (CFLAdoptProposedSummaries && !Ctx->FuncSummaries.count(F)) {
        GlobalContext::FuncSummary S;
        for (int64_t o : W.offs) {
          GlobalContext::SummaryAtom SA{};
          SA.kind = GlobalContext::SummaryAtom::ChainReg;
          SA.gsrc = canonChainKey(W.bus); // pointer key, pre-canonicalized
          SA.src = W.blkArg;
          SA.off = (int)o;
          SA.fk = 9; // conservative: no block self-bind
          S.atoms.push_back(SA);
        }
        Ctx->OwnedSummaries.push_back(std::move(S));
        Ctx->FuncSummaries[F] = &Ctx->OwnedSummaries.back();
      }
    }
    for (auto &[F, W] : callWraps) {
      std::string line = " CHAINCALL(@" + W.bus->getName().str() +
                         ":f0<-arg" + std::to_string(W.devArg) + ")";
      if (const auto *S = fileHasChain(F)) {
        bool anyChain = false;
        for (const auto &A : S->atoms)
          if (A.kind == GlobalContext::SummaryAtom::ChainCall)
            anyChain = true;
        if (anyChain) {
          CG_LOG("ChainProp: MATCH-FILE " << F->getName() << " derived"
                 << line << "\n");
          nMatch++;
          continue;
        }
      }
      if (!W.refuse.empty()) {
        CG_LOG("ChainProp: REFUSED " << F->getName() << " [" << W.refuse
               << "]" << line << "\n");
        nRefused++;
        continue;
      }
      CG_LOG("ChainProp: CALL " << F->getName() << line << "\n");
      nCall++;
      if (CFLAdoptProposedSummaries && !Ctx->FuncSummaries.count(F)) {
        GlobalContext::FuncSummary S;
        GlobalContext::SummaryAtom SA{};
        SA.kind = GlobalContext::SummaryAtom::ChainCall;
        SA.gsym = W.bus->getName().str();
        SA.src = W.devArg;
        SA.fk = 0; // additive over-approx; dispatch keeps pooled wiring
        S.atoms.push_back(SA);
        Ctx->OwnedSummaries.push_back(std::move(S));
        Ctx->FuncSummaries[F] = &Ctx->OwnedSummaries.back();
      }
    }
    CG_LOG("ChainProp: " << nReg << " REG + " << nCall << " CALL proposed, "
           << nMatch << " file-matched, " << nRefused << " refused"
           << (CFLAdoptProposedSummaries ? " (adopted)" : "") << "\n");
  }
}

// exactly the dynamic residual. Without this, FRESH routes the function
// through the allocator body-skip and dynamic registrations are silently
// severed (caught by the kernel smpboot_thread_fn zero-target diff;
// micro: t_pairs2.c).
bool summaryKeepsBody(GlobalContext *Ctx,
                                   const llvm::Function *F) {
  auto it = Ctx->FuncSummaries.find(F);
  if (it == Ctx->FuncSummaries.end()) return false;
  if (it->second->body) return true; // BODY
  for (const auto &A : it->second->atoms)
    if (A.kind == GlobalContext::SummaryAtom::Invoke) return true;
  return false;
}

// --cfl-cells, plan 3.38: POOL CLOSURE. An allocator family (the functions
// whose summary is FRESH or FREE) keeps its pool in pointer fields (free-
// list heads, slot links). Premise: those fields are allocator-internal:
// the returned block is FRESH and a freed block dead, so their content is
// no program data. Checked, not assumed: a field is pool state only when
// no function outside the family loads or stores it (by struct slot,
// across embedding and -O3 TBAA). Then the family's accesses to it are not
// modeled; otherwise they are, and the outside accessors are reported (a
// real escape, or a family member missing its summary).
void CallGraphPass::checkPoolClosure() {
  poolDrop.clear();
  auto inFamily = [&](const Function *F) {
    auto it = Ctx->FuncSummaries.find(F);
    return it != Ctx->FuncSummaries.end() &&
           (it->second->fresh || it->second->freeArg >= 0 || it->second->pool);
  };
  struct Key { StructType *S; int64_t off; };
  auto keyOf = [&](const Instruction &I, Key &k) {
    const Value *Addr = nullptr;
    if (const auto *L = dyn_cast<LoadInst>(&I)) {
      if (!L->getType()->isPointerTy()) return false;
      Addr = L->getPointerOperand();
    } else if (const auto *SI = dyn_cast<StoreInst>(&I)) {
      if (!SI->getValueOperand()->getType()->isPointerTy()) return false;
      Addr = SI->getPointerOperand();
    } else {
      return false;
    }
    if (isa<AllocaInst>(Addr->stripPointerCasts())) return false;
    return accessSlot(&I, Addr, I.getModule()->getDataLayout(), k.S, k.off);
  };
  auto sameSlot = [&](const Key &a, const Key &b, const DataLayout &DL) {
    if (a.S == b.S) return a.off == b.off;
    const StringRef an = stripStructNameSuffix(a.S->getName()), bn = stripStructNameSuffix(b.S->getName());
    if (an == bn) return a.off == b.off;
    if (a.off >= b.off && embedsAt(a.S, a.off - b.off, bn, DL)) return true;
    return b.off >= a.off && embedsAt(b.S, b.off - a.off, an, DL);
  };
  // The family's pool fields and its accesses to them.
  std::vector<Key> fields;
  std::vector<std::vector<const Instruction *>> famAccess;
  std::vector<std::set<std::string>> famNames, outside;
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M) {
      if (F.isDeclaration() || !inFamily(&F)) continue;
      for (const Instruction &I : instructions(F)) {
        Key k;
        if (!keyOf(I, k)) continue;
        size_t fi = 0;
        for (; fi < fields.size(); fi++)
          if (sameSlot(fields[fi], k, DL)) break;
        if (fi == fields.size()) {
          fields.push_back(k);
          famAccess.emplace_back();
          famNames.emplace_back();
          outside.emplace_back();
        }
        famAccess[fi].push_back(&I);
        famNames[fi].insert(F.getName().str());
      }
    }
  }
  if (fields.empty()) return;
  // Every other function's accesses.
  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M) {
      if (F.isDeclaration() || inFamily(&F)) continue;
      for (const Instruction &I : instructions(F)) {
        Key k;
        if (!keyOf(I, k)) continue;
        for (size_t fi = 0; fi < fields.size(); fi++)
          if (sameSlot(fields[fi], k, DL)) outside[fi].insert(F.getName().str());
      }
    }
  }
  size_t certified = 0, kept = 0;
  for (size_t fi = 0; fi < fields.size(); fi++) {
    const std::string fname = stripStructNameSuffix(fields[fi].S->getName()).str() + "+" +
                              std::to_string(fields[fi].off);
    std::string fam;
    for (const std::string &n : famNames[fi]) fam += " " + n;
    if (outside[fi].empty()) {
      certified++;
      poolDrop.insert(famAccess[fi].begin(), famAccess[fi].end());
      CG_LOG("PoolClosure: CERTIFIED " << fname << " (pool state of" << fam << "; "
             << famAccess[fi].size() << " accesses not modeled)\n");
    } else {
      kept++;
      std::string who;
      size_t n = 0;
      for (const std::string &o : outside[fi])
        if (n++ < 6) who += " " + o;
      CG_LOG("PoolClosure: KEPT " << fname << " (family" << fam << "; also accessed by"
             << who << (outside[fi].size() > 6 ? " ..." : "") << ")\n");
    }
  }
  CG_LOG("PoolClosure: " << certified << " fields certified as pool state, " << kept
         << " kept (accessed outside the allocator family)\n");
}

// Union and tagged-field keys (plans 3.18, 3.51) are names the graph build
// gives a body's accesses; an adopted atom summary replaces the body with
// unkeyed atoms, so the keys would be lost (every keyed read would see the
// summarized writes). Keys are computed after adoption: withdraw the
// adoption of every body with a keyed access, and of every adopted body
// that calls one (its atoms stand for the callee's writes), to a fixpoint.
void CallGraphPass::unadoptKeyedBodies() {
  if (adoptedAtomBodies.empty() || unionKeyNames.empty()) return;
  std::set<const Function *> keyed;
  for (const Function *F : adoptedAtomBodies)
    for (const Instruction &I : instructions(*F))
      if (unionKeyNames.count(&I)) { keyed.insert(F); break; }
  for (bool changed = !keyed.empty(); changed;) {
    changed = false;
    for (const Function *F : adoptedAtomBodies) {
      if (keyed.count(F)) continue;
      for (const Instruction &I : instructions(*F))
        if (const auto *CB = dyn_cast<CallBase>(&I))
          if (const Function *C = CB->getCalledFunction(); C && keyed.count(C)) {
            keyed.insert(F);
            changed = true;
            break;
          }
    }
  }
  for (const Function *F : keyed) {
    Ctx->FuncSummaries.erase(F);
    adoptedAtomBodies.erase(F);
    CG_LOG("SummaryAdopt: WITHDRAWN " << F->getName() << " [keyed accesses in the body or a callee]\n");
  }
  if (!keyed.empty())
    CG_LOG("SummaryAdopt: " << keyed.size() << " adopted bodies withdrawn for keyed accesses\n");
}
