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

// CallGraph.cc: pass skeleton: construction, the per-module driver, the solve hook, finalization.
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

// Helper to check if we should skip creating edges for a value
// --- printf-family vararg sink classification -------------------------
// A variadic callsite whose (constant) format string proves the varargs
// are only read — never captured, dispatched, or forwarded — does not
// need its tail wired into the callee's vararg summary node. On kernel
// code the printf family is the dominant vararg population and its
// summary nodes glue unrelated objects together (kernel/mm subset: the
// printf vararg web accounted for 91% of cell-cluster merges and the
// widest fact classes). Relies on the __printf convention: the format is
// the LAST FIXED parameter. Conservative fallbacks: non-constant format,
// unknown conversion, %n (writes through a pointer), and %pV (captures a
// va_list inside struct va_format) all keep full wiring.
uint64_t printfSinkCallsites = 0, printfSinkArgsSkipped = 0;
uint64_t printfNonConstFmt = 0, printfNonBenignFmt = 0;

// Helper to check if we should skip creating edges for a function call
// NOOP-summarized functions (call transfers nothing, body skipped).
// Populated at summary resolution; when --func-summaries is loaded the
// FILE is authoritative and the hardcoded name lists below are NOT
// consulted (isAllocFn precedent, task #26; migration task #44).
boost::unordered_flat_set<const Function *> g_noopBodies;
bool g_sumAuthoritative = false;

CallGraphPass::CallGraphPass(GlobalContext *Ctx_)
    : IterativeModulePass(Ctx_, "CallGraph"),
      NF(Ctx->nodeFactory),
      Graph(Ctx->constraintGraph),
      iteration(0) {}

Function* CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

size_t g_intArgUnmodeled = 0;
// Global-initializer constant expressions that may carry a pointer but
// have no transfer rule (e.g. sub/add/trunc over ptrtoint: relative
// references); declined, counted, reported -- never dropped silently.
size_t g_initCEDeclined = 0;
// Rebased-pointer rule residual: non-percpu ptrtoint chains whose
// base identity is deliberately NOT aliased (declared residual).
size_t g_rebasedPtrSkipped = 0;

// inline-asm interface-closure ledger (census: 17,804 ptr-capable
// sites / 171 templates; the families modeled here are percpu ptr
// slots, asm atomics on ptr-width ints, raw-ptr register throughs)
size_t g_staticCallWired = 0, g_staticCallNoKey = 0,
              g_staticCallUpdates = 0, g_staticCallDynUpdate = 0,
              g_tracepointProbes = 0, g_staticCallTpIter = 0;

size_t g_asmSlotLoads = 0, g_asmSlotStores = 0,
              g_asmWidthWitnessed = 0, g_asmLaunderDeclined = 0,
              g_asmRegLoads = 0, g_asmRegStores = 0, g_asmRegCopies = 0;

size_t g_intLoadUnmodeled = 0;

// Families whose IN-CORPUS consumers treat entries as code/symbol
  // METADATA, not data-flow pointers: (a) patching machinery
  // (static_call, jump_label, extable fixups, mcount) — modeled as
  // control transforms, static_call = task #14; (b) loadable-module
  // linking (__ksymtab/__kcrctab) — resolve_symbol runs on out-of-
  // corpus modules; wiring would inject EVERY exported symbol into
  // the alias world; (c) pure string/metadata tables. Excluded and
// LEDGERed as explicit boundary assumptions.
bool linkerExcludedFamily(StringRef K) {
    return K.contains("ksymtab") || K.contains("kcrctab") ||
           K.contains("static_call") || K.contains("jump_table") ||
           K.contains("ex_table") || K.contains("bug_table") ||
           K.contains("orc_") || K.contains("mcount") ||
           K.contains("tracepoint_str") || K.contains("bprintk") ||
           K.contains("dyndbg") || K.contains("modver") ||
           K.contains("kprobe_blacklist") || K.contains("notes");
}

// Apply the non-FRESH atoms of a summary at a callsite. FRESH itself is
// carried by the existing AllocFuncs machinery (per-callsite AllocSite +
// opaque heap object). Cell-copy edges are shift-preserving by
// construction (a-edge between deref nodes), which is exactly right for
// aligned whole-buffer dups (kmemdup family); prefix copies
// over-approximate soundly.
size_t g_sumInvokeRet = 0; // INVOKE :ret bindings applied
bool CallGraphPass::doInitialization(Module *M) {
  if (iteration == 0 && M == Ctx->Modules.front().first) {
    if (!FuncSummaryFile.empty() && Ctx->SummarySpecs.empty())
      loadFuncSummaries(Ctx, FuncSummaryFile);
    canonicalNodeMap.clear();
    canonicalClassMembers.clear();
    moduleIndirectCallInsts.clear();
    fieldAliasMap.clear();
    linkerSectionInPlace.clear();
    linkerSectionEncoded.clear();
    linkerSectionUnresolved.clear();
  }

  // Linker-mediated arrays (task #22): module-level asm places PREL32
  // entries (.long fn - .) into linker-gathered sections (initcalls,
  // pci_fixup, tracepoints_ptrs). The referenced functions ARE
  // address-taken — the linker embeds their address — even though no
  // IR user exists, and they are members of the section array consumed
  // via __start_X/__stop_X (wireLinkerSectionArrays).
  std::set<const Function *> asmTaken;
  if (CFLLinkerArrays && !M->getModuleInlineAsm().empty()) {
    cflWalkModuleAsm(
        M->getModuleInlineAsm(), [&](StringRef sec, StringRef sym) {
          if (sym.empty()) return;
          GlobalValue *GVal = M->getNamedValue(sym);
          if (!GVal) {
            char c0 = sym.front();
            if (isalpha((unsigned char)c0) || c0 == '_' || c0 == '$')
              linkerSectionUnresolved[sec.str()]++;
            return; // local labels / literal operands
          }
          if (auto *GA = dyn_cast<GlobalAlias>(GVal))
            GVal = dyn_cast_or_null<GlobalValue>(
                GA->getAliasee()->stripPointerCasts());
          if (!GVal) return;
          if (auto *F = dyn_cast<Function>(GVal)) {
            if (F->isIntrinsic()) return;
            asmTaken.insert(F);
            linkerSectionEncoded[sec.str()].insert(getFuncDef(F));
          } else if (auto *G = dyn_cast<GlobalVariable>(GVal)) {
            if (!G->isDeclaration())
              linkerSectionEncoded[sec.str()].insert(G);
          }
        });
  }

  for (auto &GV : M->globals()) {
    if (Ctx->ExtGobjs.find(GV.getGUID()) != Ctx->ExtGobjs.end())
      continue;
    if (GV.isDeclaration())
      continue;

    // Skip compiler-introduced globals
    if (shouldSkipValue(&GV)) {
      CG_DEBUG("Skipping compiler-introduced global: " << GV.getName() << "\n");
      continue;
    }

    NF.createValueNode(&GV);

    // section-attributed globals are linker-array members (__param,
    // .init.setup, _ftrace_events, __tracepoints, ...)
    if (CFLLinkerArrays && GV.hasSection()) {
      StringRef sec = GV.getSection();
      if (!sec.starts_with(".discard.") && sec != "llvm.metadata")
        linkerSectionInPlace[cflNormalizeSection(sec)].insert(&GV);
    }
  }

  for (Function &F : *M) {
    // initialize callers
    auto RF = getFuncDef(&F);
    CallInstSet &CIS = Ctx->Callers[RF]; // use RF to retrieve callers
    for (User *U : F.users()) {
      if (CallInst *CI = dyn_cast<CallInst>(U)) {
        if (CI->getCalledFunction() == &F)
          CIS.insert(CI);
      }
    }

    // collect address-taken functions (module-asm references count:
    // the linker materializes their address into a section array)
    if (F.hasAddressTaken() || asmTaken.count(&F)) {
      // Insert the CANONICAL definition (task #45): the raw per-TU
      // object made the set hold one decl copy per referencing TU —
      // pointer-identity consumers (the used-tally, funcOfCanon's
      // pointer-ordered overwrites) saw phantom "unused" functions
      // (kernel census: 8,306 raw vs 4,046 real; __x64_sys_getpid
      // counted both used AND unused). Reachable.cc already did this.
      Ctx->AddressTakenFuncs.insert(getFuncDef(&F));

      // only add fval -> fobj edge in call graph analysis?
      // create a value node for function pointer
      NodeIndex valNode = NF.createValueNode(&F);
      (void)valNode;
    }

    // Populate AllocFuncs. When --func-summaries is loaded, the file is
    // AUTHORITATIVE (FRESH entries drive all existing allocator paths;
    // the legacy hardcoded isAllocFn table is not consulted). Without
    // it, legacy behavior is unchanged.
    if (!Ctx->SummarySpecs.empty()) {
      g_sumAuthoritative = true; // file owns skip lists too (NOOP)
      // A per-call-site clone (--cfl-clone-per-caller: "f.site3") is
      // still f: it takes f's summary.
      StringRef sumName = F.getName();
      for (size_t at = sumName.rfind(".site"); at != StringRef::npos &&
                                               at + 5 < sumName.size() &&
                                               llvm::all_of(sumName.substr(at + 5), isDigit);
           at = sumName.rfind(".site"))
        sumName = sumName.substr(0, at);
      if (const auto *S = summaryForName(Ctx, sumName, !F.isDeclaration())) {
        // FRESH on a void-returning function is a glob overreach
        // ("vmalloc*" caught void vmalloc_init): treating it as an
        // allocator SKIPS ITS BODY, silently severing every registration
        // it performs (5.18 GT FN: free_work via INIT_WORK in
        // vmalloc_init). An allocator must return a value (pointer or
        // address-as-integer, e.g. __get_free_pages). Refuse the
        // classification loudly and keep the body.
        if (S->fresh && F.getReturnType()->isVoidTy()) {
          WARNING("FuncSummaries: FRESH pattern matched void-returning "
                  "function " << F.getName()
                  << " — allocator classification refused, body kept\n");
        } else {
          Ctx->FuncSummaries[&F] = S;
          if (S->fresh) Ctx->AllocFuncs.insert(&F);
        }
        if (S->noop) g_noopBodies.insert(&F);
      }
    } else {
      int size = 0, flag = 0;
      if (isAllocFn(F.getName(), &size, &flag))
        Ctx->AllocFuncs.insert(&F);
    }

    if (!F.isDeclaration() && !F.isIntrinsic() && !F.empty()) {
      // create nodes for function arguments and return value
      if (F.getFunctionType()->isVarArg())
        NF.createVarargNode(&F);
      for (auto &arg : F.args()) {
        NF.createValueNode(&arg);
      }
      if (!F.getReturnType()->isVoidTy()) {
        NF.createReturnNode(&F);
      }

      // Create per-instruction value nodes early (for global dedup).
      // Skip alloc/container functions to match doModulePass filtering.
      if (CFLGlobalDedup &&
          !Ctx->AllocFuncs.count(&F) &&
          !Ctx->ContainerFuncs.count(&F) &&
          !shouldSkipFunction(&F)) {
        for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
          const Instruction *I = &*itr;
          if (containsPointerType(I->getType()))
            NF.createValueNode(I);
          if (const ReturnInst *RI = dyn_cast<ReturnInst>(I))
            Ctx->RetSites[&F] = RI;
          if (const CallBase *CB = dyn_cast<CallBase>(I)) {
            if (const Function *CF = CB->getCalledFunction()) {
              if (Ctx->AllocFuncs.count(CF))
                Ctx->AllocSites.insert(CB);
            }
          }
        }
      }
    }
  }

  // Collect global constructors/destructors
  processCtorsDtors(M);

  // Collect ifunc resolver targets
  for (const GlobalIFunc &IF : M->ifuncs())
    collectIFuncTargets(&IF);

  if (M == Ctx->Modules.back().first) {
    for (auto const &itr: Ctx->ExtGobjs) {
      // linker-array bounds with complete, enumerable contents get
      // their OWN identity (closed world) instead of the universal
      // fallback — registered BEFORE any edges are built so every
      // load of the symbol resolves to the dedicated node
      {
        // Whole-program own identity for every other extern global
        // (--cfl-ext-globals-own-identity); linker-bounds symbols are
        // left to the closed-world logic below, which keeps universal
        // when their membership is incomplete.
        std::vector<std::string> ex0, pr0;
        const bool isBounds =
            CFLLinkerArrays &&
            linkerBoundsSectionKeys(itr.second->getName(), ex0, pr0);
        if (CFLExtGlobalsOwnIdentity && !compositional() && !isBounds)
          NF.addExtGobjOverride(itr.first);
      }
      if (CFLLinkerArrays) {
        StringRef N = itr.second->getName();
        std::vector<std::string> exact, prefix;
        if (linkerBoundsSectionKeys(N, exact, prefix) &&
            !linkerExcludedFamily(N)) {
          bool unresolved = false;
          std::set<const GlobalValue *> ip, en;
          linkerArraySources(N, ip, en, &unresolved);
          if ((!ip.empty() || !en.empty()) && !unresolved)
            NF.addExtGobjOverride(itr.first);
        }
      }
      NF.createValueNode(itr.second);
    }
    for (auto const &itr: Ctx->ExtFuncs) {
      if (!itr.second->getReturnType()->isVoidTy())
        NF.createReturnNode(itr.second);
    }
  }

  // File-entry decay validator: always on when a summary file is loaded
  // (names/keys/offsets rot silently as the kernel moves; decay must be
  // a report line, not a bisection discovery).
  if (iteration == 0 && M == Ctx->Modules.back().first &&
      !Ctx->SummarySpecs.empty())
    checkFileSummaries(Ctx);

  // Summary provers pre-pass: after ALL modules' file-summary
  // attachment (last module, first init iteration), before any
  // doModulePass graph construction — adopted proofs must precede
  // every handleCall/runOnFunction decision.
  if (iteration == 0 && M == Ctx->Modules.back().first &&
      (CFLProposeNoopSummaries || CFLProposeAtomSummaries ||
       CFLProposeSolvedSummaries || CFLProposeChainSummaries ||
       CFLAdoptProposedSummaries)) {
    if (CFLAdoptProposedSummaries && compositional()) {
      errs() << "--cfl-adopt-proposed-summaries is monolithic-only "
                "(per-TU proofs unvalidated)\n";
      assert(false && "adopt-proposed under compositional");
    }
    runSummaryProvers(M);
  }
  if (CFLCells && iteration == 0 && M == Ctx->Modules.back().first) {
    checkPoolClosure();
    checkPoolCarves();
    computeVarargSinks();
    computeVarargKeys();
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee mapping
  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;

    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      // map callsite to possible callees
      if (CallBase *CB = dyn_cast<CallBase>(&*i)) {
        if (CB->isInlineAsm())
          continue;
        // Ensure direct calls (including to alloc/container/skipped
        // functions) are recorded so they appear in the callgraph export.
        if (Function *CF = CB->getCalledFunction()) {
          const Function *RCF = getFuncDef(CF);
          if (!RCF->isIntrinsic())
            Ctx->Callees[CB].insert(RCF);
        }
        FuncSet &FS = Ctx->Callees[CB];
        // calculate the caller info here
        for (const Function *CF : FS) {
          CallInstSet &CIS = Ctx->Callers[CF];
          CIS.insert(CB);
        }
        // collect indirect call targets by type
        if (Ctx->IndirectCallInsts.find(CB) != Ctx->IndirectCallInsts.end()) {
          FuncSet &TS = calleeByType[CB];
          findCalleesByType(CB, TS);
        }
      }
    }
  }

  if (M == Ctx->Modules.back().first) {
    // Regfield detector/channels run FIRST so an applied channel is
    // reflected in the tally, the ICALL dump, and every downstream
    // consumer (apply only touches CLOSED keys; report adds nothing).
    if (CFLRegFieldReport || CFLRegFieldApply || CFLRegFieldObj)
      runRegFieldGapReport();
    // compare callees found by CFL and type matching
    size_t total = 0, match = 0;
    for (auto &it : calleeByType) {
      const CallBase *CS = it.first;
      FuncSet &TS = it.second;
      FuncSet &FS = Ctx->Callees[CS];
      total += TS.size();
      extern cl::opt<bool> CFLDumpCalleeMismatch;
      for (const Function *F : TS) {
        if (FS.find(F) != FS.end()) {
          match++;
        } else if (CFLDumpCalleeMismatch) {
          // not found by CFL
          WARNING("Callee by type not found by CFL: " << F->getName() << " for " << *CS << "\n");
        }
      }
    }
    CG_LOG("Callee by type: total " << total << ", match by CFL " << match << "\n");
    CG_LOG("InitCE LEDGER: " << g_initCEDeclined
           << " pointer-carrying constant expressions in global "
              "initializers without a transfer rule (declined)\n");
    CG_LOG("IntProvenance: modeled " << g_intProvStores << " int stores + "
           << g_intProvLoads << " int loads (witnessed); LEDGER unmodeled "
           << g_intStoreUnmodeled << " stores / " << g_intLoadUnmodeled
           << " loads / " << g_intArgUnmodeled
           << " args with interprocedural int provenance\n");
    CG_LOG("StaticCall LEDGER: " << g_staticCallWired
           << " __SCT__ callsites wired through their keys, "
           << g_staticCallUpdates << " updates wired per-callsite; "
           << g_staticCallNoKey << " without a visible key + "
           << g_staticCallDynUpdate
           << " dynamic-key updates SUPPRESSED (tracepoints covered by "
           << g_tracepointProbes << " probe-registration wirings); "
           << g_staticCallTpIter
           << " tp_func sites -> iterator (probes transitive)\n");
    CG_LOG("InlineAsm LEDGER: modeled " << g_asmSlotLoads
           << " slot loads + " << g_asmSlotStores << " slot stores ("
           << g_asmWidthWitnessed << " width-witnessed), " << g_asmRegLoads
           << " reg-through loads + " << g_asmRegStores << " stores + "
           << g_asmRegCopies << " copies; declined " << g_asmLaunderDeclined
           << " unwitnessed launder candidates\n");
    if (!Ctx->SummarySpecs.empty())
      CG_LOG("FuncSummary LEDGER: " << Ctx->FuncSummaries.size()
             << " functions summarized; applied " << g_sumCpy << " CPY, "
             << g_sumAlias << " ALIAS, " << g_sumSt << " ST, " << g_sumLabels
             << " AS (label), " << g_sumLd
             << " LD, " << g_sumFreshSub << " FRESHSUB, " << g_sumInvoke
             << " INVOKE (" << g_sumInvokeDyn
             << " dynamic-fn pooled fallbacks, " << g_sumInvokeRet
             << " :ret bindings); " << g_sumSkipped
             << " atom refs skipped (missing arg/node)\n");
    {
      uint64_t uniExtGobj = 0, uniOther = 0;
      NF.getUniversalLedger(uniExtGobj, uniOther);
      CG_LOG("UniversalPtr LEDGER: " << uniExtGobj
             << " extern-global value resolutions + " << uniOther
             << " other fallbacks; " << g_uniEdgeTouches
             << " edges touch universal, " << g_uniDerefTouches
             << " deref-throughs, " << g_uniFptrIcalls
             << " icalls read unknown extern memory directly\n");
  if (g_rebasedPtrSkipped)
    CG_LOG("RebasedPtr: " << g_rebasedPtrSkipped
           << " non-percpu ptrtoint chains left identity-free (declared "
           << "residual; percpu-gated rule)\n");
    }
    CG_LOG("PrintfSink: " << printfSinkCallsites << " benign vararg callsites ("
           << printfSinkArgsSkipped << " tail args unwired), "
           << printfNonConstFmt << " non-constant fmt kept, "
           << printfNonBenignFmt << " non-benign fmt kept\n");
    // Deterministic per-icall resolution dump (one line per pair; sort the
    // lines to diff runs — FuncSet iteration order is not stable).
    extern cl::opt<bool> CFLDumpICalls;
    if (CFLDumpICalls) {
      for (auto &it : Ctx->Callees) {
        const CallBase *CS = it.first;
        // direct-form sites stay out UNLESS they were reclassified as
        // icalls (static_call trampolines dispatch through their key)
        if (CS->isInlineAsm() ||
            (CS->getCalledFunction() &&
             !Ctx->IndirectCallInsts.count(const_cast<CallBase *>(CS)))) {
          // INVOKE re-attribution: summarized registrars carry their
          // callback pairs at the DIRECT registration callsite
          // (Callees entries beyond the direct callee). Ground-truth
          // matching needs them; a distinct prefix keeps every ICALL
          // pin byte-stable.
          if (const Function *DC = CS->getCalledFunction()) {
            const Function *DCD = getFuncDef(const_cast<Function *>(DC));
            for (const Function *F : it.second)
              if (F != DC && F != DCD) {
                const Function *R = getFuncDef(const_cast<Function *>(F));
                errs() << "REGCALL " << CS->getFunction()->getName()
                       << " :: " << DC->getName() << " -> "
                       << (R ? R : F)->getName() << "\n";
              }
          }
          continue;
        }
        for (const Function *F : it.second) {
          // Canonicalize through def/alias resolution: which object
          // carried the flow (alias-named decl vs aliasee def) is
          // input-order-dependent; the NAME must not be
          // (cross-machine pin identity, 2026-09-01).
          const Function *R = getFuncDef(const_cast<Function *>(F));
          errs() << "ICALL " << CS->getFunction()->getName() << " :: " << *CS
                 << " -> " << (R ? R : F)->getName() << "\n";
        }
      }
    }
    extern cl::opt<std::string> CFLDumpIcallsJson;
    extern cl::opt<std::string> CFLDumpTypeJson;
    // SoK-harness JSON: {"file:line": [targets...]}, deterministic
    // key order, empty-answer sites included, no-debug sites
    // counted and skipped (they cannot match a file:line GT key).
    // Shared by the flow answer (Ctx->Callees) and the type-only
    // candidate set (calleeByType) so both land in one key space.
    auto writeSiteJson = [&](const std::string &path, const CalleeMap &ans,
                             const char *tag) {
      std::map<std::string, std::set<std::string>> byLoc;
      size_t noDbg = 0;
      for (const CallBase *CS : Ctx->IndirectCallInsts) {
        const DebugLoc &DL = CS->getDebugLoc();
        if (!DL) {
          noDbg++;
          continue;
        }
        std::string key = (DL->getScope()->getFilename() + ":" +
                           Twine(DL->getLine())).str();
        auto &tset = byLoc[key];
        auto cit = ans.find(const_cast<CallBase *>(CS));
        if (cit != ans.end())
          for (const Function *F : cit->second) {
            const Function *R = getFuncDef(const_cast<Function *>(F));
            tset.insert((R ? R : F)->getName().str());
          }
      }
      std::error_code EC;
      raw_fd_ostream OS(path, EC, sys::fs::OF_Text);
      if (EC) {
        errs() << "FATAL: cannot write " << path << ": " << EC.message()
               << "\n";
        exit(1);
      }
      OS << "{";
      bool firstK = true;
      for (auto &kv : byLoc) {
        if (!firstK) OS << ",";
        firstK = false;
        OS << "\n  \"";
        OS.write_escaped(kv.first);
        OS << "\": [";
        bool firstT = true;
        for (auto &f : kv.second) {
          if (!firstT) OS << ", ";
          firstT = false;
          OS << "\"";
          OS.write_escaped(f);
          OS << "\"";
        }
        OS << "]";
      }
      OS << "\n}\n";
      CG_LOG(tag << ": " << byLoc.size() << " callsite locations -> " << path
                 << " (" << noDbg << " sites without debug info skipped)\n");
    };
    if (!CFLDumpIcallsJson.empty())
      writeSiteJson(CFLDumpIcallsJson, Ctx->Callees, "IcallJson");
    if (!CFLDumpTypeJson.empty())
      writeSiteJson(CFLDumpTypeJson, calleeByType, "TypeJson");
    // check if all address-taken functions are used in indirect calls
    FuncSet allCallees;
    for (auto &it : Ctx->Callees)
      allCallees.insert(it.second.begin(), it.second.end());
    size_t used = 0;
    // --cfl-census-type-rej: split the unused set by whether ANY input
    // icall site would type-accept the function. compat==0 = the
    // dispatch half is outside the input (slice artifact) or the
    // address is never call-dispatched (comparison/table-only) — not
    // our miss. compat>0 = a plausible dispatch site exists yet no
    // data flow reached it: the candidate FALSE-NEGATIVE inventory.
    size_t atUnusedCompat = 0, atUnusedNoSite = 0;
    // In IR order (module, then position), never the set's pointer order.
    std::vector<const Function *> atInIR;
    for (auto &MP : Ctx->Modules)
      for (const Function &G : *MP.first)
        if (Ctx->AddressTakenFuncs.count(&G))
          atInIR.push_back(&G);
    assert(atInIR.size() == Ctx->AddressTakenFuncs.size() && "every address-taken function is in a module");
    for (const Function *F : atInIR) {
      if (allCallees.find(F) != allCallees.end()) {
        used++;
      } else {
        WARNING("Address-taken function not used in indirect calls: " << F->getName() << "\n");
        if (CFLCensusTypeRej) {
          size_t compat = 0;
          for (auto *CS2 : Ctx->IndirectCallInsts)
            if (isCompatible(CS2, F))
              compat++;
          (compat ? atUnusedCompat : atUnusedNoSite)++;
          errs() << "AT-UNUSED " << F->getName() << " compat-sites "
                 << compat << "\n";
        }
        // full-constant user dump serializes entire global initializers —
        // multi-GB on kernel inputs, so keep it at debug verbosity
        if (VerboseLevel >= 3) {
          for (auto *U : F->users()) {
            if (!isa<Function>(U)) // skip personality
              errs() << "  User: " << *U << "\n";
          }
        }
      }
    }
    CG_LOG("Address-taken functions: total " << Ctx->AddressTakenFuncs.size() << ", used " << used << "\n");
    // --cfl-census-extern-bound (task #45): rank the extern boundary —
    // called functions with NO definition in the corpus (asm-defined
    // symbols, firmware stubs, out-of-corpus libraries). Pointer args /
    // pointer returns / constant-fn args size the summary-writing
    // worklist: a pointer-propagating asm function with no summary is a
    // silent flow sink. sum=1 marks names the summary file already
    // covers. Measurement only.
    if (CFLCensusExternBound) {
      struct ExtStat {
        size_t calls = 0, ptrArgs = 0, fnArgs = 0;
        bool ptrRet = false, summarized = false;
      };
      std::map<std::string, ExtStat> ext;
      for (auto &mp : Ctx->Modules)
        for (Function &EF : *mp.first) {
          if (EF.isIntrinsic()) continue;
          for (const User *U : EF.users()) {
            const auto *CB = dyn_cast<CallBase>(U);
            if (!CB || CB->getCalledOperand()->stripPointerCasts() != &EF)
              continue;
            Function *D = getFuncDef(&EF);
            if (!D->isDeclaration()) continue; // defined somewhere in corpus
            auto &st = ext[D->getName().str()];
            st.calls++;
            st.ptrRet |= containsPointerType(D->getReturnType());
            st.summarized = Ctx->FuncSummaries.count(D) ||
                            Ctx->FuncSummaries.count(&EF);
            for (const Value *A : CB->args()) {
              if (A->getType()->isPointerTy()) {
                st.ptrArgs++;
                if (isa<Function>(A->stripPointerCasts())) st.fnArgs++;
              }
            }
          }
        }
      std::vector<std::pair<std::string, ExtStat>> rank(ext.begin(),
                                                        ext.end());
      std::sort(rank.begin(), rank.end(), [](auto &a, auto &b) {
        if (a.second.fnArgs != b.second.fnArgs)
          return a.second.fnArgs > b.second.fnArgs;
        if (a.second.ptrArgs != b.second.ptrArgs)
          return a.second.ptrArgs > b.second.ptrArgs;
        return a.second.calls > b.second.calls;
      });
      size_t unsummarizedPtr = 0;
      for (auto &p : rank)
        if (!p.second.summarized && (p.second.ptrArgs || p.second.ptrRet))
          unsummarizedPtr++;
      errs() << "EXTERN-BOUND census: " << rank.size()
             << " extern called fns, " << unsummarizedPtr
             << " pointer-bearing WITHOUT a summary\n";
      size_t shownEB = 0;
      for (auto &p : rank) {
        if (shownEB++ >= 2000) { errs() << "EXTERN-BOUND   ...\n"; break; }
        errs() << "EXTERN-BOUND   " << p.first << " calls " << p.second.calls
               << " ptrargs " << p.second.ptrArgs << " fnargs "
               << p.second.fnArgs << " ptret " << (int)p.second.ptrRet
               << " sum " << (int)p.second.summarized << "\n";
      }
    }
    if (CFLCensusTypeRej)
      errs() << "AT-UNUSED summary: " << atUnusedNoSite
             << " with NO type-compatible input site (slice artifact / "
             << "non-dispatch address use), " << atUnusedCompat
             << " WITH a compatible site but no flow (candidate FN "
             << "inventory)\n";
  }

  return false;
}

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  if (CFLConfirmFresh && iteration == 0 && M == Ctx->Modules.front().first)
    confirmFreshWrappers(); // all modules loaded; AllocFuncs seeded
  if (CFLCells && iteration == 0 && M == Ctx->Modules.front().first)
    labelPackedArrays(); // rule (a): before anything reads a global's layout
  if (CFLCells && iteration == 0 && M == Ctx->Modules.front().first)
    computeLinkWords(); // plan 3.55 R1: tagged-pointer link words (report only; read by R3's LINKWORD storage)

  if (CFLConfirmInvoke && iteration == 0 && M == Ctx->Modules.front().first)
    confirmInvokeSummaries(); // before any callsite wiring

  if (CFLCensusInvoke && iteration == 0 && M == Ctx->Modules.front().first)
    runInvokeCensus(); // all modules + summaries loaded; adds no edges

  if ((CFLConfirmSinks || CFLSinkInstr) && iteration == 0 &&
      M == Ctx->Modules.front().first)
    runSinkConfirmer(); // contract gate BEFORE any sealing can happen

  if (CFLTracepointKeys && iteration == 0 &&
      M == Ctx->Modules.front().first)
    bindTracepointMediatorPairs(); // before any callsite is visited

  if ((CFLCensusUnions || CFLUnionKeys != "off") && iteration == 0 &&
      M == Ctx->Modules.front().first)
    runUnionCensus(); // census, and the union keys graph build applies
  if (CFLCells && CFLUnionKeys == "tag" && iteration == 0 && M == Ctx->Modules.front().first)
    computeTaggedFields(); // plan 3.51: keys for fields tagged by a sibling
  // Report only: after carves, the confirmer's fresh wrappers, and the
  // union keys and tagged fields (a cursor inside a union is checked on
  // its keys, plan 3.55 Q-d); under --cfl-cells nothing between its old
  // place and here runs (tracepoint keys are refused, the confirmers and
  // censuses are off unless asked).
  // --cfl-cells refuses --cfl-reachable (KAMain.cc): every body is emitted.
  if (CFLCells && iteration == 0 && M == Ctx->Modules.front().first)
  {
    buildMintTable(); // what each allocation is minted as, before the closure reads it
    buildSiteNames(); // B: which sites are named for the covers
  }
  if (CFLCells && (CFLContainerClosure || !Ctx->Containers.empty()) && iteration == 0 &&
      M == Ctx->Modules.front().first)
    checkContainerClosure();
  if (CFLCells && CFLUnionKeys != "off" && iteration == 0 && M == Ctx->Modules.front().first)
    unadoptKeyedBodies(); // keyed bodies keep their accesses

  if (CFLCensusNexus && iteration == 0 && M == Ctx->Modules.front().first)
    runNexusCensus(); // measurement-only, adds no edges

  // process global initializers and functions, only the first iteration
  if (iteration == 0) {
    // Pre-size edge vector on first module to avoid repeated reallocations.
    // Estimate ~2 edges per instruction (most instructions emit one edge
    // and trigger at least one more).
    if (M == Ctx->Modules.front().first) {
      size_t totalInsts = 0;
      for (auto &[Mod, _] : Ctx->Modules)
        for (Function &F : *Mod)
          totalInsts += F.getInstructionCount();
      Graph.reserve(totalInsts * 2);

      // Run global dedup on first module (all nodes exist from doInitialization).
      // The intra-procedural rules in globalDedupScanFunction are flow-insensitive-safe
      // by construction; cross-call merges in globalDedupScanCallEdges only fire for
      // single-callsite callees and are sound under per-TU solving as well.
      // Per-TU dense mapping below uses getCanonicalNode() so dedup classes are
      // visible to the solver.
      if (CFLGlobalDedup)
        runGlobalDedup();
    }

    const size_t edgeStart = Graph.size();
    if (namedPlanes() || CFLCells) { // cells: the labels read the bases
      if (!accessNames)
        accessNames = std::make_unique<ka::AccessNames>();
      accessNames->scanBases(*M);
    }
    moduleDerefEdgeRoots.clear();
    moduleFieldWildcardRoots.clear();
    moduleConstGEPFieldDone.clear();
    curDL = &M->getDataLayout();

    for (auto &GV : M->globals()) {
      // Skip compiler-introduced globals
      if (shouldSkipValue(&GV)) {
        CG_DEBUG("Skipping initializer for compiler global: " << GV.getName() << "\n");
        continue;
      }

      if (GV.hasInitializer()) {
        NodeIndex valNode = NF.getValueNodeFor(&GV);
        assert(valNode != AndersNodeFactory::InvalidIndex && "Global value node not found!");
        NodeIndex deref = NF.createDereferenceNode(valNode);
        Graph.addDeref(valNode, deref);
        CG_DEBUG("Processing initializer for GV " << GV.getName() << "\n");
        auto init = GV.getInitializer();
        initNamedS = nullptr; // slot names start at the first named struct
        initOff = 0;
        initUnion = false;
        initAbsOff = 0;
        initGV = &GV;
        processInitializer(deref, init, "", -1,
                           Graph.fieldSensitive() ? valNode
                                               : AndersNodeFactory::InvalidIndex);
      }
    }

    if (CFLReachable) {
      // Bodies enter by reachability from the entries; seeded once, after
      // every module's global initializers are in the graph.
      if (M == Ctx->Modules.back().first) seedReachable();
    } else
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty() ||
          (Ctx->AllocFuncs.count(&F) && !summaryKeepsBody(Ctx, &F)) ||
          Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      runOnFunction(&F);
    }

    // Build field-store map from IR uses (direct stores + one-level callbacks).
    // In per-TU mode, funcFieldStores was cleared above; in monolithic mode
    // it accumulates across modules.  processInitializer already added
    // global-initializer entries for this module.
    buildFieldStoreMapFromIR(M);

    moduleBuilt(M, edgeStart, Graph.size());

    // Linker-array wiring needs every module's section members and asm
    // targets: run once, after the last module's own edges. In per-TU
    // compositional mode these edges are cross-module by nature and
    // fall outside all module ranges — repair mode won't recompute
    // them; monolithic flows-to/saturation consume them normally.
    if (M == Ctx->Modules.back().first) {
      wireLinkerSectionArrays();
      finalizeChainPairs();
    }
  }

  if (M != Ctx->Modules.back().first)
    return false;
  return solve();
}

void CallGraphPass::logHighDegreeNodes(size_t threshold, size_t topN) {
  CG_LOG("Analyzing constraint graph structure...\n");
  std::vector<std::pair<NodeIndex, size_t>> topNodes;
  Graph.analyzeHighDegreeNodes(threshold, topN, &topNodes);
  if (!topNodes.empty()) {
    CG_LOG("Examining top " << topNodes.size() << " high-degree nodes:\n");
    for (const auto &[nodeId, degree] : topNodes)
      NF.dumpNode(nodeId);
  }
}

bool CallGraphPass::solve() {
  if (VerboseLevel >= 2) {
    size_t byKind[4] = {0, 0, 0, 0};
    for (const GraphEdge &E : Graph.edges())
      byKind[(int)E.kind]++;
    CG_LOG("ConstraintGraph: iteration " << iteration << ": "
           << Graph.size() << " edges (" << byKind[(int)EdgeKind::Copy]
           << " copy, " << byKind[(int)EdgeKind::Deref] << " deref, "
           << byKind[(int)EdgeKind::Field] << " field, "
           << byKind[(int)EdgeKind::FieldAny]
           << " field-any); a grammar-labelled graph has twice as many\n");
  }
  logHighDegreeNodes(1000, 20);
  if (!CFLDumpAGraph.empty() && iteration == 0)
    dumpRawGraph(CFLDumpAGraph); // before presolve: raw value nodes
  if (CFLCells) { // no presolve: cells are never unified
    if (CFLConstructCensus && iteration == 0) runConstructCensus();
    // A later iteration mints at the allocator calls the earlier ones
    // resolved (indirect calls marked in Ctx->AllocSites): the table is
    // rebuilt over them (iteration 0's is built before the closure).
    if (iteration > 0) buildMintTable(), buildSiteNames();
    bool again = runCellResolution();
    iteration++;
    return again;
  }
  ensureUnnamedShadows();
  logNamedCells();
  if (!CFLPreSolveOnce || iteration == 0)
    preSolveCopyFieldMerge(nullptr);
  // Answer-anchored resolution. Outer fixpoint: re-solve while
  // resolution wires new callee flows (the iterative driver re-enters
  // doModulePass while we return true; iteration >= 1 skips the edge
  // build and goes straight to the solve).
  bool again = runFlowsToResolution();
  iteration++;
  return again;
}
