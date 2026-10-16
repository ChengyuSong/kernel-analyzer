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

// Names.cc: names the solve reads through: the field-name certifier and tables, object tables, tracepoint keys.
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

size_t g_tpKeyConstBinds = 0, g_tpKeyMediatorBinds = 0,
              g_tpKeyDispatchWires = 0, g_tpKeyUnclassified = 0,
              g_tpKeyKeylessIter = 0, g_tpKeyUnmapped = 0,
              g_tpKeyClassFnSkipped = 0, g_tpKeyMediatorDataPools = 0,
              g_tpKeyIterLoadsSevered = 0;
static size_t g_regfieldBarePtrFnStores = 0;
// --cfl-regfield-report (targeted-fs detector): rank (struct+offset)
// registration fields by the gap between the resolved fanout at their
// reader icalls and the registration population actually stored
// through them. A narrow witnessed population under a huge fanout is
// the deep-collapse signature: the reader inherited a pooled cone
// that field residues would sever, so the parent struct is a
// candidate for --cfl-nexus-fields. Targeted fs is exact by
// construction — the suggestion only chooses where residues are
// SPENT, so an open (unwitnessed) population is never a soundness
// problem, it just stays out of the auto-suggestion. Population
// sources: constant-Function stores; one argument hop for
// install-API shapes (the constant lives at the API's callers);
// global-initializer slots; copy-edge closure between field keys
// (control-struct relays). Keys with dispatch but no witnessed
// population are reported unsuggested — same-slot instance pools
// (work/timer rendezvous) look exactly like that, and residues
// cannot split them.
void CallGraphPass::runRegFieldGapReport() {
  // Deepest named struct traversed by the GEP chain + byte offset
  // within it ("var" once a non-constant index follows the struct).
  auto deepKey = [](const Value *P, const DataLayout &DL) -> std::string {
    P = P->stripPointerCasts();
    SmallVector<const GEPOperator *, 4> chain;
    while (const auto *G = dyn_cast<GEPOperator>(P)) {
      chain.push_back(G);
      P = G->getPointerOperand()->stripPointerCasts();
    }
    std::string SName;
    uint64_t SOff = 0;
    bool haveS = false, varTail = false;
    for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
      for (auto GTI = gep_type_begin(*it), E = gep_type_end(*it); GTI != E;
           ++GTI) {
        if (StructType *ST = GTI.getStructTypeOrNull()) {
          uint64_t fi = cast<ConstantInt>(GTI.getOperand())->getZExtValue();
          uint64_t eo = DL.getStructLayout(ST)->getElementOffset(fi);
          if (ST->hasName() && !isAnonStruct(ST)) {
            SName = stripStructNameSuffix(ST->getStructName()).str();
            SOff = eo;
            haveS = true;
            varTail = false;
          } else if (haveS && !varTail) {
            SOff += eo;
          }
        } else if (haveS && !varTail) {
          if (const auto *CI = dyn_cast<ConstantInt>(GTI.getOperand()))
            SOff += (uint64_t)CI->getSExtValue() *
                    DL.getTypeAllocSize(GTI.getIndexedType());
          else
            varTail = true;
        }
      }
    }
    if (!haveS) return std::string();
    return SName + "+" +
           (varTail ? std::string("var") : std::to_string(SOff));
  };

  std::map<std::string, std::set<std::string>> regs; // key -> fn names
  std::set<std::string> open;                        // unwitnessed stores
  std::map<std::string, std::set<std::string>> copyIn; // dst <- src keys
  // OBJECT-population channel (--cfl-regfield-obj, the re-founding):
  // for ops-POINTER fields, certify WHICH ops globals can occupy the
  // field; dispatch tables then derive from reading the objects'
  // initializer slots (Lean objclamp_sound). This is the ONLY lever
  // reaching GEP-less slot-0 dispatches (fn = load(load(&o->ops)):
  // no named-struct GEP exists, so fn-slot keys cannot see the site
  // — the class that carried the post-regfield fat tail).
  // Population members are (GV, base, stride): bare &G = (G,0,0);
  // interior &G+off = (G,off,0); var-indexed &G[i]+f = (G,f,elemSize)
  // — taxonomy row 5 (svc rq_procinfo: &table[i] stored into request
  // fields). Stride composes with the dispatch-side stride at read.
  using ObjMember = std::tuple<const GlobalVariable *, int64_t, uint64_t>;
  std::map<std::string, std::set<ObjMember>> objRegs;
  auto objMemberOf = [](const Value *V, const DataLayout &DLx)
      -> std::optional<ObjMember> {
    int64_t base = 0;
    uint64_t stride = 0;
    V = V->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(V)) {
      for (auto GTI = gep_type_begin(G), E2 = gep_type_end(G); GTI != E2;
           ++GTI) {
        if (const auto *CI = dyn_cast<ConstantInt>(GTI.getOperand())) {
          if (StructType *ST = GTI.getStructTypeOrNull())
            base += (int64_t)DLx.getStructLayout(ST)->getElementOffset(
                CI->getZExtValue());
          else
            base += CI->getSExtValue() *
                    (int64_t)DLx.getTypeAllocSize(GTI.getIndexedType());
        } else if (!GTI.getStructTypeOrNull() && stride == 0) {
          stride = DLx.getTypeAllocSize(GTI.getIndexedType());
          if (!stride) return std::nullopt;
        } else {
          return std::nullopt;
        }
      }
      V = G->getPointerOperand()->stripPointerCasts();
    }
    const auto *GVr = dyn_cast<GlobalVariable>(V);
    if (!GVr || base < 0) return std::nullopt;
    return ObjMember{GVr, base, stride};
  };
  std::set<std::string> objOpen; // unwitnessed pointer store to the key
  std::map<std::string, std::string> objOpenWhy; // first culprit (audit)
  auto objOpenAt = [&](const std::string &K, const llvm::Instruction *I) {
    objOpen.insert(K);
    if (!objOpenWhy.count(K) && I)
      objOpenWhy[K] = (I->getFunction()->getName() + "::" +
                       I->getOpcodeName()).str();
  };
  std::map<std::string, std::set<std::string>> objCopyIn;
  // Obj-channel bulk hazard, FINER than hazBulk: a whole-object copy
  // whose SOURCE is the same struct type moves already-witnessed
  // pointer values between instances (lock-duplication idiom) —
  // population-preserving, NOT a hazard. Only transfers from unknown
  // buffers can introduce unwitnessed pointers.
  std::set<std::string> objHazBulk;
  std::map<std::string, size_t> objCopySameOff; // untyped same-offset
                                                // instance-copy rescues
                                                // (stated assumption)
  std::map<std::string, size_t> objCopyListAnchor; // container_of-
                                                   // anchored rescues
  // Link-member offsets per struct: container_of sources are pointers
  // anchored AT a link member (list traversal), so a copy's source
  // offset reconciles as link_off + net == field_off. Direct members
  // only (v1); covers the file_lock/fl_list shape.
  std::map<std::string, std::set<int64_t>> linkOffs;
  {
    static const std::set<std::string> linkTys = {
        "struct.list_head",   "struct.hlist_node",
        "struct.hlist_bl_node", "struct.llist_node",
        "struct.hlist_nulls_node", "struct.rb_node"};
    for (auto &mp : Ctx->Modules) {
      const DataLayout &DL = mp.first->getDataLayout();
      for (StructType *ST : mp.first->getIdentifiedStructTypes()) {
        if (!ST->hasName() || isAnonStruct(ST) || ST->isOpaque() || !ST->isSized()) continue;
        const std::string SN0 =
            stripStructNameSuffix(ST->getStructName()).str();
        const StructLayout *SL = DL.getStructLayout(ST);
        for (unsigned i = 0; i < ST->getNumElements(); i++)
          if (auto *ET = dyn_cast<StructType>(ST->getElementType(i)))
            if (ET->hasName() && !isAnonStruct(ET) &&
                linkTys.count(
                    stripStructNameSuffix(ET->getStructName()).str()))
              linkOffs[SN0].insert((int64_t)SL->getElementOffset(i));
      }
    }
  }
  // Audit provenance: which source contributed each name (0=const-
  // global initializer, 1=store/cmpxchg-const, 2=install-API arg hop,
  // 3=copy closure) + keys fed by a NON-const global's initializer.
  std::map<std::string, std::array<std::set<std::string>, 4>> popSrc;
  std::set<std::string> initNonConst;
  auto addPop = [&](const std::string &Key, const std::string &N,
                    int src) {
    regs[Key].insert(N);
    popSrc[Key][src].insert(N);
  };
  // Channel-closedness hazards (a key may only auto-close with ALL of
  // these at zero — a channel table that misses a registrant drops
  // true pairs, so every unclassifiable mutation path must refuse):
  std::map<std::string, size_t> hazAtomic;  // cmpxchg/xchg on the slot
  std::map<std::string, size_t> hazEscape;  // slot address escapes
  std::set<std::string> hazBulk;            // struct hit by non-const
                                            // memcpy/memmove (all keys)

  // WITNESS-BY-USE (docs/regfield-literal-table-gap.md): value-
  // identified registry of every initialized global whose initializer
  // carries function pointers, keyed by the canonical (defining)
  // global. A NAMED-typed table is witnessed by the initializer walk
  // below; a literal-typed one has no key of its own and must be
  // witnessed at its USE sites instead — const-source copies attribute
  // into the DESTINATION's keys, population membership feeds the
  // fn-slot tables at apply, and keys whose reader base cannot be
  // enumerated absorb every loose table (attribute-or-refuse; the
  // refusal is coarse attribution, never a silent drop).
  std::map<const GlobalVariable *, std::map<uint64_t, const Function *>>
      fnTables;
  std::map<const GlobalVariable *, size_t> initAttrCount; // walk-witnessed
  std::set<const GlobalVariable *> looseCopied; // const-src copy, no
                                                // dest layout context
  for (auto &mp : Ctx->Modules) {
    const DataLayout &DLg = mp.first->getDataLayout();
    for (GlobalVariable &GV : mp.first->globals()) {
      if (!GV.hasInitializer()) continue;
      const GlobalVariable *GC = &GV;
      if (const auto *C2 =
              dyn_cast_or_null<GlobalVariable>(canonChainKey(&GV)))
        GC = C2;
      std::map<uint64_t, const Function *> slots;
      walkInitFnSlots(GV.getInitializer(), 0, DLg, slots);
      if (!slots.empty()) fnTables[GC].insert(slots.begin(), slots.end());
    }
  }

  // --cfl-filter-ledger: per-pair provenance for every channel removal
  // (all three clamp sites below). Joining the FILTERED lines against
  // any ground truth certifies that no observed pair was filtered —
  // and when one was, the line names the responsible key and site.
  auto ledger = [](const char *mech, const std::string &key,
                   const CallBase *CB, const Function *F) {
    if (!CFLFilterLedger) return;
    std::string loc = "-";
    if (DILocation *DIL = CB->getDebugLoc())
      loc = (DIL->getFilename() + ":" + Twine(DIL->getLine())).str();
    errs() << "FILTERED " << mech << " " << key << " "
           << CB->getFunction()->getName() << " @" << loc << " -> "
           << F->getName() << "\n";
  };

  for (auto &mp : Ctx->Modules) {
    const DataLayout &DL = mp.first->getDataLayout();
    // registration side: dynamic stores
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty()) continue;
      if (shouldSkipFunction(&F)) continue;
      for (const Instruction &I : instructions(F)) {
        // hazard sweep: atomics on field slots; bulk copies into a
        // struct from a non-constant source; field addresses used as
        // anything other than a direct load/store pointer
        if (const auto *AX = dyn_cast<AtomicCmpXchgInst>(&I)) {
          std::string Key = deepKey(AX->getPointerOperand(), DL);
          if (!Key.empty()) {
            if (const auto *Fn = dyn_cast<Function>(
                    AX->getNewValOperand()->stripPointerCasts()))
              addPop(Key, Fn->getName().str(), 1);
            else
              hazAtomic[Key]++;
          }
        } else if (const auto *AR = dyn_cast<AtomicRMWInst>(&I)) {
          std::string Key = deepKey(AR->getPointerOperand(), DL);
          if (!Key.empty()) hazAtomic[Key]++;
        } else if (const auto *MI = dyn_cast<AnyMemTransferInst>(&I)) {
          std::string Key = deepKey(MI->getRawDest(), DL);
          const auto *SG = dyn_cast<GlobalVariable>(
              MI->getRawSource()->stripPointerCasts());
          // const-global source is covered by the initializer pass
          // (same struct keys); anything else is an opaque write
          const bool constSrc = SG && SG->isConstant() &&
                                SG->hasInitializer();
          // obj channel: source provably the SAME struct type =
          // population-preserving copy, exempt from objHazBulk
          auto srcTypeName = [&]() -> std::string {
            const Value *S = MI->getRawSource()->stripPointerCasts();
            if (const auto *AI = dyn_cast<AllocaInst>(S))
              if (auto *ST = dyn_cast<StructType>(AI->getAllocatedType()))
                if (ST->hasName() && !isAnonStruct(ST))
                  return stripStructNameSuffix(ST->getStructName()).str();
            if (SG)
              if (auto *ST = dyn_cast<StructType>(SG->getValueType()))
                if (ST->hasName() && !isAnonStruct(ST))
                  return stripStructNameSuffix(ST->getStructName()).str();
            return std::string();
          };
          // WITNESS-BY-USE fix A: a const-global source's fn slots are
          // attributed into the DESTINATION struct's keys at copy-
          // shifted offsets — by layout, never by the source's
          // (possibly literal) type name. This replaces the vacuous
          // "covered by the initializer pass" exemption: the 7
          // literal-typed static x86_pmu tables at 5.18 were never
          // covered, and the exemption let their keys close without
          // them. Entries beyond the copy length are attributed too —
          // table over-inclusion is sound (a bigger table removes
          // less). A fn-bearing const source with NO destination
          // layout context joins the loose set; unresolved-base keys
          // absorb it at apply.
          if (constSrc) {
            const GlobalVariable *SGc = SG;
            if (const auto *SC =
                    dyn_cast_or_null<GlobalVariable>(canonChainKey(SG)))
              SGc = SC;
            auto ti = fnTables.find(SGc);
            if (ti != fnTables.end()) {
              std::string DN;
              int64_t DOff = -1;
              const size_t plus0 = Key.find('+');
              if (!Key.empty() &&
                  Key.find("+var") == std::string::npos) {
                DN = Key.substr(0, plus0);
                (void)!StringRef(Key).substr(plus0 + 1)
                    .getAsInteger(10, DOff);
              } else if (Key.empty()) {
                const Value *DP = MI->getRawDest()->stripPointerCasts();
                Type *DT = nullptr;
                if (const auto *DG = dyn_cast<GlobalVariable>(DP))
                  DT = DG->getValueType();
                else if (const auto *DA = dyn_cast<AllocaInst>(DP))
                  DT = DA->getAllocatedType();
                auto *DST = dyn_cast_or_null<StructType>(DT);
                if (DST && DST->hasName() && !isAnonStruct(DST)) {
                  DN = stripStructNameSuffix(DST->getStructName()).str();
                  DOff = 0;
                }
              }
              if (DOff >= 0) {
                for (const auto &[fo, Fn] : ti->second)
                  addPop(DN + "+" + std::to_string((uint64_t)DOff + fo),
                         Fn->getName().str(), 1);
              } else {
                looseCopied.insert(SGc);
              }
            }
          }
          if (!Key.empty()) {
            const std::string SN0 = Key.substr(0, Key.find('+'));
            if (!constSrc) {
              hazBulk.insert(SN0);
              if (srcTypeName() != SN0) objHazBulk.insert(SN0);
            }
          } else if (!constSrc) {
            // bare-pointer memcpy: attribute via the source or dest
            // alloca's allocated struct type when visible
            const std::string STN = srcTypeName();
            for (const Value *P :
                 {MI->getRawDest()->stripPointerCasts(),
                  MI->getRawSource()->stripPointerCasts()})
              if (const auto *AI = dyn_cast<AllocaInst>(P))
                if (auto *ST =
                        dyn_cast<StructType>(AI->getAllocatedType()))
                  if (ST->hasName() && !isAnonStruct(ST)) {
                    const std::string N =
                        stripStructNameSuffix(ST->getStructName()).str();
                    hazBulk.insert(N);
                    if (STN != N) objHazBulk.insert(N);
                  }
          }
        }
        for (const Use &Op : I.operands()) {
          const auto *G = dyn_cast<GEPOperator>(Op.get());
          if (!G) continue;
          const bool ptrPos =
              (isa<LoadInst>(&I) && Op.getOperandNo() == 0) ||
              (isa<StoreInst>(&I) &&
               Op.getOperandNo() == StoreInst::getPointerOperandIndex()) ||
              (isa<AtomicCmpXchgInst>(&I) && Op.getOperandNo() == 0) ||
              (isa<AtomicRMWInst>(&I) && Op.getOperandNo() == 0) ||
              // memcpy/memmove/memset dest+src are pointer positions:
              // bulk transfers have their OWN hazard (hazBulk); double-
              // counting them as slot-address escapes blocked keys a
              // field-range copy merely starts at (file_lock+168)
              (isa<AnyMemIntrinsic>(&I) && Op.getOperandNo() <= 1) ||
              isa<GetElementPtrInst>(&I);
          if (ptrPos) continue;
          std::string Key = deepKey(G, DL);
          if (!Key.empty()) hazEscape[Key]++;
        }
        const auto *SI = dyn_cast<StoreInst>(&I);
        if (!SI) continue;
        std::string Key = deepKey(SI->getPointerOperand(), DL);
        if (Key.empty()) {
          // Whole-object store through a bare pointer (no GEP):
          // `*buf = (struct cpu_stop_work){.fn = fn}` writes fn
          // fields with no field key. Invisible-but-unhazarded was a
          // certifier hole (found by the km audit) — open every key
          // of the VALUE's struct type. Scalar fn stores through
          // bare pointers have no attributable type: counted as the
          // global residual, reported below.
          Type *VT = SI->getValueOperand()->getType();
          if (auto *ST = dyn_cast<StructType>(VT)) {
            if (ST->hasName() && !isAnonStruct(ST)) {
              hazBulk.insert(
                  stripStructNameSuffix(ST->getStructName()).str());
              // obj channel: whole-object store of a LOADED value =
              // instance copy (population-preserving); anything else
              // (insertvalue-built, unknown) can smuggle pointers
              if (!isa<LoadInst>(SI->getValueOperand()))
                objHazBulk.insert(
                    stripStructNameSuffix(ST->getStructName()).str());
            }
          } else if (isa<Function>(
                         SI->getValueOperand()->stripPointerCasts())) {
            g_regfieldBarePtrFnStores++;
          }
          continue;
        }
        const Value *V = SI->getValueOperand()->stripPointerCasts();
        if (const auto *Fn = dyn_cast<Function>(V)) {
          addPop(Key, Fn->getName().str(), 1);
        } else if (const auto *A = dyn_cast<Argument>(V)) {
          // Install-API hop: the population is the constants at the
          // API's callers — but ONLY if EVERY caller witnesses one.
          // A single variable-passing caller means an unwitnessed
          // registrant, so the key must stay open (a channel built
          // from the partial table would drop true pairs).
          // DIRECT callers only: Ctx->Callers also holds resolved
          // indirect callsites, whose caller set is itself the smear
          // under repair — trusting them lets junk arguments from
          // spuriously-resolved icalls pollute the table (observed:
          // clear_page_erms entering irqaction+0). An indirect
          // caller therefore opens the key.
          bool all = true, anyC = false;
          bool allObj = true, anyObj = false;
          auto ci = Ctx->Callers.find(A->getParent());
          if (ci != Ctx->Callers.end())
            for (auto *CB : ci->second) {
              Function *DC =
                  const_cast<Function *>(CB->getCalledFunction());
              if (!DC || getFuncDef(DC) !=
                             getFuncDef(const_cast<Function *>(
                                 A->getParent()))) {
                all = false;
                allObj = false;
                continue;
              }
              if (A->getArgNo() >= CB->arg_size()) {
                all = false;
                allObj = false;
                continue;
              }
              const Value *AV =
                  CB->getArgOperand(A->getArgNo())->stripPointerCasts();
              if (const auto *CF = dyn_cast<Function>(AV)) {
                addPop(Key, CF->getName().str(), 2);
                anyC = true;
                allObj = false; // a fn constant is not an ops object
              } else {
                all = false;
                if (auto M = objMemberOf(
                        AV, CB->getModule()->getDataLayout())) {
                  objRegs[Key].insert(*M); // install-API hop, obj side
                  anyObj = true;
                } else if (!isa<ConstantPointerNull>(AV)) {
                  allObj = false;
                }
              }
            }
          if (!all || !anyC) open.insert(Key);
          // obj channel: ANY caller actual that is not a witnessed
          // &global / null makes the field's object population
          // unwitnessed (fn constants included: they mark a fn slot,
          // where the obj channel is inapplicable anyway)
          if (!allObj) objOpenAt(Key, SI);
          (void)anyObj;
        } else if (const auto *LI = dyn_cast<LoadInst>(V)) {
          std::string SK = deepKey(LI->getPointerOperand(), DL);
          if (!SK.empty() && SK != Key) {
            copyIn[Key].insert(SK);
            objCopyIn[Key].insert(SK);
          } else {
            open.insert(Key); // fn-channel semantics unchanged
            // obj channel: SAME-key copy (lock duplication idiom:
            // new->fl_ops = fl->fl_ops) is population-preserving —
            // only an UNKEYED load source is unwitnessed. Instcombine
            // asymmetry rescue: clang lowers same-struct field copies
            // with the LOAD side as an untyped i8 GEP (posix_test_lock
            // fl_lmops, 2026-08-26) — when the untyped source's
            // constant byte offset EQUALS the dest key's offset, treat
            // as an instance copy. STATED ASSUMPTION (audited as its
            // own class): a same-byte-offset pointer copy targets the
            // same field of the same struct type; GT gates it.
            if (SK.empty()) {
              const Value *LP =
                  LI->getPointerOperand()->stripPointerCasts();
              APInt loff(64, 0);
              bool cst = true;
              while (const auto *G = dyn_cast<GEPOperator>(LP)) {
                if (!G->accumulateConstantOffset(DL, loff)) {
                  cst = false;
                  break;
                }
                LP = G->getPointerOperand()->stripPointerCasts();
              }
              int64_t keyOff = -1;
              const size_t plus = Key.rfind('+');
              if (plus != std::string::npos)
                (void)!StringRef(Key).substr(plus + 1)
                    .getAsInteger(10, keyOff);
              const int64_t net = loff.getSExtValue();
              if (cst && keyOff >= 0 && net == keyOff) {
                objCopySameOff[Key]++; // base-anchored instance copy
              } else if (cst && keyOff >= 0) {
                // container_of anchor: source root points AT a link
                // member (list traversal), so link_off + net ==
                // field_off reconciles a same-field instance copy
                // (posix_test_lock fl_lmops via fl_list). STATED
                // ASSUMPTION, tagged per key, GT-gated like same-off.
                bool anchored = false;
                auto li2 =
                    linkOffs.find(Key.substr(0, Key.find('+')));
                if (li2 != linkOffs.end())
                  for (int64_t L : li2->second)
                    if (L + net == keyOff) {
                      anchored = true;
                      break;
                    }
                if (anchored)
                  objCopyListAnchor[Key]++;
                else
                  objOpenAt(Key, SI);
              } else {
                objOpenAt(Key, SI);
              }
            }
          }
        } else if (containsPointerType(V->getType())) {
          open.insert(Key); // fn-channel semantics unchanged
          if (auto M = objMemberOf(V, DL))
            objRegs[Key].insert(*M); // &ops_global / &table[i] member
          else if (!isa<ConstantPointerNull>(V))
            objOpenAt(Key, SI); // computed/heap pointer: unwitnessed
        }
      }
    }
    // registration side: global-initializer slots, attributed to the
    // DEEPEST NAMED ancestor struct (deepKey's convention). Carrying
    // the (name, offset) context downward also witnesses fn slots
    // inside LITERAL structs nested in named ones — previously
    // silently dropped (the literal-table gap's nested variant). A
    // top-level literal table has no context: its slots stay in
    // fnTables and are witnessed by use (copy / population / loose).
    for (GlobalVariable &GV : mp.first->globals()) {
      if (!GV.hasInitializer()) continue;
      const GlobalVariable *GVc = &GV;
      if (const auto *C2 =
              dyn_cast_or_null<GlobalVariable>(canonChainKey(&GV)))
        GVc = C2;
      std::function<void(const Constant *, const std::string &, uint64_t,
                         bool)>
          walk = [&](const Constant *C, const std::string &PN,
                     uint64_t PO, bool haveP) {
            if (const auto *CS = dyn_cast<ConstantStruct>(C)) {
              StructType *ST = CS->getType();
              const StructLayout *SL = DL.getStructLayout(ST);
              const bool named = ST->hasName() && !isAnonStruct(ST);
              const std::string SN =
                  named ? stripStructNameSuffix(ST->getStructName()).str()
                        : PN;
              const bool haveCtx = named || haveP;
              for (unsigned i = 0; i < CS->getNumOperands(); i++) {
                const Constant *E = CS->getOperand(i);
                const uint64_t EO =
                    (named ? 0 : PO) + SL->getElementOffset(i);
                const auto *Fn =
                    dyn_cast<Function>(E->stripPointerCasts());
                if (Fn) {
                  if (haveCtx) {
                    std::string K = SN + "+" + std::to_string(EO);
                    addPop(K, Fn->getName().str(), 0);
                    if (!GV.isConstant()) initNonConst.insert(K);
                    initAttrCount[GVc]++;
                  }
                } else {
                  // obj channel: initializer slot holding &ops_global
                  if (haveCtx)
                    if (auto M = objMemberOf(E, DL))
                      objRegs[SN + "+" + std::to_string(EO)].insert(*M);
                  walk(E, SN, EO, haveCtx);
                }
              }
            } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
              uint64_t es = DL.getTypeAllocSize(
                  CA->getType()->getElementType());
              for (unsigned e = 0; e < CA->getNumOperands(); e++)
                walk(cast<Constant>(CA->getOperand(e)), PN, PO + e * es,
                     haveP);
            }
          };
      walk(GV.getInitializer(), "", 0, false);
    }
  }

  // Loose tables: fn slots the initializer walk could not attribute
  // to any named key (top-level literal-typed constants — the 7
  // static x86_pmu instances at 5.18, bfd's cache_iovec) plus const
  // sources copied without destination layout context. Witnessed by
  // use at apply; NEVER silently dropped again.
  std::set<const GlobalVariable *> looseTables(looseCopied);
  for (const auto &[GVt, slots] : fnTables)
    if (initAttrCount[GVt] < slots.size()) looseTables.insert(GVt);
  if (!looseTables.empty())
    errs() << "RegFieldGap: " << looseTables.size()
           << " loose fn-tables (initializer fn slots with no named-key "
              "attribution; witnessed by use at apply)\n";

  // Copy-edge closure (control-struct relays): populations and
  // openness both flow along key-to-key copies.
  for (bool changed = true; changed;) {
    changed = false;
    for (auto &[dst, srcs] : copyIn) {
      auto &D = regs[dst];
      size_t before = D.size();
      bool wasOpen = open.count(dst);
      for (const auto &s : srcs) {
        auto ri = regs.find(s);
        if (ri != regs.end() && !ri->second.empty()) {
          D.insert(ri->second.begin(), ri->second.end());
          auto &sc = popSrc[dst][3];
          sc.insert(ri->second.begin(), ri->second.end());
        } else if (!open.count(s)) {
          // Copy-in from a key with NO witnessed population:
          // evidence-free is not enumerable (the name-keyed census
          // cannot distinguish "never stored" from "stored through a
          // spelling it cannot see" — libjpeg installs sep_upsample
          // into my_upsampler+var, blocked, then relays
          // jpeg_upsampler+8 -> jpeg_d_post_controller+8). The dest
          // table would silently miss the relayed value: refuse.
          open.insert(dst);
        }
        if (open.count(s)) open.insert(dst);
      }
      if (D.size() != before || (!wasOpen && open.count(dst)))
        changed = true;
    }
  }
  // Obj-population copy closure (mirrors the fn closure above).
  for (bool changed = true; changed;) {
    changed = false;
    for (auto &[dst, srcs] : objCopyIn) {
      auto &D = objRegs[dst];
      size_t before = D.size();
      bool wasOpen = objOpen.count(dst);
      for (const auto &s : srcs) {
        auto ri = objRegs.find(s);
        if (ri != objRegs.end() && !ri->second.empty())
          D.insert(ri->second.begin(), ri->second.end());
        else if (!objOpen.count(s)) {
          // Mirror of the fn closure's empty-source refusal.
          objOpen.insert(dst);
          if (!objOpenWhy.count(dst))
            objOpenWhy[dst] = "copy<-" + s + "(empty population)";
        }
        if (objOpen.count(s)) {
          objOpen.insert(dst);
          if (!objOpenWhy.count(dst) && objOpenWhy.count(s))
            objOpenWhy[dst] = "copy<-" + s + "(" + objOpenWhy[s] + ")";
        }
      }
      if (D.size() != before || (!wasOpen && objOpen.count(dst)))
        changed = true;
    }
  }

  // Dispatch side: field-load-fed icalls with their resolved fanout.
  struct Disp {
    size_t sites = 0, maxFan = 0;
    uint64_t sumFan = 0;
    std::string sample;
    std::set<std::string> outers; // two-level dispatch: the struct
                                  // holding the ops POINTER — its cells
                                  // carry the pooled conflation, so a
                                  // flagged inner key must bring the
                                  // outer type into the nexus list too
                                  // (bpf_link for bpf_link_ops)
    std::vector<const CallBase *> readers; // sites, for channel apply
    std::set<std::string> outerKeys; // full outer field keys — their
                                     // populations feed this key's
                                     // table at apply (witness-by-use)
    std::set<const GlobalVariable *> baseGlobals; // direct-global bases
    bool unresolvedBase = false; // some reader's instance is not
                                 // enumerable (arg/phi/call base): the
                                 // key absorbs ALL loose tables
  };
  std::map<std::string, Disp> disp;
  for (auto *CB : icallsInIROrder(Ctx)) {
    auto ci = Ctx->Callees.find(CB);
    if (ci == Ctx->Callees.end() || ci->second.empty()) continue;
    const auto *LI =
        dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
    if (!LI) continue;
    const DataLayout &DL = LI->getModule()->getDataLayout();
    std::string Key = deepKey(LI->getPointerOperand(), DL);
    if (Key.empty()) continue;
    Disp &D = disp[Key];
    D.sites++;
    D.sumFan += ci->second.size();
    D.maxFan = std::max(D.maxFan, (size_t)ci->second.size());
    if (D.sample.empty())
      D.sample = CB->getFunction()->getName().str();
    D.readers.push_back(CB);
    const Value *B = LI->getPointerOperand()->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(B))
      B = G->getPointerOperand()->stripPointerCasts();
    if (const auto *L1 = dyn_cast<LoadInst>(B)) {
      std::string OK = deepKey(L1->getPointerOperand(), DL);
      size_t p = OK.find('+');
      if (p != std::string::npos && D.outers.size() < 4)
        D.outers.insert(OK.substr(0, p));
      if (!OK.empty())
        D.outerKeys.insert(OK);
      else
        D.unresolvedBase = true;
    } else if (const auto *BG = dyn_cast<GlobalVariable>(B)) {
      D.baseGlobals.insert(BG);
    } else if (!isa<AllocaInst>(B)) {
      // arg/phi/select/call bases: the instance behind this reader
      // is not enumerable — coarse witnessing at apply. (An alloca
      // is a local instance whose slot writes are type-keyed stores
      // or copies, both witnessed above.)
      D.unresolvedBase = true;
    }
  }

  // Rank by fanout; auto-suggest narrow closed-enough populations
  // under wide fanout. Thresholds are report-tuning, not soundness.
  struct Row {
    const std::string *key;
    size_t pop;
    bool op, flag;
    const Disp *d;
  };
  std::vector<Row> rows;
  std::set<std::string> suggest;
  size_t witnessed = 0, flagged = 0;
  for (auto &[K, D] : disp) {
    size_t pop = 0;
    auto ri = regs.find(K);
    if (ri != regs.end()) pop = ri->second.size();
    if (pop) witnessed++;
    bool flag = pop > 0 && pop <= 32 && D.maxFan >= 24 &&
                D.maxFan >= 4 * pop;
    if (flag) {
      flagged++;
      // --cfl-nexus-fields takes bare names and prepends "struct.";
      // non-struct-prefixed keys (unions) are not expressible there.
      StringRef sn = StringRef(K).take_front(K.find('+'));
      if (sn.consume_front("struct."))
        suggest.insert(sn.str());
      for (const std::string &O : D.outers) {
        StringRef on(O);
        if (on.consume_front("struct."))
          suggest.insert(on.str());
      }
    }
    rows.push_back({&K, pop, open.count(K) != 0, flag, &D});
  }
  std::sort(rows.begin(), rows.end(), [](const Row &A, const Row &B) {
    if (A.flag != B.flag) return A.flag;
    return A.d->maxFan > B.d->maxFan;
  });
  errs() << "RegFieldGap: " << disp.size() << " dispatch field keys ("
         << witnessed << " with witnessed population), " << flagged
         << " flagged across " << suggest.size() << " structs\n";
  size_t shown = 0;
  for (const Row &R : rows) {
    if (shown++ >= 60) break;
    errs() << "RegFieldGap: " << (R.flag ? "FLAG " : "     ") << *R.key
           << " stored=" << R.pop << (R.op ? "+" : "")
           << " sites=" << R.d->sites << " fanout max=" << R.d->maxFan
           << " avg=" << (R.d->sumFan / R.d->sites) << " dispatch@"
           << R.d->sample;
    {
      // Closure-blocker attribution: WHY a flagged key was not applied
      // — the worklist decision data (2,267 flagged-unapplied at 5.18
      // fs carry the residual fat tail; fanout 4,648 vs pop 2-9).
      const std::string SN2 = R.key->substr(0, R.key->find('+'));
      std::string why;
      if (R.op) why += " open-stores";
      if (hazAtomic.count(*R.key)) why += " atomic";
      if (hazEscape.count(*R.key)) why += " slot-escape";
      if (hazBulk.count(SN2)) why += " bulk-copy";
      if (R.key->find("+var") != std::string::npos) why += " var-off";
      if (!why.empty()) errs() << " blocked:[" << why << " ]";
    }
    auto ri = regs.find(*R.key);
    if (ri != regs.end()) {
      errs() << " fns:";
      size_t n = 0;
      for (const auto &N : ri->second) {
        if (n++ >= 3) break;
        errs() << " " << N;
      }
    }
    errs() << "\n";
  }
  if (!suggest.empty()) {
    errs() << "RegFieldGap SUGGEST --cfl-nexus-fields=";
    bool first = true;
    for (const auto &S : suggest) {
      errs() << (first ? "" : ",") << S;
      first = false;
    }
    errs() << "\n";
  }

  // --cfl-regfield-apply: auto-generated identity channels for keys
  // whose registration population is machine-certified CLOSED — every
  // mutation path classified (witnessed stores/hops/copies/
  // initializers), zero hazards (unwitnessed stores, atomics, bulk
  // copies, escaping slot addresses). Resolution at the key's reader
  // sites intersects with the table: monotone removal only (-N/+0 by
  // construction), certified per key in the ledger below. OPEN keys
  // are never touched — they remain report material for the manual
  // channel pipeline. Residual assumption (shared with the hand-built
  // channels): a write reaching the slot without any typed GEP to the
  // struct (raw-arithmetic punning) is invisible to the certifier.
  if (!CFLRegFieldApply) return;
  size_t chKeys = 0, chSites = 0, chRemoved = 0;
  for (auto &[K, D] : disp) {
    auto ri = regs.find(K);
    if (ri == regs.end() || ri->second.empty()) continue;
    const std::string SN = K.substr(0, K.find('+'));
    const bool closed = !open.count(K) && !hazAtomic.count(K) &&
                        !hazEscape.count(K) && !hazBulk.count(SN) &&
                        K.find("+var") == std::string::npos;
    if (!closed) continue;
    // WITNESS-BY-USE enrichment (fix B): before intersecting, the
    // table absorbs every enumerable instance whose IR spelling
    // carries no type name — loose tables reachable through this
    // key's reader bases (population members behind the outer field
    // keys, direct global bases), and, for readers whose base is not
    // enumerable, ALL loose tables. Purely additive (over-inclusion
    // is sound); named-typed instances are already witnessed by the
    // initializer walk. Offset-blind on purpose: a loose member may
    // be an array of tables whose element geometry the key cannot
    // see — precision costs bloat, never a dropped true pair.
    {
      size_t enriched = 0;
      const std::string &KK = K; // lambdas cannot capture the binding
      auto addLoose = [&](const GlobalVariable *GVl) {
        if (!looseTables.count(GVl)) return;
        auto ti2 = fnTables.find(GVl);
        if (ti2 == fnTables.end()) return;
        if (!GVl->isConstant()) initNonConst.insert(KK);
        for (const auto &[fo, Fn] : ti2->second)
          if (ri->second.insert(Fn->getName().str()).second) {
            popSrc[KK][3].insert(Fn->getName().str());
            enriched++;
          }
      };
      // An OPEN or hazarded outer key means this key's instance set
      // is NOT enumerable through the population (bfd->xvec: the vec
      // addresses arrive as LOADED pointers from a pointer array, so
      // membership is unwitnessed) — same coarse absorption as an
      // unresolved base. Only a hazard-free population enumerates.
      bool coarse = D.unresolvedBase;
      for (const std::string &OK : D.outerKeys) {
        const std::string OSN = OK.substr(0, OK.find('+'));
        auto oi2 = objRegs.find(OK);
        // No evidence is NOT clean: an outer key with an EMPTY
        // population and no openness record means no store was ever
        // witnessed under this spelling — either the field is fed
        // through a spelling this key cannot see (LLVM unifies
        // isomorphic structs per-TU under one name: bfd appeared as
        // aout_data_struct in binutils) or the base is dead. Both
        // mean the instance set is not enumerable here.
        if (objOpen.count(OK) || hazAtomic.count(OK) ||
            hazEscape.count(OK) || objHazBulk.count(OSN) ||
            OK.find("+var") != std::string::npos ||
            oi2 == objRegs.end() || oi2->second.empty())
          coarse = true;
        if (oi2 == objRegs.end()) continue;
        for (const auto &[GV0, mbase, mstride] : oi2->second) {
          (void)mbase;
          (void)mstride;
          const GlobalVariable *GVm = GV0;
          if (const auto *GC2 =
                  dyn_cast_or_null<GlobalVariable>(canonChainKey(GVm)))
            GVm = GC2;
          addLoose(GVm);
        }
      }
      for (const GlobalVariable *BG0 : D.baseGlobals) {
        const GlobalVariable *BG = BG0;
        if (const auto *GC2 =
                dyn_cast_or_null<GlobalVariable>(canonChainKey(BG)))
          BG = GC2;
        addLoose(BG);
      }
      if (coarse)
        for (const GlobalVariable *LT : looseTables) addLoose(LT);
      if (enriched && CFLRegFieldAudit)
        errs() << "RegFieldChannel: ENRICH " << K << " +" << enriched
               << " loose-table fns"
               << (coarse ? " (coarse: unresolved base / open outer)" : "")
               << "\n";
    }
    size_t rem = 0, kept = 0;
    for (const CallBase *CB : D.readers) {
      auto ci = Ctx->Callees.find(CB);
      if (ci == Ctx->Callees.end()) continue;
      FuncSet keep;
      for (const Function *F : ci->second)
        if (ri->second.count(F->getName().str()))
          keep.insert(F);
      if (!CFLRegFieldWatch.empty()) {
        // Attribution instrument: which key removes a watched fn at
        // which site (GT-loss forensics; see 2026-08-25 gate).
        StringRef spec(CFLRegFieldWatch);
        for (const Function *F : ci->second) {
          if (keep.count(F)) continue;
          StringRef rest = spec;
          while (!rest.empty()) {
            auto [head, tail] = rest.split(',');
            if (!head.empty() && F->getName() == head)
              errs() << "RegFieldWatch: key " << K << " removes "
                     << F->getName() << " at "
                     << CB->getFunction()->getName() << "\n";
            rest = tail;
          }
        }
      }
      if (CFLFilterLedger)
        for (const Function *F : ci->second)
          if (!keep.count(F)) ledger("regfield-key", K, CB, F);
      rem += ci->second.size() - keep.size();
      kept += keep.size();
      ci->second = keep;
    }
    if (rem == 0) continue;
    chKeys++;
    chSites += D.readers.size();
    chRemoved += rem;
    errs() << "RegFieldChannel: CLOSED " << K << " table="
           << ri->second.size() << " sites=" << D.readers.size()
           << " -" << rem << "/+0 kept=" << kept << "\n";
    if (CFLRegFieldAudit) {
      // Provenance certificate per applied key: how each table entry
      // was witnessed, and the risk class. GREEN = every entry from a
      // CONST global's initializer (rodata-immutable — closedness is
      // structural). YELLOW = store/arg-hop-witnessed or a non-const
      // initializer (closedness rests on the hazard counters).
      // ORANGE = table depends on copy-closure (longest inference
      // chain — audit these first).
      auto &S = popSrc[K];
      const bool nonC = initNonConst.count(K) != 0;
      const char *cls = !S[3].empty()
                            ? "ORANGE"
                            : (!S[1].empty() || !S[2].empty() || nonC)
                                  ? "YELLOW"
                                  : "GREEN";
      errs() << "RegFieldAudit: " << cls << " " << K << " init="
             << S[0].size() << (nonC ? "(nonconst)" : "")
             << " store=" << S[1].size() << " hop=" << S[2].size()
             << " copy=" << S[3].size() << " table:";
      size_t n = 0;
      for (const auto &N : ri->second) {
        if (n++ >= 40) { errs() << " ..."; break; }
        errs() << " " << N;
      }
      errs() << "\n";
    }
  }
  errs() << "RegFieldChannel: applied " << chKeys << " closed keys, "
         << chSites << " sites, -" << chRemoved << "/+0 pairs; RESIDUAL "
         << g_regfieldBarePtrFnStores
         << " fn stores through bare pointers (unattributable to any "
         << "key — the certifier's stated blind spot)\n";

  // OBJECT-population apply (--cfl-regfield-obj): two-level dispatch
  // sites, INCLUDING the GEP-less slot-0 class. Site claim: the fptr
  // load's pointer is inner-offset (0 with no GEP, or all-constant
  // GEP offsets) into a value LOADED from a certified outer key.
  // Table = fn at that inner offset in each certified ops GLOBAL's
  // initializer — slot-exact is justified because "no GEP" IS a
  // certified offset derivation (exactly 0); ambiguous chains skip
  // (fail-safe). Writable (non-const) population members refuse the
  // key: their slots are runtime-patchable (mptcp af_ops pattern).
  // Soundness schema: proof/lean Channels.objclamp_sound.
  if (CFLRegFieldObj) {
    auto fnAtInitOffset = [](const GlobalVariable *GV,
                             uint64_t off) -> const Function * {
      const DataLayout &DL = GV->getParent()->getDataLayout();
      const Constant *C = GV->getInitializer();
      while (C) {
        if (const auto *CSt = dyn_cast<ConstantStruct>(C)) {
          const StructLayout *SL = DL.getStructLayout(CSt->getType());
          unsigned e = SL->getElementContainingOffset(off);
          off -= SL->getElementOffset(e);
          C = CSt->getOperand(e);
        } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
          uint64_t es =
              DL.getTypeAllocSize(CA->getType()->getElementType());
          if (!es) return nullptr;
          if (off / es >= CA->getNumOperands()) return nullptr;
          C = CA->getOperand(off / es);
          off %= es;
        } else {
          break;
        }
      }
      if (!C || off != 0) return nullptr;
      return dyn_cast<Function>(C->stripPointerCasts());
    };
    struct ObjLedger {
      size_t sites = 0, rem = 0, kept = 0, objs = 0;
    };
    std::map<std::string, ObjLedger> led; // "key slot=N"
    size_t objSkipOpen = 0, objSkipNonConst = 0;
    for (auto *CB : icallsInIROrder(Ctx)) {
      auto ci = Ctx->Callees.find(CB);
      if (ci == Ctx->Callees.end() || ci->second.empty()) continue;
      const auto *L1 =
          dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
      if (!L1) continue;
      const DataLayout &DLm = L1->getModule()->getDataLayout();
      const Value *P = L1->getPointerOperand()->stripPointerCasts();
      APInt off(DLm.getIndexSizeInBits(0), 0);
      bool okOff = true;
      uint64_t varElemSize = 0; // one variable ARRAY index allowed:
                                // element stride for rodata-table reads
      while (const auto *G = dyn_cast<GEPOperator>(P)) {
        // Per-index walk (accumulateConstantOffset can partially
        // mutate on failure): const steps accumulate; exactly ONE
        // variable index stepping an ARRAY is tolerated (rodata table
        // dispatch: fn = load(gep(tbl, idx))).
        bool bad2 = false;
        for (auto GTI = gep_type_begin(G), E = gep_type_end(G);
             GTI != E; ++GTI) {
          if (const auto *CI2 = dyn_cast<ConstantInt>(GTI.getOperand())) {
            if (StructType *ST2 = GTI.getStructTypeOrNull())
              off += APInt(off.getBitWidth(),
                           DLm.getStructLayout(ST2)->getElementOffset(
                               CI2->getZExtValue()));
            else
              off += APInt(off.getBitWidth(),
                           (uint64_t)(CI2->getSExtValue() *
                                      (int64_t)DLm.getTypeAllocSize(
                                          GTI.getIndexedType())));
          } else if (!GTI.getStructTypeOrNull() && varElemSize == 0) {
            varElemSize = DLm.getTypeAllocSize(GTI.getIndexedType());
            if (!varElemSize) { bad2 = true; break; }
          } else {
            bad2 = true; // second var index / var struct step
            break;
          }
        }
        if (bad2) {
          okOff = false;
          break;
        }
        P = G->getPointerOperand()->stripPointerCasts();
      }
      if (!okOff || off.isNegative()) continue;
      // Rodata-table dispatch: root is a CONST global read through at
      // most one variable array index — the answer is bounded by the
      // initializer contents, no closure certificate needed (pure
      // rodata read; GREEN by construction). Covers the slot-0
      // array-element class invisible to both fn keys (no struct GEP
      // step for field 0) and the load-rooted obj path.
      if (const auto *RG = dyn_cast<GlobalVariable>(P)) {
        const GlobalVariable *RGc = RG;
        if (const auto *RC =
                dyn_cast_or_null<GlobalVariable>(canonChainKey(RG)))
          RGc = RC;
        if (!RGc->isConstant() || !RGc->hasInitializer()) continue;
        const uint64_t innerOff = off.getZExtValue();
        if (varElemSize && innerOff >= varElemSize)
          continue; // const part must be the within-element field
        std::set<int64_t> fnOffs;
        walkInitFnOffsets(RGc->getInitializer(), 0,
                          RGc->getParent()->getDataLayout(), fnOffs);
        FuncSet table;
        for (int64_t fo : fnOffs) {
          const uint64_t sel =
              varElemSize ? (uint64_t)fo % varElemSize : (uint64_t)fo;
          if (sel != innerOff) continue;
          if (const Function *Fn = fnAtInitOffset(RGc, (uint64_t)fo))
            table.insert(getFuncDef(const_cast<Function *>(Fn)));
        }
        if (table.empty()) continue;
        FuncSet keep;
        for (const Function *F : ci->second)
          if (table.count(getFuncDef(const_cast<Function *>(F))))
            keep.insert(F);
        if (ci->second.size() == keep.size()) continue;
        if (CFLFilterLedger)
          for (const Function *F : ci->second)
            if (!keep.count(F))
              ledger("regfield-rodata",
                     std::string("RODATA:") + RGc->getName().str() +
                         " slot=" + std::to_string(innerOff),
                     CB, F);
        auto &LG = led[std::string("RODATA:") + RGc->getName().str() +
                       (varElemSize ? "[var]" : "") + " slot=" +
                       std::to_string(innerOff)];
        LG.sites++;
        LG.rem += ci->second.size() - keep.size();
        LG.kept += keep.size();
        LG.objs = 1;
        ci->second = keep;
        continue;
      }
      const auto *L2 = dyn_cast<LoadInst>(P);
      if (!L2) continue;
      std::string OK = deepKey(L2->getPointerOperand(), DLm);
      if (OK.empty()) continue;
      auto oi = objRegs.find(OK);
      if (oi == objRegs.end() || oi->second.empty()) continue;
      const std::string SN = OK.substr(0, OK.find('+'));
      const bool closed = !objOpen.count(OK) && !hazAtomic.count(OK) &&
                          !hazEscape.count(OK) && !objHazBulk.count(SN) &&
                          OK.find("+var") == std::string::npos;
      if (!closed) {
        objSkipOpen++;
        if (CFLRegFieldAudit)
          errs() << "RegFieldObj: SKIP " << OK << " objs="
                 << oi->second.size() << " reason=["
                 << (objOpen.count(OK)
                         ? (" open@" + (objOpenWhy.count(OK)
                                            ? objOpenWhy[OK]
                                            : std::string("?")))
                         : "")
                 << (hazAtomic.count(OK) ? " atomic" : "")
                 << (hazEscape.count(OK) ? " escape" : "")
                 << (objHazBulk.count(SN) ? " bulk" : "")
                 << (OK.find("+var") != std::string::npos ? " var" : "")
                 << " ]\n";
        continue;
      }
      const uint64_t innerOff = off.getZExtValue();
      FuncSet table;
      bool bad = false;
      for (const auto &[GV0, mbase, mstride] : oi->second) {
        const GlobalVariable *GV = GV0;
        // Cross-TU declarations must canonicalize to their defining
        // TU's global (the extern-hub/98bdfd5 lesson): an `external
        // constant` decl has no initializer and would misread as a
        // writable member.
        if (const auto *GC =
                dyn_cast_or_null<GlobalVariable>(canonChainKey(GV)))
          GV = GC;
        if (!GV->isConstant() || !GV->hasInitializer()) {
          bad = true; // writable ops object: slots patchable at runtime
          break;
        }
        if (mstride && varElemSize) {
          bad = true; // var on BOTH member and dispatch side: v1 refuses
          break;
        }
        // Effective slot rule (member (GV, base, mstride) composed
        // with dispatch innerOff/varElemSize): with a stride on either
        // side the slot is (fo - base) mod stride == innerOff mod
        // stride (union over elements — the stride-union lesson,
        // GT 79->90); without, exactly base + innerOff.
        const uint64_t stride2 = mstride ? mstride : varElemSize;
        if (stride2 == 0) {
          if (const Function *Fn = fnAtInitOffset(
                  GV, (uint64_t)(mbase + (int64_t)innerOff)))
            table.insert(getFuncDef(const_cast<Function *>(Fn)));
        } else {
          std::set<int64_t> fnOffs2;
          walkInitFnOffsets(GV->getInitializer(), 0,
                            GV->getParent()->getDataLayout(), fnOffs2);
          for (int64_t fo : fnOffs2)
            if (fo >= mbase &&
                (uint64_t)(fo - mbase) % stride2 == innerOff % stride2)
              if (const Function *Fn = fnAtInitOffset(GV, (uint64_t)fo))
                table.insert(getFuncDef(const_cast<Function *>(Fn)));
        }
      }
      if (bad) {
        objSkipNonConst++;
        continue;
      }
      FuncSet keep;
      for (const Function *F : ci->second)
        if (table.count(getFuncDef(const_cast<Function *>(F))))
          keep.insert(F);
      if (ci->second.size() == keep.size()) continue;
      if (!CFLRegFieldWatch.empty()) {
        StringRef spec(CFLRegFieldWatch);
        for (const Function *F : ci->second) {
          if (keep.count(F)) continue;
          StringRef rest = spec;
          while (!rest.empty()) {
            auto [head, tail] = rest.split(',');
            if (!head.empty() && F->getName() == head)
              errs() << "RegFieldWatch: objkey " << OK << " slot="
                     << innerOff << " removes " << F->getName() << " at "
                     << CB->getFunction()->getName() << "\n";
            rest = tail;
          }
        }
      }
      if (CFLFilterLedger)
        for (const Function *F : ci->second)
          if (!keep.count(F))
            ledger("regfield-obj",
                   OK + " slot=" + std::to_string(innerOff), CB, F);
      auto &LG = led[OK + " slot=" + std::to_string(innerOff)];
      LG.sites++;
      LG.rem += ci->second.size() - keep.size();
      LG.kept += keep.size();
      LG.objs = oi->second.size();
      ci->second = keep;
    }
    size_t tKeys = 0, tSites = 0, tRem = 0;
    for (auto &[K, L] : led) {
      tKeys++;
      tSites += L.sites;
      tRem += L.rem;
      errs() << "RegFieldObj: CLOSED " << K << " objs=" << L.objs
             << " sites=" << L.sites << " -" << L.rem << "/+0 kept="
             << L.kept;
      {
        const std::string bare = K.substr(0, K.find(' '));
        auto ci2 = objCopySameOff.find(bare);
        if (ci2 != objCopySameOff.end())
          errs() << " [ASSUME same-off-copy x" << ci2->second << "]";
        auto ci3 = objCopyListAnchor.find(bare);
        if (ci3 != objCopyListAnchor.end())
          errs() << " [ASSUME list-anchored-copy x" << ci3->second << "]";
      }
      errs() << "\n";
    }
    errs() << "RegFieldObj: applied " << tKeys << " (key,slot) channels, "
           << tSites << " sites, -" << tRem << "/+0 pairs; skipped "
           << objSkipOpen << " open/hazard keys, " << objSkipNonConst
           << " with writable population members\n";
  }
}

// ---- Tracepoint keyed channels (task #35, --cfl-tracepoint-keys) ----
// Per-key channel = two synthetic JUNCTION value nodes (fn, data), NOT
// memory cells. v1 used fnCell = deref(@__tracepoint_X) and was
// byte-identical to the pin at kernel scale (-0/+59-flap): the tp
// structs' deref cells are inside the giant cluster there (tp pointers
// travel through the __tracepoint_ptrs section arrays and iterator
// formals, merging every tp's cells), so reading the channel imported
// the whole quotient even though the channel CONTENT was exact.
// Junction nodes are referenced by nothing but the model's own edges —
// no pointer ever names them, no cell join can absorb them. With the
// registration bodies and the iterator funcs-loads severed, plain
// a-edges probe -> J_X -> called-operand ARE the exact dispatch.
// Keyed by the key's CANONICAL NODE, not the GlobalVariable*: each TU
// has its own declaration object for an extern tracepoint, and all of
// them must land on one junction (getRepNodeForValue resolves decl ->
// def through the GUID linking).
static boost::unordered_flat_map<NodeIndex, std::pair<NodeIndex, NodeIndex>>
    g_tpKeyJunctionMap;

std::pair<NodeIndex, NodeIndex>
CallGraphPass::tracepointJunctions(const GlobalVariable *KeyGV) {
  NodeIndex keyN = getRepNodeForValue(KeyGV);
  if (keyN == AndersNodeFactory::InvalidIndex) {
    g_tpKeyUnmapped++; // LOUD in the LEDGER — census says this is empty
    keyN = getCanonicalNode(NF.createValueNode(KeyGV));
  } else {
    keyN = getCanonicalNode(keyN);
  }
  auto it = g_tpKeyJunctionMap.find(keyN);
  if (it != g_tpKeyJunctionMap.end())
    return it->second;
  NodeIndex fnJ = getCanonicalNode(NF.createValueNode(nullptr));
  NodeIndex dataJ = getCanonicalNode(NF.createValueNode(nullptr));
  auto p = std::make_pair(fnJ, dataJ);
  g_tpKeyJunctionMap.emplace(keyN, p);
  return p;
}

void CallGraphPass::bindTracepointProbe(const GlobalVariable *KeyGV,
                                        const Value *ProbeV,
                                        const Value *DataV,
                                        bool fromWalker) {
  auto [fnJ, dataJ] = tracepointJunctions(KeyGV);
  (void)fnJ; // v3: fn plane is answer-level, no graph edge (see above)
  NodeIndex keyN = getRepNodeForValue(KeyGV);
  keyN = keyN == AndersNodeFactory::InvalidIndex
             ? AndersNodeFactory::InvalidIndex
             : getCanonicalNode(keyN);
  if (const auto *PF = dyn_cast<Function>(ProbeV)) {
    if (keyN != AndersNodeFactory::InvalidIndex) {
      g_tpKeyProbes[keyN].insert(getFuncDef(const_cast<Function *>(PF)));
      (fromWalker ? g_tpKeyMediatorBinds : g_tpKeyConstBinds)++;
    }
  } else if (keyN != AndersNodeFactory::InvalidIndex) {
    // dynamic probe value: the table is incomplete for this key — its
    // dispatch sites fall back to the graph path, counted LOUDLY
    // (census: zero such registrations at kernel scale)
    g_tpKeyHasDynProbe.insert(keyN);
    g_tpKeyDynProbe++;
  }
  if (DataV && !shouldSkipValue(DataV)) {
    NodeIndex dataN = getRepNodeForValue(DataV);
    if (dataN != AndersNodeFactory::InvalidIndex &&
        !NF.isSpecialNode(dataN))
      addAssignmentEdge(dataN, dataJ);
  }
}

// Struct-mediated registrations: trace_event_reg registers
// call->class->probe / ->perf_probe on call->tp; bpf_probe_register
// registers btp->bpf_func on btp->tp. Both (key, probe) pairs exist
// as static-initializer co-residents — trace_event_call references
// its class (probe fns live in the class initializer) and its
// tracepoint; bpf_raw_event_map holds {tp, bpf_func} directly. The
// registrar callsites themselves are severed like every family site;
// the pairs bound here replace them. Probe-fn filters are the
// macro-generated prefixes; anything else in a class initializer is
// counted, not bound.
void CallGraphPass::bindTracepointMediatorPairs() {
  auto collectRefs = [](const Constant *Init,
                        SmallVectorImpl<const GlobalValue *> &out) {
    SmallVector<const Constant *, 16> wl{Init};
    SmallPtrSet<const Constant *, 32> seen;
    while (!wl.empty()) {
      const Constant *C = wl.pop_back_val();
      if (!seen.insert(C).second)
        continue;
      if (const auto *GVal = dyn_cast<GlobalValue>(C)) {
        out.push_back(GVal);
        continue;
      }
      for (const Use &U : C->operands())
        if (const auto *OC = dyn_cast<Constant>(U))
          wl.push_back(OC);
    }
  };
  boost::unordered_flat_set<const GlobalVariable *> keySet;
  for (auto &mp : Ctx->Modules) {
    for (const GlobalVariable &GV : mp.first->globals()) {
      if (!GV.hasInitializer())
        continue;
      // Only the two registrar-container shapes may bind pairs. Without
      // this, @llvm.used (which references every tracepoint, class and
      // probe in the TU) bound ALL of a TU's probes to whichever
      // tracepoint ref came first — wrong-proto cross-binds surfaced as
      // isCompatible rejections, same-template ones silently inflated
      // one key per TU.
      const auto *GVT = dyn_cast<StructType>(GV.getValueType());
      const bool isEventCall = GVT && GVT->hasName() &&
                               GVT->getName().contains("trace_event_call");
      // bpf maps are union-wrapped (%union.anon.N { %struct.bpf_raw_
      // event_map }) so the type name is invisible at the top level —
      // the placement section is the semantic anchor.
      const bool isBpfMap =
          GV.getSection() == "__bpf_raw_tp_map" ||
          (GVT && GVT->hasName() &&
           GVT->getName().contains("bpf_raw_event_map"));
      if (!isEventCall && !isBpfMap)
        continue;
      SmallVector<const GlobalValue *, 16> refs;
      collectRefs(GV.getInitializer(), refs);
      const GlobalVariable *tpKey = nullptr;
      for (const GlobalValue *R : refs)
        if (R->getName().starts_with("__tracepoint_")) {
          tpKey = dyn_cast<GlobalVariable>(R);
          break;
        }
      if (!tpKey)
        continue;
      bool bound = false;
      // bpf_raw_event_map shape: {tp, __bpf_trace_X} in one initializer
      if (isBpfMap)
        for (const GlobalValue *R : refs)
          if (const auto *PF = dyn_cast<Function>(R)) {
            if (PF->getName().starts_with("__bpf_trace_")) {
              bindTracepointProbe(tpKey, PF, nullptr, /*fromWalker=*/true);
              bound = true;
            } else {
              g_tpKeyClassFnSkipped++;
            }
          }
      // trace_event_call shape: class global carries the probe fns
      for (const GlobalValue *R : refs) {
        const auto *ClsGV = dyn_cast<GlobalVariable>(R);
        if (!ClsGV || ClsGV == &GV || ClsGV == tpKey ||
            !ClsGV->hasInitializer())
          continue;
        const auto *ST = dyn_cast<StructType>(ClsGV->getValueType());
        if (!ST || !ST->hasName() ||
            !ST->getName().contains("trace_event_class"))
          continue;
        SmallVector<const GlobalValue *, 16> crefs;
        collectRefs(ClsGV->getInitializer(), crefs);
        for (const GlobalValue *CR : crefs)
          if (const auto *PF = dyn_cast<Function>(CR)) {
            StringRef pn = PF->getName();
            if (pn.starts_with("trace_event_raw_event_") ||
                pn.starts_with("perf_trace_")) {
              bindTracepointProbe(tpKey, PF, nullptr, /*fromWalker=*/true);
              bound = true;
            } else if (pn != "trace_event_reg" &&
                       pn != "trace_event_raw_init") {
              g_tpKeyClassFnSkipped++;
            }
          }
      }
      if (bound && keySet.insert(tpKey).second)
        g_tpWalkerKeys.push_back(tpKey);
    }
  }
  CG_LOG("TracepointKeys: walker bound " << g_tpKeyMediatorBinds
         << " mediator (key,probe) pairs over " << g_tpWalkerKeys.size()
         << " keys (" << g_tpKeyClassFnSkipped
         << " non-probe initializer fns skipped, " << g_tpKeyUnmapped
         << " unmapped keys)\n");
}
