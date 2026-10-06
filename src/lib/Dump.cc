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

// Dump.cc: outputs and dumps: call-graph JSON, raw graph, fn-pointer offsets.
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

// Raw constraint graph for offline reference solvers: nodes are the
// factory's own indices (pre-presolve; build-time merges are listed
// separately in .raw.canon so a reader can apply or ignore them), GEP
// edges carry their exact byte offset, and the indirect-call sites and
// address-taken functions are tabulated so the reader can do its own
// resolution and wiring instead of inheriting this solver's.
void CallGraphPass::dumpRawGraph(const std::string &prefix) {
  const std::string pfx = prefix + ".raw";
  std::error_code e1, e2, e3, e4, e5;
  raw_fd_ostream nodesOut(pfx + ".nodes", e1);
  raw_fd_ostream edgesOut(pfx + ".edges", e2);
  raw_fd_ostream canonOut(pfx + ".canon", e3);
  raw_fd_ostream icallsOut(pfx + ".icalls", e4);
  raw_fd_ostream funcsOut(pfx + ".funcs", e5);
  if (e1 || e2 || e3 || e4 || e5) {
    WARNING("FlowsTo: cannot write raw graph dump " << pfx << "\n");
    return;
  }
  const DataLayout &DL0 = Ctx->Modules.front().first->getDataLayout();
  boost::unordered_flat_map<NodeIndex, NodeIndex> cellPtr;
  for (auto &[p, d] : NF.getDerefMap()) cellPtr[d] = p;
  auto rawName = [&](NodeIndex m) -> std::string {
    std::string pre;
    for (int lvl = 0; lvl < 3 && NF.isDereferenceNode(m); lvl++) {
      auto it = cellPtr.find(m);
      if (it == cellPtr.end()) return pre + "<deref#" + std::to_string(m) + ">";
      pre += "*";
      m = it->second;
    }
    const Value *V = NF.getValueForNode(m);
    if (!V) {
      auto pit = g_opaqueProvenance.find(m);
      if (pit != g_opaqueProvenance.end()) return pre + pit->second;
      return pre + (NF.isObjectNode(m) ? "<obj>" : "<syn>");
    }
    if (const auto *A = dyn_cast<Argument>(V))
      return pre + (A->getParent()->getName() + "::arg" + Twine(A->getArgNo())).str();
    if (const auto *I = dyn_cast<Instruction>(V)) {
      std::string s = (I->getFunction()->getName() + "::" + I->getOpcodeName()).str();
      if (const auto *CB = dyn_cast<CallBase>(I)) {
        const Function *CF = CB->getCalledFunction();
        s += ":" + (CF ? CF->getName().str() : std::string("<icall>"));
      }
      return pre + s;
    }
    if (V->hasName()) return pre + V->getName().str();
    if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
      const Value *base = CE;
      while (const auto *U = dyn_cast<ConstantExpr>(base)) base = U->getOperand(0);
      return pre + "cexpr:" + CE->getOpcodeName() + "(" +
             (base->hasName() ? base->getName().str() : "?") + ")";
    }
    return pre + "<const>";
  };
  auto rawKind = [&](NodeIndex m) -> std::string {
    if (NF.isDereferenceNode(m)) return "deref";
    // Object nodes carry their allocation's Value (call, alloca, global,
    // function): classify them as objects before looking at the Value.
    if (NF.isObjectNode(m))
      return std::string("obj") + (NF.isHeapObject(m) ? ":heap" : ":static");
    if (NF.isCellNode(m)) return "cell";
    const Value *V = NF.getValueForNode(m);
    if (!V) return "syn";
    if (isa<Argument>(V)) return "arg";
    if (const auto *I = dyn_cast<Instruction>(V))
      return std::string("inst:") + I->getOpcodeName();
    if (isa<Function>(V)) return "fn";
    if (isa<GlobalVariable>(V)) return "global";
    if (isa<ConstantExpr>(V)) return "cexpr";
    return "const";
  };
  // GEP byte offset: 1 = constant (off set), 2 = variable index, 0 = not a GEP
  auto gepOffset = [&](NodeIndex m, int64_t &off) -> int {
    const Value *V = NF.getValueForNode(m);
    const auto *G = dyn_cast_or_null<GEPOperator>(V);
    if (!G || NF.isDereferenceNode(m)) return 0;
    const DataLayout &DL =
        isa<Instruction>(V) ? cast<Instruction>(V)->getModule()->getDataLayout()
                            : DL0;
    APInt ap(64, 0);
    if (G->accumulateConstantOffset(DL, ap)) { off = ap.getSExtValue(); return 1; }
    return 2;
  };
  std::set<std::tuple<const Value *, std::string, unsigned>> directActuals;
  for (auto &Mp : Ctx->Modules)
    for (Function &F : *Mp.first)
      for (Instruction &I : instructions(F))
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (const Function *CF = CB->getCalledFunction())
            for (unsigned i = 0; i < CB->arg_size(); i++)
              directActuals.insert({CB->getArgOperand(i), CF->getName().str(), i});
  boost::unordered_flat_set<NodeIndex> seen;
  auto noteNode = [&](NodeIndex n) { seen.insert(n); };
  for (const GraphEdge &E : Graph.edges()) {
    noteNode(E.from); noteNode(E.to);
    std::string kind;
    if (E.kind == EdgeKind::Deref) kind = "d";
    else {
      const bool sd = NF.isDereferenceNode(E.from), td = NF.isDereferenceNode(E.to);
      int64_t off = 0;
      int g = gepOffset(E.to, off);
      if (E.kind == EdgeKind::Field) kind = "f" + std::to_string(E.bucket);
      else if (E.kind == EdgeKind::FieldAny) kind = "fx";
      if (sd && td) kind = "memcpy";
      else if (td) kind = "store";
      else if (sd) kind = "load";
      else if (g == 1) kind = "gep:" + std::to_string(off);
      else if (g == 2) kind = "gepX";
      else {
        const Value *Vt = NF.getValueForNode(E.to);
        const Value *Vs = NF.getValueForNode(E.from);
        if (const auto *A = dyn_cast_or_null<Argument>(Vt))
          kind = (Vs && directActuals.count({Vs, A->getParent()->getName().str(),
                                             A->getArgNo()}))
                     ? "call" : "icall";
        else if (Vt && isa<CallBase>(Vt)) kind = "ret";
        else if (const auto *I = dyn_cast_or_null<Instruction>(Vt))
          kind = std::string("copy:") + I->getOpcodeName();
        else kind = kind.empty() ? "copy" : kind;
      }
    }
    edgesOut << E.from << " " << E.to << " " << kind << "\n";
  }
  auto nodeOf = [&](const Value *V) -> NodeIndex {
    NodeIndex n = NF.getValueNodeFor(V);
    if (n == AndersNodeFactory::InvalidIndex)
      if (const auto *C = dyn_cast<Constant>(V))
        n = NF.getValueNodeForConstant(C);
    return n;
  };
  size_t sid = 0;
  for (auto *CS : Ctx->IndirectCallInsts) {
    Value *fp = CS->getCalledOperand()->stripPointerCastsAndAliases();
    NodeIndex fn = NF.getValueNodeFor(fp);
    if (fn == AndersNodeFactory::InvalidIndex) continue;
    NodeIndex res = NF.getValueNodeFor(CS);
    noteNode(fn);
    if (res != AndersNodeFactory::InvalidIndex) noteNode(res);
    std::string loc = "?";
    if (const DILocation *L = CS->getDebugLoc())
      loc = (L->getFilename() + ":" + Twine(L->getLine())).str();
    icallsOut << "I " << sid << " " << fn << " "
              << (res == AndersNodeFactory::InvalidIndex ? -1 : (int64_t)res)
              << " " << loc << " " << CS->getFunction()->getName() << "\n";
    for (unsigned i = 0; i < CS->arg_size(); i++) {
      NodeIndex a = nodeOf(CS->getArgOperand(i));
      if (a == AndersNodeFactory::InvalidIndex) continue;
      noteNode(a);
      icallsOut << "A " << sid << " " << i << " " << a << "\n";
    }
    for (const Function *F : Ctx->AddressTakenFuncs)
      if (isCompatible(CS, F))
        icallsOut << "C " << sid << " " << F->getName() << "\n";
    sid++;
  }
  for (const Function *F0 : Ctx->AddressTakenFuncs) {
    Function *F = getFuncDef(const_cast<Function *>(F0));
    NodeIndex fn = NF.getValueNodeFor(F);
    if (fn == AndersNodeFactory::InvalidIndex) continue;
    NodeIndex ret = F->isDeclaration() ? AndersNodeFactory::InvalidIndex
                                       : NF.getReturnNodeFor(F);
    noteNode(fn);
    if (ret != AndersNodeFactory::InvalidIndex) noteNode(ret);
    funcsOut << "F " << F->getName() << " " << fn << " "
             << (ret == AndersNodeFactory::InvalidIndex ? -1 : (int64_t)ret)
             << " " << (F->isVarArg() ? 1 : 0) << " "
             << F->getFunctionType()->getNumParams() << "\n";
    for (const Argument &A : F->args()) {
      NodeIndex a = NF.getValueNodeFor(&A);
      if (a == AndersNodeFactory::InvalidIndex) continue;
      noteNode(a);
      funcsOut << "P " << F->getName() << " " << A.getArgNo() << " " << a << "\n";
    }
  }
  // Object identity for cells: a deref node's pointer, and every
  // object node's base + offset, so a reader can key cells by
  // (object, byte offset) itself.
  for (NodeIndex n : seen) {
    nodesOut << n << " " << rawKind(n) << " " << rawName(n);
    if (NF.isDereferenceNode(n)) {
      auto it = cellPtr.find(n);
      nodesOut << " ptr=" << (it == cellPtr.end() ? -1 : (int64_t)it->second);
    }
    // Object extent where the IR states it (allocas, globals); heap
    // objects have none — the reader must bound them itself.
    if (const Value *V = NF.getValueForNode(n)) {
      if (const auto *AI = dyn_cast<AllocaInst>(V)) {
        if (!AI->isArrayAllocation())
          nodesOut << " size=" << AI->getModule()->getDataLayout().getTypeAllocSize(
                                     AI->getAllocatedType());
      } else if (const auto *GV = dyn_cast<GlobalVariable>(V)) {
        nodesOut << " size=" << GV->getParent()->getDataLayout().getTypeAllocSize(
                                   GV->getValueType());
      } else if (isa<Function>(V)) {
        nodesOut << " size=1"; // one address: the entry
      }
    }
    // Allocation-site value nodes are origins in their own right (the
    // pointer IS the address of the fresh object), like globals,
    // allocas and functions; mark them so a reader can seed them.
    if (AllocSites.count(n)) nodesOut << " alloc";
    nodesOut << "\n";
    NodeIndex c = getCanonicalNode(n);
    if (c != n) canonOut << n << " " << c << "\n";
  }
  CG_LOG("FlowsTo: raw graph dumped to " << pfx << ".{nodes,edges,canon,icalls,funcs} ("
         << seen.size() << " nodes, " << Graph.size() << " edges, " << sid
         << " icall sites)\n");
}

// Residue-modulus input census (--cfl-dump-fnptr-offsets): every
// (deepest named struct, byte offset) slot observed to HOLD a function —
// from global initializers (the ops-table population) and direct
// fn-constant stores (INIT_WORK-style). The Z_P planes can only split
// what P separates: any struct with two fn slots at offsets congruent
// mod P is unsplittable at that P (fs13 exemplar: file_operations spans
// ~30 slots > 13 residues — pigeonhole inside ONE struct). The offline
// scorer picks P from this dump.
void kaCollectFnPtrOffsets(
    ModuleList &modules,
    llvm::function_ref<void(StringRef, uint64_t, StringRef)> sink) {
  std::function<void(const Constant *, Type *, const DataLayout &)> walk =
      [&](const Constant *C, Type *Ty, const DataLayout &DL) {
        if (auto *ST = dyn_cast<StructType>(Ty)) {
          if (ST->isOpaque())
            return;
          const StructLayout *SL = DL.getStructLayout(ST);
          for (unsigned i = 0; i < ST->getNumElements(); i++) {
            const Constant *E = C->getAggregateElement(i);
            if (!E)
              continue;
            Type *ET = ST->getElementType(i);
            if (const auto *F =
                    dyn_cast<Function>(E->stripPointerCasts())) {
              if (!ST->isLiteral() && ST->hasName())
                sink(stripStructNameSuffix(ST->getStructName()),
                     SL->getElementOffset(i), F->getName());
            } else if (isa<StructType>(ET) || isa<ArrayType>(ET)) {
              walk(E, ET, DL);
            }
          }
        } else if (auto *AT = dyn_cast<ArrayType>(Ty)) {
          for (unsigned i = 0; i < AT->getNumElements(); i++) {
            const Constant *E = C->getAggregateElement(i);
            if (E)
              walk(E, AT->getElementType(), DL);
          }
        }
      };
  for (auto &mp : modules) {
    const DataLayout &DL = mp.first->getDataLayout();
    for (GlobalVariable &GV : mp.first->globals())
      if (GV.hasInitializer())
        walk(GV.getInitializer(), GV.getValueType(), DL);
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.empty())
        continue;
      for (inst_iterator II = inst_begin(F), IE = inst_end(F); II != IE;
           ++II) {
        auto *SI = dyn_cast<StoreInst>(&*II);
        if (!SI)
          continue;
        const auto *SF =
            dyn_cast<Function>(SI->getValueOperand()->stripPointerCasts());
        if (!SF)
          continue;
        const auto *GEP = dyn_cast<GEPOperator>(
            SI->getPointerOperand()->stripPointerCasts());
        if (!GEP)
          continue;
        Type *CurTy = GEP->getSourceElementType();
        StringRef deepName;
        uint64_t deepOff = 0;
        auto idx = GEP->idx_begin();
        if (idx == GEP->idx_end())
          continue;
        ++idx; // skip pointer index
        for (; idx != GEP->idx_end(); ++idx) {
          if (auto *ST = dyn_cast<StructType>(CurTy)) {
            auto *CI = dyn_cast<ConstantInt>(*idx);
            if (!CI)
              break;
            unsigned fi = (unsigned)CI->getZExtValue();
            if (fi >= ST->getNumElements())
              break;
            if (!ST->isLiteral() && ST->hasName()) {
              deepName = stripStructNameSuffix(ST->getStructName());
              deepOff = DL.getStructLayout(ST)->getElementOffset(fi);
            } else if (!deepName.empty()) {
              deepOff += DL.getStructLayout(ST)->getElementOffset(fi);
            }
            CurTy = ST->getElementType(fi);
          } else if (auto *AT = dyn_cast<ArrayType>(CurTy)) {
            CurTy = AT->getElementType();
          } else {
            break;
          }
        }
        if (!deepName.empty())
          sink(deepName, deepOff, SF->getName());
      }
    }
  }
}

// Residue-modulus input census (--cfl-dump-fnptr-offsets): see
// kaCollectFnPtrOffsets. The Z_P planes can only split what P
// separates (fs13 exemplar: file_operations spans ~30 slots > 13
// residues — pigeonhole inside ONE struct).
void CallGraphPass::dumpFnPtrOffsets() {
  boost::unordered_flat_set<std::string> emitted;
  kaCollectFnPtrOffsets(
      Ctx->Modules, [&](StringRef sName, uint64_t off, StringRef fn) {
        std::string key =
            (sName + "\t" + std::to_string(off) + "\t" + fn).str();
        if (!emitted.insert(key).second)
          return;
        errs() << "FNPTR-OFFSET " << sName << " " << off << " " << fn
               << "\n";
      });
  errs() << "FNPTR-OFFSET census complete (" << emitted.size()
         << " distinct slot records)\n";
}

// ---- JSON call graph export helpers ----

// Extract source file path from debug info for a function.
// Iterates instructions to find DILocation, falls back to module source filename.
static std::string getFuncSourceFile(const Function *F) {
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (DILocation *Loc = I.getDebugLoc()) {
        StringRef Dir = Loc->getDirectory();
        StringRef File = Loc->getFilename();
        if (File.empty()) {
          if (DILocation *IL = Loc->getInlinedAt()) {
            Dir = IL->getDirectory();
            File = IL->getFilename();
          }
        }
        if (!File.empty()) {
          if (sys::path::is_absolute(File))
            return File.str();
          SmallString<256> FullPath;
          if (!Dir.empty())
            FullPath = Dir;
          sys::path::append(FullPath, File);
          sys::path::remove_dots(FullPath, true);
          return std::string(FullPath);
        }
      }
    }
  }
  // Fallback to module source filename
  return F->getParent()->getSourceFileName();
}

// Return a function ID: bare name for external linkage, "file:name" for internal.
static std::string getFuncId(const Function *F) {
  // For intrinsics, use the base name without type suffixes
  // e.g., "llvm.memcpy.p0.p0.i64" -> "llvm.memcpy"
  if (F->isIntrinsic())
    return Intrinsic::getBaseName(F->getIntrinsicID()).str();
  if (F->hasExternalLinkage())
    return F->getName().str();
  return getFuncSourceFile(F) + ":" + F->getName().str();
}

// Extract source line from a CallBase's debug location.
// Returns 0 if no debug info available.
static unsigned getCallLine(const CallBase *CI) {
  if (DILocation *Loc = CI->getDebugLoc()) {
    unsigned L = Loc->getLine();
    if (L == 0) {
      if (DILocation *IL = Loc->getInlinedAt())
        L = IL->getLine();
    }
    return L;
  }
  return 0;
}

// Get the min/max line range of a function from debug info.
static std::pair<unsigned, unsigned> getFuncLineRange(const Function *F) {
  unsigned minLine = UINT_MAX, maxLine = 0;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (DILocation *Loc = I.getDebugLoc()) {
        unsigned L = Loc->getLine();
        if (L > 0) {
          if (L < minLine) minLine = L;
          if (L > maxLine) maxLine = L;
        }
      }
    }
  }
  if (minLine == UINT_MAX)
    minLine = 0;
  return {minLine, maxLine};
}

void CallGraphPass::dumpCallGraphJSON(StringRef Path) {
  std::error_code EC;
  raw_fd_ostream OS(Path, EC);
  if (EC) {
    WARNING("Failed to open call graph JSON file for writing: " << Path
            << ": " << EC.message() << "\n");
    return;
  }

  // Deterministic order (the maps below are keyed by pointers): every
  // function and call instruction gets its ordinal in module order.
  DenseMap<const Function *, uint64_t> FuncOrd;
  DenseMap<const CallBase *, uint64_t> CallOrd;
  for (auto &[M, Name] : Ctx->Modules)
    for (Function &F : *M) {
      FuncOrd.try_emplace(&F, FuncOrd.size());
      for (Instruction &I : instructions(F))
        if (const auto *CB = dyn_cast<CallBase>(&I))
          CallOrd.try_emplace(CB, CallOrd.size());
    }
  auto funcOrd = [&](const Function *F) {
    auto It = FuncOrd.find(F);
    assert(It != FuncOrd.end() && "call graph names a function of no module");
    return It->second;
  };
  auto callOrd = [&](const CallBase *CB) {
    auto It = CallOrd.find(CB);
    assert(It != CallOrd.end() && "call graph names a call of no module");
    return It->second;
  };

  // Collect all functions that appear in Callees or Callers.
  // Group by getFuncId to merge multiple Function* for the same symbol
  // (e.g., external declarations appear in each module).
  DenseSet<const Function *> AllFuncs;
  for (auto &[CS, FS] : Ctx->Callees) {
    const Function *Caller = CS->getFunction();
    if (Caller && !Caller->isDeclaration() && !Caller->isIntrinsic())
      AllFuncs.insert(Caller);
    for (const Function *F : FS) {
      if (F && !(F->isIntrinsic() && !isImportantIntrinsic(F)))
        AllFuncs.insert(F);
    }
  }
  for (auto &[F, CIS] : Ctx->Callers) {
    if (F && !(F->isIntrinsic() && !isImportantIntrinsic(F)))
      AllFuncs.insert(F);
  }
  // One entry per function ID. An external symbol (a bare-name ID) is
  // the definition the analysis linked it to (getFuncDef; its
  // declarations otherwise). Every other ID is keyed by its file and can
  // have several bodies — a header's static inline function has one per
  // translation unit, each resolving its own indirect calls — and lists
  // the callees of all of them. File, line range and linkage come from
  // the first definition in module order (a declaration only when no
  // definition exists).
  std::map<std::string, std::vector<const Function *>> ByID;
  for (const Function *F : AllFuncs) {
    const Function *G = F->hasExternalLinkage()
                            ? getFuncDef(const_cast<Function *>(F))
                            : F;
    ByID[getFuncId(F)].push_back(G);
  }
  for (auto &[ID, Fs] : ByID) {
    std::sort(Fs.begin(), Fs.end(), [&](const Function *A, const Function *B) {
      if (A->isDeclaration() != B->isDeclaration())
        return !A->isDeclaration();
      return funcOrd(A) < funcOrd(B);
    });
    Fs.erase(std::unique(Fs.begin(), Fs.end()), Fs.end());
  }

  // Build merged Callers map keyed by getFuncId string, since external
  // declarations have separate Function* per module.
  StringMap<std::vector<const CallBase *>> MergedCallers;
  for (auto &[F, CIS] : Ctx->Callers) {
    if (!F || (F->isIntrinsic() && !isImportantIntrinsic(F)))
      continue;
    auto &merged = MergedCallers[getFuncId(F)];
    merged.insert(merged.end(), CIS.begin(), CIS.end());
  }
  for (auto &E : MergedCallers) {
    auto &V = E.second;
    std::sort(V.begin(), V.end(), [&](const CallBase *A, const CallBase *B) {
      return callOrd(A) < callOrd(B);
    });
    V.erase(std::unique(V.begin(), V.end()), V.end());
  }

  json::Object Functions;
  size_t totalEdges = 0, directEdges = 0, indirectEdges = 0;

  for (auto &[FuncID, Fs] : ByID) {
    const Function *F = Fs.front();
    if (F->isIntrinsic() && !isImportantIntrinsic(F))
      continue;

    std::string SrcFile = getFuncSourceFile(F);
    auto [LineStart, LineEnd] = getFuncLineRange(F);

    json::Object FuncObj;
    FuncObj["file"] = SrcFile;
    if (LineStart > 0)
      FuncObj["line_start"] = static_cast<int64_t>(LineStart);
    if (LineEnd > 0)
      FuncObj["line_end"] = static_cast<int64_t>(LineEnd);
    FuncObj["linkage"] = F->hasExternalLinkage() ? "external" : "internal";

    // Build callees array by iterating call instructions of each body;
    // a later body's edge already listed by an earlier body is skipped.
    json::Array CalleesArr;
    std::set<std::tuple<std::string, bool, unsigned>> earlierBodies, thisBody;
    for (const Function *Body : Fs) {
      if (Body->isDeclaration())
        break; // definitions sort first
      for (auto &BB : *Body) {
        for (auto &I : BB) {
          const CallBase *CI = dyn_cast<CallBase>(&I);
          if (!CI || CI->isInlineAsm())
            continue;

          auto it = Ctx->Callees.find(CI);
          if (it == Ctx->Callees.end())
            continue;

          bool isDirect = (CI->getCalledFunction() != nullptr);
          unsigned line = getCallLine(CI);

          std::vector<std::pair<std::string, const Function *>> Targets;
          for (const Function *Callee : it->second)
            if (!(Callee->isIntrinsic() && !isImportantIntrinsic(Callee)))
              Targets.emplace_back(getFuncId(Callee), Callee);
          std::sort(Targets.begin(), Targets.end(),
                    [&](const auto &A, const auto &B) {
                      if (A.first != B.first)
                        return A.first < B.first;
                      return funcOrd(A.second) < funcOrd(B.second);
                    });
          for (auto &[CalleeID, Callee] : Targets) {
            auto Key = std::make_tuple(CalleeID, isDirect, line);
            if (earlierBodies.count(Key))
              continue;
            thisBody.insert(Key);
            json::Object Edge;
            Edge["callee"] = CalleeID;
            Edge["call_type"] = isDirect ? "direct" : "indirect";
            if (line > 0)
              Edge["line"] = static_cast<int64_t>(line);
            CalleesArr.push_back(std::move(Edge));
            totalEdges++;
            if (isDirect) directEdges++;
            else indirectEdges++;
          }
        }
      }
      earlierBodies.insert(thisBody.begin(), thisBody.end());
      thisBody.clear();
    }
    FuncObj["callees"] = std::move(CalleesArr);

    // Build callers array from merged callers map
    json::Array CallersArr;
    auto callerIt = MergedCallers.find(FuncID);
    if (callerIt != MergedCallers.end()) {
      for (const CallBase *CI : callerIt->second) {
        const Function *CallerF = CI->getFunction();
        if (!CallerF || (CallerF->isIntrinsic() && !isImportantIntrinsic(CallerF)))
          continue;
        bool isDirect = (CI->getCalledFunction() != nullptr);
        unsigned line = getCallLine(CI);

        json::Object Edge;
        Edge["caller"] = getFuncId(CallerF);
        Edge["call_type"] = isDirect ? "direct" : "indirect";
        if (line > 0)
          Edge["line"] = static_cast<int64_t>(line);
        CallersArr.push_back(std::move(Edge));
      }
    }
    FuncObj["callers"] = std::move(CallersArr);

    Functions[FuncID] = std::move(FuncObj);
  }

  json::Object Metadata;
  Metadata["version"] = 1;
  Metadata["total_functions"] = static_cast<int64_t>(Functions.size());
  Metadata["total_call_edges"] = static_cast<int64_t>(totalEdges);
  Metadata["total_direct_calls"] = static_cast<int64_t>(directEdges);
  Metadata["total_indirect_calls"] = static_cast<int64_t>(indirectEdges);
  Metadata["soundness_capped"] = soundnessCapped;

  json::Object Root;
  Root["metadata"] = std::move(Metadata);
  Root["functions"] = std::move(Functions);

  OS << json::Value(std::move(Root)) << "\n";
  CG_LOG("Exported call graph JSON to " << Path << ": "
         << AllFuncs.size() << " functions, "
         << totalEdges << " edges ("
         << directEdges << " direct, "
         << indirectEdges << " indirect)\n");
}
