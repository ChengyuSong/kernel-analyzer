/*
 * Witness-taint propagation (v2 consolidation of the certified-channel
 * witness classes; docs/rendezvous-keying-design.md).
 *
 * Question answered per indirect callsite: what VALUES can its fptr
 * hold, under a strict lattice
 *     Wit ::= Fn(F) | Obj(root, off, stride)   root in {global, alloca}
 * with a poison top. Evaluation is demand-driven backward from the
 * callsite with memoization; memory reads go through two cell spaces:
 *
 *   exact cells  (root, off)   — writes through direct &root GEP
 *                                chains + initializer facts
 *   typed cells  (Sname, off)  — writes through pointers whose GEP
 *                                names struct S at offset off (any
 *                                base: heap instances aggregate here,
 *                                like the regfield walk's keys)
 *
 * An exact read unions the matching typed cell (aliased writes through
 * memory-obtained pointers land there). Escapes poison: a slot address
 * in a non-pointer position poisons that cell; ptrtoint / extern-call
 * / return-from-address-taken poisons the whole root. Stores that are
 * attributable to NEITHER space are the walk's stated blind spot,
 * counted LOUDLY, not poisoning (same certified contract as
 * regfield-apply's bare-pointer residual).
 *
 * Soundness posture mirrors the shipped channels: every rule
 * over-approximates or refuses (returns top). Fn-channel/obj-channel
 * results are not consulted; this is an independent lever gated on
 * the same ladder (pairs -N/+0, GT FN-identity).
 */

#include "WitnessTaint.h"
#include "Flags.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using namespace llvm;

namespace {

constexpr size_t kSetCap = 256;  // witness-set width cap -> top
constexpr unsigned kMaxSweeps = 6;

struct WitVal {
  // kind 0 = Fn (root = Function), 1 = Obj (root = GlobalVariable or
  // AllocaInst; off = byte offset; stride = var-index element size, 0
  // if exact)
  int kind;
  const Value *root;
  int64_t off;
  uint64_t stride;
  bool operator<(const WitVal &o) const {
    return std::tie(kind, root, off, stride) <
           std::tie(o.kind, o.root, o.off, o.stride);
  }
  bool operator==(const WitVal &o) const {
    return std::tie(kind, root, off, stride) ==
           std::tie(o.kind, o.root, o.off, o.stride);
  }
};

struct WitSet {
  bool top = false;
  std::set<WitVal> vals;
  bool insert(const WitVal &v) {
    if (top) return false;
    if (vals.size() >= kSetCap) {
      top = true;
      vals.clear();
      return true;
    }
    return vals.insert(v).second;
  }
  bool merge(const WitSet &o) {
    if (top) return false;
    if (o.top) {
      top = true;
      vals.clear();
      return true;
    }
    bool ch = false;
    for (const auto &v : o.vals) ch |= insert(v);
    return ch;
  }
  bool operator==(const WitSet &o) const {
    return top == o.top && vals == o.vals;
  }
};

static StringRef stripSuffix(StringRef n) {
  // struct.foo.123 -> struct.foo
  size_t d = n.rfind('.');
  if (d != StringRef::npos && d > 0) {
    bool digits = d + 1 < n.size();
    for (size_t i = d + 1; i < n.size(); i++)
      digits &= isdigit(n[i]);
    if (digits) return n.take_front(d);
  }
  return n;
}

class WitnessTaint {
public:
  explicit WitnessTaint(GlobalContext *Ctx) : Ctx(Ctx) {}
  void run();

private:
  GlobalContext *Ctx;

  // ---- canonicalization (cross-TU) ----
  const Function *funcDef(const Function *F) {
    if (!F->isDeclaration()) return F;
    auto it = Ctx->Funcs.find(F->getGUID());
    return it != Ctx->Funcs.end() ? it->second : F;
  }
  const GlobalValue *globDef(const GlobalValue *G) {
    if (const auto *GV = dyn_cast<GlobalVariable>(G))
      if (GV->isDeclarationForLinker()) {
        auto it = Ctx->Gobjs.find(G->getGUID());
        if (it != Ctx->Gobjs.end()) return it->second;
      }
    return G;
  }

  // ---- pointer shape (syntactic; for WRITE indexing only) ----
  // Walks GEP chains; returns root + const off + at most one array
  // stride. Non-conforming -> root = nullptr.
  struct PtrShape {
    const Value *root = nullptr; // Argument/Load/Global/Alloca/...
    int64_t off = 0;
    uint64_t stride = 0;
    std::string typedName; // innermost named-struct + its field off
    int64_t typedOff = 0;
    bool hasTyped = false;
  };
  PtrShape shapeOf(const Value *P, const DataLayout &DL) {
    PtrShape S;
    P = P->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(P)) {
      for (auto GTI = gep_type_begin(G), E = gep_type_end(G); GTI != E;
           ++GTI) {
        if (const auto *CI = dyn_cast<ConstantInt>(GTI.getOperand())) {
          int64_t eo;
          if (StructType *ST = GTI.getStructTypeOrNull()) {
            eo = (int64_t)DL.getStructLayout(ST)->getElementOffset(
                CI->getZExtValue());
            if (ST->hasName()) {
              // deepKey parity: INNERMOST named struct wins and the
              // typed offset re-bases at it (outermost-wins fragmented
              // nested ops keys: vd->tx.callback wrote virt_dma_desc+N
              // while readers keyed dma_async_tx_descriptor+24 —
              // emptied vchan_complete at the slice)
              S.typedName = stripSuffix(ST->getStructName()).str();
              S.typedOff = eo;
              S.hasTyped = true;
            } else if (S.hasTyped) {
              S.typedOff += eo;
            }
          } else {
            eo = CI->getSExtValue() *
                 (int64_t)DL.getTypeAllocSize(GTI.getIndexedType());
            if (S.hasTyped) S.typedOff += eo;
          }
          S.off += eo;
        } else if (!GTI.getStructTypeOrNull() && S.stride == 0) {
          S.stride = DL.getTypeAllocSize(GTI.getIndexedType());
          if (!S.stride) { S.root = nullptr; return S; }
        } else {
          S.root = nullptr;
          return S;
        }
      }
      P = G->getPointerOperand()->stripPointerCasts();
    }
    S.root = P;
    // typedOff is relative to the innermost named struct: recompute as
    // off minus everything outside it is hard in one pass; for the
    // typed space we use the innermost named struct's own field offset
    // — approximated by taking the LAST named-struct step's element
    // offset chain. v1 keeps it simple: typed key valid only when the
    // named struct step is the OUTERMOST const contribution, i.e. use
    // (typedName, off) when the root itself is untyped. This matches
    // the regfield walk's deepKey semantics (last named struct wins,
    // subsequent const offsets accumulate).
    return S;
  }

  // ---- write index ----
  using ExactKey = std::pair<const Value *, int64_t>; // canonical root
  using TypedKey = std::pair<std::string, int64_t>;
  std::map<ExactKey, std::vector<const StoreInst *>> exactWr;
  std::map<TypedKey, std::vector<const StoreInst *>> typedWr;
  std::set<const Value *> rootEscaped;   // whole-root poison
  std::set<ExactKey> exactPoison;        // slot-address escape / atomics
  std::set<TypedKey> typedPoison;
  std::set<std::string> typedBulk;       // unknown-source bulk over S
  size_t blindStores = 0;                // stated blind spot (counted)

  // memoized cell / value states
  std::map<ExactKey, WitSet> exactCell;
  std::map<TypedKey, WitSet> typedCell;
  std::set<ExactKey> exactCellReady;
  std::set<TypedKey> typedCellReady;
  DenseMap<const Value *, WitSet> memo;
  DenseSet<const Value *> inProgress;
  bool changedThisSweep = false;

  // callers index for formal binding (direct, canonicalized)
  std::map<const Function *, std::vector<const CallBase *>> directCallers;
  std::set<const Function *> addrTaken;

  void indexModule(Module *M);
  WitSet evalValue(const Value *V, const DataLayout &DL);
  WitSet evalConstant(const Constant *C, const DataLayout &DL);
  WitSet readCell(const WitVal &ptr, const DataLayout &DL);
  WitSet &exactCellState(const ExactKey &K, const DataLayout &DL);
  WitSet &typedCellState(const TypedKey &K, const DataLayout &DL);
  void seedInitializer(const GlobalVariable *GV);
};

void WitnessTaint::indexModule(Module *M) {
  const DataLayout &DL = M->getDataLayout();
  for (GlobalVariable &GV : M->globals())
    if (GV.hasInitializer()) seedInitializer(&GV);
  for (Function &F : *M) {
    // address-takenness: any non-callee use
    for (const Use &U : F.uses()) {
      const auto *CB = dyn_cast<CallBase>(U.getUser());
      if (!CB || !CB->isCallee(&U)) {
        addrTaken.insert(funcDef(&F));
        break;
      }
    }
    if (F.isDeclaration()) continue;
    for (const Instruction &I : instructions(F)) {
      if (const auto *CB = dyn_cast<CallBase>(&I)) {
        if (const Function *CF = CB->getCalledFunction())
          directCallers[funcDef(CF)].push_back(CB);
        // escapes: pointer args to non-direct/extern callees
        const Function *CF = CB->getCalledFunction();
        const bool opaque =
            !CF || funcDef(CF)->isDeclaration() || CB->isInlineAsm();
        if (opaque && !isa<AnyMemIntrinsic>(&I))
          for (const Value *A : CB->args())
            if (A->getType()->isPointerTy()) {
              PtrShape S = shapeOf(A, DL);
              if (S.root) {
                if (isa<GlobalVariable>(S.root) || isa<AllocaInst>(S.root))
                  rootEscaped.insert(
                      isa<GlobalVariable>(S.root)
                          ? (const Value *)globDef(cast<GlobalValue>(S.root))
                          : S.root);
              }
            }
        if (const auto *MI = dyn_cast<AnyMemTransferInst>(&I)) {
          // bulk copies: same certified treatment as the walk — an
          // unknown-source transfer over a named struct poisons its
          // typed space; same-typed and const-global sources are
          // population-preserving
          PtrShape D = shapeOf(MI->getRawDest(), DL);
          PtrShape Ssrc = shapeOf(MI->getRawSource(), DL);
          auto tyOf = [&](const PtrShape &PS) -> std::string {
            if (PS.hasTyped) return PS.typedName;
            if (PS.root)
              if (const auto *AI = dyn_cast<AllocaInst>(PS.root))
                if (auto *ST = dyn_cast<StructType>(AI->getAllocatedType()))
                  if (ST->hasName())
                    return stripSuffix(ST->getStructName()).str();
            return std::string();
          };
          const std::string dt = tyOf(D), st = tyOf(Ssrc);
          const auto *SG = dyn_cast_or_null<GlobalVariable>(
              Ssrc.root ? Ssrc.root : nullptr);
          const bool constSrc = SG && SG->isConstant() && SG->hasInitializer();
          if (!dt.empty() && dt != st && !constSrc) typedBulk.insert(dt);
          // const-global source into exact root: copy via cell reads at
          // query time is v2 work; v1 poisons the exact dest object
          // unless const source (then typed/init facts already cover)
          if (D.root && !constSrc && dt.empty() &&
              (isa<GlobalVariable>(D.root) || isa<AllocaInst>(D.root)))
            rootEscaped.insert(isa<GlobalVariable>(D.root)
                                   ? (const Value *)globDef(
                                         cast<GlobalValue>(D.root))
                                   : D.root);
        }
        continue;
      }
      if (const auto *PTI = dyn_cast<PtrToIntInst>(&I)) {
        PtrShape S = shapeOf(PTI->getOperand(0), DL);
        if (S.root && (isa<GlobalVariable>(S.root) || isa<AllocaInst>(S.root)))
          rootEscaped.insert(isa<GlobalVariable>(S.root)
                                 ? (const Value *)globDef(
                                       cast<GlobalValue>(S.root))
                                 : S.root);
        continue;
      }
      if (const auto *AX = dyn_cast<AtomicCmpXchgInst>(&I)) {
        PtrShape S = shapeOf(AX->getPointerOperand(), DL);
        if (S.root) {
          if (S.hasTyped) typedPoison.insert({S.typedName, S.typedOff});
          const Value *R = isa<GlobalVariable>(S.root)
                               ? (const Value *)globDef(
                                     cast<GlobalValue>(S.root))
                               : S.root;
          if (isa<GlobalVariable>(S.root) || isa<AllocaInst>(S.root))
            exactPoison.insert({R, S.off});
        }
        continue;
      }
      if (const auto *AR = dyn_cast<AtomicRMWInst>(&I)) {
        PtrShape S = shapeOf(AR->getPointerOperand(), DL);
        if (S.hasTyped) typedPoison.insert({S.typedName, S.typedOff});
        continue;
      }
      const auto *SI = dyn_cast<StoreInst>(&I);
      if (!SI) continue;
      if (!SI->getValueOperand()->getType()->isPointerTy() &&
          !SI->getValueOperand()->getType()->isStructTy())
        continue; // only pointer-bearing stores matter for the lattice
      PtrShape S = shapeOf(SI->getPointerOperand(), DL);
      bool attributed = false;
      if (S.root && S.stride == 0) {
        if (const auto *GV = dyn_cast<GlobalVariable>(S.root)) {
          exactWr[{globDef(GV), S.off}].push_back(SI);
          attributed = true;
        } else if (isa<AllocaInst>(S.root)) {
          exactWr[{S.root, S.off}].push_back(SI);
          attributed = true;
        }
      }
      if (S.hasTyped && S.stride == 0) {
        typedWr[{S.typedName, S.typedOff}].push_back(SI);
        attributed = true;
      }
      if (!attributed) {
        // stated blind spot (bare-pointer / strided stores): counted,
        // not poisoning — the same certified contract as the walk's
        // g_regfieldBarePtrFnStores residual
        blindStores++;
      }
    }
  }
}

void WitnessTaint::seedInitializer(const GlobalVariable *GV) {
  const DataLayout &DL = GV->getParent()->getDataLayout();
  const GlobalValue *canon = globDef(GV);
  std::function<void(const Constant *, int64_t)> walk =
      [&](const Constant *C, int64_t base) {
        if (const auto *CS = dyn_cast<ConstantStruct>(C)) {
          const StructLayout *SL = DL.getStructLayout(CS->getType());
          StructType *ST = CS->getType();
          for (unsigned i = 0; i < CS->getNumOperands(); i++) {
            const int64_t eo = base + SL->getElementOffset(i);
            const Constant *E = CS->getOperand(i);
            WitSet W = evalConstant(E, DL);
            if (!W.top && !W.vals.empty()) {
              exactCell[{canon, eo}].merge(W);
              if (ST->hasName())
                typedCell[{stripSuffix(ST->getStructName()).str(),
                           (int64_t)SL->getElementOffset(i)}]
                    .merge(W);
            }
            walk(E, eo);
          }
        } else if (const auto *CA = dyn_cast<ConstantArray>(C)) {
          const uint64_t es =
              DL.getTypeAllocSize(CA->getType()->getElementType());
          for (unsigned i = 0; i < CA->getNumOperands(); i++)
            walk(CA->getOperand(i), base + (int64_t)(i * es));
        }
      };
  walk(GV->getInitializer(), 0);
}

WitSet WitnessTaint::evalConstant(const Constant *C, const DataLayout &DL) {
  WitSet W;
  const Value *S = C->stripPointerCasts();
  if (const auto *F = dyn_cast<Function>(S)) {
    W.insert({0, funcDef(F), 0, 0});
    return W;
  }
  if (isa<ConstantPointerNull>(S) || isa<UndefValue>(S)) return W; // empty
  if (const auto *GV = dyn_cast<GlobalVariable>(S)) {
    W.insert({1, globDef(GV), 0, 0});
    return W;
  }
  if (const auto *GA = dyn_cast<GlobalAlias>(S))
    return evalConstant(GA->getAliasee(), DL);
  if (const auto *CE = dyn_cast<ConstantExpr>(C))
    if (CE->getOpcode() == Instruction::GetElementPtr) {
      PtrShape PS;
      // reuse shapeOf via the operator view
      PS = shapeOf(CE, DL);
      if (PS.root)
        if (const auto *GV = dyn_cast<GlobalVariable>(PS.root)) {
          W.insert({1, globDef(GV), PS.off, PS.stride});
          return W;
        }
    }
  if (!C->getType()->isPointerTy()) return W; // scalar: irrelevant
  W.top = true;
  return W;
}

WitSet &WitnessTaint::exactCellState(const ExactKey &K,
                                     const DataLayout &DL) {
  WitSet &Cell = exactCell[K];
  if (exactCellReady.count(K)) return Cell;
  exactCellReady.insert(K);
  if (rootEscaped.count(K.first) || exactPoison.count(K)) {
    Cell.top = true;
    return Cell;
  }
  auto wr = exactWr.find(K);
  if (wr != exactWr.end())
    for (const StoreInst *SI : wr->second) {
      WitSet W = evalValue(SI->getValueOperand(),
                           SI->getModule()->getDataLayout());
      if (Cell.merge(W)) changedThisSweep = true;
    }
  return Cell;
}

WitSet &WitnessTaint::typedCellState(const TypedKey &K,
                                     const DataLayout &DL) {
  WitSet &Cell = typedCell[K];
  if (typedCellReady.count(K)) return Cell;
  typedCellReady.insert(K);
  if (typedPoison.count(K) || typedBulk.count(K.first)) {
    Cell.top = true;
    return Cell;
  }
  auto wr = typedWr.find(K);
  if (wr != typedWr.end())
    for (const StoreInst *SI : wr->second) {
      WitSet W = evalValue(SI->getValueOperand(),
                           SI->getModule()->getDataLayout());
      if (Cell.merge(W)) changedThisSweep = true;
    }
  return Cell;
}

WitSet WitnessTaint::readCell(const WitVal &ptr, const DataLayout &DL) {
  WitSet R;
  if (ptr.kind != 1) {
    R.top = true;
    return R;
  }
  const Value *root = ptr.root;
  if (rootEscaped.count(root)) {
    R.top = true;
    return R;
  }
  if (const auto *GV = dyn_cast<GlobalVariable>(root)) {
    if (GV->isConstant() && GV->hasInitializer()) {
      // rodata read: bounded by initializer facts alone (typed-space
      // aliased writes cannot exist for const objects)
      if (ptr.stride == 0) {
        R.merge(exactCellState({root, ptr.off}, DL));
      } else {
        for (auto &[K, C] : exactCell) {
          if (K.first != root) continue;
          if (K.second >= ptr.off &&
              (uint64_t)(K.second - ptr.off) % ptr.stride == 0)
            R.merge(exactCellState(K, DL));
        }
      }
      return R;
    }
  }
  if (ptr.stride != 0) {
    R.top = true; // var-index over writable object: refuse (v1)
    return R;
  }
  R.merge(exactCellState({root, ptr.off}, DL));
  // aliased writes through memory-obtained pointers land in the typed
  // space: union the root's own struct-type cell when known
  std::string tn;
  if (const auto *GV = dyn_cast<GlobalVariable>(root)) {
    if (auto *ST = dyn_cast<StructType>(GV->getValueType()))
      if (ST->hasName()) tn = stripSuffix(ST->getStructName()).str();
  } else if (const auto *AI = dyn_cast<AllocaInst>(root)) {
    if (auto *ST = dyn_cast<StructType>(AI->getAllocatedType()))
      if (ST->hasName()) tn = stripSuffix(ST->getStructName()).str();
  }
  if (!tn.empty()) R.merge(typedCellState({tn, ptr.off}, DL));
  return R;
}

WitSet WitnessTaint::evalValue(const Value *V, const DataLayout &DL) {
  V = V->stripPointerCasts();
  if (const auto *C = dyn_cast<Constant>(V)) return evalConstant(C, DL);
  auto mit = memo.find(V);
  if (mit != memo.end() && !inProgress.count(V)) return mit->second;
  if (inProgress.count(V)) return memo[V]; // cycle: current state
  inProgress.insert(V);
  WitSet W;
  if (const auto *A = dyn_cast<Argument>(V)) {
    const Function *F = funcDef(A->getParent());
    if (addrTaken.count(F)) {
      W.top = true;
    } else {
      auto ci = directCallers.find(F);
      if (ci == directCallers.end()) {
        // no visible callers: nothing flows (dead or boundary-called
        // without address — boundary callers cannot pass tracked
        // values we'd miss, but they can pass ANYTHING) -> top
        W.top = true;
      } else {
        for (const CallBase *CB : ci->second) {
          if (A->getArgNo() >= CB->arg_size()) {
            W.top = true;
            break;
          }
          W.merge(evalValue(CB->getArgOperand(A->getArgNo()),
                            CB->getModule()->getDataLayout()));
          if (W.top) break;
        }
      }
    }
  } else if (const auto *LI = dyn_cast<LoadInst>(V)) {
    if (!LI->getType()->isPointerTy()) {
      W.top = false; // scalar load: no lattice value
    } else {
      const DataLayout &DLL = LI->getModule()->getDataLayout();
      WitSet P = evalValue(LI->getPointerOperand(), DLL);
      if (!P.top) {
        for (const auto &pv : P.vals) {
          W.merge(readCell(pv, DLL));
          if (W.top) break;
        }
      }
      if (P.top || W.top) {
        // Walk-parity rule: base provenance unknown (heap instance)
        // but the pointer SHAPE names a struct field — read the
        // type-aggregated cell, exactly the regfield walk's key
        // semantics. Without this every heap-container dispatch is
        // top and the pass cannot subsume the fn channel.
        PtrShape S = shapeOf(LI->getPointerOperand(), DLL);
        if (S.hasTyped && S.stride == 0) {
          W = typedCellState({S.typedName, S.typedOff}, DLL);
        } else {
          W = WitSet();
          W.top = true;
        }
      }
    }
  } else if (const auto *G = dyn_cast<GEPOperator>(V)) {
    PtrShape S = shapeOf(G, DL);
    if (!S.root) {
      W.top = true;
    } else if (isa<GlobalVariable>(S.root) || isa<AllocaInst>(S.root)) {
      const Value *R = isa<GlobalVariable>(S.root)
                           ? (const Value *)globDef(
                                 cast<GlobalValue>(S.root))
                           : S.root;
      W.insert({1, R, S.off, S.stride});
    } else {
      // GEP over a computed pointer: shift the base's Obj entries
      WitSet B = evalValue(S.root, DL);
      if (B.top) {
        W.top = true;
      } else {
        for (const auto &bv : B.vals) {
          if (bv.kind != 1 || (bv.stride && S.stride)) {
            W.top = true;
            break;
          }
          W.insert({1, bv.root, bv.off + S.off,
                    bv.stride ? bv.stride : S.stride});
        }
      }
    }
  } else if (const auto *PN = dyn_cast<PHINode>(V)) {
    for (const Value *IV : PN->incoming_values()) {
      W.merge(evalValue(IV, DL));
      if (W.top) break;
    }
  } else if (const auto *SEL = dyn_cast<SelectInst>(V)) {
    W.merge(evalValue(SEL->getTrueValue(), DL));
    if (!W.top) W.merge(evalValue(SEL->getFalseValue(), DL));
  } else if (const auto *AI = dyn_cast<AllocaInst>(V)) {
    W.insert({1, AI, 0, 0});
  } else if (const auto *CB = dyn_cast<CallBase>(V)) {
    const Function *CF = CB->getCalledFunction();
    if (CF && !funcDef(CF)->isDeclaration()) {
      const Function *DF = funcDef(CF);
      for (const BasicBlock &BB : *DF)
        if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
          if (RI->getReturnValue()) {
            W.merge(evalValue(RI->getReturnValue(),
                              DF->getParent()->getDataLayout()));
            if (W.top) break;
          }
    } else {
      W.top = V->getType()->isPointerTy();
    }
  } else if (V->getType()->isPointerTy()) {
    W.top = true; // inttoptr, exotic
  }
  inProgress.erase(V);
  auto &slot = memo[V];
  if (!(slot == W)) {
    slot = W;
    changedThisSweep = true;
  }
  return slot;
}

void WitnessTaint::run() {
  for (auto &mp : Ctx->Modules) indexModule(mp.first);
  errs() << "WitTaint: index " << exactWr.size() << " exact / "
         << typedWr.size() << " typed write keys, " << rootEscaped.size()
         << " escaped roots, " << blindStores
         << " blind stores (stated blind spot)\n";

  // Query all icall operands to fixpoint.
  std::vector<const CallBase *> sites(Ctx->IndirectCallInsts.begin(),
                                      Ctx->IndirectCallInsts.end());
  for (unsigned sweep = 0; sweep < kMaxSweeps; sweep++) {
    changedThisSweep = false;
    // allow re-derivation with grown cells
    memo.clear();
    exactCellReady.clear();
    typedCellReady.clear();
    // NOTE: exactCell/typedCell keep their accumulated contents (the
    // monotone state); ready-flags reset so writers re-evaluate over
    // the new memo.
    for (const CallBase *CB : sites)
      (void)evalValue(CB->getCalledOperand(),
                      CB->getModule()->getDataLayout());
    if (!changedThisSweep) break;
  }

  size_t closed = 0, topSites = 0, mixed = 0, removed = 0, kept = 0,
         emptied = 0;
  for (const CallBase *CB : sites) {
    auto ci = Ctx->Callees.find(const_cast<CallBase *>(CB));
    if (ci == Ctx->Callees.end() || ci->second.empty()) continue;
    WitSet W = evalValue(CB->getCalledOperand(),
                         CB->getModule()->getDataLayout());
    if (W.top) {
      topSites++;
      continue;
    }
    bool pure = !W.vals.empty();
    for (const auto &v : W.vals) pure &= (v.kind == 0);
    if (!pure) {
      mixed++;
      continue;
    }
    FuncSet keep;
    for (const Function *F : ci->second)
      for (const auto &v : W.vals)
        if (v.root == funcDef(F)) {
          keep.insert(F);
          break;
        }
    if (keep.size() == ci->second.size()) continue;
    if (!CFLRegFieldWatch.empty()) {
      StringRef spec(CFLRegFieldWatch);
      for (const Function *F : ci->second) {
        if (keep.count(F)) continue;
        StringRef rest = spec;
        while (!rest.empty()) {
          auto [head, tail] = rest.split(',');
          if (!head.empty() && F->getName() == head)
            errs() << "WitTaint: removes " << F->getName() << " at "
                   << CB->getFunction()->getName() << " (set="
                   << W.vals.size() << ")\n";
          rest = tail;
        }
      }
    }
    removed += ci->second.size() - keep.size();
    kept += keep.size();
    closed++;
    if (keep.empty()) emptied++;
    ci->second = keep;
  }
  errs() << "WitTaint: " << closed << " sites clamped (" << emptied
         << " to EMPTY — review), -" << removed
         << "/+0 pairs (kept " << kept << "); " << topSites
         << " top, " << mixed << " mixed/empty of " << sites.size()
         << " icall sites\n";
}

} // namespace

void runWitnessTaint(GlobalContext *Ctx) { WitnessTaint(Ctx).run(); }
