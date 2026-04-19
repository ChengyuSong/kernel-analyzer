/*
 * IRSidecar — per-function IR fact exporter.
 *
 * Walks each loaded module's function definitions and emits one
 * <bc-basename>.facts.json per module. See todo-kamain-ir-sidecar.md
 * for the schema. v1 emits: effects, branches, int_ops, ranges,
 * features, ir_hash, cg_hash. (aliases/callsites/nondet_sources
 * are out of scope for v1.)
 */

#include "IRSidecar.h"
#include "Annotation.h"
#include "Common.h"

#include <llvm/ADT/APInt.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/KnownBits.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/SHA256.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace llvm;

// ------------ small helpers (file-local) ------------

static std::string sidecarSHA256Hex(StringRef content) {
  SHA256 hasher;
  hasher.update(content);
  auto digest = hasher.final();
#if LLVM_VERSION_MAJOR >= 15
  return toHex(ArrayRef<uint8_t>(digest), /*LowerCase=*/true);
#else
  return toHex(arrayRefFromStringRef(digest), /*LowerCase=*/true);
#endif
}

static std::string getFuncSourceFile(const Function *F) {
  for (const auto &BB : *F) {
    for (const auto &I : BB) {
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
  return F->getParent()->getSourceFileName();
}

static std::string getFuncId(const Function *F) {
  if (F->isIntrinsic())
    return Intrinsic::getBaseName(F->getIntrinsicID()).str();
  if (F->hasExternalLinkage())
    return F->getName().str();
  return getFuncSourceFile(F) + ":" + F->getName().str();
}

// "file:line" or "" when no debug info.
static std::string getInstLoc(const Instruction *I) {
  if (DILocation *Loc = I->getDebugLoc()) {
    StringRef File = Loc->getFilename();
    unsigned Line = Loc->getLine();
    if (Line == 0) {
      if (DILocation *IL = Loc->getInlinedAt())
        Line = IL->getLine();
    }
    if (!File.empty() && Line > 0)
      return (File + ":" + Twine(Line)).str();
  }
  return "";
}

// Print an SSA-style operand name: "%out", "%2", "@global", "i32 5".
static std::string ssaName(const Value *V) {
  std::string s;
  raw_string_ostream os(s);
  V->printAsOperand(os, /*PrintType=*/false);
  return os.str();
}

static std::string typeName(Type *T) {
  std::string s;
  raw_string_ostream os(s);
  T->print(os);
  return os.str();
}

static std::string bbName(const BasicBlock *BB) {
  std::string s;
  raw_string_ostream os(s);
  BB->printAsOperand(os, /*PrintType=*/false);
  return os.str();
}

// Render an APInt as a signed decimal string, regardless of width.
static std::string apintSigned(const APInt &V) {
  SmallString<32> S;
  V.toString(S, 10, /*Signed=*/true);
  return std::string(S);
}

static std::string apintUnsigned(const APInt &V) {
  SmallString<32> S;
  V.toString(S, 10, /*Signed=*/false);
  return std::string(S);
}

// Strip llvm intrinsic version suffix: "llvm.memcpy.p0.p0.i64" -> "llvm.memcpy".
static std::string calleeNameOf(const CallBase *CB) {
  if (const Function *F = CB->getCalledFunction())
    return getFuncId(F);
  return "<indirect>";
}

// Render an AttributeSet as a JSON array of textual attributes.
// Captures enum / int / type attrs (e.g. "nounwind", "memory(read)",
// "align 8", "dereferenceable(16)", "byval(%struct.S)"). Skips string
// attrs — those are codegen-only noise like "target-cpu"="x86-64",
// "frame-pointer"="all", "stack-protector-buffer-size"="8" that the
// Clang frontend pins onto every function and that Phase 3 doesn't
// need for semantic reasoning.
static json::Array attrSetToJson(AttributeSet AS) {
  json::Array Out;
  for (Attribute A : AS) {
    if (!A.isValid() || A.isStringAttribute())
      continue;
    Out.push_back(A.getAsString(/*InAttrGrp=*/false));
  }
  return Out;
}

// Build {function, return, params[]} attr block from any AttributeList.
// Works for both Function and CallBase since both expose getAttributes().
static json::Object attrListToJson(const AttributeList &AL, unsigned numArgs) {
  json::Object O;
  O["function"] = attrSetToJson(AL.getFnAttrs());
  O["return"] = attrSetToJson(AL.getRetAttrs());
  json::Array Params;
  for (unsigned i = 0; i < numArgs; i++)
    Params.push_back(attrSetToJson(AL.getParamAttrs(i)));
  O["params"] = std::move(Params);
  return O;
}

// Atomic ordering -> string. Empty for NotAtomic so callers can omit.
static std::string atomicOrderingStr(AtomicOrdering AO) {
  switch (AO) {
    case AtomicOrdering::NotAtomic:              return "";
    case AtomicOrdering::Unordered:              return "unordered";
    case AtomicOrdering::Monotonic:              return "monotonic";
    case AtomicOrdering::Acquire:                return "acquire";
    case AtomicOrdering::Release:                return "release";
    case AtomicOrdering::AcquireRelease:         return "acq_rel";
    case AtomicOrdering::SequentiallyConsistent: return "seq_cst";
  }
  return "";
}

// True iff Ptr is a GEP (instruction or constexpr) carrying inbounds.
// One-step lookback only — chasing further would duplicate alias analysis.
static bool ptrIsInboundsGEP(const Value *Ptr) {
  if (auto *GEP = dyn_cast<GEPOperator>(Ptr))
    return GEP->isInBounds();
  return false;
}

static const char *atomicRMWOpStr(AtomicRMWInst::BinOp Op) {
  switch (Op) {
    case AtomicRMWInst::Xchg: return "xchg";
    case AtomicRMWInst::Add:  return "add";
    case AtomicRMWInst::Sub:  return "sub";
    case AtomicRMWInst::And:  return "and";
    case AtomicRMWInst::Nand: return "nand";
    case AtomicRMWInst::Or:   return "or";
    case AtomicRMWInst::Xor:  return "xor";
    case AtomicRMWInst::Max:  return "max";
    case AtomicRMWInst::Min:  return "min";
    case AtomicRMWInst::UMax: return "umax";
    case AtomicRMWInst::UMin: return "umin";
    case AtomicRMWInst::FAdd: return "fadd";
    case AtomicRMWInst::FSub: return "fsub";
    default:                  return "unknown";
  }
}

// Extract recognized load metadata into a JSON object: !range, !nonnull,
// !dereferenceable, !invariant.load. Returns empty Object if none present.
// Skip TBAA / !alias.scope / !noalias / !prof / !nontemporal — consumer
// can't act on them and they balloon the file.
static json::Object loadMetadataToJson(const LoadInst &LI) {
  json::Object MD;

  if (MDNode *RM = LI.getMetadata(LLVMContext::MD_range)) {
    json::Array Ranges;
    for (unsigned i = 0; i + 1 < RM->getNumOperands(); i += 2) {
      auto *Lo = mdconst::dyn_extract<ConstantInt>(RM->getOperand(i));
      auto *Hi = mdconst::dyn_extract<ConstantInt>(RM->getOperand(i + 1));
      if (!Lo || !Hi) continue;
      json::Array Pair;
      Pair.push_back(apintSigned(Lo->getValue()));
      Pair.push_back(apintSigned(Hi->getValue()));
      Ranges.push_back(std::move(Pair));
    }
    if (!Ranges.empty()) MD["range"] = std::move(Ranges);
  }

  if (LI.getMetadata(LLVMContext::MD_nonnull))
    MD["nonnull"] = true;

  if (MDNode *DM = LI.getMetadata(LLVMContext::MD_dereferenceable)) {
    if (DM->getNumOperands() >= 1) {
      if (auto *CI = mdconst::dyn_extract<ConstantInt>(DM->getOperand(0)))
        MD["dereferenceable"] = static_cast<int64_t>(CI->getZExtValue());
    }
  }

  if (LI.getMetadata(LLVMContext::MD_invariant_load))
    MD["invariant"] = true;

  return MD;
}

// True iff all sub-arrays in an attr block are empty — used to skip
// emitting noisy callsite_attrs when the callsite adds nothing over
// the callee's declared attrs.
static bool isAttrBlockEmpty(const json::Object &O) {
  auto isEmpty = [](const json::Value *V) {
    if (!V) return true;
    const json::Array *A = V->getAsArray();
    return !A || A->empty();
  };
  if (!isEmpty(O.get("function"))) return false;
  if (!isEmpty(O.get("return"))) return false;
  const json::Array *P = O.get("params") ? O.get("params")->getAsArray() : nullptr;
  if (P) {
    for (const auto &v : *P) {
      const json::Array *A = v.getAsArray();
      if (A && !A->empty()) return false;
    }
  }
  return true;
}

// ------------ per-function emitter ------------

namespace {

class FuncEmitter {
public:
  FuncEmitter(const Function *F_, GlobalContext *Ctx_)
    : F(F_), Ctx(Ctx_), DL(F_->getParent()->getDataLayout()) {}

  json::Object emit();

private:
  const Function *F;
  GlobalContext *Ctx;
  const DataLayout &DL;

  unsigned eIdCounter = 0, bIdCounter = 0, ioIdCounter = 0, rIdCounter = 0;

  json::Array effects;
  json::Array branches;
  json::Array int_ops;
  json::Array ranges;

  // Value -> range id (for dedup across int_ops references).
  DenseMap<const Value *, std::string> rangeIds;

  // Feature counts (derived).
  unsigned allocCount = 0, freeCount = 0;
  unsigned storeCount = 0, loadCount = 0;
  unsigned callCount = 0, indirectCallCount = 0;
  unsigned signedArithCount = 0;  // add/sub/mul with nsw set
  unsigned divCount = 0;          // sdiv/udiv/srem/urem
  unsigned shiftCount = 0;        // shl/ashr/lshr
  unsigned signCastCount = 0;     // trunc/sext/zext

  std::string nextEId() { return "e" + std::to_string(++eIdCounter); }
  std::string nextBId() { return "b" + std::to_string(++bIdCounter); }
  std::string nextIoId() { return "io" + std::to_string(++ioIdCounter); }
  std::string nextRId() { return "r" + std::to_string(++rIdCounter); }

  // Compute (or look up) a range id for an integer-typed Value via
  // computeKnownBits. Returns "" if V is not integer-typed or no range
  // info is recoverable.
  std::string ensureRange(const Value *V) {
    if (!V || !V->getType()->isIntegerTy())
      return "";
    auto it = rangeIds.find(V);
    if (it != rangeIds.end())
      return it->second;

    KnownBits KB = computeKnownBits(V, DL);
    // Skip if everything is unknown — no signal.
    if (KB.isUnknown())
      return "";

    std::string id = nextRId();
    rangeIds[V] = id;

    json::Object R;
    R["id"] = id;
    R["ssa"] = ssaName(V);
    R["bitwidth"] = static_cast<int64_t>(KB.getBitWidth());
    R["min_signed"] = apintSigned(KB.getSignedMinValue());
    R["max_signed"] = apintSigned(KB.getSignedMaxValue());
    R["min_unsigned"] = apintUnsigned(KB.getMinValue());
    R["max_unsigned"] = apintUnsigned(KB.getMaxValue());
    if (auto *I = dyn_cast<Instruction>(V)) {
      std::string loc = getInstLoc(I);
      if (!loc.empty()) R["loc"] = loc;
    }
    ranges.push_back(std::move(R));
    return id;
  }

  void visitInst(const Instruction &I);
  void emitStore(const StoreInst &SI);
  void emitLoad(const LoadInst &LI);
  void emitAtomicRMW(const AtomicRMWInst &AI);
  void emitCmpXchg(const AtomicCmpXchgInst &CX);
  void emitCall(const CallBase &CB);
  void emitReturn(const ReturnInst &RI);
  void emitBranch(const BranchInst &BR);
  void emitBinOp(const BinaryOperator &BO);
  void emitCast(const CastInst &CI);
};

void FuncEmitter::emitStore(const StoreInst &SI) {
  storeCount++;
  json::Object E;
  E["id"] = nextEId();
  E["kind"] = "write";
  E["target"] = ssaName(SI.getPointerOperand());
  E["value"] = ssaName(SI.getValueOperand());
  E["guard_bb"] = bbName(SI.getParent());
  std::string loc = getInstLoc(&SI);
  if (!loc.empty()) E["loc"] = loc;
  E["align"] = static_cast<int64_t>(SI.getAlign().value());
  if (SI.isVolatile()) E["volatile"] = true;
  std::string ord = atomicOrderingStr(SI.getOrdering());
  if (!ord.empty()) E["atomic"] = ord;
  if (ptrIsInboundsGEP(SI.getPointerOperand())) E["inbounds"] = true;
  effects.push_back(std::move(E));
}

void FuncEmitter::emitLoad(const LoadInst &LI) {
  loadCount++;
  json::Object E;
  E["id"] = nextEId();
  E["kind"] = "read";
  E["target_ssa"] = ssaName(&LI);
  E["source"] = ssaName(LI.getPointerOperand());
  E["guard_bb"] = bbName(LI.getParent());
  std::string loc = getInstLoc(&LI);
  if (!loc.empty()) E["loc"] = loc;
  E["align"] = static_cast<int64_t>(LI.getAlign().value());
  if (LI.isVolatile()) E["volatile"] = true;
  std::string ord = atomicOrderingStr(LI.getOrdering());
  if (!ord.empty()) E["atomic"] = ord;
  if (ptrIsInboundsGEP(LI.getPointerOperand())) E["inbounds"] = true;
  json::Object MD = loadMetadataToJson(LI);
  if (!MD.empty()) E["load_md"] = std::move(MD);
  effects.push_back(std::move(E));
}

void FuncEmitter::emitAtomicRMW(const AtomicRMWInst &AI) {
  json::Object E;
  E["id"] = nextEId();
  E["kind"] = "atomicrmw";
  E["op"] = atomicRMWOpStr(AI.getOperation());
  E["target"] = ssaName(AI.getPointerOperand());
  E["value"] = ssaName(AI.getValOperand());
  if (!AI.getType()->isVoidTy())
    E["target_ssa"] = ssaName(&AI);
  E["guard_bb"] = bbName(AI.getParent());
  std::string loc = getInstLoc(&AI);
  if (!loc.empty()) E["loc"] = loc;
  E["align"] = static_cast<int64_t>(AI.getAlign().value());
  std::string ord = atomicOrderingStr(AI.getOrdering());
  if (!ord.empty()) E["atomic"] = ord;
  if (ptrIsInboundsGEP(AI.getPointerOperand())) E["inbounds"] = true;
  effects.push_back(std::move(E));
}

void FuncEmitter::emitCmpXchg(const AtomicCmpXchgInst &CX) {
  json::Object E;
  E["id"] = nextEId();
  E["kind"] = "cmpxchg";
  E["target"] = ssaName(CX.getPointerOperand());
  E["compare"] = ssaName(CX.getCompareOperand());
  E["new_value"] = ssaName(CX.getNewValOperand());
  E["target_ssa"] = ssaName(&CX);
  E["guard_bb"] = bbName(CX.getParent());
  std::string loc = getInstLoc(&CX);
  if (!loc.empty()) E["loc"] = loc;
  E["align"] = static_cast<int64_t>(CX.getAlign().value());
  std::string sord = atomicOrderingStr(CX.getSuccessOrdering());
  std::string ford = atomicOrderingStr(CX.getFailureOrdering());
  if (!sord.empty()) E["atomic_success"] = sord;
  if (!ford.empty()) E["atomic_failure"] = ford;
  if (ptrIsInboundsGEP(CX.getPointerOperand())) E["inbounds"] = true;
  effects.push_back(std::move(E));
}

void FuncEmitter::emitCall(const CallBase &CB) {
  // Skip pure debug intrinsics.
  if (isa<DbgInfoIntrinsic>(&CB))
    return;
  // Skip lifetime/assume markers — noise.
  if (const IntrinsicInst *II = dyn_cast<IntrinsicInst>(&CB)) {
    switch (II->getIntrinsicID()) {
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
    case Intrinsic::assume:
    case Intrinsic::donothing:
    case Intrinsic::sideeffect:
      return;
    default:
      break;
    }
  }

  std::string callee = calleeNameOf(&CB);
  bool isIndirect = (CB.getCalledFunction() == nullptr) && !CB.isInlineAsm();

  // Categorize: alloc / free / generic call.
  const Function *CF = CB.getCalledFunction();
  bool isAlloc = false, isFree = false;
  if (CF) {
    StringRef Name = CF->getName();
    if (Ctx->AllocFuncs.count(CF) || isAllocFn(Name))
      isAlloc = true;
    else if (isFreeFn(Name))
      isFree = true;
  } else if (Ctx->AllocSites.count(&CB)) {
    isAlloc = true;
  }

  json::Object E;
  E["id"] = nextEId();
  E["guard_bb"] = bbName(CB.getParent());
  std::string loc = getInstLoc(&CB);
  if (!loc.empty()) E["loc"] = loc;

  if (isAlloc) {
    allocCount++;
    E["kind"] = "alloc";
    E["via"] = callee;
    if (!CB.getType()->isVoidTy())
      E["target_ssa"] = ssaName(&CB);
    // Heuristic: first integer-typed arg is the size expression.
    for (unsigned i = 0; i < CB.arg_size(); ++i) {
      Value *A = CB.getArgOperand(i);
      if (A->getType()->isIntegerTy()) {
        E["size_ssa"] = ssaName(A);
        std::string rid = ensureRange(A);
        if (!rid.empty()) E["size_range"] = rid;
        break;
      }
    }
  } else if (isFree) {
    freeCount++;
    E["kind"] = "free";
    E["via"] = callee;
    if (CB.arg_size() > 0)
      E["target_ssa"] = ssaName(CB.getArgOperand(0));
  } else {
    callCount++;
    if (isIndirect) indirectCallCount++;
    E["kind"] = "call";
    E["callee"] = callee;
    E["indirect"] = isIndirect;
    json::Array args;
    for (unsigned i = 0; i < CB.arg_size(); ++i)
      args.push_back(ssaName(CB.getArgOperand(i)));
    E["args_ssa"] = std::move(args);
    if (!CB.getType()->isVoidTy())
      E["return_ssa"] = ssaName(&CB);
    // Per-callsite attribute overrides — emit only when non-empty.
    json::Object CSAttrs = attrListToJson(CB.getAttributes(),
                                          static_cast<unsigned>(CB.arg_size()));
    if (!isAttrBlockEmpty(CSAttrs))
      E["callsite_attrs"] = std::move(CSAttrs);
  }
  effects.push_back(std::move(E));
}

void FuncEmitter::emitReturn(const ReturnInst &RI) {
  json::Object E;
  E["id"] = nextEId();
  E["kind"] = "return";
  E["guard_bb"] = bbName(RI.getParent());
  if (RI.getReturnValue())
    E["value_ssa"] = ssaName(RI.getReturnValue());
  std::string loc = getInstLoc(&RI);
  if (!loc.empty()) E["loc"] = loc;
  effects.push_back(std::move(E));
}

void FuncEmitter::emitBranch(const BranchInst &BR) {
  if (!BR.isConditional())
    return;
  json::Object B;
  B["id"] = nextBId();
  B["cond"] = ssaName(BR.getCondition());
  const BasicBlock *T = BR.getSuccessor(0);
  const BasicBlock *FBB = BR.getSuccessor(1);
  B["true_bb"] = bbName(T);
  B["false_bb"] = bbName(FBB);
  std::string loc = getInstLoc(&BR);
  if (!loc.empty()) B["loc"] = loc;

  // Mark dead sides if LLVM emitted unreachable as the immediate terminator.
  bool tDead = isa<UnreachableInst>(T->getTerminator());
  bool fDead = isa<UnreachableInst>(FBB->getTerminator());
  if (tDead && !fDead) B["unreachable_side"] = "true";
  else if (fDead && !tDead) B["unreachable_side"] = "false";
  else if (tDead && fDead) B["unreachable_side"] = "both";
  branches.push_back(std::move(B));
}

void FuncEmitter::emitBinOp(const BinaryOperator &BO) {
  unsigned op = BO.getOpcode();
  bool isArith = false, isDiv = false, isShift = false;
  const char *opName = nullptr;
  bool divIsSigned = false;
  switch (op) {
    case Instruction::Add: opName = "add"; isArith = true; break;
    case Instruction::Sub: opName = "sub"; isArith = true; break;
    case Instruction::Mul: opName = "mul"; isArith = true; break;
    case Instruction::SDiv: opName = "sdiv"; isDiv = true; divIsSigned = true; break;
    case Instruction::UDiv: opName = "udiv"; isDiv = true; break;
    case Instruction::SRem: opName = "srem"; isDiv = true; divIsSigned = true; break;
    case Instruction::URem: opName = "urem"; isDiv = true; break;
    case Instruction::Shl:  opName = "shl";  isShift = true; break;
    case Instruction::AShr: opName = "ashr"; isShift = true; break;
    case Instruction::LShr: opName = "lshr"; isShift = true; break;
    default: return;
  }

  bool nsw = false, nuw = false;
  if (auto *OBO = dyn_cast<OverflowingBinaryOperator>(&BO)) {
    nsw = OBO->hasNoSignedWrap();
    nuw = OBO->hasNoUnsignedWrap();
  }
  if (nsw) signedArithCount++;
  if (isDiv) divCount++;
  if (isShift) shiftCount++;

  json::Object O;
  O["id"] = nextIoId();
  O["op"] = opName;
  O["type"] = typeName(BO.getType());
  O["lhs_ssa"] = ssaName(BO.getOperand(0));
  O["rhs_ssa"] = ssaName(BO.getOperand(1));

  // wraps_legally: true iff !nsw — for add/sub/mul/shl.
  if (isArith || op == Instruction::Shl) {
    O["nsw"] = nsw;
    O["nuw"] = nuw;
    O["wraps_legally"] = !nsw;
  }

  if (isDiv) {
    O["signed"] = divIsSigned;
    O["rhs_nonzero"] = isKnownNonZero(BO.getOperand(1), DL);
    std::string rid = ensureRange(BO.getOperand(1));
    if (!rid.empty()) O["rhs_range"] = rid;
  }

  if (isShift) {
    Value *Amt = BO.getOperand(1);
    O["amt_ssa"] = ssaName(Amt);
    std::string rid = ensureRange(Amt);
    if (!rid.empty()) O["amt_range"] = rid;
    bool amtInRange = false;
    if (auto *IT = dyn_cast<IntegerType>(BO.getType())) {
      KnownBits KB = computeKnownBits(Amt, DL);
      // amt_in_range iff max possible amount < bitwidth.
      amtInRange = !KB.isUnknown() && KB.getMaxValue().ult(IT->getBitWidth());
    }
    O["amt_in_range"] = amtInRange;
  }

  // Range refs for arithmetic operands — useful for boundary reasoning.
  if (isArith) {
    std::string lr = ensureRange(BO.getOperand(0));
    std::string rr = ensureRange(BO.getOperand(1));
    if (!lr.empty()) O["lhs_range"] = lr;
    if (!rr.empty()) O["rhs_range"] = rr;
  }
  std::string loc = getInstLoc(&BO);
  if (!loc.empty()) O["loc"] = loc;
  int_ops.push_back(std::move(O));
}

void FuncEmitter::emitCast(const CastInst &CI) {
  unsigned op = CI.getOpcode();
  const char *opName = nullptr;
  switch (op) {
    case Instruction::Trunc: opName = "trunc"; break;
    case Instruction::SExt:  opName = "sext";  break;
    case Instruction::ZExt:  opName = "zext";  break;
    default: return;
  }
  signCastCount++;

  json::Object O;
  O["id"] = nextIoId();
  O["op"] = opName;
  O["from"] = typeName(CI.getSrcTy());
  O["to"] = typeName(CI.getDestTy());
  O["src_ssa"] = ssaName(CI.getOperand(0));
  std::string rid = ensureRange(CI.getOperand(0));
  if (!rid.empty()) O["src_range"] = rid;

  // src_fits_dst:
  //  - zext/sext widen, so the src value always fits in dst by construction.
  //  - trunc narrows; check src ConstantRange fits in dst width.
  bool srcFitsDst = false;
  if (op == Instruction::ZExt || op == Instruction::SExt) {
    srcFitsDst = true;
  } else if (op == Instruction::Trunc) {
    if (auto *DT = dyn_cast<IntegerType>(CI.getDestTy())) {
      KnownBits KB = computeKnownBits(CI.getOperand(0), DL);
      if (!KB.isUnknown()) {
        unsigned dstBits = DT->getBitWidth();
        bool fitsUnsigned = KB.getMaxValue().isIntN(dstBits);
        bool fitsSigned = KB.getSignedMinValue().isSignedIntN(dstBits) &&
                          KB.getSignedMaxValue().isSignedIntN(dstBits);
        srcFitsDst = fitsUnsigned && fitsSigned;
      }
    }
  }
  O["src_fits_dst"] = srcFitsDst;
  std::string loc = getInstLoc(&CI);
  if (!loc.empty()) O["loc"] = loc;
  int_ops.push_back(std::move(O));
}

void FuncEmitter::visitInst(const Instruction &I) {
  if (auto *SI = dyn_cast<StoreInst>(&I)) emitStore(*SI);
  else if (auto *LI = dyn_cast<LoadInst>(&I)) emitLoad(*LI);
  else if (auto *AI = dyn_cast<AtomicRMWInst>(&I)) emitAtomicRMW(*AI);
  else if (auto *CX = dyn_cast<AtomicCmpXchgInst>(&I)) emitCmpXchg(*CX);
  else if (auto *CB = dyn_cast<CallBase>(&I)) emitCall(*CB);
  else if (auto *RI = dyn_cast<ReturnInst>(&I)) emitReturn(*RI);
  else if (auto *BR = dyn_cast<BranchInst>(&I)) emitBranch(*BR);
  else if (auto *BO = dyn_cast<BinaryOperator>(&I)) emitBinOp(*BO);
  else if (auto *CI = dyn_cast<CastInst>(&I)) emitCast(*CI);
}

json::Object FuncEmitter::emit() {
  // Walk in deterministic order (BB order, then instruction order).
  for (const auto &BB : *F)
    for (const auto &I : BB)
      visitInst(I);

  // Function body hash (textual IR — equivalent to bitcode for invalidation).
  std::string irText;
  {
    raw_string_ostream os(irText);
    F->print(os, /*AAW=*/nullptr, /*ShouldPreserveUseListOrder=*/false,
            /*IsForDebug=*/false);
  }
  std::string ir_hash = sidecarSHA256Hex(irText);

  // Callgraph hash: sorted callee-id list across all callsites in F.
  std::vector<std::string> callees;
  for (const auto &BB : *F) {
    for (const auto &I : BB) {
      const CallBase *CB = dyn_cast<CallBase>(&I);
      if (!CB) continue;
      auto it = Ctx->Callees.find(CB);
      if (it == Ctx->Callees.end()) continue;
      for (const Function *Callee : it->second)
        callees.push_back(getFuncId(Callee));
    }
  }
  std::sort(callees.begin(), callees.end());
  callees.erase(std::unique(callees.begin(), callees.end()), callees.end());
  std::string cgMaterial;
  for (auto &c : callees) { cgMaterial.append(c); cgMaterial.push_back('\n'); }
  std::string cg_hash = sidecarSHA256Hex(cgMaterial);

  // Signature features.
  unsigned ptrParams = 0;
  for (const Argument &A : F->args())
    if (A.getType()->isPointerTy()) ptrParams++;
  bool returnIsPtr = F->getReturnType()->isPointerTy();

  json::Object Features;
  Features["alloc_count"] = static_cast<int64_t>(allocCount);
  Features["free_count"] = static_cast<int64_t>(freeCount);
  Features["store_count"] = static_cast<int64_t>(storeCount);
  Features["load_count"] = static_cast<int64_t>(loadCount);
  Features["call_count"] = static_cast<int64_t>(callCount);
  Features["indirect_call_count"] = static_cast<int64_t>(indirectCallCount);
  Features["branch_count"] = static_cast<int64_t>(bIdCounter);
  Features["signed_arith_count"] = static_cast<int64_t>(signedArithCount);
  Features["div_count"] = static_cast<int64_t>(divCount);
  Features["shift_count"] = static_cast<int64_t>(shiftCount);
  Features["sign_changing_cast_count"] = static_cast<int64_t>(signCastCount);
  Features["ptr_params"] = static_cast<int64_t>(ptrParams);
  Features["return_is_ptr"] = returnIsPtr;
  Features["arg_count"] = static_cast<int64_t>(F->arg_size());
  Features["is_vararg"] = F->isVarArg();

  json::Object Out;
  Out["function"] = getFuncId(F);
  Out["ir_hash"] = ir_hash;
  Out["cg_hash"] = cg_hash;
  Out["effects"] = std::move(effects);
  Out["branches"] = std::move(branches);
  Out["int_ops"] = std::move(int_ops);
  Out["ranges"] = std::move(ranges);
  Out["features"] = std::move(Features);
  Out["attrs"] = attrListToJson(F->getAttributes(),
                                static_cast<unsigned>(F->arg_size()));
  return Out;
}

} // end anonymous namespace

// ------------ exporter entry point ------------

void IRSidecarExporter::dump(StringRef Dir) {
  if (Dir.empty()) return;

  std::error_code EC = sys::fs::create_directories(Dir);
  if (EC) {
    WARNING("IRSidecar: failed to create dir " << Dir << ": "
            << EC.message() << "\n");
    return;
  }

  std::set<std::string> usedBasenames;
  size_t totalFuncs = 0, totalFiles = 0;

  for (auto &[M, ModName] : Ctx->Modules) {
    auto pathIt = Ctx->ModuleMaps.find(M);
    StringRef bcPath = (pathIt != Ctx->ModuleMaps.end())
                       ? pathIt->second
                       : ModName;

    // Derive sidecar filename from basename. Warn on collision but
    // overwrite — caller is expected to keep basenames unique within
    // a sidecar dir.
    StringRef base = sys::path::filename(bcPath);
    std::string outName = (base + ".facts.json").str();
    if (!usedBasenames.insert(outName).second) {
      WARNING("IRSidecar: duplicate basename '" << base << "' in "
              << Dir << "; later module overwrites earlier output\n");
    }

    SmallString<256> outPath(Dir);
    sys::path::append(outPath, outName);

    json::Object Functions;
    size_t funcCount = 0;
    for (Function &F : *M) {
      if (F.isDeclaration() || F.empty()) continue;
      if (F.isIntrinsic()) continue;

      // Skip non-canonical defs (weak/linkonce dupes from other modules
      // already covered by their canonical sidecar).
      if (!F.hasLocalLinkage()) {
        auto fIt = Ctx->Funcs.find(F.getGUID());
        if (fIt != Ctx->Funcs.end() && fIt->second != &F)
          continue;
      }

      FuncEmitter FE(&F, Ctx);
      json::Object FuncObj = FE.emit();
      std::string FID = getFuncId(&F);
      Functions[FID] = std::move(FuncObj);
      funcCount++;
    }

    json::Object Metadata;
    Metadata["version"] = 1;
    Metadata["bc_path"] = bcPath.str();
    Metadata["total_functions"] = static_cast<int64_t>(funcCount);

    json::Object Root;
    Root["metadata"] = std::move(Metadata);
    Root["functions"] = std::move(Functions);

    std::error_code FEC;
    raw_fd_ostream OS(outPath, FEC);
    if (FEC) {
      WARNING("IRSidecar: failed to open " << outPath
              << " for writing: " << FEC.message() << "\n");
      continue;
    }
    OS << json::Value(std::move(Root)) << "\n";
    totalFuncs += funcCount;
    totalFiles++;
  }

  errs() << "[IRSidecar] wrote " << totalFiles << " sidecar file(s), "
         << totalFuncs << " function(s) total to " << Dir << "\n";
}
