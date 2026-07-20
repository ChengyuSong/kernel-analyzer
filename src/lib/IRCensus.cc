/*
 * IR-construct coverage census (task: encoder totality audit)
 *
 * Enumerates instruction opcodes, intrinsics, external callees, inline
 * asm, constant-expression kinds and pointer-relevant operand shapes
 * across the loaded corpus, and classifies each against a disposition
 * table derived from CallGraphPass::InstHandler (the CFL edge builder's
 * visitor). Output categories:
 *   HANDLED    — a visitor emits edges for it
 *   NOOP       — deliberately no edges, with a written justification
 *   SUSPECT    — pointer-relevant but NOT visited (silent default
 *                handler) — each is a potential encoder unsoundness
 *   UNDISP     — not in the table at all; the census exists to make
 *                these loud
 *
 * Copyright (C) 2026 Chengyu Song
 * For licensing details see LICENSE
 */

#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

#include <cassert>
#include <cstdio>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <algorithm>

#include "IRCensus.h"

using namespace llvm;

namespace {

struct Disposition {
  const char *status; // HANDLED / NOOP / SUSPECT
  const char *note;
};

// Source of truth: CallGraphPass::InstHandler visit list (CallGraph.h)
// plus reviewed no-ops. Everything absent here reports as UNDISP.
const std::map<unsigned, Disposition> &opcodeTable() {
  static const std::map<unsigned, Disposition> T = {
    // --- visited by InstHandler: emits edges ---
    {Instruction::Ret, {"HANDLED", "visitReturnInst"}},
    {Instruction::Call, {"HANDLED", "visitCallBase"}},
    {Instruction::Invoke, {"HANDLED", "visitCallBase"}},
    {Instruction::CallBr, {"HANDLED", "visitCallBase"}},
    {Instruction::Alloca, {"HANDLED", "visitAllocaInst (origin)"}},
    {Instruction::Load, {"HANDLED", "visitLoadInst (d-edges)"}},
    {Instruction::Store, {"HANDLED", "visitStoreInst (d-edges)"}},
    {Instruction::GetElementPtr, {"HANDLED", "visitGetElementPtrInst (f)"}},
    {Instruction::BitCast, {"HANDLED", "visitBitCastInst (a)"}},
    {Instruction::PHI, {"HANDLED", "visitPHINode (a per incoming)"}},
    {Instruction::Select, {"HANDLED", "visitSelectInst (a per arm)"}},
    {Instruction::ExtractElement, {"HANDLED", "visitExtractElementInst"}},
    {Instruction::InsertElement, {"HANDLED", "visitInsertElementInst"}},
    {Instruction::ShuffleVector, {"HANDLED", "visitShuffleVectorInst"}},
    {Instruction::ExtractValue, {"HANDLED", "visitExtractValueInst"}},
    {Instruction::InsertValue, {"HANDLED", "visitInsertValueInst"}},
    {Instruction::IntToPtr, {"HANDLED", "visitIntToPtrInst"}},
    {Instruction::PtrToInt, {"HANDLED", "visitPtrToIntInst"}},
    {Instruction::VAArg, {"HANDLED", "visitVAArgInst"}},
    // binary operators — one visitor covers the whole range
    {Instruction::Add, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::FAdd, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::Sub, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::FSub, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::Mul, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::FMul, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::UDiv, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::SDiv, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::FDiv, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::URem, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::SRem, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::FRem, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::Shl, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::LShr, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::AShr, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::And, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::Or, {"HANDLED", "visitBinaryOperator"}},
    {Instruction::Xor, {"HANDLED", "visitBinaryOperator"}},
    // --- justified no-ops: no pointer data can flow ---
    {Instruction::Br, {"NOOP", "control flow only"}},
    {Instruction::Switch, {"NOOP", "control flow only"}},
    {Instruction::IndirectBr, {"NOOP", "blockaddress targets, control only"}},
    {Instruction::Unreachable, {"NOOP", "control flow only"}},
    {Instruction::Fence, {"NOOP", "no data operands"}},
    {Instruction::ICmp, {"NOOP", "produces i1, ptr operands not forwarded"}},
    {Instruction::FCmp, {"NOOP", "produces i1"}},
    {Instruction::FNeg, {"NOOP", "float only"}},
    {Instruction::FPTrunc, {"NOOP", "float only"}},
    {Instruction::FPExt, {"NOOP", "float only"}},
    {Instruction::UIToFP, {"NOOP", "float result"}},
    {Instruction::SIToFP, {"NOOP", "float result"}},
    {Instruction::FPToUI, {"NOOP", "int result from float"}},
    {Instruction::FPToSI, {"NOOP", "int result from float"}},
    // rare EH machinery, count but don't alarm (reviewed: no fptr flow
    // we consume; landingpad/resume are the ones that matter and they
    // are SUSPECT below)
    {Instruction::CatchPad, {"NOOP", "windows EH, absent from corpora"}},
    {Instruction::CleanupPad, {"NOOP", "windows EH"}},
    {Instruction::CatchSwitch, {"NOOP", "windows EH"}},
    {Instruction::CatchRet, {"NOOP", "windows EH"}},
    {Instruction::CleanupRet, {"NOOP", "windows EH"}},
    // --- pointer-relevant but NOT visited: silent default today ---
    {Instruction::AtomicRMW, {"HANDLED",
       "visitAtomicRMWInst (ptr xchg = fused store+load)"}},
    {Instruction::AtomicCmpXchg, {"HANDLED",
       "visitAtomicCmpXchgInst (store + old into {old,i1})"}},
    {Instruction::Freeze, {"HANDLED", "visitFreezeInst (copy)"}},
    {Instruction::AddrSpaceCast, {"HANDLED",
       "visitAddrSpaceCastInst (copy)"}},
    {Instruction::Trunc, {"SUSPECT",
       "int provenance chains (ptrtoint laundering)"}},
    {Instruction::ZExt, {"SUSPECT",
       "int provenance chains (ptrtoint laundering)"}},
    {Instruction::SExt, {"SUSPECT",
       "int provenance chains (ptrtoint laundering)"}},
    {Instruction::LandingPad, {"SUSPECT",
       "yields {exn ptr, sel} — thrown-object flow (C++ corpora)"}},
    {Instruction::Resume, {"SUSPECT",
       "rethrow consumes {exn ptr, sel}"}},
  };
  return T;
}

// prefix -> disposition for intrinsics
const std::vector<std::pair<const char *, Disposition>> &intrinsicTable() {
  static const std::vector<std::pair<const char *, Disposition>> T = {
    {"llvm.memcpy", {"HANDLED", "handleMemcpy / visitMemTransferInst"}},
    {"llvm.memmove", {"HANDLED", "handleMemcpy / visitMemTransferInst"}},
    {"llvm.memset", {"HANDLED", "visitMemSetInst"}},
    {"llvm.dbg.", {"NOOP", "debug info"}},
    {"llvm.lifetime.", {"NOOP", "lifetime markers"}},
    {"llvm.assume", {"NOOP", "no data flow"}},
    {"llvm.expect", {"SUSPECT", "forwards first operand (usually int)"}},
    {"llvm.prefetch", {"NOOP", "hint"}},
    {"llvm.donothing", {"NOOP", "nop"}},
    {"llvm.trap", {"NOOP", "control"}},
    {"llvm.debugtrap", {"NOOP", "control"}},
    {"llvm.ubsantrap", {"NOOP", "control"}},
    {"llvm.stackprotector", {"NOOP", "guard slot"}},
    {"llvm.stacksave", {"NOOP", "stack ptr, not an object"}},
    {"llvm.stackrestore", {"NOOP", "stack ptr"}},
    {"llvm.va_start", {"NOOP", "modeled via vararg node wiring"}},
    {"llvm.va_end", {"NOOP", "modeled via vararg node wiring"}},
    {"llvm.va_copy", {"SUSPECT", "copies va_list state — review wiring"}},
    {"llvm.eh.typeid.for", {"NOOP", "int result"}},
    {"llvm.eh.sjlj", {"SUSPECT", "sjlj EH state"}},
    {"llvm.frameaddress", {"NOOP", "opaque frame ptr"}},
    {"llvm.returnaddress", {"NOOP", "opaque code ptr"}},
    {"llvm.thread.pointer", {"SUSPECT", "TLS base ptr — review percpu/TLS use"}},
    {"llvm.ptr.annotation", {"SUSPECT", "forwards annotated ptr"}},
    {"llvm.annotation", {"NOOP", "int annotation"}},
    {"llvm.var.annotation", {"NOOP", "marker"}},
    {"llvm.launder.invariant.group", {"SUSPECT", "forwards ptr"}},
    {"llvm.strip.invariant.group", {"SUSPECT", "forwards ptr"}},
    {"llvm.invariant.start", {"NOOP", "marker"}},
    {"llvm.invariant.end", {"NOOP", "marker"}},
    {"llvm.masked.load", {"SUSPECT", "vector memory op — no d-edges today"}},
    {"llvm.masked.store", {"SUSPECT", "vector memory op"}},
    {"llvm.masked.gather", {"SUSPECT", "vector memory op"}},
    {"llvm.masked.scatter", {"SUSPECT", "vector memory op"}},
    {"llvm.vector.reduce.", {"NOOP", "int/float reduction"}},
    {"llvm.experimental.noalias", {"SUSPECT", "forwards ptr"}},
    {"llvm.objectsize", {"NOOP", "int result"}},
    {"llvm.is.constant", {"NOOP", "i1 result"}},
    {"llvm.bswap", {"NOOP", "int"}},
    {"llvm.bitreverse", {"NOOP", "int"}},
    {"llvm.ctpop", {"NOOP", "int"}},
    {"llvm.ctlz", {"NOOP", "int"}},
    {"llvm.cttz", {"NOOP", "int"}},
    {"llvm.abs", {"NOOP", "int"}},
    {"llvm.smax", {"NOOP", "int"}}, {"llvm.smin", {"NOOP", "int"}},
    {"llvm.umax", {"NOOP", "int"}}, {"llvm.umin", {"NOOP", "int"}},
    {"llvm.fshl", {"NOOP", "int"}}, {"llvm.fshr", {"NOOP", "int"}},
    {"llvm.sadd.", {"NOOP", "int ovf"}}, {"llvm.uadd.", {"NOOP", "int ovf"}},
    {"llvm.ssub.", {"NOOP", "int ovf"}}, {"llvm.usub.", {"NOOP", "int ovf"}},
    {"llvm.smul.", {"NOOP", "int ovf"}}, {"llvm.umul.", {"NOOP", "int ovf"}},
    {"llvm.fabs", {"NOOP", "float"}}, {"llvm.floor", {"NOOP", "float"}},
    {"llvm.ceil", {"NOOP", "float"}}, {"llvm.trunc.", {"NOOP", "float"}},
    {"llvm.rint", {"NOOP", "float"}}, {"llvm.sqrt", {"NOOP", "float"}},
    {"llvm.pow", {"NOOP", "float"}}, {"llvm.fma", {"NOOP", "float"}},
    {"llvm.fmuladd", {"NOOP", "float"}},
    {"llvm.minnum", {"NOOP", "float"}}, {"llvm.maxnum", {"NOOP", "float"}},
    {"llvm.copysign", {"NOOP", "float"}},
    {"llvm.read_register", {"NOOP", "opaque"}},
    {"llvm.write_register", {"NOOP", "opaque"}},
    {"llvm.x86.", {"SUSPECT", "target intrinsic — review per name"}},
  };
  return T;
}

bool typeHasPointer(Type *T, std::set<Type *> &seen) {
  if (!T || !seen.insert(T).second) return false;
  if (T->isPointerTy()) return true;
  for (Type *S : T->subtypes())
    if (typeHasPointer(S, seen)) return true;
  return false;
}
bool typeHasPointer(Type *T) {
  std::set<Type *> seen;
  return typeHasPointer(T, seen);
}

// Can this type hold a pointer VALUE bit-for-bit (integer laundering)?
// Any integer >= pointer width qualifies (i64/i128 on x86-64).
bool typeHasPtrWidthInt(Type *T, unsigned ptrBits, std::set<Type *> &seen) {
  if (!T || !seen.insert(T).second) return false;
  if (auto *IT = dyn_cast<IntegerType>(T))
    return IT->getBitWidth() >= ptrBits;
  for (Type *S : T->subtypes())
    if (typeHasPtrWidthInt(S, ptrBits, seen)) return true;
  return false;
}
bool typeHasPtrWidthInt(Type *T, unsigned ptrBits) {
  std::set<Type *> seen;
  return typeHasPtrWidthInt(T, ptrBits, seen);
}

struct Tally {
  uint64_t count = 0;
  uint64_t ptrRelevant = 0; // instances whose operand/result types carry ptr
};

// ---- inline asm classification ---------------------------------------
// Ordered by severity for pointer analysis: what can the asm do to the
// value-flow graph, judged from the constraint signature + operand and
// elementtype widths (the only information the IR retains)?
enum AsmCat : unsigned {
  AsmPtrOut = 0,   // result carries a pointer: asm can MINT a pointer
  AsmMemPtr,       // indirect operand whose elementtype contains a pointer:
                   // asm loads/stores pointer VALUES through memory
  AsmPtrInReg,     // raw pointer in a register (non-indirect): the address
                   // escapes; with a memory clobber the asm may deref it
  AsmMemPtrWidth,  // indirect operand of pointer WIDTH (i64/i128): cannot be
                   // typed but CAN launder a pointer value (atomic64 etc.)
  AsmMemNarrow,    // indirect operands all narrower than a pointer: the asm
                   // physically CANNOT move a pointer value through them
  AsmImmPtr,       // pointer bound to an IMMEDIATE constraint (i/s/n/X) and
                   // no memory clobber: a link-time constant symbol embedded
                   // in metadata sections (__bug_table/__jump_table) or used
                   // as a direct operand — no runtime value flow. (imm ptr
                   // WITH a memory clobber classifies as ptr-in-reg: the asm
                   // could store the symbol somewhere the program reads.)
  AsmBarrier,      // no ptr-capable operands; memory clobber / side effect
                   // only (compiler barrier) — no value flow possible
  AsmPure,         // int/flag-only computation, no memory
  AsmNumCats
};
const char *asmCatName(unsigned c) {
  static const char *N[] = {"ptr-out",       "mem-ptr",    "ptr-in-reg",
                            "mem-ptr-width", "mem-narrow", "imm-ptr",
                            "barrier",       "pure"};
  return N[c];
}
// Is this category a pointer-analysis exposure (belongs on the ledger)?
bool asmCatExposed(unsigned c) { return c <= AsmMemPtrWidth; }

struct AsmInfo {
  uint64_t count = 0;
  unsigned cat = AsmPure;
  bool isGoto = false, memClobber = false;
  unsigned nIndirect = 0, nPtrReg = 0, nImmPtr = 0;
  bool hasCall = false; // asm text contains a call — direct-call family
  std::string example; // first-seen "module|function"
  std::string constraints;
  std::string text;
};

AsmCat classifyAsm(const CallBase *CB, const InlineAsm *IA,
                   unsigned ptrBits, bool &memClobber, unsigned &nIndirect,
                   unsigned &nPtrReg, unsigned &nImmPtr) {
  memClobber = false;
  nIndirect = nPtrReg = nImmPtr = 0;
  bool memPtr = false, memPtrWidth = false, memAny = false;
  // Call args map, in order, to: indirect outputs, then all inputs
  // (labels and clobbers consume no args).
  unsigned argIdx = 0;
  for (const InlineAsm::ConstraintInfo &CI : IA->ParseConstraints()) {
    if (CI.Type == InlineAsm::isClobber) {
      for (const std::string &Code : CI.Codes)
        if (StringRef(Code).contains("memory")) memClobber = true;
      continue;
    }
    if (CI.Type == InlineAsm::isLabel) continue;
    bool consumesArg = (CI.Type == InlineAsm::isInput) ||
                       (CI.Type == InlineAsm::isOutput && CI.isIndirect);
    if (!consumesArg) continue;
    assert(argIdx < CB->arg_size() && "asm constraint/arg count mismatch");
    if (CI.isIndirect) {
      nIndirect++;
      memAny = true;
      // LLVM 14+ requires elementtype(<ty>) on indirect asm operands —
      // the accessed width is knowable.
      if (Type *ET = CB->getParamElementType(argIdx)) {
        if (typeHasPointer(ET))
          memPtr = true;
        else if (typeHasPtrWidthInt(ET, ptrBits))
          memPtrWidth = true;
      } else {
        memPtrWidth = true; // width unknown — conservative
      }
    } else if (CB->getArgOperand(argIdx)->getType()->isPointerTy()) {
      bool allImm = !CI.Codes.empty();
      for (const std::string &Code : CI.Codes)
        allImm &= (Code == "i" || Code == "s" || Code == "n" || Code == "X");
      if (allImm)
        nImmPtr++;
      else
        nPtrReg++;
    }
    argIdx++;
  }
  if (typeHasPointer(CB->getType())) return AsmPtrOut;
  if (memPtr) return AsmMemPtr;
  if (nPtrReg) return AsmPtrInReg;
  if (nImmPtr && memClobber) return AsmPtrInReg; // could store the symbol
  if (memPtrWidth) return AsmMemPtrWidth;
  if (memAny) return AsmMemNarrow;
  if (nImmPtr) return AsmImmPtr;
  if (memClobber || IA->hasSideEffects()) return AsmBarrier;
  return AsmPure;
}

// ---- JSON emission ----------------------------------------------------
void jsonEsc(raw_ostream &os, StringRef s) {
  for (unsigned char c : s) {
    switch (c) {
    case '"': os << "\\\""; break;
    case '\\': os << "\\\\"; break;
    case '\n': os << "\\n"; break;
    case '\t': os << "\\t"; break;
    case '\r': os << "\\r"; break;
    default:
      if (c < 0x20) {
        char buf[8];
        snprintf(buf, sizeof(buf), "\\u%04x", c);
        os << buf;
      } else {
        os << (char)c;
      }
    }
  }
}

} // namespace

IRCensusResult runIRCensus(GlobalContext *Ctx, const std::string &jsonOut,
                           bool printTables) {
  std::map<unsigned, Tally> opTally;
  std::map<std::string, Tally> intrinTally;
  std::map<std::string, uint64_t> extCallees; // declared, non-intrinsic
  std::map<unsigned, uint64_t> constExprTally;
  uint64_t asmSites = 0;
  std::map<std::string, AsmInfo> asmTable; // key = constraints \x1f text
  uint64_t asmCatSites[AsmNumCats] = {0};
  uint64_t aggLoadStore = 0, vecPtrOps = 0, totalInsts = 0, totalFuncs = 0;
  std::set<const Constant *> ceSeen;

  std::function<void(const Constant *)> walkCE = [&](const Constant *C) {
    if (!ceSeen.insert(C).second) return;
    if (const auto *CE = dyn_cast<ConstantExpr>(C))
      constExprTally[CE->getOpcode()]++;
    for (const Use &U : C->operands())
      if (const auto *OC = dyn_cast<Constant>(U.get()))
        if (!isa<GlobalValue>(OC)) // stop at symbol boundaries
          walkCE(OC);
  };

  for (auto &[M, Name] : Ctx->Modules) {
    for (GlobalVariable &GV : M->globals())
      if (GV.hasInitializer())
        walkCE(GV.getInitializer());
    for (Function &F : *M) {
      if (F.isDeclaration()) continue;
      totalFuncs++;
      for (Instruction &I : instructions(F)) {
        totalInsts++;
        auto &t = opTally[I.getOpcode()];
        t.count++;
        bool ptrRel = typeHasPointer(I.getType());
        for (Use &U : I.operands()) {
          ptrRel = ptrRel || typeHasPointer(U->getType());
          if (auto *C = dyn_cast<Constant>(U.get()))
            if (!isa<GlobalValue>(C) && !isa<ConstantData>(C))
              walkCE(C);
        }
        if (ptrRel) t.ptrRelevant++;
        if ((isa<LoadInst>(I) || isa<StoreInst>(I))) {
          Type *VT = isa<LoadInst>(I)
                         ? I.getType()
                         : cast<StoreInst>(I).getValueOperand()->getType();
          if ((VT->isAggregateType() || VT->isVectorTy()) && typeHasPointer(VT))
            aggLoadStore++;
        }
        if (I.getType()->isVectorTy() && typeHasPointer(I.getType()))
          vecPtrOps++;
        if (auto *CB = dyn_cast<CallBase>(&I)) {
          if (CB->isInlineAsm()) {
            asmSites++;
            auto *IA = cast<InlineAsm>(CB->getCalledOperand());
            unsigned ptrBits =
                M->getDataLayout().getPointerSizeInBits();
            bool memClob = false;
            unsigned nInd = 0, nPtrReg = 0, nImmPtr = 0;
            AsmCat cat = classifyAsm(CB, IA, ptrBits, memClob, nInd,
                                     nPtrReg, nImmPtr);
            asmCatSites[cat]++;
            std::string key =
                IA->getConstraintString() + '\x1f' + IA->getAsmString();
            AsmInfo &ai = asmTable[key];
            if (ai.count == 0) {
              ai.cat = cat;
              ai.memClobber = memClob;
              ai.nIndirect = nInd;
              ai.nPtrReg = nPtrReg;
              ai.nImmPtr = nImmPtr;
              ai.isGoto = isa<CallBrInst>(CB);
              ai.hasCall = StringRef(IA->getAsmString()).contains("call");
              ai.example = Name.str() + "|" + F.getName().str();
              ai.constraints = IA->getConstraintString();
              ai.text = IA->getAsmString();
            } else {
              // same (constraints, text) can classify differently across
              // sites — elementtype and result types vary (one percpu
              // template serves i64 and ptr slots); keep the most severe
              ai.cat = std::min(ai.cat, (unsigned)cat);
              ai.memClobber |= memClob;
              ai.nIndirect = std::max(ai.nIndirect, nInd);
              ai.nPtrReg = std::max(ai.nPtrReg, nPtrReg);
              ai.nImmPtr = std::max(ai.nImmPtr, nImmPtr);
              ai.isGoto |= isa<CallBrInst>(CB);
            }
            ai.count++;
            continue;
          }
          const Function *CF = CB->getCalledFunction();
          if (CF && CF->isIntrinsic()) {
            auto &it = intrinTally[CF->getName().str()];
            it.count++;
            if (ptrRel) it.ptrRelevant++;
          } else if (CF && CF->isDeclaration() &&
                     Ctx->Funcs.find(CF->getGUID()) == Ctx->Funcs.end()) {
            extCallees[CF->getName().str()]++;
          }
        }
      }
    }
  }

  // ---- report ----
  IRCensusResult R;
  auto &OT = opcodeTable();
  if (printTables)
    errs() << "CENSUS ================ opcode dispositions ================\n";
  std::vector<std::pair<uint64_t, unsigned>> ops;
  for (auto &[op, t] : opTally) ops.push_back({t.count, op});
  std::sort(ops.rbegin(), ops.rend());
  for (auto &[cnt, op] : ops) {
    auto it = OT.find(op);
    const char *st = it != OT.end() ? it->second.status : "UNDISP";
    const char *note = it != OT.end() ? it->second.note : "NOT IN TABLE";
    auto &t = opTally[op];
    if (it == OT.end()) {
      R.undispKinds++;
      R.undispNames.push_back(std::string("op ") +
                              Instruction::getOpcodeName(op));
    }
    if (it != OT.end() && std::string(st) == "SUSPECT")
      R.suspectPtrInsts += t.ptrRelevant;
    if (printTables)
      errs() << "CENSUS op " << Instruction::getOpcodeName(op) << " " << cnt
             << " ptr-relevant " << t.ptrRelevant << " " << st << " : "
             << note << "\n";
  }
  if (printTables)
    errs() << "CENSUS ================ intrinsics ================\n";
  auto &IT = intrinsicTable();
  std::vector<std::pair<uint64_t, std::string>> ins;
  for (auto &[n, t] : intrinTally) ins.push_back({t.count, n});
  std::sort(ins.rbegin(), ins.rend());
  // remember each intrinsic's disposition for the JSON pass
  std::map<std::string, const Disposition *> intrinDisp;
  for (auto &[cnt, n] : ins) {
    const Disposition *d = nullptr;
    for (auto &[pfx, disp] : IT)
      if (StringRef(n).starts_with(pfx)) { d = &disp; break; }
    intrinDisp[n] = d;
    if (!d) {
      R.undispKinds++;
      R.undispNames.push_back("intrin " + n);
    }
    if (d && std::string(d->status) == "SUSPECT")
      R.suspectPtrInsts += intrinTally[n].ptrRelevant;
    if (printTables)
      errs() << "CENSUS intrin " << n << " " << cnt << " ptr-relevant "
             << intrinTally[n].ptrRelevant << " "
             << (d ? d->status : "UNDISP") << " : "
             << (d ? d->note : "NOT IN TABLE") << "\n";
  }
  if (printTables) {
    errs() << "CENSUS ================ constant expressions ================\n";
    for (auto &[op, cnt] : constExprTally)
      errs() << "CENSUS constexpr " << Instruction::getOpcodeName(op) << " "
             << cnt << "\n";
  }
  std::vector<std::pair<uint64_t, std::string>> exts;
  for (auto &[n, c] : extCallees) exts.push_back({c, n});
  std::sort(exts.rbegin(), exts.rend());
  if (printTables) {
    errs() << "CENSUS ================ external callees (top 40) ============\n";
    for (size_t i = 0; i < std::min<size_t>(40, exts.size()); i++)
      errs() << "CENSUS extern " << exts[i].second << " " << exts[i].first
             << "\n";
  }
  // asm category breakdown — always printed: this is the kernel's
  // dominant untyped exposure, the summary must carry it
  uint64_t asmCatDistinct[AsmNumCats] = {0};
  uint64_t asmExposedSites = 0;
  for (auto &[k, ai] : asmTable) asmCatDistinct[ai.cat]++;
  errs() << "CENSUS ================ inline asm ================\n";
  for (unsigned c = 0; c < AsmNumCats; c++) {
    if (asmCatExposed(c)) asmExposedSites += asmCatSites[c];
    errs() << "CENSUS asm-cat " << asmCatName(c) << " sites "
           << asmCatSites[c] << " distinct " << asmCatDistinct[c]
           << (asmCatExposed(c) ? "  [LEDGER: ptr-capable]" : "") << "\n";
  }
  errs() << "CENSUS asm exposure: " << asmExposedSites << " of " << asmSites
         << " sites can move a pointer (categories ptr-out/mem-ptr/"
            "ptr-in-reg/mem-ptr-width)\n";
  errs() << "CENSUS ================ summary ================\n";
  errs() << "CENSUS summary funcs " << totalFuncs << " insts " << totalInsts
         << " asm-sites " << asmSites << " asm-distinct " << asmTable.size()
         << " extern-decls " << extCallees.size()
         << " agg/vec-ptr-load-store " << aggLoadStore << " vec-ptr-ops "
         << vecPtrOps << "\n";
  errs() << "CENSUS summary UNDISPOSITIONED kinds " << R.undispKinds
         << ", SUSPECT ptr-relevant instances " << R.suspectPtrInsts << "\n";

  // ---- machine-readable ledger artifact ----
  if (!jsonOut.empty()) {
    std::error_code EC;
    raw_fd_ostream os(jsonOut, EC, sys::fs::OF_Text);
    if (EC) {
      errs() << "CENSUS ERROR: cannot write '" << jsonOut
             << "': " << EC.message() << "\n";
      abort(); // artifact was requested; silent loss is not an option
    }
    os << "{\n  \"tool\": \"kanalyzer --ir-census\",\n";
    os << "  \"summary\": {\"funcs\": " << totalFuncs << ", \"insts\": "
       << totalInsts << ", \"asm_sites\": " << asmSites
       << ", \"asm_distinct\": " << asmTable.size()
       << ", \"asm_exposed_sites\": " << asmExposedSites
       << ", \"extern_decls\": " << extCallees.size()
       << ", \"agg_vec_ptr_load_store\": " << aggLoadStore
       << ", \"vec_ptr_ops\": " << vecPtrOps
       << ", \"undisp_kinds\": " << R.undispKinds
       << ", \"suspect_ptr_instances\": " << R.suspectPtrInsts << "},\n";
    // opcodes
    os << "  \"opcodes\": [\n";
    for (size_t i = 0; i < ops.size(); i++) {
      unsigned op = ops[i].second;
      auto it = OT.find(op);
      os << "    {\"name\": \"" << Instruction::getOpcodeName(op)
         << "\", \"count\": " << ops[i].first << ", \"ptr_relevant\": "
         << opTally[op].ptrRelevant << ", \"status\": \""
         << (it != OT.end() ? it->second.status : "UNDISP")
         << "\", \"note\": \"";
      jsonEsc(os, it != OT.end() ? it->second.note : "NOT IN TABLE");
      os << "\"}" << (i + 1 < ops.size() ? "," : "") << "\n";
    }
    os << "  ],\n  \"intrinsics\": [\n";
    for (size_t i = 0; i < ins.size(); i++) {
      const std::string &n = ins[i].second;
      const Disposition *d = intrinDisp[n];
      os << "    {\"name\": \"";
      jsonEsc(os, n);
      os << "\", \"count\": " << ins[i].first << ", \"ptr_relevant\": "
         << intrinTally[n].ptrRelevant << ", \"status\": \""
         << (d ? d->status : "UNDISP") << "\", \"note\": \"";
      jsonEsc(os, d ? d->note : "NOT IN TABLE");
      os << "\"}" << (i + 1 < ins.size() ? "," : "") << "\n";
    }
    os << "  ],\n  \"constexprs\": [\n";
    {
      size_t i = 0;
      for (auto &[op, cnt] : constExprTally) {
        os << "    {\"name\": \"" << Instruction::getOpcodeName(op)
           << "\", \"count\": " << cnt << "}"
           << (++i < constExprTally.size() ? "," : "") << "\n";
      }
    }
    os << "  ],\n  \"extern_callees\": [\n";
    for (size_t i = 0; i < exts.size(); i++) {
      os << "    {\"name\": \"";
      jsonEsc(os, exts[i].second);
      os << "\", \"count\": " << exts[i].first << "}"
         << (i + 1 < exts.size() ? "," : "") << "\n";
    }
    os << "  ],\n  \"asm_categories\": [\n";
    for (unsigned c = 0; c < AsmNumCats; c++)
      os << "    {\"category\": \"" << asmCatName(c) << "\", \"sites\": "
         << asmCatSites[c] << ", \"distinct\": " << asmCatDistinct[c]
         << ", \"ptr_capable\": " << (asmCatExposed(c) ? "true" : "false")
         << "}" << (c + 1 < AsmNumCats ? "," : "") << "\n";
    os << "  ],\n  \"asm_distinct\": [\n";
    {
      std::vector<const AsmInfo *> byCount;
      for (auto &[k, ai] : asmTable) byCount.push_back(&ai);
      std::sort(byCount.begin(), byCount.end(),
                [](const AsmInfo *a, const AsmInfo *b) {
                  if (a->cat != b->cat) return a->cat < b->cat;
                  return a->count > b->count;
                });
      for (size_t i = 0; i < byCount.size(); i++) {
        const AsmInfo &ai = *byCount[i];
        os << "    {\"category\": \"" << asmCatName(ai.cat)
           << "\", \"count\": " << ai.count
           << ", \"goto\": " << (ai.isGoto ? "true" : "false")
           << ", \"mem_clobber\": " << (ai.memClobber ? "true" : "false")
           << ", \"indirect_ops\": " << ai.nIndirect
           << ", \"ptr_reg_args\": " << ai.nPtrReg
           << ", \"imm_ptr_args\": " << ai.nImmPtr
           << ", \"has_call\": " << (ai.hasCall ? "true" : "false")
           << ", \"example\": \"";
        jsonEsc(os, ai.example);
        os << "\", \"constraints\": \"";
        jsonEsc(os, ai.constraints);
        os << "\", \"text\": \"";
        jsonEsc(os, ai.text);
        os << "\"}" << (i + 1 < byCount.size() ? "," : "") << "\n";
      }
    }
    // the ledger: every construct class the encoder does NOT model,
    // with instance counts — the per-corpus unsoundness bill
    os << "  ],\n  \"ledger\": [\n";
    {
      std::vector<std::string> rows;
      for (auto &[cnt, op] : ops) {
        auto it = OT.find(op);
        if (it == OT.end() || std::string(it->second.status) == "SUSPECT") {
          std::string r = "    {\"kind\": \"opcode\", \"name\": \"";
          r += Instruction::getOpcodeName(op);
          r += "\", \"instances\": " + std::to_string(cnt) +
               ", \"ptr_relevant\": " +
               std::to_string(opTally[op].ptrRelevant) + "}";
          rows.push_back(r);
        }
      }
      for (auto &[cnt, n] : ins) {
        const Disposition *d = intrinDisp[n];
        if (!d || std::string(d->status) == "SUSPECT") {
          std::string r = "    {\"kind\": \"intrinsic\", \"name\": \"" + n +
                          "\", \"instances\": " + std::to_string(cnt) +
                          ", \"ptr_relevant\": " +
                          std::to_string(intrinTally[n].ptrRelevant) + "}";
          rows.push_back(r);
        }
      }
      for (unsigned c = 0; c < AsmNumCats; c++)
        if (asmCatExposed(c) && asmCatSites[c])
          rows.push_back(std::string("    {\"kind\": \"asm\", \"name\": \"") +
                         asmCatName(c) + "\", \"instances\": " +
                         std::to_string(asmCatSites[c]) +
                         ", \"ptr_relevant\": " +
                         std::to_string(asmCatSites[c]) + "}");
      for (size_t i = 0; i < rows.size(); i++)
        os << rows[i] << (i + 1 < rows.size() ? "," : "") << "\n";
    }
    os << "  ]\n}\n";
    errs() << "CENSUS ledger artifact written: " << jsonOut << "\n";
  }
  return R;
}
