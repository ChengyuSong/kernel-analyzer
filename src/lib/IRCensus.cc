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

struct Tally {
  uint64_t count = 0;
  uint64_t ptrRelevant = 0; // instances whose operand/result types carry ptr
};

} // namespace

void runIRCensus(GlobalContext *Ctx) {
  std::map<unsigned, Tally> opTally;
  std::map<std::string, Tally> intrinTally;
  std::map<std::string, uint64_t> extCallees; // declared, non-intrinsic
  std::map<unsigned, uint64_t> constExprTally;
  uint64_t asmSites = 0;
  std::set<std::string> asmStrings;
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
            if (auto *IA = dyn_cast<InlineAsm>(CB->getCalledOperand()))
              asmStrings.insert(IA->getAsmString());
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
  auto &OT = opcodeTable();
  uint64_t undispKinds = 0, suspectPtrInst = 0;
  errs() << "CENSUS ================ opcode dispositions ================\n";
  std::vector<std::pair<uint64_t, unsigned>> ops;
  for (auto &[op, t] : opTally) ops.push_back({t.count, op});
  std::sort(ops.rbegin(), ops.rend());
  for (auto &[cnt, op] : ops) {
    auto it = OT.find(op);
    const char *st = it != OT.end() ? it->second.status : "UNDISP";
    const char *note = it != OT.end() ? it->second.note : "NOT IN TABLE";
    auto &t = opTally[op];
    if (it == OT.end()) undispKinds++;
    if (it != OT.end() && std::string(st) == "SUSPECT")
      suspectPtrInst += t.ptrRelevant;
    errs() << "CENSUS op " << Instruction::getOpcodeName(op) << " " << cnt
           << " ptr-relevant " << t.ptrRelevant << " " << st << " : "
           << note << "\n";
  }
  errs() << "CENSUS ================ intrinsics ================\n";
  auto &IT = intrinsicTable();
  std::vector<std::pair<uint64_t, std::string>> ins;
  for (auto &[n, t] : intrinTally) ins.push_back({t.count, n});
  std::sort(ins.rbegin(), ins.rend());
  for (auto &[cnt, n] : ins) {
    const Disposition *d = nullptr;
    for (auto &[pfx, disp] : IT)
      if (StringRef(n).starts_with(pfx)) { d = &disp; break; }
    if (!d) undispKinds++;
    if (d && std::string(d->status) == "SUSPECT")
      suspectPtrInst += intrinTally[n].ptrRelevant;
    errs() << "CENSUS intrin " << n << " " << cnt << " ptr-relevant "
           << intrinTally[n].ptrRelevant << " "
           << (d ? d->status : "UNDISP") << " : "
           << (d ? d->note : "NOT IN TABLE") << "\n";
  }
  errs() << "CENSUS ================ constant expressions ================\n";
  for (auto &[op, cnt] : constExprTally)
    errs() << "CENSUS constexpr " << Instruction::getOpcodeName(op) << " "
           << cnt << "\n";
  errs() << "CENSUS ================ external callees (top 40) ============\n";
  std::vector<std::pair<uint64_t, std::string>> exts;
  for (auto &[n, c] : extCallees) exts.push_back({c, n});
  std::sort(exts.rbegin(), exts.rend());
  for (size_t i = 0; i < std::min<size_t>(40, exts.size()); i++)
    errs() << "CENSUS extern " << exts[i].second << " " << exts[i].first
           << "\n";
  errs() << "CENSUS ================ summary ================\n";
  errs() << "CENSUS summary funcs " << totalFuncs << " insts " << totalInsts
         << " asm-sites " << asmSites << " asm-distinct "
         << asmStrings.size() << " extern-decls " << extCallees.size()
         << " agg/vec-ptr-load-store " << aggLoadStore << " vec-ptr-ops "
         << vecPtrOps << "\n";
  errs() << "CENSUS summary UNDISPOSITIONED kinds " << undispKinds
         << ", SUSPECT ptr-relevant instances " << suspectPtrInst << "\n";
}
