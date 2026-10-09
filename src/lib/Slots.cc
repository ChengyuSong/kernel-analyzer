/*
 * Call graph construction
 *
 * Copyright (C) 2024 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// Slots.cc: naming a memory slot an access reaches as (struct, byte offset)
// across embedding and -O3 (struct GEPs, and struct-path TBAA when -O3
// dropped an all-zero GEP). Shared by the Driver pre-passes and the
// summary checks (pool closure).

#include "CallGraphInternal.h"
#include <llvm/IR/Metadata.h>

// Does struct type T hold a struct named S at byte offset off (itself, or
// through first-member / field embedding)?
bool embedsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL) {
  for (int depth = 0; depth < 32 && T && off >= 0; depth++) {
    auto *ST = dyn_cast<StructType>(T);
    if (!ST || ST->isOpaque()) return false;
    if (off == 0 && ST->hasName() && stripStructNameSuffix(ST->getName()) == S) return true;
    const StructLayout *SL = DL.getStructLayout(ST);
    if ((uint64_t)off >= SL->getSizeInBytes()) return false;
    unsigned i = SL->getElementContainingOffset(off);
    off -= (int64_t)SL->getElementOffset(i);
    T = ST->getElementType(i);
  }
  return false;
}

// The struct GEP an address is (bitcasts only: stripPointerCasts would also
// strip an all-zero GEP, the method at offset 0 of its struct).
const GEPOperator *structGEP(const Value *A) {
  while (const auto *BC = dyn_cast<BitCastOperator>(A)) A = BC->getOperand(0);
  return dyn_cast<GEPOperator>(A);
}

// The (struct, byte offset) an access names: its struct GEP, else its
// struct-path TBAA tag (-O3 drops all-zero GEPs; the tag keeps the base
// struct and the offset).
bool accessSlot(const Instruction *I, const Value *Addr, const DataLayout &DL,
                       StructType *&S, int64_t &off) {
  if (const GEPOperator *G = structGEP(Addr)) {
    S = dyn_cast<StructType>(G->getSourceElementType());
    APInt Ap(64, 0);
    if (S && S->hasName() && G->accumulateConstantOffset(DL, Ap)) {
      off = Ap.getSExtValue();
      return true;
    }
  }
  const MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa);
  if (!Tag || Tag->getNumOperands() < 3 || Tag->getOperand(0) == Tag->getOperand(1)) return false;
  const auto *B = dyn_cast<MDNode>(Tag->getOperand(0));
  const auto *N = B && B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
  const auto *TO = mdconst::dyn_extract<ConstantInt>(Tag->getOperand(2));
  if (!N || !TO) return false;
  S = StructType::getTypeByName(I->getContext(), ("struct." + N->getString()).str());
  if (!S) return false;
  // The tag's offset is relative to the base struct; the address must be
  // the struct's start plus that offset, which the tag asserts.
  off = TO->getSExtValue();
  return true;
}

// Does an access's struct-path TBAA tag reach struct SN (IR name,
// "struct.T") at byte offset o: walking from the tag's base type into the
// member that contains the access offset (an anonymous typedef'd struct
// whose first member is SN: cjpeg's my_memory_mgr { jpeg_memory_mgr pub; }).
bool tbaaReaches(const Instruction *I, StringRef SN, int64_t o) {
  const MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa);
  if (!Tag || Tag->getNumOperands() < 3 || Tag->getOperand(0) == Tag->getOperand(1)) return false;
  const auto *TO = mdconst::dyn_extract<ConstantInt>(Tag->getOperand(2));
  const auto *B = dyn_cast<MDNode>(Tag->getOperand(0));
  if (!TO || !B) return false;
  int64_t off = TO->getSExtValue();
  for (int depth = 0; depth < 16 && B; depth++) {
    const auto *N = B->getNumOperands() ? dyn_cast<MDString>(B->getOperand(0)) : nullptr;
    if (N && !N->getString().empty() && ("struct." + N->getString()).str() == SN && off == o)
      return true;
    // Members: (type, offset) pairs after the name.
    const MDNode *next = nullptr;
    int64_t best = -1;
    for (unsigned k = 1; k + 1 < B->getNumOperands(); k += 2) {
      const auto *MO = mdconst::dyn_extract<ConstantInt>(B->getOperand(k + 1));
      if (MO && MO->getSExtValue() <= off && MO->getSExtValue() > best) {
        best = MO->getSExtValue();
        next = dyn_cast<MDNode>(B->getOperand(k));
      }
    }
    if (!next || best < 0) return false;
    off -= best;
    B = next;
  }
  return false;
}

