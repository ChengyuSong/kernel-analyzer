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

// GraphBuild.cc: constraint-graph construction from IR: instructions, calls, memcpy, GEP fields, initializers, linker arrays, inline asm, canonical nodes, global dedup, reachability-driven body admission.
// Part of CallGraphPass; shared declarations in CallGraphInternal.h.

#include "CallGraphInternal.h"

#include <llvm/BinaryFormat/Dwarf.h>

namespace {

static bool isZeroOffsetGEP(const Value *V) {
  const auto *GEP = dyn_cast<GEPOperator>(V);
  if (!GEP)
    return false;
  for (const Use &IdxU : GEP->indices()) {
    const Value *Idx = IdxU.get();
    const auto *CI = dyn_cast<ConstantInt>(Idx);
    if (!CI || !CI->isZero())
      return false;
  }
  return true;
}

static const Value *stripAllocaAliasBase(const Value *V) {
  const Value *Cur = V;
  while (Cur) {
    const Value *Stripped = Cur->stripPointerCasts();
    if (Stripped != Cur) {
      Cur = Stripped;
      continue;
    }
    const auto *GEP = dyn_cast<GEPOperator>(Cur);
    if (!GEP || !isZeroOffsetGEP(GEP))
      break;
    Cur = GEP->getPointerOperand();
  }
  return Cur;
}

static bool isIgnorableAllocaIntrinsic(const CallBase *CB) {
  const Function *CF = CB ? CB->getCalledFunction() : nullptr;
  if (!CF || !CF->isIntrinsic())
    return false;
  switch (CF->getIntrinsicID()) {
    case Intrinsic::dbg_declare:
    case Intrinsic::dbg_value:
#if LLVM_VERSION_MAJOR >= 15
    case Intrinsic::dbg_assign:
#endif
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
      return true;
    default:
      return false;
  }
}

} // namespace

static bool getConstantFmtString(const Value *V, StringRef &out) {
  V = V->stripPointerCasts();
  if (const auto *GEP = dyn_cast<GEPOperator>(V)) {
    if (!GEP->hasAllZeroIndices())
      return false;
    V = GEP->getPointerOperand()->stripPointerCasts();
  }
  const auto *GV = dyn_cast<GlobalVariable>(V);
  if (!GV || !GV->hasInitializer())
    return false;
  const auto *CDA = dyn_cast<ConstantDataArray>(GV->getInitializer());
  if (!CDA || !CDA->isCString())
    return false;
  out = CDA->getAsCString();
  return true;
}

static bool formatVarargsBenign(StringRef fmt) {
  for (size_t i = 0; i < fmt.size(); i++) {
    if (fmt[i] != '%')
      continue;
    if (++i >= fmt.size())
      return false; // trailing '%': malformed
    if (fmt[i] == '%')
      continue;
    while (i < fmt.size() &&
           (isDigit(fmt[i]) || StringRef("-+ #0'.*").contains(fmt[i])))
      i++;
    while (i < fmt.size() && StringRef("hlLzjtq").contains(fmt[i]))
      i++;
    if (i >= fmt.size())
      return false;
    const char c = fmt[i];
    if (c == 'p') {
      // %p extensions are read-only symbol/address renderers EXCEPT %pV.
      if (i + 1 < fmt.size() && fmt[i + 1] == 'V')
        return false;
      continue;
    }
    if (StringRef("diouxXcCsSeEfgGaA").contains(c))
      continue;
    return false; // %n or unknown conversion: keep full wiring
  }
  return true;
}

static bool printfVarargSinkCallsite(const CallBase *CS, const Function *CF,
                                     bool countStats = false) {
  const unsigned numFormals = CF->arg_size();
  if (numFormals == 0 || CS->arg_size() <= numFormals)
    return false; // no variadic tail to skip
  StringRef fmt;
  if (!getConstantFmtString(CS->getArgOperand(numFormals - 1), fmt)) {
    if (countStats) printfNonConstFmt++;
    return false;
  }
  if (!formatVarargsBenign(fmt)) {
    if (countStats) printfNonBenignFmt++;
    return false;
  }
  return true;
}

bool shouldSkipValue(const Value *V) {
  if (!V)
    return true;

  // Skip nullptr
  if (isa<ConstantPointerNull>(V))
    return true;

  // Skip compiler-introduced values
  if (isCompilerIntroducedValue(V))
    return true;

  return false;
}

// Helper: returns true if T is a pointer or a vector-of-pointer type.
static bool containsPointerTypeImpl(Type *T, SmallPtrSetImpl<Type *> &Seen) {
  if (!T)
    return false;
  if (!Seen.insert(T).second)
    return false;

  if (T->isPointerTy())
    return true;

  if (auto *VT = dyn_cast<VectorType>(T))
    return containsPointerTypeImpl(VT->getElementType(), Seen);

  if (auto *AT = dyn_cast<ArrayType>(T))
    return containsPointerTypeImpl(AT->getElementType(), Seen);

  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->isOpaque())
      return false;
    for (Type *ElemTy : ST->elements()) {
      if (containsPointerTypeImpl(ElemTy, Seen))
        return true;
    }
  }

  return false;
}

// Helper: returns true if T is a pointer, a vector-of-pointer type, or an
// aggregate (array/struct) that recursively contains pointers.
bool containsPointerType(Type *T) {
  SmallPtrSet<Type *, 16> Seen;
  return containsPointerTypeImpl(T, Seen);
}

static bool isLoweredVAListTypeImpl(Type *T, SmallPtrSetImpl<Type *> &Seen) {
  if (!T)
    return false;
  if (!Seen.insert(T).second)
    return false;

  if (auto *AT = dyn_cast<ArrayType>(T))
    return isLoweredVAListTypeImpl(AT->getElementType(), Seen);
  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->hasName()) {
      StringRef N = ST->getName();
      if (N.contains("va_list") || N.contains("__va_list_tag"))
        return true;
    }
    if (ST->isOpaque())
      return false;
    for (Type *ElemTy : ST->elements()) {
      if (isLoweredVAListTypeImpl(ElemTy, Seen))
        return true;
    }
  }
  return false;
}

static bool isLoweredVAListType(Type *T) {
  SmallPtrSet<Type *, 16> Seen;
  return isLoweredVAListTypeImpl(T, Seen);
}

static bool derivesFromLoweredVAListImpl(const Value *V,
                                         SmallPtrSetImpl<const Value *> &Seen,
                                         unsigned Depth) {
  if (!V || Depth > 64)
    return false;

  V = V->stripPointerCasts();

  if (!Seen.insert(V).second)
    return false;

  if (const auto *AI = dyn_cast<AllocaInst>(V))
    return isLoweredVAListType(AI->getAllocatedType());

  if (const auto *GEP = dyn_cast<GEPOperator>(V))
    return derivesFromLoweredVAListImpl(GEP->getPointerOperand(), Seen, Depth + 1);

  if (const auto *LI = dyn_cast<LoadInst>(V))
    return derivesFromLoweredVAListImpl(LI->getPointerOperand(), Seen, Depth + 1);

  if (const auto *PN = dyn_cast<PHINode>(V)) {
    for (const Value *In : PN->incoming_values()) {
      if (derivesFromLoweredVAListImpl(In, Seen, Depth + 1))
        return true;
    }
    return false;
  }

  if (const auto *SI = dyn_cast<SelectInst>(V))
    return derivesFromLoweredVAListImpl(SI->getTrueValue(), Seen, Depth + 1) ||
           derivesFromLoweredVAListImpl(SI->getFalseValue(), Seen, Depth + 1);

  if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
    switch (CE->getOpcode()) {
      case Instruction::GetElementPtr:
      case Instruction::BitCast:
      case Instruction::AddrSpaceCast:
        return derivesFromLoweredVAListImpl(CE->getOperand(0), Seen, Depth + 1);
      default:
        return false;
    }
  }

  return false;
}

// Detect lowered vararg loads (e.g. loads from __va_list_tag-based state)
// when frontends lower va_arg to memory operations instead of VAArgInst.
static bool derivesFromLoweredVAList(const Value *V) {
  SmallPtrSet<const Value *, 32> Seen;
  return derivesFromLoweredVAListImpl(V, Seen, 0);
}

// The va_list object an access reads through: a va_list stack slot, or
// the base of a GEP that indexes a va_list (a va_list received as a
// parameter is an untyped pointer; its GEPs carry the type). Walks the
// lowered va_arg sequence: load of overflow_arg_area / reg_save_area,
// byte offsets, phis and selects of them. nullptr if none.
static const Value *vaListBaseImpl(const Value *V,
                                   SmallPtrSetImpl<const Value *> &Seen) {
  if (!V || Seen.size() > 64)
    return nullptr;
  V = V->stripPointerCasts();
  if (!Seen.insert(V).second)
    return nullptr;
  if (const auto *AI = dyn_cast<AllocaInst>(V))
    return isLoweredVAListType(AI->getAllocatedType()) ? AI : nullptr;
  if (const auto *GEP = dyn_cast<GEPOperator>(V)) {
    if (isLoweredVAListType(GEP->getSourceElementType()))
      return GEP->getPointerOperand()->stripPointerCasts();
    return vaListBaseImpl(GEP->getPointerOperand(), Seen);
  }
  if (const auto *LI = dyn_cast<LoadInst>(V))
    return vaListBaseImpl(LI->getPointerOperand(), Seen);
  if (const auto *PN = dyn_cast<PHINode>(V)) {
    for (const Value *In : PN->incoming_values())
      if (const Value *B = vaListBaseImpl(In, Seen))
        return B;
    return nullptr;
  }
  if (const auto *SI = dyn_cast<SelectInst>(V)) {
    if (const Value *B = vaListBaseImpl(SI->getTrueValue(), Seen))
      return B;
    return vaListBaseImpl(SI->getFalseValue(), Seen);
  }
  return nullptr;
}

static const Value *vaListBase(const Value *V) {
  SmallPtrSet<const Value *, 16> Seen;
  return vaListBaseImpl(V, Seen);
}

bool shouldSkipFunction(const Function *F) {
  if (!F)
    return false;
  if (g_sumAuthoritative)
    return g_noopBodies.count(F) != 0;
  if (!F->hasName())
    return false;

  StringRef name = F->getName();

  // Legacy hardcoded skip lists — active ONLY without --func-summaries
  // (micros / bare runs keep their historical behavior).
  if (isFreeFn(name) || isKernelUtilityFn(name))
    return true;

  return false;
}

// Strip LLVM's numeric suffix (e.g., ".0", ".123") from struct names.
// When linking multiple modules, LLVM appends these suffixes to avoid
// name collisions, but they represent the same C struct type.
StringRef stripStructNameSuffix(StringRef Name) {
  size_t DotPos = Name.rfind('.');
  if (DotPos == StringRef::npos || DotPos == 0)
    return Name;
  // Only strip if everything after the last '.' is digits
  StringRef Suffix = Name.substr(DotPos + 1);
  if (!Suffix.empty() && Suffix.find_first_not_of("0123456789") == StringRef::npos)
    return Name.substr(0, DotPos);
  return Name;
}

// Walk GEP indexed type chain to find the innermost named struct field access.
// Returns true if a named non-union struct field was found, with structName
// and fieldIdx set to the stripped struct name and field index respectively.
bool CallGraphPass::getGEPStructField(const GEPOperator *GEP,
                                       std::string &structName,
                                       unsigned &fieldIdx) {
  bool found = false;
  Type *CurTy = GEP->getSourceElementType();

  // Skip the first index (pointer/array offset into base type)
  auto idx = GEP->idx_begin();
  if (idx == GEP->idx_end())
    return false;
  ++idx; // skip first index

  while (idx != GEP->idx_end()) {
    if (StructType *STy = dyn_cast<StructType>(CurTy)) {
      ConstantInt *CI = dyn_cast<ConstantInt>(*idx);
      if (!CI)
        break; // non-constant index, give up
      unsigned fIdx = CI->getZExtValue();
      // Record if this is a named, non-union struct
      if (!STy->isLiteral() && STy->hasName() &&
          !LLVM_STRING_STARTS_WITH(STy->getStructName(), "union")) {
        structName = stripStructNameSuffix(STy->getStructName()).str();
        fieldIdx = fIdx;
        found = true;
      }
      if (fIdx < STy->getNumElements())
        CurTy = STy->getElementType(fIdx);
      else
        break;
    } else if (ArrayType *ATy = dyn_cast<ArrayType>(CurTy)) {
      CurTy = ATy->getElementType();
    } else if (VectorType *VTy = dyn_cast<VectorType>(CurTy)) {
      CurTy = VTy->getElementType();
    } else {
      break;
    }
    ++idx;
  }

  return found;
}

bool CallGraphPass::getFieldKeyFromPointerOperand(const Value *Ptr,
                                                  std::string &structName,
                                                  unsigned &fieldIdx,
                                                  Type *&fieldTy) const {
  fieldTy = nullptr;
  if (!Ptr)
    return false;

  // Handle nested GEP chains by walking upward through pointer operands until
  // we can recover a named struct field key.
  const Value *Cur = Ptr;
  SmallPtrSet<const Value *, 16> Seen;
  constexpr unsigned kMaxDepth = 32;
  for (unsigned Depth = 0; Cur && Depth < kMaxDepth; ++Depth) {
    Cur = Cur->stripPointerCastsAndAliases();
    if (!Seen.insert(Cur).second)
      break;

    const auto *GEP = dyn_cast<GEPOperator>(Cur);
    if (!GEP)
      break;

    if (getGEPStructField(GEP, structName, fieldIdx)) {
      fieldTy = GEP->getResultElementType();
      return true;
    }

    Cur = GEP->getPointerOperand();
  }

  return false;
}

bool CallGraphPass::getGlobalFieldBoundaryKey(const Value *V,
                                              std::string &key) const {
  const auto *CE = dyn_cast_or_null<ConstantExpr>(V);
  if (!CE || CE->getOpcode() != Instruction::GetElementPtr)
    return false;

  const auto *GEP = dyn_cast<GEPOperator>(CE);
  if (!GEP)
    return false;

  std::string structName;
  unsigned fieldIdx = 0;
  if (!getGEPStructField(GEP, structName, fieldIdx))
    return false;

  const Value *base = GEP->getPointerOperand()->stripPointerCasts();
  const auto *GV = dyn_cast<GlobalVariable>(base);
  if (!GV)
    return false;

  key = ("globfield:" + std::to_string(GV->getGUID()) + ":" +
         std::to_string(fieldIdx));
  return true;
}

bool CallGraphPass::getCallSiteFieldKey(const Value *FPtr,
                                        std::string &structName,
                                        unsigned &fieldIdx) const {
  const auto *LI = dyn_cast_or_null<LoadInst>(FPtr);
  if (!LI)
    return false;

  const Value *loadPtr = LI->getPointerOperand()->stripPointerCasts();
  const auto *GEP = dyn_cast<GEPOperator>(loadPtr);
  if (!GEP)
    return false;

  if (!getGEPStructField(GEP, structName, fieldIdx))
    return false;

  // Pattern: load ptr from a struct-typed field pointer without an explicit
  // trailing ", 0" index (e.g. load ptr, ptr gep(..., i32 field)).
  // In LLVM this loads the first element of that nested struct. Refine to the
  // nested field key so field filtering can distinguish callback slots.
  const auto *ST = dyn_cast<StructType>(GEP->getResultElementType());
  if (!ST || ST->isLiteral() || !ST->hasName() || ST->isOpaque() ||
      LLVM_STRING_STARTS_WITH(ST->getStructName(), "union"))
    return true;
  if (ST->getNumElements() == 0)
    return true;
  if (!ST->getElementType(0)->isPointerTy() || !LI->getType()->isPointerTy())
    return true;

  structName = stripStructNameSuffix(ST->getStructName()).str();
  fieldIdx = 0;
  return true;
}

bool CallGraphPass::isStructLayoutCompatible(const StructType *ST1,
                                              const StructType *ST2) {
  unsigned numEl = ST1->getNumElements();
  if (numEl != ST2->getNumElements())
    return false;

  for (unsigned i = 0; i < numEl; ++i) {
    if (!isCompatibleType(ST1->getElementType(i), ST2->getElementType(i)))
      return false;
  }
  return true;
}

bool CallGraphPass::isCompatibleType(const Type *T1, const Type *T2) {
  if (T1 == T2) {
      return true;
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
  } else if (T1->isIntegerTy()) {
    // All integer types are compatible (C allows implicit conversions)
    if (T2->isIntegerTy())
      return true;

    return false;
  } else if (T1->isPointerTy()) {
    // All pointer types are compatible (opaque pointers in LLVM 13+,
    // and C allows implicit void* conversions)
    if (T2->isPointerTy())
      return true;

    return false;
  } else if (T1->isArrayTy()) {
    if (!T2->isArrayTy())
      return false;

    Type *ElT1 = T1->getArrayElementType();
    Type *ElT2 = T2->getArrayElementType();
    return isCompatibleType(ElT1, ElT2);
  } else if (T1->isStructTy()) {
    const StructType *ST1 = cast<StructType>(T1);
    const StructType *ST2 = dyn_cast<StructType>(T2);
    if (!ST2)
      return false;

    // Both literal: compare structurally
    if (ST1->isLiteral() && ST2->isLiteral())
      return isStructLayoutCompatible(ST1, ST2);

    // One literal, one named: not compatible
    if (ST1->isLiteral() != ST2->isLiteral())
      return false;

    // Both named: compare names after stripping LLVM's numeric suffixes
    // (LLVM appends .0, .1, etc. when linking modules with same-named structs)
    StringRef Name1 = stripStructNameSuffix(ST1->getStructName());
    StringRef Name2 = stripStructNameSuffix(ST2->getStructName());
    return Name1.equals(Name2);
  } else if (T1->isFunctionTy()) {
    const FunctionType *FT1 = cast<FunctionType>(T1);
    const FunctionType *FT2 = dyn_cast<FunctionType>(T2);
    if (!FT2)
      return false;

    if (!isCompatibleType(FT1->getReturnType(), FT2->getReturnType()))
      return false;

    // assume varg is always compatible with varg?
    if (FT1->isVarArg()) {
      if (FT2->isVarArg())
        return true;
      else
        return false;
    }

    // compare args, again ...
    unsigned numParam1 = FT1->getNumParams();
    if (numParam1 != FT2->getNumParams())
      return false;

    for (unsigned i = 0; i < numParam1; ++i) {
      if (!isCompatibleType(FT1->getParamType(i), FT2->getParamType(i)))
        return false;
    }
    return true;
  } else if (T1->getTypeID() <= Type::FP128TyID) {
    return T1->getTypeID() == T2->getTypeID();
  } else {
    errs() << "Unhandled Types:" << *T1 << " :: " << *T2 << "\n";
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool CallGraphPass::isCompatible(const CallBase *CS, const Function *F) {
  if (F->isIntrinsic())
    return false;

  const FunctionType *FTy = F->getFunctionType();
  unsigned NumFixedParams = FTy->getNumParams();
  unsigned NumActualArgs = CS->arg_size();

  // For vararg functions, callsite must provide at least the fixed parameters
  if (FTy->isVarArg()) {
    if (NumActualArgs < NumFixedParams)
      return false;
  } else {
    // For non-vararg, require exact argument count match
    if (NumActualArgs != NumFixedParams)
      return false;
    // --cfl-varargs-strict: behind a variadic-typed pointer ("T (A, ...)")
    // a fixed-arity callee must match the pointer's fixed-parameter count,
    // not the actual count. clang types an unprototyped (K&R) call as
    // variadic with every actual as a fixed parameter, so K&R dispatch is
    // unaffected; a genuine "(fmt, ...)" prototype stops admitting every
    // address-taken function of the actuals' arity (nm-new einfo sites).
    if (CFLVarargsStrict) {
      const FunctionType *CTy = CS->getFunctionType();
      if (CTy->isVarArg() && CTy->getNumParams() != NumFixedParams)
        return false;
    }
  }

  // Return type: if the callsite result is unused, accept any return type.
  // Otherwise require compatibility.
  if (!CS->use_empty() && !CS->getType()->isVoidTy()) {
    if (!isCompatibleType(F->getReturnType(), CS->getType()))
      return false;
  }

  // Type matching on the fixed parameters
  auto AI = CS->arg_begin();
  for (unsigned i = 0; i < NumFixedParams; ++i, ++AI) {
    Type *FormalTy = FTy->getParamType(i);
    Type *ActualTy = (*AI)->getType();

    if (!isCompatibleType(FormalTy, ActualTy))
      return false;
  }

  return true;
}

bool CallGraphPass::findCalleesByType(const CallBase *CS, FuncSet &FS) {
  //errs() << *CS << "\n";
  for (const Function *F : Ctx->AddressTakenFuncs) {
    if (isCompatible(CS, const_cast<Function*>(F)))
      FS.insert(F);
  }

  return false;
}

bool CallGraphPass::handleMemcpy(const CallBase *CS) {
  Value *dst = CS->getArgOperand(0);
  Value *src = CS->getArgOperand(1);
  CG_LOG("Memcpy: " << *dst << " = " << *src << "\n");
  NodeIndex dstNode = getRepNodeForValue(dst);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Memcpy dst node not found!");
  // if (dstNode == AndersNodeFactory::InvalidIndex) {
  //   dstNode = NF.createValueNode(dst);
  //   CG_DEBUG("Create value node " << dstNode << " for memcpy dst " << *dst << "\n");
  // }
  NodeIndex srcNode = getRepNodeForValue(src);
  assert(srcNode != AndersNodeFactory::InvalidIndex && "Memcpy src node not found!");
  // if (srcNode == AndersNodeFactory::InvalidIndex) {
  //   srcNode = NF.createValueNode(src);
  //   CG_DEBUG("Create value node " << srcNode << " for memcpy src " << *src << "\n");
  // }
  // field-insensitive: *dst = *src
  NodeIndex derefDst = getRepDerefNode(dstNode);
  NodeIndex derefSrc = getRepDerefNode(srcNode);
  addAssignmentEdge(derefSrc, derefDst);

  // Field mode: the deref-to-deref edge only links the offset-0 cells, but an
  // aggregate copy moves every field. When both operands agree on the copied
  // struct type, emit directional per-field cell copies (precise). Otherwise
  // fall back to value-aliasing the two pointers plus wildcard loops (sound
  // for any layout, but smears fields and directions).
  if (Graph.fieldSensitive()) {
    auto pointeeCopyType = [](const Value *P) -> Type * {
      const Value *V = P->stripPointerCasts();
      if (const auto *AI = dyn_cast<AllocaInst>(V))
        return AI->getAllocatedType();
      if (const auto *GV = dyn_cast<GlobalVariable>(V))
        return GV->getValueType();
      if (const auto *GEP = dyn_cast<GEPOperator>(V))
        return GEP->getResultElementType();
      return nullptr;
    };
    Type *dstTy = pointeeCopyType(dst);
    Type *srcTy = pointeeCopyType(src);
    while (dstTy && (isa<ArrayType>(dstTy) || isa<VectorType>(dstTy)))
      dstTy = dstTy->getContainedType(0);
    while (srcTy && (isa<ArrayType>(srcTy) || isa<VectorType>(srcTy)))
      srcTy = srcTy->getContainedType(0);
    // Size gate for the residue copy: small constant-length copies are
    // the struct-copy idiom (assignment lowering, copy_from_user-style
    // targets) and deserve the precise encoding; large or variable
    // lengths are bulk data moves (container backing stores), where
    // faithfully chaining residue cells through every reallocation
    // explodes fact volume for zero callgraph value (measured on
    // harfbuzz: >646M facts and climbing vs 570M with the wildcard).
    const auto *lenCI = CS->arg_size() > 2
                            ? dyn_cast<ConstantInt>(CS->getArgOperand(2))
                            : nullptr;
    const bool smallCopy = lenCI && lenCI->getZExtValue() <= 512;
    if (dstTy && dstTy == srcTy && isa<StructType>(dstTy) && curDL) {
      emitFieldwiseCopyEdges(srcNode, dstNode, dstTy, 0);
    } else if (CFLResidueCopies && flowsTo() && smallCopy) {
      // Layout-free residue copy: a byte copy preserves offsets, so under
      // the mod-P encoding "for every residue r: *(dst+r) = *(src+r)" is
      // sound for any length and any opaque pointee — no type info, no
      // wildcard smear, and directional (the old fallback value-aliased
      // both pointers bidirectionally). Residue 0 is the deref-to-deref
      // edge already emitted above. Flows-to only: the extra f-edges
      // multiply the Dn/Up chain scaffolding the saturation solver
      // materializes (8x+ solve blowup measured on libpng).
      const unsigned P = Graph.numFieldBuckets();
      NodeIndex sParent = getCanonicalNode(srcNode);
      NodeIndex dParent = getCanonicalNode(dstNode);
      if (CFLLazyAddress) {
        // Exact addresses have no finite residue set to copy over: an
        // unknown-layout copy is the range wildcard on both sides.
        addFieldWildcardLoop(sParent, "memcpy-unknown-layout");
        addFieldWildcardLoop(dParent, "memcpy-unknown-layout");
      } else
      for (unsigned r = 1; r < P; r++) {
        NodeIndex sF = getFieldPtrNode(sParent, (int64_t)r);
        NodeIndex dF = getFieldPtrNode(dParent, (int64_t)r);
        Graph.addField(sParent, getCanonicalNode(sF), (int)r);
        Graph.addField(dParent, getCanonicalNode(dF), (int)r);
        addAssignmentEdge(getRepDerefNode(getCanonicalNode(sF)),
                          getRepDerefNode(getCanonicalNode(dF)));
      }
    } else if (flowsTo()) {
      // Bulk / unknown-layout copy under flows-to: a directional content
      // move over every offset of both objects. The wildcard on each
      // pointer makes the deref-to-deref edge above read all cells of
      // the source objects and write all cells of the destination
      // objects. No value alias: memcpy never makes dst point where
      // src points. The old bidirectional pointer alias welded the
      // copied object and the byte buffer into one points-to set
      // (nm-new: elf_link_add_object_symbols' as-needed rehash
      // `memcpy(old_ent, p, entsize)` made every hash entry alias the
      // scratch buffer, which then carried strings and function
      // addresses into asection/link-hash pointers).
      addFieldWildcardLoop(srcNode, "memcpy-bulk");
      addFieldWildcardLoop(dstNode, "memcpy-bulk");
    } else {
      addAssignmentEdge(srcNode, dstNode);
      addAssignmentEdge(dstNode, srcNode);
      addFieldWildcardLoop(srcNode, "memcpy-bulk-or-nonflowsto");
      addFieldWildcardLoop(dstNode, "memcpy-bulk-or-nonflowsto");
    }
  }

  return false;
}

// Directional per-field content copy for an aggregate copy of type `Ty` from
// *srcAddr to *dstAddr: for every pointer-bearing field, connect the source
// field cell to the destination field cell through matched f-edges. Arrays
// collapse to their element; unions stop descent with wildcard loops.
void CallGraphPass::emitFieldwiseCopyEdges(NodeIndex srcAddr, NodeIndex dstAddr,
                                           Type *Ty, unsigned depth) {
  while (Ty && (isa<ArrayType>(Ty) || isa<VectorType>(Ty)))
    Ty = Ty->getContainedType(0);
  auto *STy = dyn_cast_or_null<StructType>(Ty);
  if (!STy) {
    // Pointer-bearing scalar cell: copy the cell itself.
    addAssignmentEdge(getRepDerefNode(getCanonicalNode(srcAddr)),
                      getRepDerefNode(getCanonicalNode(dstAddr)));
    return;
  }
  if (depth > 8 ||
      (STy->hasName() && LLVM_STRING_STARTS_WITH(STy->getStructName(), "union"))) {
    addFieldWildcardLoop(srcAddr, "fieldwise-copy-depth-cap");
    addFieldWildcardLoop(dstAddr, "fieldwise-copy-depth-cap");
    addAssignmentEdge(getRepDerefNode(getCanonicalNode(srcAddr)),
                      getRepDerefNode(getCanonicalNode(dstAddr)));
    return;
  }
  const StructLayout *SL = curDL->getStructLayout(STy);
  for (unsigned i = 0; i < STy->getNumElements(); i++) {
    Type *elemTy = STy->getElementType(i);
    if (!containsPointerType(elemTy))
      continue;
    int64_t off = (int64_t)SL->getElementOffset(i);
    NodeIndex sF = srcAddr, dF = dstAddr;
    if (off != 0) {
      NodeIndex sParent = getCanonicalNode(srcAddr);
      NodeIndex dParent = getCanonicalNode(dstAddr);
      sF = getFieldPtrNode(sParent, off);
      dF = getFieldPtrNode(dParent, off);
      addFieldEdgesExact(sParent, getCanonicalNode(sF), off, 0, false, STy);
      addFieldEdgesExact(dParent, getCanonicalNode(dF), off, 0, false, STy);
    }
    emitFieldwiseCopyEdges(sF, dF, elemTy, depth + 1);
  }
}

static bool ptrToIntTagRoundTripOnly(const llvm::Value *PTI);
// Census: the op class that made the last tag-walk refuse. The
// either-or instrument: constant offsets are recoverable residues
// (a future int-domain field edge), value-unknown arithmetic is a
// justified admission — the split decides which lever applies.
static const char *g_tagWalkWhy = "";
static std::string tagWalkTag(const char *base) {
  return std::string(base) + ":" + (*g_tagWalkWhy ? g_tagWalkWhy : "clean");
}
size_t g_intStoreUnmodeled = 0;
bool CallGraphPass::handleCall(const CallBase *CS, const Function *CF,
                               int opsSkipArg) {
  if (CF->isIntrinsic()) {
    // handle intrinsic functions
    return false;
  }

  // Transfer summary: the atoms fully describe the interface — apply
  // them and skip arg/ret wiring (per-callsite semantics, no shared
  // formal/ret mixing). FRESH-bearing summaries normally short-circuit
  // earlier via the AllocSites branch; this path serves non-fresh
  // summaries and fresh ones reached through indirect resolution.
  bool retBound = false;
  {
    auto sit = Ctx->FuncSummaries.find(CF);
    // Summaries bind the callee's transfer to THIS callsite's actuals
    // — correct at DIRECT callsites (the adoption contract). At
    // INDIRECTLY-RESOLVED sites the callee set is answer-quality
    // (pool smear included): applying atoms there welds the callee's
    // cells to every wrongly-resolved site's actuals both ways (5.18:
    // ethtool_set_ethtool_phy_ops's ST atom pulled ethtool_phy_ops'
    // cell into the pool, 4 reader sites went full-pool, +27k pairs).
    // Indirect resolutions keep the pooled arg/ret wiring.
    const bool directSite =
        CS->getCalledFunction() ||
        !Ctx->IndirectCallInsts.count(const_cast<llvm::CallBase *>(CS));
    // TRANSFER-FREE summaries (NOOP/EMPTY: zero atoms) are safe at
    // indirectly-resolved sites too: they only SKIP wiring, so at a
    // wrongly-resolved callee that's a no-op and at the real callee
    // it's the proof. The ethtool hazard above is edge-ADDING atoms
    // binding callee cells to wrong sites' actuals — those stay
    // direct-only. This is what severs pooled-container wiring at
    // icall dispatch (sysctl proc_handler family: every subsystem's
    // ctl_table into every generic handler's formal, the km
    // 56-subsystem weld).
    const bool transferFree =
        sit != Ctx->FuncSummaries.end() &&
        (sit->second->noop ||
         (sit->second->atoms.empty() && !sit->second->fresh &&
          !sit->second->none));
    if (sit != Ctx->FuncSummaries.end() && (directSite || transferFree)) {
      if (!applySummaryAtoms(CS, *sit->second, &retBound, sit->first))
        return false;
      // Invoke atom with dynamic fn at this callsite: fall through to
      // the pooled arg/ret wiring (sound, LEDGERed). retBound=true
      // means an INVOKE :ret atom already wired this callsite's
      // return per-fn — the shared HOF return edge is the severed
      // ret-pooling channel, so it must NOT also be added below.
    }
  }

  // Skip utility functions to reduce edge explosion
  if (shouldSkipFunction(CF)) {
    CG_DEBUG("Skipping utility function: " << CF->getName() << "\n");
    return false;
  }

  if (CF->empty()) {
    // External function — handle memcpy/memmove specially.
    WARNING("Call: " << CF->getName() << " is empty!\n");
    if (CF->getName() == "memcpy" || CF->getName() == "memmove")
      handleMemcpy(CS);

    // In compositional mode, fall through to create on-demand arg/ret nodes
    // so cross-TU data flow is captured in the compressed graph.
    if (!exportsCallBoundaries())
      return false;
  }

  wireCallArgs(CS, CF, opsSkipArg);

  // handle return (pointer or pointer-bearing aggregate, e.g. {ptr,ptr})
  if (!retBound && containsPointerType(CF->getReturnType())) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    if (retNode == AndersNodeFactory::InvalidIndex ||
        retNode == NF.getUniversalPtrNode()) {
      // On-demand return node for declared function.
      retNode = NF.createReturnNode(CF);
    }
    retNode = getCanonicalNode(retNode);
    // The callsite may not have a value node if it discards the return value
    // (e.g., void-typed callsite matched via permissive isCompatible)
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      addAssignmentEdge(retNode, callNode);
  } else if (!retBound && curDL &&
             isPtrWidthInt(CF->getReturnType(), *curDL)) {
    // Laundered-pointer int return (the __fdget idiom). For DEFINED
    // callees, create the return node on demand: waiting for the
    // callee's visitReturnInst is visitation-order-dependent (5.18:
    // read_write.o handled before file.o meant __fdget_pos had no
    // return node when ksys_lseek's callsite was wired — FN). The
    // callee's own return wiring is witness-gated, so an unwitnessed
    // node stays fact-free and the edge is inert. Declared int
    // externs still get nothing — the boundary census owns those.
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    if ((retNode == AndersNodeFactory::InvalidIndex ||
         retNode == NF.getUniversalPtrNode()) &&
        !CF->empty())
      retNode = NF.createReturnNode(CF);
    if (retNode != AndersNodeFactory::InvalidIndex &&
        retNode != NF.getUniversalPtrNode()) {
      retNode = getCanonicalNode(retNode);
      NodeIndex callNode = getRepNodeForValue(CS);
      if (callNode == AndersNodeFactory::InvalidIndex)
        callNode = getCanonicalNode(NF.createValueNode(CS));
      addAssignmentEdge(retNode, callNode);
      // Segment-local field claim for the call-result segment.
      if (Graph.fieldSensitive() && !ptrToIntTagRoundTripOnly(CS))
        addFieldWildcardLoop(callNode,
                             tagWalkTag("int-callret-dirty-segment").c_str());
    }
  }

  return false;
}

// Actual->formal (and variadic-tail) wiring for a callsite, shared by
// handleCall and the summary dynamic-fn pooled fallback at allocator
// branches (which must feed the callee body WITHOUT the shared-return
// edge: the callsite's fresh object is its return identity).
void CallGraphPass::wireCallArgs(const CallBase *CS, const Function *CF,
                                 int skipArg) {
  // handle args:
  // - fixed arguments map to formal params
  // - variadic tail (if any) maps to the callee's vararg summary node
  unsigned numArgs = CS->arg_size();
  unsigned numFormals = CF->arg_size();
  unsigned minArgs = std::min(numArgs, numFormals);
  for (unsigned i = 0; i < minArgs; i++) {
    if ((int)i == skipArg)
      continue; // ops-pairs tightening: receiver bound per-pair instead
    Value *arg = CS->getArgOperand(i);
    // First-class aggregates ({ptr,ptr} closures, coerced small structs)
    // carry pointer identity by value — skip only pointer-free types.
    if (!containsPointerType(arg->getType())) {
      // Laundered-pointer int ARGUMENT: the same idiom the return-side
      // fixes (9f3639e/dc5e801) closed, on the other boundary — a
      // tagged word passed by value severed provenance identically
      // (`f((unsigned long)file | flag)` and the callee untags).
      // Witness-gated like returns; defined callees only (the extern
      // boundary is census-owned). Edges are inert unless real
      // pointer facts flow.
      bool declined = false;
      if (curDL && isPtrWidthInt(arg->getType(), *curDL) && !CF->empty() &&
          !shouldSkipValue(arg) && mayCarryPtrProvenance(arg, 8, declined)) {
        NodeIndex argNode = getRepNodeForValue(arg);
        if (argNode == AndersNodeFactory::InvalidIndex)
          argNode = getCanonicalNode(NF.createValueNode(arg));
        Value *farg = CF->getArg(i);
        NodeIndex formalNode = getRepNodeForValue(farg);
        if (formalNode == AndersNodeFactory::InvalidIndex)
          formalNode = getCanonicalNode(NF.createValueNode(farg));
        addAssignmentEdge(argNode, formalNode);
        // Segment-local field claim for the formal's segment
        // (idempotent across callsites: wildcard set dedups).
        if (Graph.fieldSensitive() && !ptrToIntTagRoundTripOnly(farg))
          addFieldWildcardLoop(
              formalNode, tagWalkTag("int-formal-dirty-segment").c_str());
      } else if (declined) {
        g_intArgUnmodeled++;
      }
      continue;
    }
    if (shouldSkipValue(arg)) {
      CG_DEBUG("Skipping compiler-introduced argument: " << *arg << "\n");
      continue;
    }
    NodeIndex argNode = getRepNodeForValue(arg);
    if (argNode == AndersNodeFactory::InvalidIndex) {
      argNode = NF.createValueNode(arg);
      argNode = getCanonicalNode(argNode);
      CG_DEBUG("Create value node " << argNode << " for Arg " << *arg << "\n");
    }

    Value *farg = CF->getArg(i);
    NodeIndex formalNode = getRepNodeForValue(farg);
    if (formalNode == AndersNodeFactory::InvalidIndex) {
      // On-demand node for declared function formal argument.
      formalNode = NF.createValueNode(farg);
      formalNode = getCanonicalNode(formalNode);
    }
    addAssignmentEdge(argNode, formalNode);
  }
  if (CF->isVarArg()) {
    if (CFLPrintfVarargSink && printfVarargSinkCallsite(CS, CF, true)) {
      // Benign printf-style callsite: varargs are read-only renderer
      // inputs; skip the vararg-summary wiring entirely.
      printfSinkCallsites++;
      printfSinkArgsSkipped += numArgs - numFormals;
    } else {
      NodeIndex varargNode = NF.getVarargNodeFor(CF);
      if (varargNode == AndersNodeFactory::InvalidIndex)
        varargNode = NF.createVarargNode(CF);
      varargNode = getCanonicalNode(varargNode);
      for (unsigned i = numFormals; i < numArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!containsPointerType(arg->getType())) {
          // Laundered ints ride varargs too (non-benign-fmt callsites
          // only; printf sinks are intercepted above). Same witness
          // gate as fixed args.
          bool declined = false;
          if (curDL && isPtrWidthInt(arg->getType(), *curDL) &&
              !CF->empty() && !shouldSkipValue(arg) &&
              mayCarryPtrProvenance(arg, 8, declined)) {
            NodeIndex argNode = getRepNodeForValue(arg);
            if (argNode == AndersNodeFactory::InvalidIndex)
              argNode = getCanonicalNode(NF.createValueNode(arg));
            addAssignmentEdge(argNode, varargNode);
          } else if (declined) {
            g_intArgUnmodeled++;
          }
          continue;
        }
        if (shouldSkipValue(arg)) {
          CG_DEBUG("Skipping compiler-introduced variadic argument: " << *arg << "\n");
          continue;
        }
        NodeIndex argNode = getRepNodeForValue(arg);
        if (argNode == AndersNodeFactory::InvalidIndex) {
          argNode = NF.createValueNode(arg);
          argNode = getCanonicalNode(argNode);
        }
        addAssignmentEdge(argNode, varargNode);
      }
    }
  }

}

bool CallGraphPass::handleContainerCall(const CallBase *CS, const Function *CF) {
  auto it = Ctx->ContainerFuncs.find(CF);
  if (it == Ctx->ContainerFuncs.end())
    return false;

  const auto &Info = it->second;
  CG_DEBUG("ContainerCall: " << CF->getName() << " at " << *CS << "\n");

  // Get the container object node
  unsigned containerIdx = (unsigned)Info.containerArg;
  if (containerIdx >= CS->arg_size())
    return false;
  Value *containerArg = CS->getArgOperand(containerIdx);
  if (!containerArg->getType()->isPointerTy())
    return false;
  NodeIndex containerNode = getRepNodeForValue(containerArg);
  if (containerNode == AndersNodeFactory::InvalidIndex) {
    containerNode = NF.createValueNode(containerArg);
    containerNode = getCanonicalNode(containerNode);
    CG_DEBUG("Create value node " << containerNode
             << " for container arg " << *containerArg << "\n");
  }

  // Get or create dereference node for the container (represents "*container")
  // Field mode: container helpers access arbitrary interior fields.
  if (Graph.fieldSensitive())
    addFieldWildcardLoop(containerNode, "container-helper");
  NodeIndex derefNode = getRepDerefNode(containerNode);

  // Handle store args: val -> *container (assignment edges)
  for (int storeIdx : Info.storeArgs) {
    if ((unsigned)storeIdx >= CS->arg_size())
      continue;
    Value *val = CS->getArgOperand(storeIdx);
    if (!val->getType()->isPointerTy())
      continue;
    if (shouldSkipValue(val))
      continue;
    NodeIndex valNode = getRepNodeForValue(val);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(val);
      valNode = getCanonicalNode(valNode);
      CG_DEBUG("Create value node " << valNode
               << " for store arg " << *val << "\n");
    }
    addAssignmentEdge(valNode, derefNode);
    CG_DEBUG("ContainerStore: " << valNode << " -> " << derefNode << "\n");
  }

  // Handle load return: *container -> callsite result
  if (Info.loadReturn && CF->getReturnType()->isPointerTy()) {
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex) {
      addAssignmentEdge(derefNode, callNode);
      CG_DEBUG("ContainerLoad: " << derefNode << " -> " << callNode << "\n");
    }
  }

  return false;
}

bool CallGraphPass::removeCallEdges(const CallBase *CS, const Function *CF) {
  assert(!CF->isIntrinsic() && "Intrinsic function should not be here!");

  // handle args
  unsigned numArgs = CS->arg_size();
  unsigned numFormals = CF->arg_size();
  // Remove fixed-arg edges
  unsigned minArgs = std::min(numArgs, numFormals);
  for (unsigned i = 0; i < minArgs; i++) {
    Value *arg = CS->getArgOperand(i);
    // Must mirror handleCall: pointer-bearing aggregates are wired too.
    if (!containsPointerType(arg->getType())) {
      // Mirror the witnessed int-arg wiring exactly (same gate, same
      // witness call — deterministic), else retraction leaves stale
      // laundered-int edges.
      bool declined = false;
      if (curDL && isPtrWidthInt(arg->getType(), *curDL) && !CF->empty() &&
          !shouldSkipValue(arg) && mayCarryPtrProvenance(arg, 8, declined)) {
        NodeIndex argNode = getRepNodeForValue(arg);
        NodeIndex formalNode = getRepNodeForValue(CF->getArg(i));
        if (argNode != AndersNodeFactory::InvalidIndex &&
            formalNode != AndersNodeFactory::InvalidIndex)
          Graph.removeCopy(getCanonicalNode(argNode),
                                   getCanonicalNode(formalNode));
      }
      continue;
    }
    if (shouldSkipValue(arg))
      continue; // handleCall never wired these
    NodeIndex argNode = getRepNodeForValue(arg);
    assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
    Value *farg = CF->getArg(i);
    NodeIndex formalNode = getRepNodeForValue(farg);
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    Graph.removeCopy(getCanonicalNode(argNode), getCanonicalNode(formalNode));
  }
  // Remove variadic-tail edges
  if (CF->isVarArg() &&
      !(CFLPrintfVarargSink && printfVarargSinkCallsite(CS, CF))) {
    NodeIndex varargNode = getCanonicalNode(NF.getVarargNodeFor(CF));
    assert(varargNode != AndersNodeFactory::InvalidIndex && "Vararg node not found!");
    for (unsigned i = numFormals; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!containsPointerType(arg->getType())) {
        bool declined = false;
        if (curDL && isPtrWidthInt(arg->getType(), *curDL) && !CF->empty() &&
            !shouldSkipValue(arg) && mayCarryPtrProvenance(arg, 8, declined)) {
          NodeIndex argNode = getRepNodeForValue(arg);
          if (argNode != AndersNodeFactory::InvalidIndex)
            Graph.removeCopy(getCanonicalNode(argNode), varargNode);
        }
        continue;
      }
      if (shouldSkipValue(arg))
        continue; // handleCall never wired these
      NodeIndex argNode = getRepNodeForValue(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      Graph.removeCopy(getCanonicalNode(argNode), varargNode);
    }
  }

  // handle return (must mirror handleCall)
  if (containsPointerType(CF->getReturnType())) {
    NodeIndex retNode = getCanonicalNode(NF.getReturnNodeFor(CF));
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      Graph.removeCopy(getCanonicalNode(retNode), getCanonicalNode(callNode));
  } else if (curDL && isPtrWidthInt(CF->getReturnType(), *curDL)) {
    // Mirror the laundered-int return wiring (9f3639e/dc5e801) —
    // retraction previously left these edges stale (latent asymmetry;
    // imprecision, not unsoundness).
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    if (retNode != AndersNodeFactory::InvalidIndex &&
        retNode != NF.getUniversalPtrNode()) {
      NodeIndex callNode = getRepNodeForValue(CS);
      if (callNode != AndersNodeFactory::InvalidIndex)
        Graph.removeCopy(getCanonicalNode(retNode),
                                 getCanonicalNode(callNode));
    }
  }

  return false;
}

NodeIndex CallGraphPass::getCanonicalNode(NodeIndex n) const {
  if (n == AndersNodeFactory::InvalidIndex)
    return n;

  auto it = canonicalNodeMap.find(n);
  if (it == canonicalNodeMap.end())
    return n;

  NodeIndex root = it->second;
  while (root != AndersNodeFactory::InvalidIndex) {
    auto next = canonicalNodeMap.find(root);
    if (next == canonicalNodeMap.end() || next->second == root)
      break;
    root = next->second;
  }
  return root;
}

void CallGraphPass::collectCanonicalMembers(NodeIndex n, std::vector<NodeIndex> &out) const {
  out.clear();
  if (n == AndersNodeFactory::InvalidIndex)
    return;

  NodeIndex root = getCanonicalNode(n);
  auto it = canonicalClassMembers.find(root);
  if (it == canonicalClassMembers.end() || it->second.empty()) {
    out.push_back(root);
    return;
  }

  out.reserve(it->second.size());
  for (NodeIndex member : it->second)
    out.push_back(member);
}

NodeIndex CallGraphPass::getRepNodeForValue(const Value *V) {
  if (!V)
    return AndersNodeFactory::InvalidIndex;
  NodeIndex n = NF.getValueNodeFor(V);
  if (n == AndersNodeFactory::InvalidIndex)
    return n;
  // Canonical ConstantExpr-GEP nodes need their base connection emitted
  // (once per module) wherever they appear as operands: field-chain
  // edges in field mode, the plain GetElementPtr 'a' edge otherwise.
  if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
    if (CE->getOpcode() == Instruction::GetElementPtr)
      ensureConstGEPFieldEdges(CE);
  }
  return getCanonicalNode(n);
}

// Universal-ptr exposure ledger (task #22 postmortem): the universal
// fallback silently absorbed 17.7k wired edges once — every touch is
// now counted and reported so a repeat is loud, not a 3h kernel run.
size_t g_uniEdgeTouches = 0, g_uniDerefTouches = 0,
              g_uniFptrIcalls = 0;
NodeIndex CallGraphPass::getRepDerefNode(NodeIndex ptrNode) {
  if (ptrNode == NF.getUniversalPtrNode() ||
      ptrNode == NF.getUniversalObjNode())
    g_uniDerefTouches++; // memory modeled through unknown-extern hub
  if (ptrNode == AndersNodeFactory::InvalidIndex)
    return AndersNodeFactory::InvalidIndex;

  NodeIndex canonical = getCanonicalNode(ptrNode);
  NodeIndex derefNode = NF.getDereferenceNodeFor(canonical);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    derefNode = NF.createDereferenceNode(canonical);
    CG_DEBUG("Create deref node " << derefNode << " for canonical node " << canonical << "\n");
  }

  // In compositional per-TU mode, canonical nodes may be shared across TUs.
  // Re-emit ptr<->deref constraints once per module so each TU edge slice
  // retains the local memory edge context after splitting.
  if (moduleDerefEdgeRoots.insert(canonical).second)
    Graph.addDeref(canonical, derefNode);

  return derefNode;
}

void CallGraphPass::addAssignmentEdge(NodeIndex src, NodeIndex dst) {
  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex s = getCanonicalNode(src);
  NodeIndex d = getCanonicalNode(dst);
  // Before the s == d shortcut: a presolve class may hold both the value
  // and the cell, but the cell's unnamed shadow is outside every class.
  fileUnnamedWrite(s, src, dst);
  if (s == d) return;
  if (s == NF.getUniversalPtrNode() || d == NF.getUniversalPtrNode() ||
      s == NF.getUniversalObjNode() || d == NF.getUniversalObjNode())
    g_uniEdgeTouches++;
  Graph.addCopy(s, d);
}

// ---- Named cells (--cfl-named-planes) ----
// Realization of NamedCells.lean's planes by separate nodes: the cell
// itself keeps every write (unnamed loads read it, exactly as without
// names); a shadow per (cell, name) holds the writes filed under that
// name, and the Unnamed shadow every other write into the cell. A
// shadow has no Deref edge: the solver keeps it as a satellite of its
// cell's class and merges the satellites of one name whenever two
// classes merge, so a merged class keeps its content by name. Shadows
// stay out of presolve classes and SCC collapse, never mint an identity
// of their own, and receive the cell's identity in the Unnamed shadow
// instead (FlowsToSolver.cc).

bool CallGraphPass::namedPlanes() const { return CFLNamedPlanes && flowsTo(); }

NodeIndex CallGraphPass::cellParent(NodeIndex cell) {
  if (NF.isDereferenceNode(cell)) {
    if (shadowInfo.count(cell))
      return AndersNodeFactory::InvalidIndex; // a shadow is no cell
    return NF.getDerefParent(cell);
  }
  if (!NF.isObjectNode(cell))
    return AndersNodeFactory::InvalidIndex;
  // Object nodes are cells when a Deref edge reaches them (allocation
  // contents): index the Deref edges added since the last look.
  if (Graph.removalCount() != objCellRemovals) {
    objCellRemovals = Graph.removalCount();
    objCellScan = 0;
  }
  const auto &E = Graph.edges();
  for (; objCellScan < E.size(); objCellScan++)
    if (E[objCellScan].kind == EdgeKind::Deref &&
        NF.isObjectNode(E[objCellScan].to))
      objCellParent.emplace(E[objCellScan].to, E[objCellScan].from);
  auto it = objCellParent.find(cell);
  return it == objCellParent.end() ? AndersNodeFactory::InvalidIndex
                                   : it->second;
}

std::pair<NodeIndex, uint32_t> CallGraphPass::shadowInfoOf(NodeIndex n) const {
  auto it = shadowInfo.find(n);
  if (it == shadowInfo.end())
    return {AndersNodeFactory::InvalidIndex, ka::AccessNames::Original};
  return it->second;
}

NodeIndex CallGraphPass::namedShadow(NodeIndex cell, uint32_t name) {
  assert(name != ka::AccessNames::Original && "the original is the cell");
  assert(!isShadowCell(cell) && "shadows have no shadows");
  const uint64_t key = (uint64_t)cell << 32 | name;
  auto it = shadowOf.find(key);
  if (it != shadowOf.end())
    return it->second;
  assert(cellParent(cell) != AndersNodeFactory::InvalidIndex &&
         "only a cell has shadows");
  const NodeIndex sh = NF.createDereferenceNode(AndersNodeFactory::InvalidIndex);
  shadowOf.emplace(key, sh);
  shadowInfo.emplace(sh, std::make_pair(cell, name));
  namedStats.shadows++;
  return sh;
}

bool CallGraphPass::isCellNode(NodeIndex n) {
  if (isShadowCell(n))
    return false;
  const bool deref = NF.isDereferenceNode(n);
  if (!deref && !NF.isObjectNode(n))
    return false;
  if (cellParent(n) == AndersNodeFactory::InvalidIndex) {
    // An object no Deref edge reaches is not memory in this graph (it is
    // read only as a value); every dereference node has its pointer.
    assert(!deref && "dereference node without a pointer");
    return false;
  }
  return true;
}

void CallGraphPass::fileUnnamedWrite(NodeIndex s, NodeIndex src,
                                     NodeIndex dst) {
  if (namedFiling || !namedPlanes() || !isCellNode(dst))
    return;
  if (isCellNode(src) && !cellWriteIsValue) {
    // A copy from cell to cell (memcpy, CPY/MOVE summaries, asm, field-
    // wise copies) moves bytes to the same offsets, so content keeps the
    // name it was stored under: unnamed to unnamed here, each name's
    // shadow to the same name's once the solve shows which names the
    // source holds (wireCopyNames).
    Graph.addCopy(namedShadow(src, ka::AccessNames::Unnamed),
                  namedShadow(dst, ka::AccessNames::Unnamed));
    Graph.addCopy(namedShadow(src, ka::AccessNames::Identity),
                  namedShadow(dst, ka::AccessNames::Identity));
    if (cellCopySeen.insert(((uint64_t)src << 32) | dst).second)
      cellCopies.emplace_back(src, dst);
    namedStats.cellCopies++;
    return;
  }
  // Not a copy: where does the writer point? A typed single leaf is a
  // named write (the store's own address had no name, e.g. a summary
  // atom or int-provenance store through a field address); any other
  // typed position opens the names it may cover; no struct at all is
  // the counted blind spot.
  std::string where;
  const DataLayout *DLw = curDL;
  const ka::AccessNames::Position pos = writerPosition(dst, where);
  if ((pos.S || pos.DIS) && DLw) {
    const uint32_t n = cellWriteSize
                           ? accessNames->ofPosition(pos, cellWriteSize, *DLw)
                           : ka::AccessNames::Unnamed;
    if (n != ka::AccessNames::Unnamed) {
      fileNamedWrite(s, dst, n);
      namedStats.typedWrites++;
      return;
    }
    if (pos.S) {
      openStruct(pos.S, where);
    } else { // a debug-info-only struct we cannot enumerate: counted
      blindWrites++;
      blindBy[where]++;
    }
  } else if (pos.tainted && !pos.open.empty()) {
    for (llvm::StructType *S : pos.open)
      openStruct(S, where);
  } else {
    blindWrites++;
    blindBy[where]++;
    if ((CFLCensusTypeLabels || !CFLRuleReport.empty()))
      blindWriteLog.emplace_back(dst, where);
    // --cfl-name-by-target: no position at all; the solve decides by the
    // objects the pointer reaches (FlowsToSolver.cc, flushDeferredUnnamed).
    if (CFLNameByTarget && NF.isDereferenceNode(dst)) {
      deferredUnnamed.emplace_back(s, dst, namedShadow(dst, ka::AccessNames::Unnamed));
      namedStats.unnamedWrites++;
      return;
    }
    // ... and a write straight into an object is filed by that object now.
    if (CFLNameByTarget && NF.isObjectNode(dst) &&
        isPointerVariable(NF.getValueForNode(dst))) {
      namedStats.pointerVarWrites++;
      return; // raw cell only
    }
  }
  Graph.addCopy(s, namedShadow(dst, ka::AccessNames::Unnamed));
  namedStats.unnamedWrites++;
}

// A stack or global object whose declared type (debug info) is a pointer
// or an array of pointers: no struct field lives in it.
bool CallGraphPass::isPointerVariable(const Value *V) {
  const DIType *T = nullptr;
  if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) {
    for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(AI)))
      if (auto *Var = DDI->getVariable()) { T = Var->getType(); break; }
  } else if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) {
    SmallVector<DIGlobalVariableExpression *, 1> GVEs;
    GV->getDebugInfo(GVEs);
    if (!GVEs.empty()) T = GVEs[0]->getVariable()->getType();
  }
  for (int i = 0; i < 8 && T; i++) {
    if (const auto *D = dyn_cast<DIDerivedType>(T)) {
      const unsigned Tg = D->getTag();
      if (Tg == dwarf::DW_TAG_pointer_type) return true;
      if (Tg == dwarf::DW_TAG_typedef || Tg == dwarf::DW_TAG_const_type ||
          Tg == dwarf::DW_TAG_volatile_type) { T = D->getBaseType(); continue; }
      return false;
    }
    if (const auto *C = dyn_cast<DICompositeType>(T))
      if (C->getTag() == dwarf::DW_TAG_array_type) { T = C->getBaseType(); continue; }
    return false;
  }
  return false;
}

bool CallGraphPass::namedCertifies() const {
  return namedPlanes() && CFLNamedUntyped == "count";
}

// --cfl-union-keys: union accesses by key (plan 3.17). With a union slot
// name (NamedCells: the union's bytes named by its struct and offset):
//   keyed write  -> its key planes and the slot;
//   unknown-key write -> the slot and the union's "#?" plane;
//   keyed read   -> its key planes and "#?" (never the slot: other keys);
//   unknown-key read -> the slot (every write).
// Without one (a struct member over the bytes) the union access is
// Unnamed and keys are its only names: keyed accesses use their key
// planes, unknown ones stay Unnamed. Key names are opened at once, so
// keyed reads also read the unnamed plane.
void CallGraphPass::applyUnionKeys(const llvm::Instruction &I,
                                   SmallVectorImpl<uint32_t> &names) {
  auto it = unionKeyNames.find(&I);
  auto ut = unionUnknownOf.find(&I);
  if (it == unionKeyNames.end() && ut == unionUnknownOf.end())
    return;
  // Only pointer accesses carry names (an integer member is no channel).
  const Type *VT = isa<StoreInst>(I) ? I.getOperand(0)->getType() : I.getType();
  if (!VT->isPointerTy())
    return;
  const bool isStore = isa<StoreInst>(I);
  const bool slotted = !names.empty() && names[0] != ka::AccessNames::Unnamed;
  auto open = [&](const std::string &k) {
    const uint32_t n = accessNames->keyName(k);
    openName(n, "union-key");
    return n;
  };
  if (it == unionKeyNames.end()) { // unknown key
    if (slotted && isStore)
      names.push_back(open(ut->second + "#?"));
    return;
  }
  const std::string prefix = it->second[0].substr(0, it->second[0].rfind('#'));
  SmallVector<uint32_t, 4> out;
  for (const std::string &k : it->second)
    out.push_back(open(k));
  if (slotted) {
    if (isStore)
      out.append(names.begin(), names.end());
    else
      out.push_back(open(prefix + "#?"));
  }
  names.assign(out.begin(), out.end());
}

void CallGraphPass::openName(uint32_t name, StringRef culprit) {
  if (!openNames.insert(name).second)
    return;
  openWhy.emplace(name, culprit.str());
  namedOpenEpoch++;
}

void CallGraphPass::openStruct(llvm::StructType *S, StringRef culprit) {
  for (uint32_t n : accessNames->leavesOf(S, *curDL))
    openName(n, culprit);
}

ka::AccessNames::Position CallGraphPass::writerPosition(NodeIndex cell,
                                                        std::string &where) {
  if (cellWriteHasPos) {
    where = cellWriteWhere;
    return cellWritePos;
  }
  NodeIndex p = cellParent(cell);
  // byte offset accumulated over synthetic field pointers, plus what the
  // write declares the cell itself does not carry
  int64_t acc = cellWriteExtraOff;
  while (p != AndersNodeFactory::InvalidIndex) {
    if (const Value *V = NF.getValueForNode(p)) {
      if (const auto *I = dyn_cast<Instruction>(V))
        where = (I->getFunction()->getName() + "::" + I->getOpcodeName()).str();
      else if (const auto *A = dyn_cast<Argument>(V))
        where = (A->getParent()->getName() + "::arg" + Twine(A->getArgNo())).str();
      else
        where = V->hasName() ? V->getName().str() : std::string("<const>");
      ka::AccessNames::Position pos = accessNames->position(V, *curDL);
      if (pos.S && acc && !pos.tainted) {
        pos.off += acc;
        if (pos.off < 0 ||
            (uint64_t)pos.off >=
                curDL->getStructLayout(pos.S)->getSizeInBytes()) {
          pos.S = nullptr; // a field pointer past the struct: untyped
          pos.why = ka::AccessNames::OutOfRange;
        }
      }
      return pos;
    }
    auto it = fieldPtrOrigin.find(p);
    if (it == fieldPtrOrigin.end())
      break;
    acc += it->second.second;
    p = it->second.first;
  }
  where = "<synthetic>";
  return ka::AccessNames::Position();
}

// A store through several names (the lanes of a pointer vector) files
// the whole value under each: a superset of each lane's content.
void CallGraphPass::wireNamedStore(NodeIndex val, NodeIndex cell,
                                   ArrayRef<uint32_t> names) {
  if (!namedPlanes() || names.empty() ||
      names[0] == ka::AccessNames::Unnamed) {
    addAssignmentEdge(val, cell);
    namedStats.unnamedStores++;
    return;
  }
  namedFiling++;
  addAssignmentEdge(val, cell);
  namedFiling--;
  for (uint32_t name : names)
    fileNamedWrite(getCanonicalNode(val), cell, name);
  namedStats.namedStores++;
}

void CallGraphPass::wireNamedLoad(NodeIndex cell, NodeIndex val,
                                  ArrayRef<uint32_t> names) {
  if (!namedPlanes() || names.empty() ||
      names[0] == ka::AccessNames::Unnamed) {
    addAssignmentEdge(cell, val);
    namedStats.unnamedLoads++;
    return;
  }
  addAssignmentEdge(namedShadow(cell, ka::AccessNames::Identity), val);
  for (uint32_t name : names) {
    readNames.insert(name);
    addAssignmentEdge(namedShadow(cell, name), val);
    // A certified name skips the unnamed shadow until it is opened
    // (ensureUnnamedShadows adds the read then).
    if (namedCertifies() && !openNames.count(name))
      certifiedReads.emplace_back(cell, val, name);
    else
      addAssignmentEdge(namedShadow(cell, ka::AccessNames::Unnamed), val);
  }
  namedLoadCells[val] = cell;
  namedStats.namedLoads++;
}

// Planes are created on demand (plan 3.7 item 1): a name's shadow only
// once some load reads that name — until then its writes wait here; the
// unnamed shadow only where an unnamed write lands or an uncertified
// load reads; the identity shadow only at named loads (roots minted on
// other cells reach it through their class, FlowsToSolver.cc).
void CallGraphPass::fileNamedWrite(NodeIndex s, NodeIndex cell,
                                   uint32_t name) {
  if (readNames.count(name))
    Graph.addCopy(s, namedShadow(cell, name));
  else
    pendingNamedWrites.emplace_back(s, cell, name);
}

void CallGraphPass::ensureUnnamedShadows() {
  if (!namedPlanes())
    return;
  // Writes under names a load now reads get their shadows.
  size_t keptW = 0;
  for (auto &w : pendingNamedWrites) {
    const auto [s, cell, name] = w;
    if (readNames.count(name))
      Graph.addCopy(s, namedShadow(cell, name));
    else
      pendingNamedWrites[keptW++] = w;
  }
  pendingNamedWrites.resize(keptW);
  // Loads of names opened since they were wired now read the unnamed
  // shadow too (monotone: a name never closes again).
  size_t kept = 0;
  for (auto &r : certifiedReads) {
    const auto [cell, val, name] = r;
    if (openNames.count(name))
      addAssignmentEdge(namedShadow(cell, ka::AccessNames::Unnamed), val);
    else
      certifiedReads[kept++] = r;
  }
  certifiedReads.resize(kept);
}

void CallGraphPass::logNamedCells() const {
  if (!namedPlanes())
    return;
  CG_LOG("NamedCells: " << accessNames->size() - ka::AccessNames::FirstName
         << " names; "
         << namedStats.namedStores << " named / "
         << namedStats.unnamedStores << " unnamed stores, "
         << namedStats.namedLoads << " named / " << namedStats.unnamedLoads
         << " unnamed loads, " << namedStats.namedSlots << " named / "
         << namedStats.unnamedSlots << " unnamed initializer slots, "
         << namedStats.unnamedWrites << " other cell writes ("
         << namedStats.pointerVarWrites << " into pointer variables kept out of "
         << "the unnamed plane), "
         << namedStats.cellCopies << " cell-to-cell copies; "
         << namedStats.shadows << " shadow cells\n");
  std::string why;
  for (unsigned w = 0; w < ka::AccessNames::NumWhy; w++)
    why += std::string(" ") +
           ka::AccessNames::whyName((ka::AccessNames::Why)w) + "=" +
           std::to_string(accessNames->unnamedBy[w]);
  CG_LOG("NamedCells: unnamed accesses by reason:" << why << "; "
         << accessNames->namedByTBAA << " named by their TBAA tag\n");
  CG_LOG("NamedCells: " << namedStats.typedWrites
         << " unnamed writes filed by their writer's field; certificate ("
         << CFLNamedUntyped << "): " << openNames.size() << "/"
         << accessNames->size() - ka::AccessNames::FirstName
         << " names open, "
         << certifiedReads.size()
         << " loads skip the unnamed plane; blind spot: " << blindWrites
         << " untyped writes into cells\n");
  if (VerboseLevel >= 3) // who opened each name (first culprit)
    for (auto &[n, why] : openWhy)
      CG_LOG("NamedCells:   open " << accessNames->str(n) << " by " << why
             << "\n");
  std::vector<std::pair<uint64_t, std::string>> top;
  for (auto &[w, c] : blindBy)
    top.emplace_back(c, w);
  std::sort(top.rbegin(), top.rend());
  for (size_t i = 0; i < top.size() && i < 10; i++)
    CG_LOG("NamedCells:   blind " << top[i].first << " " << top[i].second
           << "\n");
}

// ---- Field-sensitive memory modeling helpers (--cfl-field-buckets > 0) ----

// Provenance for anonymous minted nodes (field pointers, FRESHSUB
// sub-objects): creation context by NF node index, consulted where
// getValueForNode comes back null. Best-effort instrument.
boost::unordered_flat_map<NodeIndex, std::string> g_opaqueProvenance;

int CallGraphPass::fieldBucket(int64_t off) const {
  const unsigned K = Graph.numFieldBuckets();
  assert(K > 0 && "fieldBucket called without field labels");
  // Modular residue, NOT a hash: bucket sums must track offset sums so the
  // shift-indexed grammar can compose nested steps against flat ones
  // ((a+b) mod K == (a mod K + b mod K) mod K). Signed-safe for
  // container_of-style negative offsets. Prefer prime K: typical offsets
  // are 8-aligned, and a prime modulus keeps them from collapsing onto a
  // couple of residues.
  int64_t r = off % (int64_t)K;
  return (int)(r < 0 ? r + (int64_t)K : r);
}

uint32_t CallGraphPass::lazyLabelFor(int64_t off, uint32_t stride, bool arith,
                                     const StructType *ty, uint32_t extent) {
  if (lazyLabels.empty()) {
    lazyLabels.push_back({0, 0, false, nullptr, 0});
    lazyLabelIdx[{0, 0, false, nullptr, 0}] = 0;
  }
  if (stride == 0) extent = 0; // an extent only qualifies a strided step
  auto [it, ins] = lazyLabelIdx.emplace(std::make_tuple(off, stride, arith, ty, extent),
                                        (uint32_t)lazyLabels.size());
  if (ins) lazyLabels.push_back({off, stride, arith, ty, extent});
  return it->second;
}

void CallGraphPass::addFieldEdgesExact(NodeIndex src, NodeIndex dst,
                                       int64_t off, uint32_t stride, bool arith,
                                       const StructType *ty, uint32_t extent) {
  Graph.addField(src, dst, fieldBucket(off));
  if (!CFLLazyAddress) return;
  // Recorded per edge (not per endpoint pair): canonical merging can
  // fold two field nodes into one destination, and each edge keeps its
  // own exact label.
  lazyFEdges.emplace_back(src, dst, lazyLabelFor(off, stride, arith, ty, extent));
}

NodeIndex CallGraphPass::getFieldPtrNode(NodeIndex parentCanon, int64_t off) {
  auto key = std::make_pair(parentCanon, off);
  auto it = fieldPtrNodes.find(key);
  if (it != fieldPtrNodes.end())
    return it->second;
  NodeIndex n = NF.createValueNode();
  fieldPtrNodes.emplace(key, n);
  fieldPtrOrigin.emplace(n, std::make_pair(parentCanon, off));
  {
    const Value *pv = NF.getValueForNode(parentCanon);
    std::string pn = "#" + std::to_string(parentCanon);
    if (pv && pv->hasName())
      pn = pv->getName().str();
    else if (pv) {
      if (const auto *pi = dyn_cast<Instruction>(pv))
        pn = (pi->getFunction()->getName() + "::" + pi->getOpcodeName())
                 .str();
      else if (const auto *pa = dyn_cast<Argument>(pv))
        pn = (pa->getParent()->getName() + "::arg" + Twine(pa->getArgNo()))
                 .str();
    }
    g_opaqueProvenance[n] = "fieldptr:" + pn + "+" + std::to_string(off);
  }
  CG_DEBUG("Create field ptr node " << n << " for (" << parentCanon
           << ", +" << off << ")\n");
  return n;
}

// Decompose a GEP into per-struct-level byte offsets:
//   - struct index steps contribute their in-struct byte offset (0 skipped:
//     field 0 shares the parent's address)
//   - array/vector index steps are skipped (arrays are collapsed, matching
//     the Andersen-side model in offsetToFieldNum)
//   - a first index over a struct/array source strides whole objects, which
//     preserves field structure under collapse, so it is skipped too
//   - a nonzero or variable first index over a scalar source (i8-style byte
//     arithmetic) has no recoverable field structure -> caller must use the
//     wildcard fallback
bool CallGraphPass::decomposeGEPLevels(const GEPOperator *GEP,
                                       const DataLayout &DL,
                                       SmallVectorImpl<int64_t> &levels,
                                       SmallVectorImpl<const StructType *> *types) const {
  levels.clear();
  if (types) types->clear();
  bool first = true;
  // The aggregate the current index steps inside (null at the pointer
  // level): a variable index over an array of known length is bounded
  // by that length.
  Type *container = nullptr;
  for (auto GTI = gep_type_begin(GEP), E = gep_type_end(GEP); GTI != E; ++GTI) {
    const Value *idx = GTI.getOperand();
    Type *containerHere = container;
    container = GTI.getIndexedType();
    if (StructType *STy = GTI.getStructTypeOrNull()) {
      const auto *CI = dyn_cast<ConstantInt>(idx);
      if (!CI)
        return false; // malformed; be conservative
      const StructLayout *SL = DL.getStructLayout(STy);
      int64_t off = (int64_t)SL->getElementOffset(CI->getZExtValue());
      if (off != 0) {
        levels.push_back(off);
        if (types) types->push_back(STy);
      }
    } else if (CFLLazyAddress) {
      // Exact addresses: a constant array index is an exact element
      // offset (element k is distinct from element 0); one variable index
      // over an element of size > 1 is a strided step; byte arithmetic
      // (element size 1) is the range wildcard.
      Type *Ty = GTI.getIndexedType();
      const uint64_t esz = DL.getTypeAllocSize(Ty);
      if (const auto *CI = dyn_cast<ConstantInt>(idx)) {
        int64_t off = CI->getSExtValue() * (int64_t)esz;
        if (off > 0 && off < ((int64_t)1 << 40)) {
          levels.push_back(off | kArithLevelTag); // element step: walk candidate
          if (types) types->push_back(nullptr);
        } else if (off != 0) {
          levels.push_back(off);
          if (types) types->push_back(nullptr);
        }
      } else {
        if (esz <= 1 || esz > 0x3fffffffULL)
          return false; // wildcard fallback
        // Low 32 bits: element count of the array being indexed (0 =
        // unbounded: pointer-level index, scalable vector, unknown).
        uint64_t count = 0;
        if (const auto *AT = dyn_cast_or_null<ArrayType>(containerHere))
          count = AT->getNumElements();
        else if (const auto *VT = dyn_cast_or_null<FixedVectorType>(containerHere))
          count = VT->getNumElements();
        if (count > 0xffffffffULL || count * esz > 0xffffffffULL) count = 0;
        levels.push_back(kStridedLevelTag | ((int64_t)esz << 32) | (int64_t)count);
        if (types) types->push_back(nullptr);
      }
    } else if (first) {
      Type *Ty = GTI.getIndexedType();
      if (!Ty->isStructTy() && !Ty->isArrayTy() && !Ty->isVectorTy()) {
        const auto *CI = dyn_cast<ConstantInt>(idx);
        if (!CI)
          return false; // variable scalar arithmetic -> wildcard fallback
        // Constant scalar-typed offsets are known field steps, including
        // the two container_of shapes: raw negative offsets and the
        // -O1-folded positive byte offsets from mid-object pointers.
        int64_t off =
            CI->getSExtValue() * (int64_t)DL.getTypeAllocSize(Ty);
        if (off != 0) {
          levels.push_back(off);
          if (types) types->push_back(nullptr);
        }
      }
    }
    first = false;
  }
  return true;
}

void CallGraphPass::addFieldChainEdges(NodeIndex baseNode, NodeIndex resultNode,
                                       ArrayRef<int64_t> levels,
                                       ArrayRef<const StructType *> types) {
  assert(!levels.empty() && "addFieldChainEdges requires at least one level");
  NodeIndex cur = getCanonicalNode(baseNode);
  for (size_t k = 0; k < levels.size(); k++) {
    const bool last = (k + 1 == levels.size());
    NodeIndex next = last ? getCanonicalNode(resultNode)
                          : getFieldPtrNode(cur, levels[k]);
    if (next == cur)
      continue;
    if (levels[k] > 0 && (levels[k] & kStridedLevelTag)) { // strided step (negative = container_of offset)
      const uint32_t stride = (uint32_t)((levels[k] >> 32) & 0x3fffffff);
      const uint32_t count = (uint32_t)(levels[k] & 0xffffffff);
      addFieldEdgesExact(cur, next, 0, stride, false, nullptr, count * stride);
    }
    else if (levels[k] > 0 && (levels[k] & kArithLevelTag))
      addFieldEdgesExact(cur, next, levels[k] & ~kArithLevelTag, 0, true);
    else
      addFieldEdgesExact(cur, next, levels[k], 0, false,
                         k < types.size() ? types[k] : nullptr);
    cur = next;
  }
}

void CallGraphPass::addFieldWildcardLoop(NodeIndex n, const char *why) {
  if (n == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex canon = getCanonicalNode(n);
  if (moduleFieldWildcardRoots.insert(canon).second) {
    Graph.addFieldAnyLoop(canon);
    wildcardReasons[why]++;
  }
}

void CallGraphPass::applyFieldFallback(NodeIndex baseNode, NodeIndex resultNode,
                                       const char *why) {
  addAssignmentEdge(baseNode, resultNode);
  addFieldWildcardLoop(baseNode, why);
}

void CallGraphPass::mergeCanonicalClasses(NodeIndex a, NodeIndex b) {
  // merging anything with the universal class would conflate the
  // unknown-extern hub with a real object — catastrophic and silent;
  // refuse loudly (no silent fallback)
  assert(a != NF.getUniversalPtrNode() && b != NF.getUniversalPtrNode() &&
         a != NF.getUniversalObjNode() && b != NF.getUniversalObjNode() &&
         "attempt to canonical-merge the universal class");
  a = getCanonicalNode(a);
  b = getCanonicalNode(b);
  if (a == b)
    return;
  if (b < a)
    std::swap(a, b); // smaller index as stable representative
  auto &membersA = canonicalClassMembers[a];
  if (membersA.empty())
    membersA.insert(a);
  auto itB = canonicalClassMembers.find(b);
  if (itB != canonicalClassMembers.end()) {
    for (NodeIndex m : itB->second) {
      canonicalNodeMap[m] = a;
      membersA.insert(m);
    }
    canonicalClassMembers.erase(b);
  }
  canonicalNodeMap[b] = a;
  membersA.insert(b);
}

// Answer-anchored flows-to resolution (ORCFL prototype). After the
// quotient (presolve merge collapses a-cycles so the copy graph is a DAG of
// classes), V restricted to function sources is pure forward propagation:
// functions have no incoming assignments. Facts are (origin root, net field
// shift) pairs mirroring the shift-indexed grammar: a-edges and M-joins
// preserve the shift, an f<r> edge adds r mod P, an fx wildcard absorbs to
// the unknown shift X. The M splice is a join rule: two cells alias when
// their parents share a fact exactly — same origin AND same shift (V), or
// either side at X (VX). container_of round trips need no special casing:
// down 8 then down 8 carries the same shift as flat down 16. Storage is
// rectangular (fact sets), never pairwise V.

// Tracepoint keyed channels (task #35). One registration family, four
// entry points; the census (km + kernel, 2026-08-02) classifies 100%
// of their callsites as CONST-key or one of the two struct-mediated
// registrars, and 100% of __traceiter_* bodies name their key.
static bool isTracepointRegFn(StringRef n) {
  return n == "tracepoint_probe_register" ||
         n == "tracepoint_probe_register_prio" ||
         n == "tracepoint_probe_register_prio_may_exist" ||
         n == "tracepoint_probe_unregister";
}
// Keys bound by the initializer walker — mediator callsites pool their
// dynamic data argument (trace_event_file, bpf_prog) into every
// walker-bound key's data cell (data was globally pooled before this
// model too; only the fn plane is keyed).
std::vector<const GlobalVariable *> g_tpWalkerKeys;
// v3 (task #35): ANSWER-LEVEL primitive. The graph cannot carry per-key
// fn channels at kernel scale: probe VALUE classes are V-merged into
// the giant (fn identity is a casualty of the quotient — TRACE-BWD
// showed __traceiter operands AND probe classes both inside one merged
// mega-class), so any graph channel imports the pool at the source.
// The census-complete registration table IS the answer for __traceiter
// sites; the resolution loop takes targets from here (the #14
// static_call precedent) and its normal arg wiring feeds the probes.
boost::unordered_flat_map<NodeIndex, FuncSet> g_tpKeyProbes;
boost::unordered_flat_map<const llvm::CallBase *, NodeIndex>
    g_tpIterIcallKey;
std::vector<SctPending> g_sctPendings;
boost::unordered_flat_map<std::string, FuncSet> g_sctKeyTable;
boost::unordered_flat_set<std::string> g_sctKeyUntabled;
size_t g_sctUpdConst = 0, g_sctUpdLoad = 0, g_sctUpdNonconform = 0,
              g_sctTablesScanned = 0, g_sctPendingNoTable = 0,
              g_sctSitesModelAnswered = 0, g_sctSitesUntabled = 0,
              g_sctTypeRej = 0;
StringRef sctCanonStructName(StringRef n) {
  // "struct.kvm_x86_ops.123" -> "struct.kvm_x86_ops" (per-TU suffixes)
  size_t dot = n.rfind('.');
  if (dot != StringRef::npos && dot + 1 < n.size() &&
      isdigit(static_cast<unsigned char>(n[dot + 1])))
    return n.substr(0, dot);
  return n;
}

// The dispatch key of a __traceiter_* body: the base of the constexpr
// GEP its funcs-head load reads from. Memoized; single-threaded visit.
static const GlobalVariable *traceiterKeyOf(const Function *F) {
  static boost::unordered_flat_map<const Function *, const GlobalVariable *>
      memo;
  auto it = memo.find(F);
  if (it != memo.end())
    return it->second;
  const GlobalVariable *key = nullptr;
  for (const Instruction &I : instructions(*F)) {
    const auto *LI = dyn_cast<LoadInst>(&I);
    if (!LI)
      continue;
    const Value *P = LI->getPointerOperand();
    if (const auto *CE = dyn_cast<ConstantExpr>(P))
      if (CE->getOpcode() == Instruction::GetElementPtr)
        P = CE->getOperand(0);
    if (const auto *GV = dyn_cast<GlobalVariable>(P->stripPointerCasts()))
      if (GV->getName().starts_with("__tracepoint_")) {
        key = GV;
        break;
      }
  }
  memo[F] = key;
  return key;
}

bool g_sinkContractChecked = false;
// task #34 re-key v3: OPAQUE-ARENA model. Two join-time seal re-keys
// were falsified at km before this: (v1) sealing cellsOf[class] of the
// confirmer's anchor values over-reached 24x (-59,737 vs name-keyed
// -2,442; presolve copy chains merge payload pointers into
// generic-pointer classes, sweeping foreign deref sites at
// irq/bpf/clocksource); (v2) sealing only each anchor's own deref node
// under-reached to -0/+0 (673 anchors collapse to 3 presolve cell
// classes; the giant-join glue forms at the rb-page OBJECT cells
// reached through OTHER pointers, so facts flow around the boundary
// cells). The object-keyed scope the name patterns approximated is
// instead obtained STRUCTURALLY: each payload accessor's callsites
// return a pointer to one shared opaque arena object (per accessor),
// replacing the ret binding into ring-buffer internals. Payload
// write->read flow is PRESERVED (sounder than the seal, which cut it);
// only the false unification of payload cells with kernel-object cells
// never forms. No join-time check, no name patterns on minted objects.
bool isSinkPayloadAccessor(StringRef n) {
  return n == "ring_buffer_event_data" || n == "perf_trace_buf_alloc";
}
size_t g_sinkArenaSites = 0;
static NodeIndex g_sinkArenaObj[2] = {AndersNodeFactory::InvalidIndex,
                                      AndersNodeFactory::InvalidIndex};


// User ingress (task #32): user bytes reach kernel memory through two
// uaccess shapes, which --cfl-cert-usercopy tags.
//   (1) bulk copies (_copy_from_user et al.): the body's rep-movsb
//       `~{memory}`-clobber asm is the SOLE source of pointer-memory
//       edges (task #23 raw-ptr closure aliases *dest<->*src and stores
//       the pointer inputs into those cells). Gated by the enclosing
//       primitive name so egress (copy_to_user) and the direction-
//       agnostic shared movsb helpers are left intact.
//   (2) scalar reads (get_user): the value materializes at the CALLER's
//       `call __get_user_N` asm as a register output loaded through the
//       user pointer (the result aggregate can be ptr-typed). The
//       enclosing fn is arbitrary, so this shape is gated by the asm
//       text mentioning __get_user ("__put_user"/egress won't match).
static bool isUserCopyFromFn(llvm::StringRef n) {
  return n == "copy_from_user" || n == "_copy_from_user" ||
         n == "__copy_from_user" || n == "__copy_from_user_inatomic" ||
         n == "copy_from_user_nofault" || n == "strncpy_from_user";
}

// --cfl-cert-usercopy (task #32): the positive-direction check. At the
// two ingress shapes above, mint a synthetic origin
// object U and assign it into the asm's raw-ptr memory cells — "user
// bytes" become a trackable root. After solve, any icall fptr class
// whose fact planes carry a U root is a stratum crossing to inventory
// (U is not a function, so it never adds a callee — but the extra
// roots can add cluster joins, so this config's ANSWERS are not
// pin-comparable).
std::vector<std::pair<NodeIndex, std::string>>
    g_userCertObjs; // (U object node, site label)
size_t g_userCertCopySites = 0, g_userCertGetSites = 0;

size_t g_tagRoundTrips = 0; // fs: ptrtoint wildcards suppressed
void CallGraphPass::ensureConstGEPFieldEdges(const ConstantExpr *CE) {
  const auto *GEP = dyn_cast<GEPOperator>(CE);
  if (!GEP)
    return;
  NodeIndex node = NF.getValueNodeFor(CE);
  if (node == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex canon = getCanonicalNode(node);
  if (!moduleConstGEPFieldDone.insert(canon).second)
    return;

  const Value *base = GEP->getPointerOperand()->stripPointerCasts();
  NodeIndex baseNode = getRepNodeForValue(base); // recurses into nested CEs
  if (baseNode == AndersNodeFactory::InvalidIndex)
    return;
  if (canon == getCanonicalNode(baseNode))
    return; // field-0 GEPs canonicalize to the base node itself

  if (!Graph.fieldSensitive() || !curDL) {
    // Field-insensitive: a non-zero-field constexpr GEP gets its own
    // node (NodeFactory gepMap) — without the grammar's plain
    // GetElementPtr edge (base -> result a) that node floats and every
    // store/load through gep(@G, field) is silently severed from the
    // global's cell (found by t_ops.c, task #30).
    addAssignmentEdge(baseNode, node);
    return;
  }

  SmallVector<int64_t, 4> levels;
  if (!decomposeGEPLevels(GEP, *curDL, levels)) {
    applyFieldFallback(baseNode, node, "constexpr-gep-variable");
    return;
  }
  if (levels.empty())
    addAssignmentEdge(baseNode, node);
  else
    addFieldChainEdges(baseNode, node, levels);
}

static bool mayBecomePointer(const llvm::Value *V, unsigned depth,
                             bool &declined);
void CallGraphPass::handleInlineAsm(CallBase &CS) {
  // Named cells: asm writes of unknown extent; a cell-to-cell flow here
  // moves values, not bytes in place.
  CellWriteSize asmWrite(*this, 0, 0, /*IsValue=*/true);
  auto *IA = cast<InlineAsm>(CS.getCalledOperand());
  auto Constraints = InlineAsm::ParseConstraints(IA->getConstraintString());
  CG_DEBUG("InlineAsm: processing \"" << IA->getAsmString()
           << "\" with " << Constraints.size() << " constraints\n");


  // Build constraint-to-arg and constraint-to-ret mappings.
  // hasArg() is true for inputs and indirect outputs (they consume a CallBase arg).
  // Non-indirect outputs produce part of the return aggregate.
  unsigned argIdx = 0, retIdx = 0;
  std::vector<int> cToArg(Constraints.size(), -1);
  std::vector<int> cToRet(Constraints.size(), -1);
  for (unsigned i = 0; i < Constraints.size(); i++) {
    auto &CI = Constraints[i];
    if (CI.Type == InlineAsm::isClobber
#if LLVM_VERSION_MAJOR >= 15
        || CI.Type == InlineAsm::isLabel
#endif
    )
      continue;
    if (CI.hasArg())
      cToArg[i] = argIdx++;
    if (CI.Type == InlineAsm::isOutput && !CI.isIndirect)
      cToRet[i] = retIdx++;
  }

  // 1. Tied constraints -> copy edges.
  // If output constraint i has MatchingInput == j, the output gets the same
  // value as the tied input. Only create edges for pointer-typed operands.
  for (unsigned i = 0; i < Constraints.size(); i++) {
    auto &CI = Constraints[i];
    if (CI.Type != InlineAsm::isOutput || CI.MatchingInput < 0)
      continue;
    unsigned tied = CI.MatchingInput;
    int srcArgIdx = cToArg[tied];
    if (srcArgIdx < 0 || (unsigned)srcArgIdx >= CS.arg_size())
      continue;
    Value *srcVal = CS.getArgOperand(srcArgIdx);
    if (!srcVal->getType()->isPointerTy())
      continue;

    NodeIndex srcNode = getRepNodeForValue(srcVal);
    if (srcNode == AndersNodeFactory::InvalidIndex)
      continue;

    NodeIndex dstNode;
    if (CI.isIndirect) {
      // Indirect output: asm writes to *arg, so the destination is the arg pointer
      int dstArgIdx = cToArg[i];
      if (dstArgIdx < 0)
        continue;
      dstNode = getRepNodeForValue(CS.getArgOperand(dstArgIdx));
    } else {
      // Register output: result flows to the CallBase instruction itself
      dstNode = getRepNodeForValue(&CS);
    }
    if (dstNode == AndersNodeFactory::InvalidIndex)
      continue;

    CG_DEBUG("InlineAsm: tied copy edge from arg " << srcArgIdx
             << " to " << (CI.isIndirect ? "indirect output" : "result") << "\n");
    addAssignmentEdge(srcNode, dstNode);
  }

  // 2. Indirect memory operands with pointer elementtype.
  // =*m (output, indirect): asm writes to *arg. Conservatively, any pointer-typed
  //   direct input could be stored there.
  // *m (input, indirect): asm reads from *arg. Loaded value could flow to
  //   pointer-typed outputs.
  for (unsigned i = 0; i < Constraints.size(); i++) {
    auto &CI = Constraints[i];
    if (!CI.isIndirect)
      continue;
    int aIdx = cToArg[i];
    if (aIdx < 0 || (unsigned)aIdx >= CS.arg_size())
      continue;

#if LLVM_VERSION_MAJOR >= 15
    Type *ET = CS.getParamElementType(aIdx);
#else
    Type *ET = CS.getArgOperand(aIdx)->getType()->isPointerTy()
      ? CS.getArgOperand(aIdx)->getType()->getPointerElementType()
      : nullptr;
#endif
    // ptr-typed slot, or a ptr-WIDTH int slot (asm atomics on i64 —
    // xchgq/lock cmpxchgq — launder fptrs exactly like the IR-level
    // _Atomic lowering; same witness discipline as visitLoad/StoreInst)
    bool ptrSlot = ET && containsPointerType(ET);
    bool widthSlot = !ptrSlot && ET && curDL &&
                     isPtrWidthInt(ET->getScalarType(), *curDL);
    if (!ptrSlot && !widthSlot)
      continue;

    NodeIndex ptrNode = getRepNodeForValue(CS.getArgOperand(aIdx));
    if (ptrNode == AndersNodeFactory::InvalidIndex)
      continue;
    NodeIndex derefNode = getRepDerefNode(ptrNode);

    if (CI.Type == InlineAsm::isOutput) {
      // store to *ptr — any ptr-typed direct input, or witnessed
      // ptr-width int input, could be what the asm stores
      for (unsigned j = 0; j < Constraints.size(); j++) {
        if (Constraints[j].Type != InlineAsm::isInput)
          continue;
        int sIdx = cToArg[j];
        if (sIdx < 0 || (unsigned)sIdx >= CS.arg_size())
          continue;
        Value *srcVal = CS.getArgOperand(sIdx);
        if (Constraints[j].isIndirect)
          continue;
        // laundered constants arrive as ptrtoint CEs whose i64 type
        // resolves to the shared ConstantInt node — unwrap to the
        // underlying pointer so the edge carries the real identity
        if (auto *PTI = dyn_cast<PtrToIntOperator>(srcVal))
          srcVal = PTI->getPointerOperand();
        bool ok = srcVal->getType()->isPointerTy();
        if (!ok && widthSlot && curDL &&
            isPtrWidthInt(srcVal->getType(), *curDL)) {
          bool declined = false;
          ok = mayCarryPtrProvenance(srcVal, 8, declined);
          if (ok) g_asmWidthWitnessed++;
          else if (declined) g_asmLaunderDeclined++;
        }
        if (!ok)
          continue;
        NodeIndex srcNode = getRepNodeForValue(srcVal);
        if (srcNode == AndersNodeFactory::InvalidIndex ||
            NF.isSpecialNode(srcNode))
          continue;
        CG_DEBUG("InlineAsm: indirect store edge from input arg " << sIdx
                 << " to deref of output arg " << aIdx << "\n");
        addAssignmentEdge(srcNode, derefNode);
        g_asmSlotStores++;
      }
    } else if (CI.Type == InlineAsm::isInput) {
      // load from *ptr — flows to the result if it is ptr-typed, or
      // ptr-width and witnessed to become a pointer downstream
      bool ok = CS.getType()->isPointerTy() ||
                containsPointerType(CS.getType());
      if (!ok && curDL && isPtrWidthInt(CS.getType(), *curDL)) {
        bool declined = false;
        ok = mayBecomePointer(&CS, 8, declined);
        if (ok) g_asmWidthWitnessed++;
        else if (declined) g_asmLaunderDeclined++;
      }
      if (ok) {
        NodeIndex dstNode = getRepNodeForValue(&CS);
        if (dstNode == AndersNodeFactory::InvalidIndex)
          dstNode = getCanonicalNode(NF.createValueNode(&CS)); // i64 result
        CG_DEBUG("InlineAsm: indirect load edge from deref of input arg "
                 << aIdx << " to result\n");
        addAssignmentEdge(derefNode, dstNode);
        g_asmSlotLoads++;
      }
    }
  }

  // 2b. Raw pointer register/address inputs ("p"/"r" constraints with
  // pointer-typed args): the asm may READ through them regardless of
  // clobbers (percpu this_cpu_read_stable), and WRITE through them
  // when it declares memory effects (memory clobber or any indirect
  // output) — rep movs/stos, uaccess bodies. Immediate-constraint
  // pointers (metadata symbols) are excluded like the census does.
  {
    bool memClobber = false, anyIndirectOut = false;
    for (auto &CI : Constraints) {
      if (CI.Type == InlineAsm::isClobber) {
        for (const std::string &Code : CI.Codes)
          if (StringRef(Code).contains("memory")) memClobber = true;
      } else if (CI.Type == InlineAsm::isOutput && CI.isIndirect) {
        anyIndirectOut = true;
      }
    }
    bool resPtrCapable = CS.getType()->isPointerTy() ||
                         containsPointerType(CS.getType());
    if (!resPtrCapable && !CS.getType()->isVoidTy() && curDL &&
        isPtrWidthInt(CS.getType(), *curDL)) {
      bool declined = false;
      resPtrCapable = mayBecomePointer(&CS, 8, declined);
      if (declined) g_asmLaunderDeclined++;
    }
    SmallVector<NodeIndex, 4> rawPtrDerefs;
    SmallVector<Value *, 4> valueInputs;
    for (unsigned i = 0; i < Constraints.size(); i++) {
      auto &CI = Constraints[i];
      if (CI.Type != InlineAsm::isInput || CI.isIndirect)
        continue;
      int aIdx = cToArg[i];
      if (aIdx < 0 || (unsigned)aIdx >= CS.arg_size())
        continue;
      Value *A = CS.getArgOperand(aIdx);
      valueInputs.push_back(A);
      if (!A->getType()->isPointerTy())
        continue;
      bool allImm = !CI.Codes.empty();
      for (const std::string &Code : CI.Codes)
        allImm &= (Code == "i" || Code == "s" || Code == "n" || Code == "X");
      if (allImm) {
        // %gs:/%fs:-addressed immediates ARE runtime accesses: x86
        // percpu codegen passes the percpu symbol as an "i" operand
        // and the asm reads %gs:sym (this_cpu_read — pcpu_hot's
        // current_task load = `current`). The segment rebase is
        // base-to-base relocation under the declared percpu
        // invariant, so *(sym) -> result is the exact model. Found
        // via the th3 (LLVM-14) corpus: 226 dropped current-loads
        // surfaced as IntToPtr src-node-not-found (2026-08-18).
        StringRef AsmStr(IA->getAsmString());
        if (!AsmStr.contains("%gs:") && !AsmStr.contains("%fs:"))
          continue; // true link-time symbol, no runtime access
      }
      NodeIndex pNode = getRepNodeForValue(A);
      if (pNode == AndersNodeFactory::InvalidIndex)
        continue;
      rawPtrDerefs.push_back(getRepDerefNode(pNode));
    }
    // MEASUREMENT-ONLY (task #32 usercopy certificate): tag the same
    // two ingress shapes with a synthetic origin object flowing into
    // the asm's memory cells — the solver then tracks "user bytes" as
    // a root and the resolution pass inventories which icall operands
    // they reach.
    if (CFLCertUserCopy && !rawPtrDerefs.empty()) {
      const bool copyBody =
          CS.getFunction() && isUserCopyFromFn(CS.getFunction()->getName());
      const bool getUser = StringRef(IA->getAsmString()).contains("__get_user");
      if (copyBody || getUser) {
        NodeIndex U = NF.createOpaqueObjectNode(&CS, true);
        for (NodeIndex derefP : rawPtrDerefs)
          addAssignmentEdge(U, derefP);
        if (copyBody)
          g_userCertCopySites++;
        else
          g_userCertGetSites++;
        g_userCertObjs.emplace_back(
            U, (CS.getFunction()->getName() +
                (copyBody ? "::copy-body" : "::get_user"))
                   .str());
      }
    }
    for (NodeIndex derefP : rawPtrDerefs) {
      if (resPtrCapable) {
        NodeIndex dstNode = getRepNodeForValue(&CS);
        if (dstNode == AndersNodeFactory::InvalidIndex)
          dstNode = getCanonicalNode(NF.createValueNode(&CS)); // i64 result
        addAssignmentEdge(derefP, dstNode);
        g_asmRegLoads++;
      }
      if (memClobber || anyIndirectOut) {
        for (Value *V : valueInputs) {
          if (auto *PTI = dyn_cast<PtrToIntOperator>(V))
            V = PTI->getPointerOperand();
          bool ok = V->getType()->isPointerTy();
          if (!ok && curDL && isPtrWidthInt(V->getType(), *curDL)) {
            bool declined = false;
            ok = mayCarryPtrProvenance(V, 8, declined);
            if (!ok && declined) g_asmLaunderDeclined++;
          }
          if (!ok)
            continue;
          NodeIndex srcNode = getRepNodeForValue(V);
          if (srcNode == AndersNodeFactory::InvalidIndex ||
              NF.isSpecialNode(srcNode))
            continue;
          addAssignmentEdge(srcNode, derefP);
          g_asmRegStores++;
        }
        for (NodeIndex derefQ : rawPtrDerefs)
          if (derefQ != derefP) {
            addAssignmentEdge(derefQ, derefP);
            g_asmRegCopies++;
          }
      }
    }
  }

  // 3. Call detection in asm text.
  // Match "call[q] <funcname>" patterns and look up targets in Ctx->Funcs.
  StringRef asmStr = IA->getAsmString();
  size_t pos = 0;
  while (pos < asmStr.size()) {
    // Find "call" keyword
    size_t callPos = asmStr.find("call", pos);
    if (callPos == StringRef::npos)
      break;

    // Skip the "call" keyword and optional suffix (callq, etc.)
    size_t cur = callPos + 4;
    while (cur < asmStr.size() && isalpha(asmStr[cur]))
      cur++;
    // Skip whitespace
    while (cur < asmStr.size() && (asmStr[cur] == ' ' || asmStr[cur] == '\t'))
      cur++;
    if (cur >= asmStr.size()) break;

    // Skip optional '*' (indirect call indicator) — we can't resolve those
    if (asmStr[cur] == '*' || asmStr[cur] == '%' || asmStr[cur] == '$') {
      pos = cur + 1;
      continue;
    }

    // Extract function name (alphanumeric + underscore + dot).
    // Also handle ${N:P} operand substitutions by stripping them — these are
    // LLVM asm operand placeholders (e.g., "call __put_user_${4:P}" where
    // ${4:P} expands to a size suffix like "1", "2", "4", "8").
    std::string funcName;
    size_t nameStart = cur;
    while (cur < asmStr.size()) {
      if (isalnum(asmStr[cur]) || asmStr[cur] == '_' || asmStr[cur] == '.') {
        funcName += asmStr[cur++];
      } else if (asmStr[cur] == '$' && cur + 1 < asmStr.size() && asmStr[cur + 1] == '{') {
        // Skip ${...} substitution
        size_t end = asmStr.find('}', cur + 2);
        if (end == StringRef::npos) break;
        cur = end + 1;
      } else {
        break;
      }
    }

    if (!funcName.empty()) {
      // Try the exact name first, then also try common size-suffixed variants
      // (e.g., __put_user_1, __put_user_2, __put_user_4, __put_user_8)
      bool found = false;
      uint64_t guid = GlobalValue::getGUID(funcName);
      auto it = Ctx->Funcs.find(guid);
      if (it != Ctx->Funcs.end()) {
        CG_LOG("InlineAsm: detected call to " << funcName << " in asm text\n");
        handleCall(&CS, it->second);
        found = true;
      } else {
        // Census the unresolved residue loudly: static_call trampolines
        // (__SCT__* — needs the __SCK__<name>.func icall model, task
        // pending) and targets defined only in .S assembly (no IR body,
        // e.g. __get_user_N) land here.
        WARNING("InlineAsm: embedded call target \"" << funcName
                << "\" has no IR definition (unmodeled) in "
                << CS.getFunction()->getName() << "\n");
      }
      // If the name ended with a ${...} substitution (stripped above),
      // try common numeric suffixes for size-parameterized kernel helpers.
      if (!found && cur > nameStart &&
          cur <= asmStr.size() && nameStart < cur) {
        for (const char *suffix : {"1", "2", "4", "8"}) {
          std::string variant = funcName + suffix;
          guid = GlobalValue::getGUID(variant);
          it = Ctx->Funcs.find(guid);
          if (it != Ctx->Funcs.end()) {
            CG_LOG("InlineAsm: detected call to " << variant << " in asm text\n");
            handleCall(&CS, it->second);
          }
        }
      }
    }
    pos = cur;
  }
}

bool CallGraphPass::isSummarizableAlloca(const AllocaInst *AI) const {
  if (!AI || !AI->getAllocatedType()->isPointerTy())
    return false;

  std::vector<const Value *> worklist;
  std::unordered_set<const Value *> seen;
  worklist.push_back(AI);
  seen.insert(AI);

  while (!worklist.empty()) {
    const Value *cur = worklist.back();
    worklist.pop_back();

    for (const User *U : cur->users()) {
      const Instruction *I = dyn_cast<Instruction>(U);
      if (I && I->getFunction() != AI->getFunction())
        return false;

      if (const auto *BC = dyn_cast<BitCastInst>(U)) {
        if (BC->getOperand(0) != cur)
          return false;
        if (seen.insert(BC).second)
          worklist.push_back(BC);
        continue;
      }

      if (const auto *ASC = dyn_cast<AddrSpaceCastInst>(U)) {
        if (ASC->getOperand(0) != cur)
          return false;
        if (seen.insert(ASC).second)
          worklist.push_back(ASC);
        continue;
      }

      if (const auto *GEP = dyn_cast<GetElementPtrInst>(U)) {
        if (GEP->getPointerOperand() != cur || !isZeroOffsetGEP(GEP))
          return false;
        if (seen.insert(GEP).second)
          worklist.push_back(GEP);
        continue;
      }

      if (const auto *LI = dyn_cast<LoadInst>(U)) {
        if (LI->getPointerOperand() != cur)
          return false;
        if (LI->isVolatile() || !LI->getType()->isPointerTy())
          return false;
        continue;
      }

      if (const auto *SI = dyn_cast<StoreInst>(U)) {
        if (SI->getPointerOperand() == cur) {
          if (SI->isVolatile())
            return false;
          const Value *stored = SI->getValueOperand();
          if (!stored->getType()->isPointerTy() && !shouldSkipValue(stored))
            return false;
          continue;
        }
        if (SI->getValueOperand() == cur)
          return false; // alloca address escapes
        return false;
      }

      if (const auto *CB = dyn_cast<CallBase>(U)) {
        if (isIgnorableAllocaIntrinsic(CB))
          continue;
        return false;
      }

      // Any other use is conservatively treated as escape/unmodeled behavior.
      return false;
    }
  }

  return true;
}

void CallGraphPass::collectLocalAllocaSummaries(const Function *F) {
  localSummarizedAllocaSlots.clear();
  localAllocaStoreVals.clear();
  localAllocaLoadVals.clear();

  if (!F)
    return;

  for (const Instruction &I : instructions(F)) {
    const auto *AI = dyn_cast<AllocaInst>(&I);
    if (!AI || !isSummarizableAlloca(AI))
      continue;
    NodeIndex slotRep = getRepNodeForValue(AI);
    if (slotRep == AndersNodeFactory::InvalidIndex)
      continue;
    localSummarizedAllocaSlots.insert(slotRep);
  }

  if (!localSummarizedAllocaSlots.empty()) {
    CG_DEBUG("Local alloca summaries in " << F->getName() << ": "
             << localSummarizedAllocaSlots.size() << "\n");
  }
}

bool CallGraphPass::resolveSummarizedAllocaSlot(const Value *Ptr, NodeIndex &slotRep) {
  slotRep = AndersNodeFactory::InvalidIndex;
  if (localSummarizedAllocaSlots.empty() || !Ptr)
    return false;

  const Value *base = stripAllocaAliasBase(Ptr);
  if (!isa<AllocaInst>(base))
    return false;

  NodeIndex node = getRepNodeForValue(base);
  if (node == AndersNodeFactory::InvalidIndex)
    return false;

  if (!localSummarizedAllocaSlots.count(node))
    return false;

  slotRep = node;
  return true;
}

void CallGraphPass::emitLocalAllocaSummaryEdges() {
  for (NodeIndex slot : localSummarizedAllocaSlots) {
    auto storesIt = localAllocaStoreVals.find(slot);
    auto loadsIt = localAllocaLoadVals.find(slot);
    if (storesIt == localAllocaStoreVals.end() || loadsIt == localAllocaLoadVals.end())
      continue;

    const auto &stores = storesIt->second;
    const auto &loads = loadsIt->second;
    if (stores.empty() || loads.empty())
      continue;

    std::unordered_set<NodeIndex> uniqueStores(stores.begin(), stores.end());
    std::unordered_set<NodeIndex> uniqueLoads(loads.begin(), loads.end());

    for (NodeIndex s : uniqueStores) {
      for (NodeIndex l : uniqueLoads)
        addAssignmentEdge(s, l);
    }
  }
}

bool CallGraphPass::runOnFunction(Function *F) {

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

  // --cfl-ablate-funcs: MEASUREMENT-ONLY UNSOUND PROBE. Skip body-edge
  // emission for the named functions (exact name, or name up to a '.'
  // uniquification suffix) to attribute hub-class gluing causally
  // (conflation report). The function stays a call target — callers
  // still wire actuals to its formals — but its body contributes no
  // flows, exactly "treat as opaque". Never use for real analysis.
  if (!CFLAblateFuncs.empty()) {
    static size_t g_ablated = 0;
    StringRef fname = F->getName();
    StringRef base = fname.take_front(fname.find('.'));
    StringRef spec(CFLAblateFuncs);
    while (!spec.empty()) {
      auto [head, rest] = spec.split(',');
      if (!head.empty() && (fname == head || base == head)) {
        WARNING("[MEASUREMENT-ONLY UNSOUND] ablating body of "
                << fname << " (" << ++g_ablated << " ablations)\n");
        return false;
      }
      spec = rest;
    }
  }

  // Per-instruction node creation is idempotent (already done in doInitialization
  // when CFLGlobalDedup is active), but we still need it for the non-dedup path.
  for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
    const Instruction *I = &*itr;
    if (containsPointerType(I->getType())) {
      NF.createValueNode(I);
    }
    if (const ReturnInst *RI = dyn_cast<ReturnInst>(I))
      Ctx->RetSites[F] = RI;

    if (const CallBase *CB = dyn_cast<CallBase>(I)) {
      if (const Function *CF = CB->getCalledFunction()) {
        if (Ctx->AllocFuncs.count(CF))
          Ctx->AllocSites.insert(CB);
      }
    }
  }

  bool allocaSummaryActive = CFLLocalAllocaSummary;
  if (allocaSummaryActive) {
    collectLocalAllocaSummaries(F);
  }

  // Use InstVisitor to handle instructions.
  InstHandler visitor(*this, F);
  visitor.visit(F);

  if (allocaSummaryActive) {
    emitLocalAllocaSummaryEdges();
  }
  // Clear alloca tracking structures
  localSummarizedAllocaSlots.clear();
  localAllocaStoreVals.clear();
  localAllocaLoadVals.clear();

  return false;
}

// Implementation of InstHandler visitor methods
void CallGraphPass::InstHandler::visitReturnInst(ReturnInst &I) {
  if (I.getNumOperands() > 0) {
    Value *rv = I.getOperand(0);
    bool intProv = false;
    if (!containsPointerType(rv->getType())) {
      // Pointer-width integer returns can carry laundered pointer
      // provenance — THE kernel idiom is __fdget/__fdget_pos returning
      // the struct-file pointer with FDPUT flags in the low bits of an
      // i64 (5.18 GT: every fd-based file access crosses this return,
      // so the whole file->f_op dispatch chain was severed and only
      // pool smear answered at f_op sites; vfs_llseek's clean phi
      // exposed it). Wire the return when the value may carry
      // provenance; consumers get facts only if real pointer facts
      // flow, so the added edges are inert for plain integers.
      bool dropped = false;
      if (!(CGP.curDL && isPtrWidthInt(rv->getType(), *CGP.curDL)) ||
          !mayCarryPtrProvenance(rv, 8, dropped)) {
        if (dropped)
          g_intStoreUnmodeled++;
        return;
      }
      intProv = true;
    }

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(rv)) {
      CG_DEBUG("Skipping return value: " << *rv << "\n");
      return;
    }

    NodeIndex rvNode = CGP.getRepNodeForValue(rv);
    if (intProv && rvNode == AndersNodeFactory::InvalidIndex)
      return; // provenance-int with no node: nothing to carry
    assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
    NodeIndex RT = CGP.NF.getReturnNodeFor(F);
    if (RT == AndersNodeFactory::InvalidIndex) {
      // int-returning functions have no pre-created return node
      RT = CGP.NF.createReturnNode(F);
    }
    CGP.addAssignmentEdge(rvNode, RT);
  }
}

void CallGraphPass::InstHandler::visitCallBase(CallBase &CS) {
  if (CS.isInlineAsm()) {
    CGP.handleInlineAsm(CS);
    return;
  }
  if (CGP.Ctx->AllocSites.count(&CS)) {
    // record allocation sites and create heap object node
    NodeIndex valNode = CGP.getRepNodeForValue(&CS);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      // Allocator returns non-pointer type (e.g. unsigned long for
      // __get_free_pages); create a value node on demand.
      valNode = CGP.NF.createValueNode(&CS);
      valNode = CGP.getCanonicalNode(valNode);
    }
    CGP.AllocSites.insert(valNode);
    NodeIndex heapObj = CGP.NF.createOpaqueObjectNode(&CS, true);
    CGP.Graph.addDeref(valNode, heapObj);
    // Keep allocator return-node flow active for compositional promotion:
    // known allocator return symbols must stay reachable even when alloc
    // callsites are short-circuited as explicit AllocSites.
    if (Function *CF = CS.getCalledFunction()) {
      // Record call edge so allocator calls appear in the callgraph export.
      auto RCF = CGP.getFuncDef(CF);
      CGP.Ctx->Callees[&CS].insert(RCF);
      auto sit = CGP.Ctx->FuncSummaries.find(RCF);
      if (sit == CGP.Ctx->FuncSummaries.end())
        sit = CGP.Ctx->FuncSummaries.find(CF);
      if (sit != CGP.Ctx->FuncSummaries.end()) {
        // Summarized allocator: the callsite's identity IS the fresh
        // object; the shared return-node edge is exactly the measured
        // cross-caller conflation channel (~470 witnessed joins at km)
        // — suppress it, then apply the remaining atoms (CPY for the
        // dup family restores the copy the skipped body drops).
        if (CGP.applySummaryAtoms(&CS, *sit->second, nullptr, sit->first))
          CGP.wireCallArgs(&CS, RCF); // dynamic-fn INVOKE: feed the body pool
      } else if (CF->getReturnType()->isPointerTy()) {
        NodeIndex retNode = CGP.NF.getReturnNodeFor(RCF);
        if (retNode == AndersNodeFactory::InvalidIndex)
          retNode = CGP.NF.createReturnNode(RCF);
        retNode = CGP.getCanonicalNode(retNode);
        CGP.addAssignmentEdge(retNode, valNode);
      }
    }
    CG_DEBUG("Create heap obj node " << heapObj << " for " << CS << "\n");
    return; // skip allocation sites
  }

  // --cfl-sink-instr (task #34 v3): OPAQUE-ARENA model at the payload
  // accessor boundary. The accessor's return is bound to ONE shared
  // opaque object per accessor (NOT per callsite — write-side and
  // read-side callsites must share the origin so payload write->read
  // flow through the arena cells is preserved), replacing the ret
  // binding into ring-buffer internals. Args still feed the real body
  // (out-params, side effects). Gated on the read-back contract
  // confirmer, which runs before any instruction visiting.
  if (CFLSinkInstr) {
    const Function *AF = dyn_cast<Function>(
        CS.getCalledOperand()->stripPointerCasts());
    if (AF && isSinkPayloadAccessor(AF->getName())) {
      assert(g_sinkContractChecked &&
             "arena planting reached before the contract check");
      NodeIndex valNode = CGP.getRepNodeForValue(&CS);
      if (valNode == AndersNodeFactory::InvalidIndex)
        valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&CS));
      NodeIndex &arena =
          g_sinkArenaObj[AF->getName() == "perf_trace_buf_alloc"];
      if (arena == AndersNodeFactory::InvalidIndex)
        arena = CGP.NF.createOpaqueObjectNode(&CS, true);
      CGP.Graph.addDeref(valNode, arena);
      Function *RCF = CGP.getFuncDef(const_cast<Function *>(AF));
      CGP.Ctx->Callees[&CS].insert(RCF);
      CGP.wireCallArgs(&CS, RCF);
      g_sinkArenaSites++;
      return; // the arena IS the return identity; skip normal ret binding
    }
  }

  // Check for function pointer cycles
  if (!CS.getCalledFunction()) {
    Value *CO = CS.getCalledOperand()->stripPointerCastsAndAliases();
    if (auto *Load = dyn_cast<LoadInst>(CO)) {
      CG_DEBUG("Indirect call through loaded function pointer: " << *Load->getPointerOperand() << "\n");
    }
  }

  // static_call updater as a MODELED PRIMITIVE (task #14): letting the
  // generic actual-to-formal wiring run on __static_call_update
  // conflates EVERY key through the shared 'key' parameter (k->func =
  // func on the param unions all keys' planes: km subset showed
  // __SCT__cond_resched "resolving" to alloc_insn_page). Per-callsite
  // wiring func -> deref(key-global) is exact and covers the body's
  // only pointer effect; non-global keys fall through to the generic
  // path + LEDGER.
  if (CFLStaticCall) {
    Function *UF = CS.getCalledFunction();
    if (UF && UF->getName() == "__static_call_update" &&
        CS.arg_size() >= 3) {
      Value *KeyV = CS.getArgOperand(0)->stripPointerCasts();
      if (auto *KeyG = dyn_cast<GlobalVariable>(KeyV)) {
        // Ops-table channel (task #36): record what this update binds.
        // Const fn -> direct table entry; load gep(%struct.X, base,
        // 0, N) -> pending (resolved against all %struct.X global
        // initializers at resolution); anything else UNTABLES the key.
        if (CFLStaticOpsTables) {
          std::string keyName = KeyG->getName().str();
          // Recursive fn-source classifier: const fn / null / ops-table
          // load, composed through select/phi (the OPTIONAL_RET0 macro
          // emits `load ?: __static_call_return0` as a select). EVERY
          // leaf must conform or the key is untabled.
          std::function<bool(const Value *, unsigned)> classify =
              [&](const Value *FV, unsigned depth) -> bool {
            if (depth > 4)
              return false;
            FV = FV->stripPointerCasts();
            if (const auto *TF = dyn_cast<Function>(FV)) {
              g_sctKeyTable[keyName].insert(
                  CGP.getFuncDef(const_cast<Function *>(TF)));
              g_sctUpdConst++;
              return true;
            }
            if (isa<ConstantPointerNull>(FV)) {
              g_sctKeyTable.try_emplace(keyName); // known key, no target
              return true;
            }
            if (const auto *LI2 = dyn_cast<LoadInst>(FV)) {
              const Value *PB =
                  LI2->getPointerOperand()->stripPointerCasts();
              // (a) base strips to a struct-typed GLOBAL (the singleton
              // pattern: @kvm_pmu_ops field 0 has NO gep, later fields
              // are canonical i8 byte-geps): map the constant byte
              // offset to a field via DataLayout.
              const Value *Base = PB;
              APInt Off(64, 0);
              bool constOff = true;
              if (const auto *GO0 = dyn_cast<GEPOperator>(PB)) {
                constOff =
                    CGP.curDL && GO0->accumulateConstantOffset(*CGP.curDL,
                                                               Off);
                Base = GO0->getPointerOperand()->stripPointerCasts();
              }
              if (const auto *BG = dyn_cast<GlobalVariable>(Base)) {
                const auto *BST =
                    dyn_cast<StructType>(BG->getValueType());
                if (constOff && BST && BST->hasName() && CGP.curDL) {
                  const StructLayout *SL = CGP.curDL->getStructLayout(
                      const_cast<StructType *>(BST));
                  uint64_t o = Off.getZExtValue();
                  if (o < SL->getSizeInBytes()) {
                    g_sctKeyTable.try_emplace(keyName);
                    g_sctPendings.push_back(
                        {keyName,
                         sctCanonStructName(BST->getName()).str(),
                         SL->getElementContainingOffset(o)});
                    g_sctUpdLoad++;
                    return true;
                  }
                }
                return false;
              }
              // (b) dynamic base: struct-typed gep with constant field
              // index (trace_event_reg / apic->f shape)
              const auto *GO = dyn_cast<GEPOperator>(PB);
              const StructType *ST2 =
                  GO ? dyn_cast<StructType>(GO->getSourceElementType())
                     : nullptr;
              const auto *Zero =
                  GO && GO->getNumIndices() == 2
                      ? dyn_cast<ConstantInt>(GO->getOperand(1))
                      : nullptr;
              const auto *FieldC =
                  Zero && Zero->isZero()
                      ? dyn_cast<ConstantInt>(GO->getOperand(2))
                      : nullptr;
              if (!ST2 || !ST2->hasName() || !FieldC)
                return false;
              g_sctKeyTable.try_emplace(keyName);
              g_sctPendings.push_back(
                  {keyName, sctCanonStructName(ST2->getName()).str(),
                   (unsigned)FieldC->getZExtValue()});
              g_sctUpdLoad++;
              return true;
            }
            if (const auto *SEL = dyn_cast<SelectInst>(FV)) {
              bool a = classify(SEL->getTrueValue(), depth + 1);
              bool b = classify(SEL->getFalseValue(), depth + 1);
              return a && b;
            }
            if (const auto *PHI2 = dyn_cast<PHINode>(FV)) {
              bool ok = true;
              for (const Value *IV : PHI2->incoming_values())
                ok &= classify(IV, depth + 1);
              return ok;
            }
            return false;
          };
          if (!classify(CS.getArgOperand(2), 0)) {
            g_sctKeyUntabled.insert(keyName);
            g_sctUpdNonconform++;
          }
        }
        NodeIndex keyNode = CGP.getRepNodeForValue(KeyG);
        NodeIndex funcNode =
            CGP.getRepNodeForValue(CS.getArgOperand(2)->stripPointerCasts());
        if (keyNode != AndersNodeFactory::InvalidIndex &&
            funcNode != AndersNodeFactory::InvalidIndex &&
            !CGP.NF.isSpecialNode(funcNode)) {
          CGP.addAssignmentEdge(
              funcNode, CGP.getRepDerefNode(CGP.getCanonicalNode(keyNode)));
          auto RUF = CGP.getFuncDef(UF);
          CGP.Ctx->Callees[&CS].insert(RUF); // keep the export edge
          g_staticCallUpdates++;
          return; // primitive modeled; skip generic arg wiring
        }
      }
      // dynamic key (tracepoint_update_call, bpf dispatcher): the
      // generic actual-to-formal wiring would conflate EVERY key
      // through the shared param — suppress it and LEDGER. The
      // tracepoint family (the dominant user) is covered exactly by
      // the tracepoint_probe_register primitive below; anything else
      // is an explicit, counted boundary assumption.
      g_staticCallDynUpdate++;
      CG_DEBUG("StaticCall: dynamic-key update suppressed at "
               << F->getName() << "\n");
      auto RUF = CGP.getFuncDef(UF);
      CGP.Ctx->Callees[&CS].insert(RUF);
      return;
    }
    // tracepoint registration primitive: register_trace_X(probe) calls
    // tracepoint_probe_register*(&__tracepoint_X, probe, data). The
    // probe becomes a target of the paired static call
    // __SCT__tp_func_X (via tracepoint_update_call's dynamic-key
    // update, suppressed above) — wire probe -> deref(__SCK__tp_func_X)
    // per callsite. Normal handleCall still runs: tp->funcs flows keep
    // feeding the __traceiter_X iterator path.
    if (UF && UF->getName().starts_with("tracepoint_probe_register") &&
        CS.arg_size() >= 2) {
      if (auto *TP = dyn_cast<GlobalVariable>(
              CS.getArgOperand(0)->stripPointerCasts())) {
        if (TP->getName().starts_with("__tracepoint_")) {
          std::string sckName =
              ("__SCK__tp_func_" + TP->getName().drop_front(13)).str();
          GlobalValue *Key = F->getParent()->getNamedValue(sckName);
          if (!Key || Key->isDeclaration()) {
            auto git = CGP.Ctx->Gobjs.find(GlobalValue::getGUID(sckName));
            if (git != CGP.Ctx->Gobjs.end())
              Key = const_cast<GlobalVariable *>(git->second);
          }
          NodeIndex probeNode = CGP.getRepNodeForValue(
              CS.getArgOperand(1)->stripPointerCasts());
          if (Key && !Key->isDeclaration() &&
              probeNode != AndersNodeFactory::InvalidIndex &&
              !CGP.NF.isSpecialNode(probeNode)) {
            NodeIndex keyNode = CGP.getRepNodeForValue(Key);
            if (keyNode != AndersNodeFactory::InvalidIndex) {
              CGP.addAssignmentEdge(
                  probeNode,
                  CGP.getRepDerefNode(CGP.getCanonicalNode(keyNode)));
              g_tracepointProbes++;
            }
          }
        }
      }
    }
  }

  // Tracepoint keyed channels (task #35): the register family's shared
  // tp formal is THE channel that pools every tracepoint's probes into
  // every __traceiter_* dispatch (pin: 964 sites x ~1,561 targets =
  // 17.9% of the kernel answer set). Sever every classifiable family
  // callsite from the generic body and bind per key instead: CONST
  // keys here; the two struct-mediated registrars are covered by the
  // initializer walker, and their dynamic data argument is pooled into
  // the walker keys' data cells (data was globally pooled before this
  // model too — only the fn plane gains keying). Unclassifiable sites
  // keep generic wiring, counted LOUDLY (census: zero at kernel scale).
  if (CFLTracepointKeys) {
    const Function *RF = dyn_cast<Function>(
        CS.getCalledOperand()->stripPointerCasts());
    if (RF && isTracepointRegFn(RF->getName()) && CS.arg_size() >= 3) {
      const Value *tpArg = CS.getArgOperand(0)->stripPointerCasts();
      const auto *TPG = dyn_cast<GlobalVariable>(tpArg);
      const bool constKey =
          TPG && TPG->getName().starts_with("__tracepoint_");
      const bool knownMediator = F->getName() == "trace_event_reg" ||
                                 F->getName() == "bpf_probe_register" ||
                                 F->getName() == "bpf_probe_unregister";
      if (constKey || knownMediator) {
        const bool unreg =
            RF->getName() == "tracepoint_probe_unregister";
        if (constKey && !unreg)
          CGP.bindTracepointProbe(TPG,
                                  CS.getArgOperand(1)->stripPointerCasts(),
                                  CS.getArgOperand(2),
                                  /*fromWalker=*/false);
        if (!constKey && !unreg) {
          // mediator data pool: this callsite's dynamic data actual
          // feeds every walker-bound key's data cell
          NodeIndex dataN =
              CGP.getRepNodeForValue(CS.getArgOperand(2));
          if (dataN != AndersNodeFactory::InvalidIndex &&
              !CGP.NF.isSpecialNode(dataN)) {
            for (const GlobalVariable *K : g_tpWalkerKeys)
              CGP.addAssignmentEdge(dataN,
                                    CGP.tracepointJunctions(K).second);
            g_tpKeyMediatorDataPools++;
          }
        }
        CGP.Ctx->Callees[&CS].insert(
            CGP.getFuncDef(const_cast<Function *>(RF)));
        return; // severed: the shared tp formal never sees this key
      }
      g_tpKeyUnclassified++; // LOUD: generic wiring kept, pool re-forms
    }
  }

  // static_call (task #14): a direct call to the undefined __SCT__X
  // trampoline dispatches through __SCK__X's func slot — the key is a
  // real IR global whose initializer (DEFINE_STATIC_CALL) and updates
  // (__static_call_update stores key->func in-corpus) are already
  // modeled. Wire deref(key) -> value(trampoline) and treat the site
  // as an icall so standard resolution + arg/ret wiring apply.
  {
    Function *SCT = CS.getCalledFunction();
    if (!SCT)
      SCT = dyn_cast<Function>(
          CS.getCalledOperand()->stripPointerCastsAndAliases());
    if (CFLStaticCall && SCT && SCT->isDeclaration() &&
        SCT->getName().starts_with("__SCT__")) {
      StringRef Suffix = SCT->getName().drop_front(7);
      // Tracepoint static calls dispatch to __traceiter_X or a probe
      // registered on X; probes are transitively reachable through the
      // iterator's own indirect call over tp->funcs, so the syntactic
      // edge SCT -> __traceiter_X is callgraph-sound AND avoids reading
      // the key plane (tp keys route through tracepoint structs that
      // live in the type-erased hub — reading them imported the whole
      // hub: km showed __SCT__tp_func_sched_wakeup "resolving" to
      // array_map ops).
      if (Suffix.starts_with("tp_func_")) {
        std::string iterName =
            ("__traceiter_" + Suffix.drop_front(8)).str();
        Function *Iter = F->getParent()->getFunction(iterName);
        if (!Iter || Iter->isDeclaration()) {
          auto fit = CGP.Ctx->Funcs.find(GlobalValue::getGUID(iterName));
          if (fit != CGP.Ctx->Funcs.end()) Iter = fit->second;
        }
        if (Iter) {
          auto RIter = CGP.getFuncDef(Iter);
          CGP.Ctx->Callees[&CS].insert(RIter);
          if (Function *RSCT = CS.getCalledFunction())
            CGP.Ctx->Callees[&CS].insert(CGP.getFuncDef(RSCT));
          g_staticCallTpIter++;
          return; // probes covered transitively via the iterator icall
        }
        g_staticCallNoKey++; // LEDGER: tp_func without visible iterator
        // fall through to the key-based path as backstop
      }
      std::string sckName = ("__SCK__" + Suffix).str();
      GlobalValue *Key = F->getParent()->getNamedValue(sckName);
      if (!Key || Key->isDeclaration()) {
        auto git = CGP.Ctx->Gobjs.find(GlobalValue::getGUID(sckName));
        if (git != CGP.Ctx->Gobjs.end())
          Key = const_cast<GlobalVariable *>(git->second);
      }
      if (Key && !Key->isDeclaration()) {
        NodeIndex keyNode = CGP.getRepNodeForValue(Key);
        NodeIndex sctNode = CGP.NF.getValueNodeFor(SCT);
        if (sctNode == AndersNodeFactory::InvalidIndex)
          sctNode = CGP.NF.createValueNode(SCT);
        if (keyNode != AndersNodeFactory::InvalidIndex) {
          CGP.addAssignmentEdge(
              CGP.getRepDerefNode(CGP.getCanonicalNode(keyNode)),
              CGP.getCanonicalNode(sctNode));
          CGP.Ctx->IndirectCallInsts.insert(&CS);
          CGP.moduleIndirectCallInsts[F->getParent()].insert(&CS);
          if (!CS.getMetadata("ka.icall.id")) {
            std::string id =
                getScopeName(F) + "#" + std::to_string(icallCounter++);
            CS.setMetadata("ka.icall.id",
                           MDNode::get(CS.getContext(),
                                       {MDString::get(CS.getContext(), id)}));
          }
          g_staticCallWired++;
          return; // resolved via flows-to, not as an opaque extern call
        }
      }
      g_staticCallNoKey++; // LEDGER: trampoline without visible key
    }
  }

  if (Function *CF = CS.getCalledFunction()) {
    // direct call
    auto RCF = CGP.getFuncDef(CF);
    CGP.Ctx->Callees[&CS].insert(RCF);
    if (CGP.Ctx->ContainerFuncs.count(RCF))
      CGP.handleContainerCall(&CS, RCF);
    else
      CGP.handleCall(&CS, RCF);
  } else {
    // indirect call (or direct call through alias/bitcast)
    Value *CO = CS.getCalledOperand()->stripPointerCastsAndAliases();
    // resolve constant expr
    if (auto *CE = dyn_cast<ConstantExpr>(CO)) {
      switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: {
          GEPOperator* GEP = dyn_cast<GEPOperator>(CE);
          CO = GEP->getPointerOperand()->stripPointerCastsAndAliases();
          break;
        }
        case Instruction::BitCast: {
          CO = CE->getOperand(0);
          break;
        }
        default:
          WARNING("Unhandled constant expression call target: " << *CE << "\n");
      }
    }
    if (Function *CF = dyn_cast<Function>(CO)) {
      // direct call through bitcast/alias
      auto RCF = CGP.getFuncDef(CF);
      CGP.Ctx->Callees[&CS].insert(RCF);
      if (CGP.Ctx->ContainerFuncs.count(RCF))
        CGP.handleContainerCall(&CS, RCF);
      else
        CGP.handleCall(&CS, RCF);
    } else if (auto *IF = dyn_cast<GlobalIFunc>(CO)) {
      auto it = CGP.IFuncTargets.find(IF);
      if (it != CGP.IFuncTargets.end()) {
        for (const Function *CF : it->second) {
          CGP.Ctx->Callees[&CS].insert(CF);
          if (CGP.Ctx->ContainerFuncs.count(CF))
            CGP.handleContainerCall(&CS, CF);
          else
            CGP.handleCall(&CS, CF);
          CG_LOG("IFunc call: " << IF->getName() << " -> " << CF->getName() << "\n");
        }
      } else {
        CG_DEBUG("IFunc call: " << IF->getName() << " has no resolved targets\n");
      }
    } else {
      // Tracepoint keyed dispatch (task #35): a __traceiter_X icall
      // reads its own key's channel cells. The generic funcs-load
      // chain stays wired but carries nothing once every registration
      // callsite is severed above — this edge pair IS the resolution.
      if (CFLTracepointKeys &&
          F->getName().starts_with("__traceiter_")) {
        if (const GlobalVariable *KeyGV = traceiterKeyOf(F)) {
          auto [fnJ, dataJ] = CGP.tracepointJunctions(KeyGV);
          (void)fnJ; // v3: answers come from the binding table
          NodeIndex keyN = CGP.getRepNodeForValue(KeyGV);
          if (keyN != AndersNodeFactory::InvalidIndex) {
            keyN = CGP.getCanonicalNode(keyN);
            g_tpIterIcallKey[&CS] = keyN;
            // The no-probe default stub is dispatched on the
            // static-call fast path; include it defensively.
            std::string stubName =
                ("__probestub_" + KeyGV->getName().drop_front(13)).str();
            Function *Stub = F->getParent()->getFunction(stubName);
            if (!Stub || Stub->isDeclaration()) {
              auto fit2 =
                  CGP.Ctx->Funcs.find(GlobalValue::getGUID(stubName));
              if (fit2 != CGP.Ctx->Funcs.end())
                Stub = fit2->second;
            }
            if (Stub)
              g_tpKeyProbes[keyN].insert(CGP.getFuncDef(Stub));
            if (CS.arg_size() >= 1) {
              NodeIndex dArg =
                  CGP.getRepNodeForValue(CS.getArgOperand(0));
              if (dArg != AndersNodeFactory::InvalidIndex)
                CGP.addAssignmentEdge(dataJ, dArg);
            }
            g_tpKeyDispatchWires++;
          }
        } else {
          g_tpKeyKeylessIter++; // LOUD: census says this is empty
        }
      }
      CGP.Ctx->IndirectCallInsts.insert(&CS);
      CGP.moduleIndirectCallInsts[F->getParent()].insert(&CS);
      // Attach deterministic icall ID as LLVM metadata.
      // Use scoped caller name for uniqueness across TUs.
      std::string id;
      id = getScopeName(F) + "#" + std::to_string(icallCounter++);
      CS.setMetadata("ka.icall.id",
          MDNode::get(CS.getContext(),
                      {MDString::get(CS.getContext(), id)}));
    }
  }
}

void CallGraphPass::InstHandler::visitAllocaInst(AllocaInst &I) {
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(&I, slotRep))
    return;

  // Create a deref node eagerly only for pointer-bearing allocas. Cells of
  // scalar allocas (bool/int out-params etc.) can never hold a function
  // pointer under tracked (pointer-typed) accesses; creating them eagerly
  // manufactured O(n^2) M-facts over empty cells (harfbuzz sanitize class).
  // A pointer-typed access through such an alloca still creates the deref
  // lazily in visitLoadInst/visitStoreInst, so this stays sound.
  if (!containsPointerType(I.getAllocatedType()))
    return;
  NodeIndex ptrNode = CGP.getRepNodeForValue(&I);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find alloca node");
  (void)CGP.getRepDerefNode(ptrNode);
}

// ---- integer-laundered pointer provenance through MEMORY ----
// ptrtoint/inttoptr/binop visitors track provenance while it stays in
// SSA registers, but the load/store guards skip integer types, so
// provenance dies at memory. Clang lowers _Atomic function pointers to
// exactly this shape (atomicrmw/cmpxchg on i64 with ptrtoint constants,
// inttoptr on the way out — see test/t_atomicptr.c), and long-carried
// pointers hit it too. Witness-based repair: a pointer-width integer
// store/load emits deref edges when a bounded def/use scan finds
// pointer provenance; the interprocedural cases the scan declines
// (int arguments, int call results, escapes via ret/call) are COUNTED
// as explicit ledger entries, never dropped silently.
size_t g_intProvStores = 0, g_intProvLoads = 0;
bool constantHasPtrToInt(const Constant *C, unsigned depth) {
  if (depth == 0) return true; // bail conservative
  if (const auto *CE = dyn_cast<ConstantExpr>(C)) {
    if (CE->getOpcode() == Instruction::PtrToInt) return true;
    for (const Use &U : CE->operands())
      if (const auto *OC = dyn_cast<Constant>(U.get()))
        if (constantHasPtrToInt(OC, depth - 1)) return true;
  }
  return false;
}

// Def-side witness: could this integer value carry pointer provenance?
bool mayCarryPtrProvenance(const Value *V, unsigned depth,
                                  bool &declined) {
  if (depth == 0) return true; // depth exhaustion: conservative yes
  if (isa<PtrToIntInst>(V)) return true;
  if (const auto *C = dyn_cast<Constant>(V)) {
    if (isa<ConstantInt>(C) || isa<ConstantData>(C)) return false;
    return constantHasPtrToInt(C, 6);
  }
  if (isa<LoadInst>(V)) return true; // slot-to-slot int copies stay live
  if (isa<Argument>(V))
    return true; // formals are wired witness-gated now: facts only if
                 // some caller actually passed provenance
  if (isa<CallBase>(V)) {
    // An int-returning call may launder a pointer THROUGH its return —
    // the 5.18 fd chain is a two-hop instance (__fdget_pos returns
    // v = __fdget(fd), __fdget returns __fget_light(...)): declining
    // here severed every hop above the ptrtoint and the whole
    // file->f_op dispatch chain died (vfs_llseek GT FN). Conservative
    // yes: the call result node carries facts only if the callee's own
    // return was provenance-witnessed and wired, so plain error-code
    // returns stay inert.
    return true;
  }
  if (const auto *I = dyn_cast<Instruction>(V)) {
    if (isa<BinaryOperator>(I) || isa<CastInst>(I) || isa<PHINode>(I) ||
        isa<SelectInst>(I) || isa<FreezeInst>(I)) {
      for (const Use &U : I->operands())
        if (U->getType()->isIntegerTy() || U->getType()->isPointerTy())
          if (mayCarryPtrProvenance(U.get(), depth - 1, declined))
            return true;
      return false;
    }
  }
  return false;
}

// Use-side witness: could this loaded integer become a pointer again?
static bool mayBecomePointer(const Value *V, unsigned depth, bool &declined) {
  if (depth == 0) return true;
  for (const User *U : V->users()) {
    if (isa<IntToPtrInst>(U)) return true;
    if (const auto *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getValueOperand() == V) return true; // flows onward via memory
      continue;
    }
    if (isa<ReturnInst>(U))
      return true; // witnessed int returns are wired (9f3639e)
    if (const auto *CB = dyn_cast<CallBase>(U)) {
      if (CB->getCalledOperand() != V)
        return true; // witnessed int args are wired now (formals
                     // receive the facts; callee side re-proves)
      continue;
    }
    if (isa<BinaryOperator>(U) || isa<CastInst>(U) || isa<PHINode>(U) ||
        isa<SelectInst>(U) || isa<FreezeInst>(U) || isa<ExtractValueInst>(U))
      if (mayBecomePointer(U, depth - 1, declined))
        return true;
  }
  return false;
}

bool isPtrWidthInt(const Type *T, const DataLayout &DL) {
  return T->isIntegerTy() &&
         T->getIntegerBitWidth() >= DL.getPointerSizeInBits();
}

void CallGraphPass::InstHandler::visitLoadInst(LoadInst &I) {
  // Tracepoint keyed dispatch (task #35): inside __traceiter_X, the
  // funcs-head load reads cells that the kernel-scale giant absorbs —
  // the keyed channel replaces this read entirely (sound: the census
  // completeness counters prove every registration is channel-bound),
  // so the generic wiring is severed here to keep the pool from
  // riding back in beside the exact channel.
  if (CFLTracepointKeys) {
    const Function *LF = I.getFunction();
    if (LF && LF->getName().starts_with("__traceiter_")) {
      const Value *P = I.getPointerOperand();
      if (const auto *CE = dyn_cast<ConstantExpr>(P))
        if (CE->getOpcode() == Instruction::GetElementPtr)
          P = CE->getOperand(0);
      if (const auto *GV = dyn_cast<GlobalVariable>(P->stripPointerCasts()))
        if (GV->getName().starts_with("__tracepoint_")) {
          g_tpKeyIterLoadsSevered++;
          return;
        }
    }
  }
  if (!containsPointerType(I.getType())) {
    // Integer-laundered provenance: a pointer-width int load whose value
    // can become a pointer again (inttoptr downstream, or stored onward)
    // must read the cell.
    bool declined = false;
    if (CGP.curDL && isPtrWidthInt(I.getType(), *CGP.curDL)) {
      if (mayBecomePointer(&I, 8, declined)) {
        NodeIndex valNode = CGP.getRepNodeForValue(&I);
        if (valNode == AndersNodeFactory::InvalidIndex)
          valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
        Value *lp = I.getOperand(0);
        NodeIndex slotRep;
        if (CGP.resolveSummarizedAllocaSlot(lp, slotRep)) {
          CGP.localAllocaLoadVals[slotRep].push_back(valNode);
        } else {
          NodeIndex pN = CGP.getRepNodeForValue(lp);
          if (pN != AndersNodeFactory::InvalidIndex)
            CGP.addAssignmentEdge(CGP.getRepDerefNode(pN), valNode);
        }
        g_intProvLoads++;
        // Segment-local field claim: facts arrive with the residues
        // the producer proved; this segment (load -> ... -> inttoptr)
        // must be tag-clean or the residue claim is wrong here.
        if (CGP.Graph.fieldSensitive() && !ptrToIntTagRoundTripOnly(&I))
          CGP.addFieldWildcardLoop(
              valNode, tagWalkTag("int-load-dirty-segment").c_str());
      } else if (declined) {
        g_intLoadUnmodeled++; // ledger
      }
    }
    return;
  }
  NodeIndex valNode = CGP.getRepNodeForValue(&I);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find load value node");

  Value *ptr = I.getOperand(0);
  // Frontends often lower va_arg to __va_list_tag memory accesses (no VAArgInst).
  // Connect such pointer loads to the function's vararg summary node.
  if (Function *F = I.getFunction()) {
    NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
    if (varargNode != AndersNodeFactory::InvalidIndex &&
        derivesFromLoweredVAList(ptr)) {
      CGP.addAssignmentEdge(varargNode, valNode);
      CG_DEBUG("LoweredVAArg: " << F->getName() << ": vararg node " << varargNode
               << " -> val node " << valNode << " for " << I << "\n");
    }
  }
  // A va_list received from another function: what va_start put into
  // the va_list object (the creator's variadic arguments) is what this
  // lowered va_arg reads.
  if (const Value *Base = vaListBase(ptr)) {
    NodeIndex baseNode = CGP.getRepNodeForValue(Base);
    if (baseNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(CGP.getRepDerefNode(baseNode), valNode);
  }

  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaLoadVals[slotRep].push_back(valNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find load ptr node");

  // Aggregate loads read every field: pull every residue cell into the
  // aggregate SSA value (residue 0 via the normal deref edge below). No
  // pointer wildcard — that smeared every access through this pointer's
  // aliases, not just this load.
  if (CGP.Graph.fieldSensitive() && I.getType()->isAggregateType()) {
    if (CFLResidueCopies && CGP.flowsTo()) {
      const unsigned P = CGP.Graph.numFieldBuckets();
      for (unsigned r = 1; r < P; r++) {
        NodeIndex pF = CGP.getFieldPtrNode(ptrNode, (int64_t)r);
        CGP.Graph.addField(ptrNode, CGP.getCanonicalNode(pF), (int)r);
        CGP.addAssignmentEdge(CGP.getRepDerefNode(CGP.getCanonicalNode(pF)),
                              valNode);
      }
    } else {
      CGP.addFieldWildcardLoop(ptrNode, "aggregate-load");
    }
  }

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  SmallVector<uint32_t, 4> names{ka::AccessNames::Unnamed};
  if (CGP.namedPlanes()) {
    if (I.getType()->isPointerTy())
      names[0] = CGP.accessNames->ofMemAccess(
          I, ptr, CGP.curDL->getTypeStoreSize(I.getType()), *CGP.curDL);
    else if (auto *VT = dyn_cast<VectorType>(I.getType()))
      if (VT->getElementType()->isPointerTy()) {
        auto lanes = CGP.accessNames->ofLanes(ptr, VT, *CGP.curDL);
        if (!lanes.empty())
          names = lanes;
      }
    CGP.applyUnionKeys(I, names);
  }
  if ((CFLCensusTypeLabels || !CFLRuleReport.empty()) && names[0] != ka::AccessNames::Unnamed)
    CGP.namedAccessLog.emplace_back(derefNode, names[0], &I);
  CGP.wireNamedLoad(derefNode, valNode, names);
}

void CallGraphPass::InstHandler::visitStoreInst(StoreInst &I) {
  Value *val = I.getOperand(0);
  if (!containsPointerType(val->getType())) {
    // Integer-laundered provenance: a pointer-width int store with a
    // def-side witness (ptrtoint upstream) still moves a pointer.
    bool declined = false;
    if (CGP.curDL && isPtrWidthInt(val->getType(), *CGP.curDL) &&
        !shouldSkipValue(val)) {
      if (mayCarryPtrProvenance(val, 8, declined)) {
        NodeIndex valNode = CGP.getRepNodeForValue(val);
        if (valNode == AndersNodeFactory::InvalidIndex)
          valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(val));
        if (auto *CE = dyn_cast<ConstantExpr>(val))
          if (CE->getOpcode() == Instruction::PtrToInt) {
            NodeIndex srcN = CGP.getRepNodeForValue(CE->getOperand(0));
            if (srcN != AndersNodeFactory::InvalidIndex)
              CGP.addAssignmentEdge(srcN, valNode);
          }
        Value *sp = I.getOperand(1);
        NodeIndex slotRep;
        if (CGP.resolveSummarizedAllocaSlot(sp, slotRep)) {
          CGP.localAllocaStoreVals[slotRep].push_back(valNode);
        } else {
          NodeIndex pN = CGP.getRepNodeForValue(sp);
          CellWriteSize ws(CGP, CGP.curDL->getTypeStoreSize(val->getType()));
          if (pN != AndersNodeFactory::InvalidIndex)
            CGP.addAssignmentEdge(valNode, CGP.getRepDerefNode(pN));
        }
        g_intProvStores++;
      } else if (declined) {
        g_intStoreUnmodeled++; // ledger: interprocedural int provenance
      }
    }
    return;
  }

  // Skip nullptr and compiler-introduced values
  if (shouldSkipValue(val)) {
    CG_DEBUG("Skipping value in Store: " << *val << "\n");
    return;
  }

  // Check for potential linked data structure patterns
  if (auto *GEP = dyn_cast<GetElementPtrInst>(val)) {
    auto *ptrOp = GEP->getPointerOperand();
    if (auto *Load = dyn_cast<LoadInst>(ptrOp)) {
      // Pattern: store GEP(load(ptr)), ptr - typical linked list cycle
      CG_DEBUG("Potential linked structure cycle: store GEP(load(" << *Load->getPointerOperand()
               << ")), " << *I.getPointerOperand() << "\n");
    }
  }

  NodeIndex valNode = CGP.getRepNodeForValue(val);
  // assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find store value node");
  if (valNode == AndersNodeFactory::InvalidIndex) {
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(val));
    CG_DEBUG("Create value node " << valNode << " for store " << *val << "\n");
  }

  Value *ptr = I.getOperand(1);
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaStoreVals[slotRep].push_back(valNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find store ptr node");

  // Aggregate stores write every field: push the aggregate SSA value into
  // every residue cell (residue 0 via the normal deref edge below).
  if (CGP.Graph.fieldSensitive() && val->getType()->isAggregateType()) {
    if (CFLResidueCopies && CGP.flowsTo()) {
      const unsigned P = CGP.Graph.numFieldBuckets();
      for (unsigned r = 1; r < P; r++) {
        NodeIndex pF = CGP.getFieldPtrNode(ptrNode, (int64_t)r);
        CGP.Graph.addField(ptrNode, CGP.getCanonicalNode(pF), (int)r);
        CGP.addAssignmentEdge(valNode,
                              CGP.getRepDerefNode(CGP.getCanonicalNode(pF)));
      }
    } else {
      CGP.addFieldWildcardLoop(ptrNode, "aggregate-store");
    }
  }

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  SmallVector<uint32_t, 4> names{ka::AccessNames::Unnamed};
  if (CGP.namedPlanes()) {
    if (val->getType()->isPointerTy()) {
      const uint64_t sz = CGP.curDL->getTypeStoreSize(val->getType());
      names[0] = CGP.accessNames->ofMemAccess(I, ptr, sz, *CGP.curDL);
      // A store through a phi or select of addresses (-O3 sinks the
      // stores of two branches into one, e.g. a hash bucket and a
      // chain link) lands on one of them: file it under every incoming
      // name, as lanes are. If any incoming address has no name, the
      // store stays unnamed (an untyped write).
      if (names[0] == ka::AccessNames::Unnamed) {
        SmallVector<const Value *, 8> work{ptr->stripPointerCasts()}, leaves;
        SmallPtrSet<const Value *, 8> seen;
        bool merged = false, allNamed = true;
        while (!work.empty() && allNamed) {
          const Value *P = work.pop_back_val();
          if (!seen.insert(P).second) continue;
          if (seen.size() > 16) { allNamed = false; break; }
          if (const auto *PN = dyn_cast<PHINode>(P)) {
            merged = true;
            for (const Value *In : PN->incoming_values())
              work.push_back(In->stripPointerCasts());
          } else if (const auto *SI = dyn_cast<SelectInst>(P)) {
            merged = true;
            work.push_back(SI->getTrueValue()->stripPointerCasts());
            work.push_back(SI->getFalseValue()->stripPointerCasts());
          } else {
            leaves.push_back(P);
          }
        }
        if (merged && allNamed && !leaves.empty()) {
          SmallVector<uint32_t, 4> incoming;
          for (const Value *P : leaves) {
            const uint32_t n = CGP.accessNames->ofMemAccess(I, P, sz, *CGP.curDL);
            if (n == ka::AccessNames::Unnamed) { incoming.clear(); break; }
            if (std::find(incoming.begin(), incoming.end(), n) == incoming.end())
              incoming.push_back(n);
          }
          if (!incoming.empty()) names = incoming;
        }
      }
    } else if (auto *VT = dyn_cast<VectorType>(val->getType()))
      if (VT->getElementType()->isPointerTy()) {
        auto lanes = CGP.accessNames->ofLanes(ptr, VT, *CGP.curDL);
        if (!lanes.empty())
          names = lanes;
      }
    CGP.applyUnionKeys(I, names);
  }
  if ((CFLCensusTypeLabels || !CFLRuleReport.empty()) && names[0] != ka::AccessNames::Unnamed)
    CGP.namedAccessLog.emplace_back(derefNode, names[0], &I);
  CellWriteSize ws(CGP, CGP.curDL->getTypeStoreSize(val->getType()));
  CGP.wireNamedStore(valNode, derefNode, names);
}

void CallGraphPass::InstHandler::visitGetElementPtrInst(GetElementPtrInst &GEP) {
  Value *ptr = GEP.getPointerOperand();

  // Only handle GEPs on pointer or vector-of-pointer types
  if (!containsPointerType(ptr->getType()))
    return;

  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  if (ptrNode == AndersNodeFactory::InvalidIndex) {
    // On-the-fly node creation for unhandled operands (e.g., constant vectors)
    ptrNode = CGP.getCanonicalNode(CGP.NF.createValueNode(ptr));
    CG_DEBUG("Create value node " << ptrNode << " for GEP ptr " << *ptr << "\n");
  }
  NodeIndex valNode = CGP.getRepNodeForValue(&GEP);
  if (valNode == AndersNodeFactory::InvalidIndex) {
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&GEP));
    CG_DEBUG("Create value node " << valNode << " for GEP result " << GEP << "\n");
  }

  if (CGP.Graph.fieldSensitive()) {
    SmallVector<int64_t, 4> levels;
    SmallVector<const StructType *, 4> ltys;
    const DataLayout &DL = GEP.getModule()->getDataLayout();
    if (!CGP.decomposeGEPLevels(cast<GEPOperator>(&GEP), DL, levels, &ltys))
      CGP.applyFieldFallback(ptrNode, valNode, "gep-variable-offset");
    else if (levels.empty())
      CGP.addAssignmentEdge(ptrNode, valNode);
    else
      CGP.addFieldChainEdges(ptrNode, valNode, levels, ltys);
    return;
  }

  CGP.addAssignmentEdge(ptrNode, valNode);
}

void CallGraphPass::InstHandler::visitBitCastInst(BitCastInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    srcNode = CGP.getCanonicalNode(CGP.NF.createValueNode(I.getOperand(0)));
    CG_DEBUG("Create value node " << srcNode << " for bitcast src " << *(I.getOperand(0)) << "\n");
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
    WARNING("Create value node " << dstNode << " for bitcast dst " << I << "\n");
  }
  CGP.addAssignmentEdge(srcNode, dstNode);
}

// freeze forwards its operand unchanged (poison stopper) — a plain copy
// for pointer-carrying values. Census: kernel 106 freezes, 2 on pointer
// paths; silently dropped before this visitor existed.
void CallGraphPass::InstHandler::visitFreezeInst(FreezeInst &I) {
  if (!containsPointerType(I.getType()))
    return;
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex)
    srcNode = CGP.getCanonicalNode(CGP.NF.createValueNode(I.getOperand(0)));
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  CGP.addAssignmentEdge(srcNode, dstNode);
}

// addrspacecast is ptr->ptr value flow; visitBitCastInst does not catch
// it (distinct opcode). Zero instances in current corpora — defensive.
void CallGraphPass::InstHandler::visitAddrSpaceCastInst(AddrSpaceCastInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex)
    srcNode = CGP.getCanonicalNode(CGP.NF.createValueNode(I.getOperand(0)));
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  CGP.addAssignmentEdge(srcNode, dstNode);
}

// atomicrmw on a pointer slot (xchg — the lockless fptr-swap idiom) is a
// fused store+load: new value into the cell, old value out to the result.
void CallGraphPass::InstHandler::visitAtomicRMWInst(AtomicRMWInst &I) {
  Value *val = I.getValOperand();
  if (!containsPointerType(val->getType())) {
    // _Atomic fptr slots lower to i64 xchg with ptrtoint/inttoptr —
    // accept when either side carries a provenance witness.
    bool dv = false, du = false;
    if (!(CGP.curDL && isPtrWidthInt(val->getType(), *CGP.curDL)))
      return;
    if (!mayCarryPtrProvenance(val, 8, dv) && !mayBecomePointer(&I, 8, du)) {
      if (dv || du) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex valNode = CGP.getRepNodeForValue(val);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(val));
  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  if (auto *CE = dyn_cast<ConstantExpr>(val))
    if (CE->getOpcode() == Instruction::PtrToInt) {
      NodeIndex srcN = CGP.getRepNodeForValue(CE->getOperand(0));
      if (srcN != AndersNodeFactory::InvalidIndex)
        CGP.addAssignmentEdge(srcN, valNode);
    }
  Value *ptr = I.getPointerOperand();
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaStoreVals[slotRep].push_back(valNode);
    CGP.localAllocaLoadVals[slotRep].push_back(resNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex &&
         "Failed to find atomicrmw ptr node");
  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);
  {
    CellWriteSize ws(CGP, CGP.curDL ? CGP.curDL->getTypeStoreSize(I.getType()) : 0);
    CGP.addAssignmentEdge(valNode, derefNode);
  }
  CGP.addAssignmentEdge(derefNode, resNode);
  // Segment-local field claim for the loaded-old-value side.
  if (!containsPointerType(I.getType()) && CGP.Graph.fieldSensitive() &&
      !ptrToIntTagRoundTripOnly(&I))
    CGP.addFieldWildcardLoop(resNode,
                             tagWalkTag("int-load-dirty-segment").c_str());
}

// cmpxchg on a pointer slot: conditional store of the new value plus the
// old value loaded into the {old, i1} aggregate result (extractvalue
// projects it — sound to wire both directions unconditionally).
void CallGraphPass::InstHandler::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  Value *nv = I.getNewValOperand();
  if (!containsPointerType(nv->getType())) {
    bool dv = false, du = false;
    if (!(CGP.curDL && isPtrWidthInt(nv->getType(), *CGP.curDL)))
      return;
    if (!mayCarryPtrProvenance(nv, 8, dv) && !mayBecomePointer(&I, 8, du)) {
      if (dv || du) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex valNode = CGP.getRepNodeForValue(nv);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.getCanonicalNode(CGP.NF.createValueNode(nv));
  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  if (auto *CE = dyn_cast<ConstantExpr>(nv))
    if (CE->getOpcode() == Instruction::PtrToInt) {
      NodeIndex srcN = CGP.getRepNodeForValue(CE->getOperand(0));
      if (srcN != AndersNodeFactory::InvalidIndex)
        CGP.addAssignmentEdge(srcN, valNode);
    }
  Value *ptr = I.getPointerOperand();
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaStoreVals[slotRep].push_back(valNode);
    CGP.localAllocaLoadVals[slotRep].push_back(resNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex &&
         "Failed to find cmpxchg ptr node");
  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);
  {
    CellWriteSize ws(CGP, CGP.curDL ? CGP.curDL->getTypeStoreSize(I.getNewValOperand()->getType()) : 0);
    CGP.addAssignmentEdge(valNode, derefNode);
  }
  CGP.addAssignmentEdge(derefNode, resNode);
  // Segment-local field claim for the loaded-old-value projection.
  if (!containsPointerType(I.getNewValOperand()->getType()) &&
      CGP.Graph.fieldSensitive() && !ptrToIntTagRoundTripOnly(&I))
    CGP.addFieldWildcardLoop(resNode,
                             tagWalkTag("int-load-dirty-segment").c_str());
}

static bool ptrToIntTagRoundTripOnly(const Value *PTI); // defined below
static void p2iEscapeCensus(const Value *PTI, const char *where); // defined below

// phi/select of PTR-WIDTH INTS can carry pointer provenance — clang
// folds `flag ? (ulong)&a : (ulong)&b` into a select whose operands
// are ptrtoint CONSTANT EXPRESSIONS (found by test/t_maskwalk.c:
// the whole chain silently dropped and the downstream icall resolved
// to NOTHING). Same laundering guards as the atomic handlers above;
// a CE ptrtoint contributes its pointer operand, plus — under field
// mode — the same escape-wildcard discipline visitPtrToIntInst
// applies to the instruction form (a CE never passes through that
// visitor, so this is its only wildcard site).
void CallGraphPass::InstHandler::visitPHINode(PHINode &PHI) {
  if (!containsPointerType(PHI.getType())) {
    if (!(CGP.curDL && isPtrWidthInt(PHI.getType(), *CGP.curDL)))
      return;
    bool d = false, prov = mayBecomePointer(&PHI, 8, d);
    for (unsigned i = 0, e = PHI.getNumIncomingValues(); !prov && i != e;
         ++i) {
      bool d2 = false;
      prov = mayCarryPtrProvenance(PHI.getIncomingValue(i), 8, d2);
      d |= d2;
    }
    if (!prov) {
      if (d) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&PHI);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&PHI));
  auto wireIncoming = [&](Value *src) {
    // A ptrtoint CONSTANT EXPRESSION maps to a special node (constant
    // pool), which would silently absorb the flow — unwrap to the
    // pointer operand instead.
    const auto *CE = dyn_cast<ConstantExpr>(src);
    const bool ceP2I = CE && CE->getOpcode() == Instruction::PtrToInt;
    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    if (srcNode != AndersNodeFactory::InvalidIndex &&
        !(ceP2I && CGP.NF.isSpecialNode(srcNode))) {
      CGP.addAssignmentEdge(srcNode, dstNode);
      return;
    }
    if (!ceP2I)
      return; // plain int constant: no provenance
    NodeIndex ptrN = CGP.getRepNodeForValue(CE->getOperand(0));
    if (ptrN == AndersNodeFactory::InvalidIndex || CGP.NF.isSpecialNode(ptrN))
      return;
    if (CGP.Graph.fieldSensitive() && !ptrToIntTagRoundTripOnly(CE)) {
      p2iEscapeCensus(CE, "ce");
      CGP.addFieldWildcardLoop(ptrN, "ptrtoint-escape-ce");
    }
    else if (CGP.Graph.fieldSensitive())
      g_tagRoundTrips++;
    CGP.addAssignmentEdge(ptrN, dstNode);
  };
  for (unsigned i = 0, e = PHI.getNumIncomingValues(); i != e; ++i) {
    Value *src = PHI.getIncomingValue(i);
    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in PHI: " << *src << "\n");
      continue;
    }
    wireIncoming(src);
  }
}

void CallGraphPass::InstHandler::visitSelectInst(SelectInst &I) {
  if (!containsPointerType(I.getType())) {
    if (!(CGP.curDL && isPtrWidthInt(I.getType(), *CGP.curDL)))
      return;
    bool d = false, prov = mayBecomePointer(&I, 8, d);
    for (unsigned i = 1; !prov && i < I.getNumOperands(); i++) {
      bool d2 = false;
      prov = mayCarryPtrProvenance(I.getOperand(i), 8, d2);
      d |= d2;
    }
    if (!prov) {
      if (d) g_intStoreUnmodeled++;
      return;
    }
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex)
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  auto wireIncoming = [&](Value *src) {
    // A ptrtoint CONSTANT EXPRESSION maps to a special node (constant
    // pool), which would silently absorb the flow — unwrap to the
    // pointer operand instead.
    const auto *CE = dyn_cast<ConstantExpr>(src);
    const bool ceP2I = CE && CE->getOpcode() == Instruction::PtrToInt;
    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    if (srcNode != AndersNodeFactory::InvalidIndex &&
        !(ceP2I && CGP.NF.isSpecialNode(srcNode))) {
      CGP.addAssignmentEdge(srcNode, dstNode);
      return;
    }
    if (!ceP2I)
      return; // plain int constant: no provenance
    NodeIndex ptrN = CGP.getRepNodeForValue(CE->getOperand(0));
    if (ptrN == AndersNodeFactory::InvalidIndex || CGP.NF.isSpecialNode(ptrN))
      return;
    if (CGP.Graph.fieldSensitive() && !ptrToIntTagRoundTripOnly(CE)) {
      p2iEscapeCensus(CE, "ce");
      CGP.addFieldWildcardLoop(ptrN, "ptrtoint-escape-ce");
    }
    else if (CGP.Graph.fieldSensitive())
      g_tagRoundTrips++;
    CGP.addAssignmentEdge(ptrN, dstNode);
  };
  for (unsigned i = 1; i < I.getNumOperands(); i++) {
    Value *src = I.getOperand(i);
    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in Select: " << *src << "\n");
      continue;
    }
    wireIncoming(src);
  }
}

void CallGraphPass::InstHandler::visitExtractValueInst(ExtractValueInst &EVI) {
  bool resultIsPtr = EVI.getType()->isPointerTy();

  // Check if the aggregate operand already has tracked pointer content.
  // Skip constants (undef, zeroinitializer, etc.) — they map to ConstantIntIndex
  // which doesn't carry useful pointer information.
  Value *agg = EVI.getAggregateOperand();
  NodeIndex aggNode = AndersNodeFactory::InvalidIndex;
  if (!isa<Constant>(agg))
    aggNode = CGP.NF.getValueNodeFor(agg);

  // Nothing to track if the result isn't a pointer and the aggregate
  // has no tracked pointer content to propagate through nested extracts
  if (!resultIsPtr && aggNode == AndersNodeFactory::InvalidIndex)
    return;

  // field insensitive, just connect the aggregate
  NodeIndex valNode = CGP.NF.getValueNodeFor(&EVI);
  if (valNode == AndersNodeFactory::InvalidIndex)
    valNode = CGP.NF.createValueNode(&EVI);
  valNode = CGP.getCanonicalNode(valNode);

  if (aggNode != AndersNodeFactory::InvalidIndex)
    CGP.addAssignmentEdge(aggNode, valNode);
}

void CallGraphPass::InstHandler::visitInsertValueInst(InsertValueInst &IVI) {
  // field insensitive, just connect the aggregate
  Value *val = IVI.getInsertedValueOperand();
  bool valIsPtr = val->getType()->isPointerTy();

  // Check if the aggregate operand already has tracked pointer content
  // (e.g., from a prior insertvalue that inserted a pointer).
  // Skip constants (undef, zeroinitializer, etc.) — they map to ConstantIntIndex
  // which doesn't carry useful pointer information.
  Value *agg = IVI.getAggregateOperand();
  NodeIndex aggNode = AndersNodeFactory::InvalidIndex;
  if (!isa<Constant>(agg))
    aggNode = CGP.NF.getValueNodeFor(agg);

  // Nothing to track if the inserted value isn't a pointer and the aggregate
  // has no tracked pointer content
  if (!valIsPtr && aggNode == AndersNodeFactory::InvalidIndex)
    return;

  NodeIndex resNode = CGP.NF.getValueNodeFor(&IVI);
  if (resNode == AndersNodeFactory::InvalidIndex)
    resNode = CGP.NF.createValueNode(&IVI);
  resNode = CGP.getCanonicalNode(resNode);

  // Propagate aggregate's pointer content to result
  if (aggNode != AndersNodeFactory::InvalidIndex)
    CGP.addAssignmentEdge(aggNode, resNode);

  // Propagate inserted value if it's a pointer
  if (valIsPtr) {
    NodeIndex valNode = CGP.NF.getValueNodeFor(val);
    assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find insertvalue val node");
    CGP.addAssignmentEdge(valNode, resNode);
  }
}

void CallGraphPass::InstHandler::visitIntToPtrInst(IntToPtrInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    // Dropping the edge here loses the int->ptr flow entirely — log
    // enough to classify WHY the integer source has no node (operand
    // kind + defining shape + function) so the ledger names the gap.
    const Value *src = I.getOperand(0);
    WARNING("IntToPtr: src node not found: " << I << " | src: " << *src
            << " | kind: "
            << (isa<Instruction>(src)
                    ? cast<Instruction>(src)->getOpcodeName()
                    : isa<Argument>(src)      ? "argument"
                      : isa<ConstantExpr>(src)
                          ? "constexpr"
                          : isa<Constant>(src) ? "constant" : "other")
            << " | fn: " << I.getFunction()->getName() << "\n");
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    WARNING("IntToPtr: dst node not found: " << I << "\n");
    return;
  }
  CG_DEBUG("IntToPtr: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.addAssignmentEdge(srcNode, dstNode);

  // offset_to_ptr rule: inttoptr(add/sub-chain containing ptrtoint p)
  // computes a pointer FROM an array entry — semantically a read of
  // the array (kernel PREL32 idiom: initcalls, pci_fixup, __ksymtab).
  // Pull deref(p) into the result so members wired store-like into the
  // array reach exactly these consumers and no one else. Bounded walk
  // through the integer-arithmetic chain; every ptrtoint leaf counts.
  {
    SmallVector<const Value *, 8> stack{I.getOperand(0)};
    SmallPtrSet<const Value *, 8> seen;
    SmallVector<const PtrToIntOperator *, 4> ptiLeaves;
    SmallVector<const LoadInst *, 4> loadLeaves;
    unsigned steps = 0;
    while (!stack.empty() && steps++ < 16) {
      const Value *V = stack.pop_back_val();
      if (!seen.insert(V).second) continue;
      if (const auto *PTI = dyn_cast<PtrToIntOperator>(V)) {
        ptiLeaves.push_back(PTI);
        continue;
      }
      if (const auto *LI = dyn_cast<LoadInst>(V)) {
        loadLeaves.push_back(LI);
        continue;
      }
      if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
        unsigned op = BO->getOpcode();
        if (op == Instruction::Add || op == Instruction::Sub ||
            op == Instruction::Or) {
          stack.push_back(BO->getOperand(0));
          stack.push_back(BO->getOperand(1));
        }
        continue;
      }
      if (const auto *CI2 = dyn_cast<CastInst>(V)) {
        stack.push_back(CI2->getOperand(0));
        continue;
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        for (const Value *IV : PN->incoming_values()) stack.push_back(IV);
        continue;
      }
    }
    // The pull applies only to the self-relative read p + *p: some
    // load in the chain must read THROUGH the same pointer that was
    // ptrtoint'ed (same value class). Without this the rule fires on
    // percpu rebasing (inttoptr(add(ptrtoint &var, cpu_offset))) where
    // the offset comes from another object and the array pull is
    // noise (subset: value-leak removed but pairs flat until gated).
    for (const PtrToIntOperator *PTI : ptiLeaves) {
      NodeIndex base = CGP.getRepNodeForValue(PTI->getPointerOperand());
      if (base == AndersNodeFactory::InvalidIndex ||
          CGP.NF.isSpecialNode(base))
        continue;
      // Rebased-pointer rule, PERCPU-GATED (narrowed 2026-08-12):
      // inttoptr(add-chain containing ptrtoint p) IS a pointer into
      // p's object, but applying the base->result alias to EVERY
      // ptrtoint chain multiplied the km from-scratch closure ~3.8x
      // (integer-laundered pointer arithmetic is ubiquitous and mostly
      // pool-feeding). The GT-demanded population is exactly percpu
      // rebasing (this_cpu_ptr/per_cpu_ptr on .data..percpu globals:
      // wake_up_klogd_work_func, vfree_deferred). Gate on the
      // canonical base being a percpu-section global; count the
      // skipped remainder LOUDLY — it is a declared residual, not a
      // silent drop. The self-read deref-pull below is unchanged.
      const Value *baseV = PTI->getPointerOperand()->stripPointerCasts();
      bool percpuBase = false;
      if (const auto *GV = dyn_cast<GlobalVariable>(baseV)) {
        const GlobalVariable *DGV = GV;
        auto git = CGP.Ctx->Gobjs.find(GV->getGUID());
        if (git != CGP.Ctx->Gobjs.end() && git->second)
          if (const auto *D = dyn_cast<GlobalVariable>(git->second))
            DGV = D;
        percpuBase = DGV->getSection().contains("percpu");
      }
      if (percpuBase) {
        CGP.addAssignmentEdge(base, dstNode);
        // Field mode: NO wildcard here (2026-08-13). Percpu rebasing
        // (add of __per_cpu_offset[cpu]) is base-to-base relocation —
        // the same position in another CPU's copy of the section —
        // so intra-object offsets are PRESERVED and the shift-0 edge
        // above is the exact encoding. This rides the same declared
        // percpu invariant as the identity gate itself (7d7df8a):
        // integer arithmetic on percpu-section p2i bases is per-cpu
        // rebasing. A non-rebasing offset-changing use of a percpu
        // base would violate that invariant, not just this rule.
      } else {
        g_rebasedPtrSkipped++;
      }
      bool selfRead = false;
      for (const LoadInst *LI : loadLeaves) {
        NodeIndex lp = CGP.getRepNodeForValue(
            LI->getPointerOperand()->stripPointerCasts());
        if (lp != AndersNodeFactory::InvalidIndex &&
            CGP.getCanonicalNode(lp) == CGP.getCanonicalNode(base)) {
          selfRead = true;
          break;
        }
      }
      if (selfRead)
        CGP.addAssignmentEdge(
            CGP.getRepDerefNode(CGP.getCanonicalNode(base)), dstNode);
    }
  }
}

// Kernel code tags ALIGNED pointers in their low bits (p|1 to mark,
// p&~1 to clear, v&7 to extract the tag). Sub-alignment constant
// bit-twiddling never changes the field offset, so a ptrtoint whose
// COMPLETE local use-closure is tag ops + compares + tag extraction +
// inttoptr round trips is not a field escape: the plain a-edges
// already model it exactly (shift 0) and the fx wildcard would only
// smear. Any other use — store/call/ret (downstream rebasing through
// memory is covered ONLY by the source wildcard), offset-destroying
// masks (& ~0xfff), variable or non-tag arithmetic — keeps the
// wildcard. Bounded walk; on cap, keep the wildcard (sound default).
// Census (--cfl-census-type-rej): when a p2i escape wildcards, classify
// WHY the tag-round-trip proof failed, over the FULL user cone (the
// prover bails at the first kill; the census keeps walking so an escape
// is judged by everything it does). Sizes the recoverable slice — a
// cone whose only kill is CONST_ADDSUB is exactly what a
// delta-carrying walker with f_(delta mod P) sink edges keeps exact —
// against the irreducible classes (dynamic arithmetic = array indexing
// in int clothes; offset-destroying masks; memory/call boundary
// escapes where restoration happens after a reload).
enum P2IKill : unsigned {
  K_CONST_ADDSUB = 1u << 0,
  K_DYN_ADDSUB = 1u << 1,
  K_DESTROY_MASK = 1u << 2,
  K_OTHER_BINOP = 1u << 3,
  K_STORE = 1u << 4,
  K_CALLRET = 1u << 5,
  K_TRUNC = 1u << 6,
  K_OTHER = 1u << 7,
  K_CAP = 1u << 8,
};
static unsigned p2iEscapeKillMask(const Value *PTI) {
  unsigned mask = 0;
  SmallVector<const Value *, 16> wl{PTI};
  SmallPtrSet<const Value *, 32> seen{PTI};
  unsigned steps = 0;
  while (!wl.empty()) {
    if (++steps > 256) {
      mask |= K_CAP;
      break;
    }
    const Value *V = wl.pop_back_val();
    for (const User *U : V->users()) {
      if (isa<IntToPtrInst>(U) || isa<ICmpInst>(U) || isa<SwitchInst>(U))
        continue;
      if (const auto *BO = dyn_cast<BinaryOperator>(U)) {
        const auto *CI = dyn_cast<ConstantInt>(
            BO->getOperand(BO->getOperand(0) == V ? 1 : 0));
        switch (BO->getOpcode()) {
        case Instruction::Add:
        case Instruction::Sub:
          mask |= CI ? K_CONST_ADDSUB : K_DYN_ADDSUB;
          break;
        case Instruction::Or:
        case Instruction::Xor:
          if (!CI || CI->getZExtValue() >= 8)
            mask |= K_DESTROY_MASK;
          break;
        case Instruction::And:
          if (CI && CI->getZExtValue() < 8)
            continue; // tag extraction: no pointer in result
          if (!CI || ~CI->getZExtValue() >= 8)
            mask |= K_DESTROY_MASK;
          break;
        default:
          mask |= K_OTHER_BINOP;
          break;
        }
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      if (isa<StoreInst>(U)) {
        mask |= K_STORE;
        continue;
      }
      if (isa<CallBase>(U) || isa<ReturnInst>(U)) {
        mask |= K_CALLRET;
        continue;
      }
      if (isa<TruncInst>(U)) {
        mask |= K_TRUNC;
        continue;
      }
      if (isa<ZExtInst>(U) || isa<BitCastInst>(U) || isa<FreezeInst>(U) ||
          isa<PHINode>(U) || isa<SelectInst>(U)) {
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      mask |= K_OTHER;
    }
  }
  return mask;
}

static void p2iEscapeCensus(const Value *PTI, const char *where) {
  if (!CFLCensusTypeRej)
    return;
  unsigned mask = p2iEscapeKillMask(PTI);
  std::string s;
  auto add = [&](unsigned bit, const char *name) {
    if (mask & bit) {
      if (!s.empty())
        s += ',';
      s += name;
    }
  };
  add(K_CONST_ADDSUB, "const-addsub");
  add(K_DYN_ADDSUB, "dyn-addsub");
  add(K_DESTROY_MASK, "destroy-mask");
  add(K_OTHER_BINOP, "other-binop");
  add(K_STORE, "store");
  add(K_CALLRET, "callret");
  add(K_TRUNC, "trunc");
  add(K_OTHER, "other");
  add(K_CAP, "cap");
  if (s.empty())
    s = "none"; // prover bailed on step cap only
  const Function *F = nullptr;
  if (const auto *I = dyn_cast<Instruction>(PTI))
    F = I->getFunction();
  errs() << "P2I-ESCAPE-KILL(" << where << ") " << s << " in "
         << (F ? F->getName() : StringRef("<constexpr>")) << "\n";
}

static bool ptrToIntTagRoundTripOnly(const Value *PTI) {
  SmallVector<const Value *, 16> wl{PTI};
  SmallPtrSet<const Value *, 32> seen{PTI};
  g_tagWalkWhy = "";
  unsigned steps = 0;
  while (!wl.empty()) {
    if (++steps > 128) {
      g_tagWalkWhy = "depth";
      return false;
    }
    const Value *V = wl.pop_back_val();
    for (const User *U : V->users()) {
      if (isa<IntToPtrInst>(U) || isa<ICmpInst>(U) || isa<SwitchInst>(U))
        continue; // round trip at offset 0 / compare: exact
      if (const auto *BO = dyn_cast<BinaryOperator>(U)) {
        const auto *CI = dyn_cast<ConstantInt>(
            BO->getOperand(BO->getOperand(0) == V ? 1 : 0));
        if (!CI) {
          g_tagWalkWhy = "arith-var";
          return false;
        }
        const uint64_t c = CI->getZExtValue();
        switch (BO->getOpcode()) {
        case Instruction::Or:
        case Instruction::Xor:
          if (c >= 8) {
            g_tagWalkWhy = "orxor-big";
            return false; // beyond sub-alignment bits
          }
          break;
        case Instruction::And:
          if (c < 8)
            continue; // tag EXTRACTION: result carries no pointer
          if (~c >= 8) {
            g_tagWalkWhy = "mask-destroy";
            return false; // offset-destroying mask (& ~0xfff et al.)
          }
          break; // tag clear (& ~7 and finer)
        default:
          g_tagWalkWhy = BO->getOpcode() == Instruction::Add   ? "add-const"
                         : BO->getOpcode() == Instruction::Sub ? "sub-const"
                                                               : "arith-const";
          return false;
        }
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      if (isa<ZExtInst>(U) || isa<BitCastInst>(U) || isa<FreezeInst>(U) ||
          isa<PHINode>(U) || isa<SelectInst>(U)) {
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      if (isa<TruncInst>(U)) {
        // Residue-neutral: truncation keeps the LOW bits, where all
        // offset arithmetic lives; walking through (instead of
        // bailing) still catches downstream offset-destroyers.
        // Sub-pointer-width MEMORY crossings stay out of scope: the
        // witnessed store/load modeling is ptr-width-gated, so a
        // narrowed value that crosses memory carries no facts either
        // way (declared residual — 32-bit slots cannot hold a kernel
        // VA without out-of-band high bits).
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      // SEGMENT-LOCAL PROOF BOUNDARIES (2026-08-13): memory and calls
      // cannot compute, so offset arithmetic lives only in register
      // segments between provenance boundaries. Each boundary is a
      // SAFE STOP here because the segment on the other side gets its
      // own tag-cleanliness check at its head (int loads, call
      // results, formals — see the int-segment consumer checks), and
      // the fact plumbing across the boundary is residue-preserving
      // (witnessed int store/load/ret/arg wiring).
      if (const auto *SI = dyn_cast<StoreInst>(U)) {
        if (SI->getValueOperand() == V)
          continue; // value crosses into memory; load side re-proves
        g_tagWalkWhy = "int-as-addr";
        return false; // int as store ADDRESS: not expressible, bail
      }
      if (isa<ReturnInst>(U))
        continue; // caller side re-proves at the call result
      if (const auto *CB = dyn_cast<CallBase>(U)) {
        if (CB->getCalledOperand() != V)
          continue; // argument: callee side re-proves at the formal
        g_tagWalkWhy = "int-as-callee";
        return false; // int called as function: nonsense, bail
      }
      if (const auto *GEP2 = dyn_cast<GetElementPtrInst>(U)) {
        if (GEP2->getPointerOperand() != V)
          continue; // used as INDEX only: result inherits the BASE's
                    // provenance (no edge from indices), the escaped
                    // int never re-becomes a pointer to the source
        g_tagWalkWhy = "int-as-gep-base";
        return false;
      }
      if (const auto *RMW = dyn_cast<AtomicRMWInst>(U)) {
        if (RMW->getValOperand() == V &&
            RMW->getOperation() == AtomicRMWInst::Xchg)
          continue; // pure store: consumer side re-proves the result
        g_tagWalkWhy = "rmw-arith";
        return false; // arithmetic RMW COMPUTES in memory — bail
      }
      if (const auto *CX = dyn_cast<AtomicCmpXchgInst>(U)) {
        if (CX->getNewValOperand() == V || CX->getCompareOperand() == V)
          continue; // conditional store / compare-only
        g_tagWalkWhy = "cmpxchg";
        return false;
      }
      if (isa<ExtractValueInst>(U)) { // {old,i1} projection of cmpxchg
        if (seen.insert(U).second)
          wl.push_back(U);
        continue;
      }
      g_tagWalkWhy = "user-unmodeled";
      return false;
    }
  }
  return true;
}

void CallGraphPass::InstHandler::visitPtrToIntInst(PtrToIntInst &I) {
  NodeIndex srcNode = CGP.getRepNodeForValue(I.getOperand(0));
  if (srcNode == AndersNodeFactory::InvalidIndex) {
    WARNING("PtrToInt: src node not found: " << I << "\n");
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
    CG_DEBUG("PtrToInt: created value node " << dstNode << " for " << I << "\n");
  }
  CG_DEBUG("PtrToInt: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  // Field mode: integer arithmetic on the escaped pointer can rebase it to
  // any field (disguised GEP); absorb with the wildcard loop at the source
  // — EXCEPT proven tag-bit round trips, which are exact at shift 0.
  if (CGP.Graph.fieldSensitive()) {
    if (ptrToIntTagRoundTripOnly(&I)) {
      g_tagRoundTrips++;
    } else {
      p2iEscapeCensus(&I, "inst");
      CGP.addFieldWildcardLoop(srcNode, tagWalkTag("ptrtoint-escape").c_str());
    }
  }
  CGP.addAssignmentEdge(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitBinaryOperator(BinaryOperator &I) {
  if (!I.getType()->isIntegerTy())
    return;

  // Emit a-edges from EVERY pointer-derived operand to the result, per
  // the encoding spec (operand_i -> result). The previous "other
  // operand must be constant" guard WARNed-and-dropped exactly the
  // offset_to_ptr / PREL32 consumer shape the kernel uses for
  // initcalls and pci_fixup: fn = add(ptrtoint base, sext(*entry)).
  NodeIndex dstNode = AndersNodeFactory::InvalidIndex;
  for (unsigned i = 0; i < 2; i++) {
    NodeIndex n = CGP.getRepNodeForValue(I.getOperand(i));
    if (n == AndersNodeFactory::InvalidIndex || CGP.NF.isSpecialNode(n))
      continue;
    if (dstNode == AndersNodeFactory::InvalidIndex) {
      dstNode = CGP.getRepNodeForValue(&I);
      if (dstNode == AndersNodeFactory::InvalidIndex) {
        dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
        CG_DEBUG("BinOp: created value node " << dstNode << " for " << I << "\n");
      }
    }
    CG_DEBUG("BinOp: " << n << " -> " << dstNode << " for " << I << "\n");
    CGP.addAssignmentEdge(n, dstNode);
  }
}

void CallGraphPass::InstHandler::visitVAArgInst(VAArgInst &I) {
  if (!I.getType()->isPointerTy())
    return;

  NodeIndex valNode = CGP.NF.getValueNodeFor(&I);
  if (valNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: result node not found: " << I << "\n");
    return;
  }

  // The va_list object's content (va_start wrote it, possibly in the
  // caller that passed this va_list down).
  if (NodeIndex lp = CGP.getRepNodeForValue(I.getPointerOperand());
      lp != AndersNodeFactory::InvalidIndex)
    CGP.addAssignmentEdge(CGP.getRepDerefNode(lp), valNode);
  Function *F = I.getParent()->getParent();
  NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
  if (varargNode == AndersNodeFactory::InvalidIndex)
    return; // a va_list received as a parameter: read through it above

  CG_DEBUG("VAArg: " << F->getName() << ": vararg node " << varargNode
           << " -> val node " << valNode << " for " << I << "\n");
  CGP.addAssignmentEdge(varargNode, valNode);
}

// va_start writes the function's variadic arguments into the va_list
// object; va_copy copies that object. va_arg (and its lowered loads)
// read it, so a va_list passed to another function carries its
// arguments as an ordinary pointer to the same object.
void CallGraphPass::InstHandler::visitVAStartInst(VAStartInst &I) {
  Function *F = I.getFunction();
  NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
  if (varargNode == AndersNodeFactory::InvalidIndex)
    varargNode = CGP.NF.createVarargNode(F);
  NodeIndex listNode = CGP.getRepNodeForValue(I.getArgList());
  if (listNode == AndersNodeFactory::InvalidIndex)
    return;
  CellWriteSize ws(CGP, 0);
  CGP.addAssignmentEdge(CGP.getCanonicalNode(varargNode),
                        CGP.getRepDerefNode(listNode));
}

void CallGraphPass::InstHandler::visitVACopyInst(VACopyInst &I) {
  NodeIndex dst = CGP.getRepNodeForValue(I.getDest());
  NodeIndex src = CGP.getRepNodeForValue(I.getSrc());
  if (dst == AndersNodeFactory::InvalidIndex ||
      src == AndersNodeFactory::InvalidIndex)
    return;
  CellWriteSize ws(CGP, 0);
  CGP.addAssignmentEdge(CGP.getRepDerefNode(src), CGP.getRepDerefNode(dst));
}

void CallGraphPass::InstHandler::visitMemTransferInst(MemTransferInst &I) {
  // MemTransferInst covers memcpy and memmove intrinsics
  CGP.handleMemcpy(&I);
  // Record call graph edge for the intrinsic
  if (Function *CF = I.getCalledFunction())
    CGP.Ctx->Callees[&I].insert(CF);
}

void CallGraphPass::InstHandler::visitMemSetInst(MemSetInst &I) {
  // MemSetInst covers memset intrinsics
  // For pointer analysis, memset doesn't transfer pointers, so we can ignore it
  CG_DEBUG("MemSet instruction (ignored for pointer analysis): " << I << "\n");
  // Record call graph edge for the intrinsic
  if (Function *CF = I.getCalledFunction())
    CGP.Ctx->Callees[&I].insert(CF);
}

void CallGraphPass::InstHandler::visitExtractElementInst(ExtractElementInst &I) {
  // Only when extracting a pointer from <N x ptr>
  if (!I.getType()->isPointerTy())
    return;

  Value *vec = I.getVectorOperand();
  NodeIndex vecNode = CGP.getRepNodeForValue(vec);
  if (vecNode == AndersNodeFactory::InvalidIndex) {
    CG_DEBUG("ExtractElement: vec node not found for " << *vec << "\n");
    return;
  }
  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex) {
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  }
  CGP.addAssignmentEdge(vecNode, resNode);
}

void CallGraphPass::InstHandler::visitInsertElementInst(InsertElementInst &I) {
  if (!containsPointerType(I.getType()))
    return;

  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex) {
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  }

  // Propagate the scalar pointer element into the vector
  Value *elt = I.getOperand(1);
  if (containsPointerType(elt->getType())) {
    NodeIndex eltNode = CGP.getRepNodeForValue(elt);
    if (eltNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(eltNode, resNode);
  }

  // Propagate existing elements from the source vector
  Value *vec = I.getOperand(0);
  if (!isa<UndefValue>(vec)) {
    NodeIndex vecNode = CGP.getRepNodeForValue(vec);
    if (vecNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(vecNode, resNode);
  }
}

void CallGraphPass::InstHandler::visitShuffleVectorInst(ShuffleVectorInst &I) {
  if (!containsPointerType(I.getType()))
    return;

  NodeIndex resNode = CGP.getRepNodeForValue(&I);
  if (resNode == AndersNodeFactory::InvalidIndex) {
    resNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
  }

  for (unsigned i = 0; i < 2; i++) {
    Value *vec = I.getOperand(i);
    if (isa<UndefValue>(vec))
      continue;
    NodeIndex vecNode = CGP.getRepNodeForValue(vec);
    if (vecNode != AndersNodeFactory::InvalidIndex)
      CGP.addAssignmentEdge(vecNode, resNode);
  }
}

// The named struct a literal-typed global is read as: the one struct its
// GEPs index it as (element type for an array of structs), else the
// struct its debug info declares; nullptr when neither names exactly
// one struct. Several unrelated GEP types are a pun: they are opened.
llvm::StructType *CallGraphPass::initUseTypeOf(const GlobalVariable *GV) {
  auto it = initUseType.find(GV);
  if (it != initUseType.end())
    return it->second;
  llvm::SmallVector<llvm::StructType *, 2> types;
  for (const User *U : GV->users()) {
    const auto *G = dyn_cast<GEPOperator>(U);
    if (!G || G->getPointerOperand()->stripPointerCasts() != GV)
      continue;
    Type *T = G->getSourceElementType();
    while (T->isArrayTy())
      T = T->getArrayElementType();
    auto *ST = dyn_cast<llvm::StructType>(T);
    if (!ST || ST->isLiteral() || !ST->hasName() ||
        LLVM_STRING_STARTS_WITH(ST->getName(), "union"))
      continue;
    if (std::find(types.begin(), types.end(), ST) == types.end())
      types.push_back(ST);
  }
  llvm::StructType *S = nullptr;
  if (types.size() == 1) {
    S = types[0];
  } else if (types.size() > 1) {
    for (llvm::StructType *T : types)
      openStruct(T, "init-pun:" + GV->getName().str());
  } else {
    llvm::SmallVector<DIGlobalVariableExpression *, 1> DIs;
    GV->getDebugInfo(DIs);
    for (auto *E : DIs) {
      const DIType *T = E->getVariable()->getType();
      while (const auto *D = dyn_cast_or_null<DIDerivedType>(T)) {
        if (D->getTag() != dwarf::DW_TAG_typedef &&
            D->getTag() != dwarf::DW_TAG_const_type &&
            D->getTag() != dwarf::DW_TAG_volatile_type)
          break;
        T = D->getBaseType();
      }
      while (const auto *C = dyn_cast_or_null<DICompositeType>(T)) {
        if (C->getTag() != dwarf::DW_TAG_array_type)
          break;
        T = C->getBaseType();
        while (const auto *D = dyn_cast_or_null<DIDerivedType>(T)) {
          if (D->getTag() != dwarf::DW_TAG_typedef &&
              D->getTag() != dwarf::DW_TAG_const_type)
            break;
          T = D->getBaseType();
        }
      }
      const auto *C = dyn_cast_or_null<DICompositeType>(T);
      if (!C || C->getTag() != dwarf::DW_TAG_structure_type ||
          C->getName().empty())
        continue;
      const std::string want = ("struct." + C->getName()).str();
      for (llvm::StructType *ST : GV->getParent()->getIdentifiedStructTypes())
        if (ST->hasName() && stripStructNameSuffix(ST->getName()) == want) {
          S = ST;
          break;
        }
      if (S)
        break;
    }
  }
  initUseType.emplace(GV, S);
  return S;
}

llvm::StructType *CallGraphPass::formalStruct(const Function *F,
                                              unsigned ArgNo) {
  const uint64_t key = ((uint64_t)(uintptr_t)F << 8) ^ ArgNo;
  auto it = formalStructCache.find(key);
  if (it != formalStructCache.end())
    return it->second;
  llvm::StructType *S = nullptr;
  if (const DISubprogram *SP = F->getSubprogram())
    if (const DISubroutineType *ST = SP->getType()) {
      auto Types = ST->getTypeArray();
      if (ArgNo + 1 < Types.size())
        S = accessNames->structByTag(F->getParent(),
                                     ka::diStructName(Types[ArgNo + 1], true));
    }
  if (!S && ArgNo < F->arg_size()) {
    // The one struct the body indexes the formal as (directly, or through
    // the stack slot it is spilled to at -O0).
    llvm::SmallVector<llvm::StructType *, 2> types;
    llvm::SmallVector<const Value *, 4> ptrs{F->getArg(ArgNo)};
    for (const User *U : F->getArg(ArgNo)->users())
      if (const auto *SI = dyn_cast<StoreInst>(U))
        if (SI->getValueOperand() == F->getArg(ArgNo))
          if (const auto *AI = dyn_cast<AllocaInst>(
                  SI->getPointerOperand()->stripPointerCasts()))
            for (const User *U2 : AI->users())
              if (const auto *LI = dyn_cast<LoadInst>(U2))
                ptrs.push_back(LI);
    for (const Value *Pv : ptrs)
      for (const User *U : Pv->users())
        if (const auto *G = dyn_cast<GEPOperator>(U))
          if (G->getPointerOperand()->stripPointerCasts() == Pv)
            if (auto *St = dyn_cast<llvm::StructType>(G->getSourceElementType()))
              if (!St->isLiteral() && St->hasName() &&
                  !LLVM_STRING_STARTS_WITH(St->getName(), "union") &&
                  std::find(types.begin(), types.end(), St) == types.end())
                types.push_back(St);
    if (types.size() == 1)
      S = types[0];
  }
  formalStructCache.emplace(key, S);
  return S;
}

// A pointer-carrying initializer constant `val` written into `cell`: with
// named cells it is also filed under the slot's name (initNamedS,
// initOff), or in the cell's unnamed shadow when the slot has none.
void CallGraphPass::initSlotWrite(NodeIndex val, NodeIndex cell) {
  Graph.addCopy(val, cell);
  if (!namedPlanes())
    return;
  uint32_t name = ka::AccessNames::Unnamed;
  const uint64_t psz = curDL->getPointerSize();
  const std::string gvName =
      "init:" + (initGV ? initGV->getName().str() : std::string("?"));
  if (initNamedS && !initUnion) {
    name = accessNames->ofSlot(initNamedS, initOff, psz, *curDL);
    if (name == ka::AccessNames::Unnamed)
      openStruct(initNamedS, gvName);
  } else if (initNamedS) { // a union member: read elsewhere as its type
    openStruct(initNamedS, gvName);
  } else if (initGV) {
    // A literal-typed global (designated initializers, unions, bit-
    // fields): its slots are named by the struct the program reads it
    // as (initUseTypeOf); without one they are the counted blind spot.
    if (llvm::StructType *S = initUseTypeOf(initGV)) {
      const uint64_t sz = curDL->getTypeAllocSize(S);
      name = accessNames->ofSlot(S, sz ? initAbsOff % sz : initAbsOff, psz,
                                 *curDL);
      if (name == ka::AccessNames::Unnamed)
        openStruct(S, gvName);
    } else {
      blindWrites++;
      blindBy[gvName]++;
      if ((CFLCensusTypeLabels || !CFLRuleReport.empty()))
        blindWriteLog.emplace_back(cell, gvName);
    }
  }
  if (name == ka::AccessNames::Unnamed)
    Graph.addCopy(val, namedShadow(cell, name));
  else
    fileNamedWrite(val, cell, name);
  (name == ka::AccessNames::Unnamed ? namedStats.unnamedSlots
                                    : namedStats.namedSlots)++;
}

// Process global variable initializer. Field-insensitive by default: every
// pointer in the initializer assigns into `ptrNode` (the global's deref cell).
// In field mode (`addrNode` valid), struct elements are routed into per-field
// cells reached through matched f-edges from the global's address node, so
// initializer contents stay field-separated like runtime stores.
void CallGraphPass::processInitializer(NodeIndex ptrNode, Constant *init,
                                        const std::string &enclosingStruct,
                                        int enclosingFieldIdx,
                                        NodeIndex addrNode) {
  if (!init)
    return;

  // Skip nullptr - don't create edges for null assignments
  if (isa<ConstantPointerNull>(init)) {
    CG_DEBUG("Skipping nullptr in initializer\n");
    return;
  }

  // Skip compiler-introduced values in initializers
  if (shouldSkipValue(init)) {
    CG_DEBUG("Skipping compiler value in initializer: " << *init << "\n");
    return;
  }

  // Aliases (e.g., aliased syscall wrappers) resolve to their aliasee so
  // function/global addresses stored through an alias are not dropped.
  if (auto *GA = dyn_cast<GlobalAlias>(init)) {
    auto *Aliasee = dyn_cast<Constant>(GA->getAliasee()->stripPointerCasts());
    assert(Aliasee && "GlobalAlias with non-constant aliasee in initializer");
    processInitializer(ptrNode, Aliasee, enclosingStruct, enclosingFieldIdx,
                       addrNode);
    return;
  }

  if (isa<GlobalVariable>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &globalvar: add assignment edges globalvar_val -> ptr
    initSlotWrite(valNode, ptrNode);
    CG_DEBUG("add CFL assignment edges for global variable " << cast<GlobalVariable>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (isa<Function>(init)) {
    auto *storedFunc = cast<Function>(init);
    Function *canonStoredFunc = getFuncDef(storedFunc);
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &function: add assignment edges function_val -> ptr
    initSlotWrite(valNode, ptrNode);
    // Record direct function store into struct field. A store WITHOUT a
    // derivable key (literal-struct initializer like sysctl tables, plain
    // global, top-level array) must mark the function evidence-incomplete:
    // otherwise named-struct evidence collected elsewhere would wrongly
    // reject callsites that load from the keyless location (the access
    // side may still see a named struct type, e.g. kern_table's literal
    // [38 x {ptr,...}] read through %struct.ctl_table geps).
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      funcFieldStores[canonStoredFunc].insert(
          {enclosingStruct, static_cast<unsigned>(enclosingFieldIdx)});
    else
      funcFieldStoresIncomplete.insert(canonStoredFunc);
    CG_DEBUG("add CFL assignment edges for function " << storedFunc->getName()
             << " -> " << ptrNode << "\n");
  } else if (ConstantArray *CA = dyn_cast<ConstantArray>(init)) {
    // Arrays are collapsed: all elements share the array's cell.
    const uint64_t savedAbs = initAbsOff;
    const uint64_t esz =
        curDL ? curDL->getTypeAllocSize(CA->getType()->getElementType()) : 0;
    for (unsigned i = 0; i != CA->getNumOperands(); ++i) {
      initAbsOff = savedAbs + i * esz;
      processInitializer(ptrNode, CA->getOperand(i), enclosingStruct,
                         enclosingFieldIdx, addrNode);
    }
    initAbsOff = savedAbs;
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(init)) {
    StructType *STy = CS->getType();
    const bool isUnion = STy && STy->hasName() &&
                         LLVM_STRING_STARTS_WITH(STy->getStructName(), "union");
    // Named-cell slot position of each element (initSlotWrite).
    StructType *const savedS = initNamedS;
    const uint64_t savedOff = initOff;
    const bool savedUnion = initUnion;
    const StructLayout *NL =
        (namedPlanes() && !isUnion) ? curDL->getStructLayout(STy) : nullptr;
    const uint64_t savedAbs = initAbsOff;
    const bool namedTy = !STy->isLiteral() && STy->hasName();
    const bool fieldMode = Graph.fieldSensitive() &&
                           addrNode != AndersNodeFactory::InvalidIndex &&
                           curDL && STy;
    const StructLayout *SL =
        (fieldMode && !isUnion) ? curDL->getStructLayout(STy) : nullptr;
    if (fieldMode && isUnion) {
      // Union members overlay; keep them in the parent cell and absorb any
      // deeper field access with the wildcard loop.
      addFieldWildcardLoop(addrNode, "union-initializer");
    }
    for (unsigned i = 0; i != CS->getNumOperands(); ++i) {
      std::string curStruct = enclosingStruct;
      int curField = enclosingFieldIdx;
      if (STy && !STy->isLiteral() && STy->hasName() && !isUnion) {
        curStruct = stripStructNameSuffix(STy->getStructName()).str();
        curField = i;
      }
      NodeIndex childCell = ptrNode;
      NodeIndex childAddr = addrNode;
      if (SL) {
        int64_t off = (int64_t)SL->getElementOffset(i);
        if (off != 0) {
          NodeIndex parentCanon = getCanonicalNode(addrNode);
          childAddr = getFieldPtrNode(parentCanon, off);
          addFieldEdgesExact(parentCanon, getCanonicalNode(childAddr), off, 0,
                             false, STy);
        }
        childCell = getRepDerefNode(childAddr);
      }
      if (isUnion) {
        initUnion = true;
      } else if (NL && (namedTy || savedS)) {
        initNamedS = namedTy ? STy : savedS;
        initOff = (namedTy ? 0 : savedOff) + NL->getElementOffset(i);
      }
      if (NL)
        initAbsOff = savedAbs + NL->getElementOffset(i);
      processInitializer(childCell, CS->getOperand(i), curStruct, curField,
                         childAddr);
      initNamedS = savedS;
      initOff = savedOff;
      initUnion = savedUnion;
      initAbsOff = savedAbs;
    }
  } else if (ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(init)) {
    Type *Ty = CAZ->getType();
    if (isa<ArrayType>(Ty) || isa<VectorType>(Ty)) {
      processInitializer(ptrNode, CAZ->getSequentialElement(), enclosingStruct, enclosingFieldIdx);
    } else if (StructType *CSTy = dyn_cast<StructType>(Ty)) {
      for (unsigned i = 0; i != CSTy->getNumElements(); ++i) {
        std::string curStruct = enclosingStruct;
        int curField = enclosingFieldIdx;
        if (!CSTy->isLiteral() && CSTy->hasName() &&
            !LLVM_STRING_STARTS_WITH(CSTy->getStructName(), "union")) {
          curStruct = stripStructNameSuffix(CSTy->getStructName()).str();
          curField = i;
        }
        Constant *elem = CAZ->getStructElement(i);
        processInitializer(ptrNode, elem, curStruct, curField);
      }
    }
  } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(init)) {
    switch (CE->getOpcode()) {
      case Instruction::GetElementPtr: {
        // Field mode: store the canonical constant-GEP field pointer itself
        // (its f-edges from the base are ensured on lookup), keeping the
        // stored address field-precise.
        if (Graph.fieldSensitive()) {
          NodeIndex ceNode = getRepNodeForValue(CE);
          if (ceNode != AndersNodeFactory::InvalidIndex) {
            initSlotWrite(ceNode, ptrNode);
            break;
          }
        }
        // Field-insensitive: get the base pointer with casts stripped
        const GEPOperator *GEPOp = cast<GEPOperator>(CE);
        const Value* basePtr = GEPOp->getPointerOperand()->stripPointerCasts();
        NodeIndex baseNode = NF.getValueNodeFor(basePtr);
        if (baseNode == AndersNodeFactory::InvalidIndex) {
          baseNode = NF.createValueNode(basePtr);
        }
        // ptr = base_ptr: add assignment edges base_ptr -> ptr
        initSlotWrite(baseNode, ptrNode);
        break;
      }
      case Instruction::BitCast: {
        // BitCast: process the operand directly
        processInitializer(ptrNode, CE->getOperand(0), enclosingStruct, enclosingFieldIdx);
        break;
      }
      case Instruction::IntToPtr: {
        // ptr = (ptr)int: add assignment edges constantInt -> ptr
        // Graph.addCopy(NF.getConstantIntNode(), ptrNode);
        break;
      }
      case Instruction::PtrToInt: {
        // An address kept as a pointer-width integer still carries the
        // address into the cell: Itanium member-function pointers are
        // {ptrtoint fn, adj} pairs (xpdf's Gfx::opTab: 73 operator
        // handlers were dropped here, so the dispatch at Gfx.cc:826 and
        // every call inside a handler resolved to nothing -- 73 of 535
        // fuzz-observed pdftotext targets missed; with this case
        // 535/535, 2026-09-27). Loads of such slots are integer loads;
        // the witnessed int-provenance rules carry them to inttoptr.
        processInitializer(ptrNode, CE->getOperand(0), enclosingStruct,
                           enclosingFieldIdx, addrNode);
        break;
      }
      default:
        if (constantHasPtrToInt(CE, 6) ||
            llvm::any_of(CE->operands(), [](const Use &U) {
              return U->getType()->isPointerTy();
            }))
          g_initCEDeclined++;
        CG_DEBUG("Unhandled constant expression: " << *init << "\n");
    }
  }
}

void CallGraphPass::processCtorsDtors(Module *M) {
  for (StringRef Name : {"llvm.global_ctors", "llvm.global_dtors"}) {
    GlobalVariable *GV = M->getGlobalVariable(Name);
    if (!GV || !GV->hasInitializer())
      continue;
    ConstantArray *CA = dyn_cast<ConstantArray>(GV->getInitializer());
    if (!CA)
      continue;
    for (auto &Op : CA->operands()) {
      if (isa<ConstantAggregateZero>(Op))
        continue;
      ConstantStruct *CS = cast<ConstantStruct>(Op);
      // Operand 1 is the function pointer
      if (Function *F = dyn_cast<Function>(CS->getOperand(1))) {
        auto *RF = getFuncDef(F);
        if (Ctx->CtorDtorFuncs.insert(RF).second)
          CG_LOG("CtorDtor: " << Name << " -> " << RF->getName() << "\n");
      }
    }
  }
}

void CallGraphPass::collectIFuncTargets(const GlobalIFunc *IF) {
  Function *Resolver = const_cast<GlobalIFunc*>(IF)->getResolverFunction();
  if (!Resolver || Resolver->isDeclaration()) {
    CG_DEBUG("IFunc: " << IF->getName() << " resolver not available\n");
    return;
  }
  FuncSet &Targets = IFuncTargets[IF];
  for (auto &BB : *Resolver) {
    if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
      if (!RI->getReturnValue())
        continue;
      Value *RV = RI->getReturnValue()->stripPointerCasts();
      if (auto *F = dyn_cast<Function>(RV)) {
        Targets.insert(getFuncDef(F));
      } else if (auto *LI = dyn_cast<LoadInst>(RV)) {
        // Handle pattern: store @func, %alloca; ... %rv = load %alloca; ret %rv
        Value *Ptr = LI->getPointerOperand();
        for (User *U : Ptr->users()) {
          if (auto *SI = dyn_cast<StoreInst>(U)) {
            if (SI->getPointerOperand() == Ptr) {
              if (auto *F = dyn_cast<Function>(SI->getValueOperand()->stripPointerCasts()))
                Targets.insert(getFuncDef(F));
            }
          }
        }
      }
    }
  }
  CG_LOG("IFunc: " << IF->getName() << " resolved via " << Resolver->getName()
         << " to " << Targets.size() << " target(s)\n");
  for (const Function *T : Targets)
    CG_LOG("  IFunc target: " << T->getName() << "\n");
}

// task #22 phase B: alias undefined linker-array bounds externs to their
// section members. The linker concatenates section-X items between
// __start_X/__stop_X; consumers iterate from the bounds symbol and
// either load members directly (ABS64 arrays: __param, .init.setup,
// _ftrace_events) or compute fn = entry + *entry (PREL32: initcalls,
// pci_fixup) — there the register-provenance chain (ptrtoint/add/
// inttoptr, all visited) carries the bounds symbol's VALUE to the
// consumer, so a-edges member -> bounds cover both shapes under the
// field-insensitive memory model.
// candidate section keys for a bounds symbol name; kernel bounds are
// either generic (__start_X/__stop_X <-> section X modulo _/. prefix)
// or hand-written in vmlinux.lds (the irregulars below)
bool linkerBoundsSectionKeys(StringRef N, std::vector<std::string> &exact,
                                    std::vector<std::string> &prefix) {
    StringRef K;
    if (N.starts_with("__start_")) {
      K = N.drop_front(8);
    } else if (N.starts_with("__stop_")) {
      K = N.drop_front(7);
    } else if (N.starts_with("__") &&
               (N.ends_with("_start") || N.ends_with("_end"))) {
      K = N.drop_back(N.ends_with("_start") ? 6 : 4);
      exact.push_back(K.str()); // e.g. __governor_thermal_table
      K = K.drop_front(2);      // e.g. initcall5, setup, con_initcall
    } else {
      return false;
    }
    exact.push_back(K.str());         // __param, __tracepoints_ptrs
    exact.push_back(("_" + K).str()); // _ftrace_events
    exact.push_back(("." + K).str()); // .apicdrivers
    if (K.starts_with("initcall")) {
      // per-level bounds delimit a contiguous run of .initcallN.init
      // sections; the union of all levels over-approximates soundly
      prefix.push_back(".initcall");
    } else if (K == "setup") {
      exact.push_back(".init.setup");
    } else if (K == "con_initcall") {
      exact.push_back(".con_initcall.init");
    } else if (K == "_bpf_raw_tp") {
      exact.push_back("__bpf_raw_tp_map");
    } else if (K.starts_with("pci_fixups_")) {
      exact.push_back((".pci_fixup_" + K.drop_front(11)).str());
    } else if (K == "ftrace_eval_maps") {
      exact.push_back("_ftrace_eval_map");
    }
    return true;
}

// union of members over the bounds symbol's candidate sections; sets
// *unresolved when any matched section had symbol-looking module-asm
// entries that resolve to nothing (membership incomplete)
bool CallGraphPass::linkerArraySources(StringRef boundsName,
                                       std::set<const GlobalValue *> &inPlace,
                                       std::set<const GlobalValue *> &encoded,
                                       bool *unresolved) {
  if (unresolved) *unresolved = false;
  std::vector<std::string> exact, prefix;
  if (!linkerBoundsSectionKeys(boundsName, exact, prefix)) return false;
  auto take = [&](const std::string &sec) {
    auto ip = linkerSectionInPlace.find(sec);
    if (ip != linkerSectionInPlace.end())
      inPlace.insert(ip->second.begin(), ip->second.end());
    auto en = linkerSectionEncoded.find(sec);
    if (en != linkerSectionEncoded.end())
      encoded.insert(en->second.begin(), en->second.end());
    if (unresolved && linkerSectionUnresolved.count(sec))
      *unresolved = true;
  };
  auto takePrefix = [&](const std::string &p,
                        const std::map<std::string,
                                       std::set<const GlobalValue *>> &m) {
    for (auto it = m.lower_bound(p);
         it != m.end() && StringRef(it->first).starts_with(p); ++it)
      take(it->first);
  };
  for (const std::string &k : exact) take(k);
  for (const std::string &p : prefix) {
    takePrefix(p, linkerSectionInPlace);
    takePrefix(p, linkerSectionEncoded);
  }
  return true;
}

void CallGraphPass::wireLinkerSectionArrays() {
  if (!CFLLinkerArrays) return;
  size_t wired = 0, matched = 0, unmatched = 0, nodeless = 0;
  size_t excluded = 0, keptUniversal = 0;
  for (const auto &[guid, EGV] : Ctx->ExtGobjs) {
    StringRef N = EGV->getName();
    std::vector<std::string> exact, prefix;
    if (!linkerBoundsSectionKeys(N, exact, prefix)) continue;
    if (linkerExcludedFamily(N)) {
      excluded++;
      CG_DEBUG("LinkerArrays: bounds " << N
               << " excluded (metadata/patching/module-linking family)\n");
      continue;
    }
    bool unresolved = false;
    std::set<const GlobalValue *> inPlace, encoded;
    linkerArraySources(N, inPlace, encoded, &unresolved);
    if (unresolved) {
      // membership incomplete: symbol keeps the universal fallback,
      // which already over-approximates its reads — wiring would only
      // re-inject members into the universal hub
      keptUniversal++;
      CG_LOG("LinkerArrays: LEDGER bounds " << N
             << " kept universal (unresolved section entries)\n");
      continue;
    }
    if (inPlace.empty() && encoded.empty()) {
      // bounds over metadata sections (orc, bug/ex tables) or arrays
      // with no member in the corpus — ledgered, not silently dropped
      unmatched++;
      CG_DEBUG("LinkerArrays: bounds " << N
               << " has no IR-visible members\n");
      continue;
    }
    if (perTUSolve()) {
      // Per-TU compositional mode cannot compose these flows: the
      // member->bounds edges are added once, after the last module,
      // and belong to no TU's graph, so no TU exports the bounds
      // symbol the compose-time boundary sanity check demands — the
      // composed solve is guaranteed to be rejected many minutes from
      // now. Fail here, at the first wireable bounds symbol.
      errs() << "wireLinkerSectionArrays: bounds symbol " << N
             << " has IR-visible members, but per-TU compositional mode "
                "cannot compose linker-section-array flows. Rerun with "
                "--cfl-compositional=false, or drop the flows explicitly "
                "with --cfl-linker-arrays=false (UNSOUND for kernel "
                "corpora).\n";
      exit(1);
    }
    NodeIndex eNode = NF.getValueNodeFor(EGV);
    assert(eNode != AndersNodeFactory::InvalidIndex &&
           "ExtGobj without value node");
    size_t before = wired;
    auto resolveNode = [&](const GlobalValue *S) -> NodeIndex {
      NodeIndex sNode = NF.getValueNodeFor(S);
      if (sNode == AndersNodeFactory::InvalidIndex) {
        if (auto *F = dyn_cast<Function>(S)) {
          // cross-module asm reference whose defining module was
          // initialized before the reference was seen — mint now
          sNode = NF.createValueNode(F);
          Ctx->AddressTakenFuncs.insert(
              getFuncDef(const_cast<Function *>(F)));
        } else {
          nodeless++; // skipped compiler global — ledgered
        }
      }
      return sNode;
    };
    // In-place members ARE the array elements: the bounds symbol
    // aliases their objects (value edges). Encoded (PREL32) members
    // live in deref(bounds), read out by the offset_to_ptr pull rule.
    // Precision rests on the bounds symbol having its OWN identity
    // (extGobjOverride) — wiring into the universal fallback leaked
    // every member into all unmodeled-extern reads (whole kernel
    // +2.7M pairs, 72% pci-quirk stubs at unrelated icalls).
    for (const GlobalValue *S : inPlace) {
      NodeIndex sNode = resolveNode(S);
      if (sNode == AndersNodeFactory::InvalidIndex) continue;
      addAssignmentEdge(sNode, eNode);
      wired++;
    }
    for (const GlobalValue *S : encoded) {
      NodeIndex sNode = resolveNode(S);
      if (sNode == AndersNodeFactory::InvalidIndex) continue;
      addAssignmentEdge(sNode, getRepDerefNode(getCanonicalNode(eNode)));
      wired++;
    }
    if (wired > before) matched++;
    CG_DEBUG("LinkerArrays: " << N << " <- " << (wired - before)
             << " members\n");
  }
  CG_LOG("LinkerArrays: " << matched << " bounds symbols wired, " << wired
         << " member flows; LEDGER " << unmatched
         << " bounds without IR-visible members, " << excluded
         << " excluded metadata/patching/module-linking bounds, "
         << keptUniversal << " kept universal (unresolved entries), "
         << nodeless << " nodeless members skipped\n");
}

bool CallGraphPass::addFieldAlias(const FieldStoreKey &A, const FieldStoreKey &B) {
  if (A == B)
    return false;
  bool changed = false;
  changed |= fieldAliasMap[A].insert(B).second;
  changed |= fieldAliasMap[B].insert(A).second;
  return changed;
}

bool CallGraphPass::fieldFilterAccepts(const Function *F,
                                       const std::string &callSiteStruct,
                                       unsigned callSiteFieldIdx) const {
  const Function *canonF = F;
  if (F) {
    auto itDef = Ctx->Funcs.find(F->getGUID());
    if (itDef != Ctx->Funcs.end())
      canonF = itDef->second;
  }

  // A function with any unclassified address escape must never be rejected.
  if (funcFieldStoresIncomplete.count(canonF))
    return true;

  auto it = funcFieldStores.find(canonF);
  if (it == funcFieldStores.end())
    return true;
  const auto &fieldSet = it->second;
  if (fieldSet.empty())
    return true;

  FieldStoreKey callSiteKey{callSiteStruct, callSiteFieldIdx};
  if (fieldSet.count(callSiteKey))
    return true;

  SmallVector<FieldStoreKey, 16> work;
  std::unordered_set<FieldStoreKey, FieldStoreKeyHash> seen;
  work.push_back(callSiteKey);
  seen.insert(callSiteKey);

  constexpr size_t kMaxAliasVisits = 256;
  size_t visits = 0;
  while (!work.empty() && visits++ < kMaxAliasVisits) {
    FieldStoreKey cur = work.pop_back_val();
    auto aliasIt = fieldAliasMap.find(cur);
    if (aliasIt == fieldAliasMap.end())
      continue;
    for (const auto &aliasKey : aliasIt->second) {
      if (fieldSet.count(aliasKey))
        return true;
      if (seen.insert(aliasKey).second)
        work.push_back(aliasKey);
    }
  }

  // If the BFS was exhausted (worklist non-empty but visit limit reached),
  // conservatively accept to avoid unsound rejections.
  if (!work.empty())
    return true;

  return false;
}

void CallGraphPass::buildFieldStoreMapFromIR(Module *M) {
  size_t directStores = 0, callbackStores = 0, copyAliases = 0;
  auto addAggregateCopyAliases = [&](const Value *DstPtr, const Value *SrcPtr) {
    std::string dstStruct, srcStruct;
    unsigned dstField = 0, srcField = 0;
    Type *dstFieldTy = nullptr;
    Type *srcFieldTy = nullptr;

    bool hasDst = getFieldKeyFromPointerOperand(DstPtr, dstStruct, dstField, dstFieldTy);
    bool hasSrc = getFieldKeyFromPointerOperand(SrcPtr, srcStruct, srcField, srcFieldTy);
    if (!hasDst && !hasSrc)
      return;

    auto addParentToNested = [&](const FieldStoreKey &parentKey, Type *fieldTy) {
      auto *ST = dyn_cast_or_null<StructType>(fieldTy);
      if (!ST || ST->isOpaque() || ST->isLiteral() || !ST->hasName())
        return;
      if (LLVM_STRING_STARTS_WITH(ST->getStructName(), "union"))
        return;
      std::string childStruct = stripStructNameSuffix(ST->getStructName()).str();
      for (unsigned i = 0; i < ST->getNumElements(); i++) {
        if (addFieldAlias(parentKey, {childStruct, i}))
          copyAliases++;
      }
    };

    if (hasDst && hasSrc && addFieldAlias({dstStruct, dstField}, {srcStruct, srcField}))
      copyAliases++;
    if (hasDst)
      addParentToNested({dstStruct, dstField}, dstFieldTy);
    if (hasSrc)
      addParentToNested({srcStruct, srcField}, srcFieldTy);

    auto *DstST = dyn_cast_or_null<StructType>(dstFieldTy);
    auto *SrcST = dyn_cast_or_null<StructType>(srcFieldTy);
    if (DstST && SrcST &&
        !DstST->isOpaque() && !SrcST->isOpaque() &&
        !DstST->isLiteral() && !SrcST->isLiteral() &&
        DstST->hasName() && SrcST->hasName() &&
        !LLVM_STRING_STARTS_WITH(DstST->getStructName(), "union") &&
        !LLVM_STRING_STARTS_WITH(SrcST->getStructName(), "union") &&
        isStructLayoutCompatible(DstST, SrcST)) {
      std::string dstChild = stripStructNameSuffix(DstST->getStructName()).str();
      std::string srcChild = stripStructNameSuffix(SrcST->getStructName()).str();
      for (unsigned i = 0; i < DstST->getNumElements(); i++) {
        if (addFieldAlias({dstChild, i}, {srcChild, i}))
          copyAliases++;
      }
    }
  };

  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;
    if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
      continue;
    if (shouldSkipFunction(&F))
      continue;

    for (inst_iterator II = inst_begin(F), IE = inst_end(F); II != IE; ++II) {
      // Case 1: Direct store of function pointer to struct field
      //   store @func, (getelementptr %struct, %ptr, 0, N)
      if (auto *SI = dyn_cast<StoreInst>(&*II)) {
        const Value *stored = SI->getValueOperand()->stripPointerCasts();
        if (auto *StoredFunc = dyn_cast<Function>(stored)) {
          Function *canonStoredFunc = getFuncDef(const_cast<Function *>(StoredFunc));
          std::string sName;
          unsigned fIdx = 0;
          Type *fieldTy = nullptr;
          if (getFieldKeyFromPointerOperand(SI->getPointerOperand(), sName, fIdx, fieldTy)) {
            funcFieldStores[canonStoredFunc].insert({sName, fIdx});
            directStores++;
          }
          continue;
        }
        // Case 1b: scalar field-to-field pointer copy — a->f = b->g
        // (load + store). The dst key must alias the src key or the
        // field filter rejects every function registered at src when a
        // dispatcher reads the CACHED dst field. THE process_one_work
        // pattern: worker->current_func = work->func; ...;
        // worker->current_func(work) — the callsite key is (worker,
        // current_func) while every INIT_WORK store keys (work_struct,
        // func); without this alias the filter rejected every
        // WELL-TYPED work fn at the dispatcher and kept only fns whose
        // stores escaped classification (untyped i8 geps) — 82 of the
        // GT FNs. Aliases only widen acceptance of a reject-only
        // filter: sound.
        if (const auto *LI2 = dyn_cast<LoadInst>(stored)) {
          if (LI2->getType()->isPointerTy()) {
            std::string dName, sName2;
            unsigned dIdx = 0, sIdx2 = 0;
            Type *dTy = nullptr, *sTy = nullptr;
            if (getFieldKeyFromPointerOperand(SI->getPointerOperand(), dName,
                                              dIdx, dTy) &&
                getFieldKeyFromPointerOperand(LI2->getPointerOperand(), sName2,
                                              sIdx2, sTy) &&
                addFieldAlias({dName, dIdx}, {sName2, sIdx2}))
              copyAliases++;
          }
        }
        continue;
      }

      if (auto *MTI = dyn_cast<MemTransferInst>(&*II)) {
        addAggregateCopyAliases(MTI->getRawDest(), MTI->getRawSource());
        continue;
      }

      // Case 3: Function pointer passed as callback argument
      //   call @setter(%obj, @func) where setter stores param to struct field
      auto *CB = dyn_cast<CallBase>(&*II);
      if (!CB || CB->isInlineAsm()) continue;
      if (Function *Callee = CB->getCalledFunction()) {
        StringRef calleeName = Callee->getName();
        if ((LLVM_STRING_STARTS_WITH(calleeName, "llvm.memcpy.") ||
             LLVM_STRING_STARTS_WITH(calleeName, "llvm.memmove.") ||
             calleeName == "memcpy" ||
             calleeName == "memmove") &&
            CB->arg_size() >= 2) {
          addAggregateCopyAliases(CB->getArgOperand(0), CB->getArgOperand(1));
        }
      }

      for (unsigned i = 0; i < CB->arg_size(); i++) {
        auto *ArgFunc = dyn_cast<Function>(
            CB->getArgOperand(i)->stripPointerCasts());
        if (!ArgFunc) continue;
        Function *canonArgFunc = getFuncDef(ArgFunc);

        // Find the callee's definition (may be in another module)
        Function *callee = CB->getCalledFunction();
        if (!callee) continue;
        if (callee->isDeclaration()) {
          callee = getFuncDef(callee);
          if (callee->isDeclaration()) continue;
        }
        if (callee->empty()) continue;
        if (i >= callee->arg_size()) continue;

        // Trace parameter's uses in callee's body (one level only).
        // Handle the common -O0 pattern where params are stored to allocas:
        //   store %param, %alloca
        //   ...
        //   %val = load %alloca
        //   store %val, (GEP %struct, field N)
        Argument *param = callee->getArg(i);
        // Collect values that carry the parameter: the param itself,
        // casts of it, and loads from allocas it was stored to.
        SmallVector<Value*, 8> paramValues;
        paramValues.push_back(param);
        for (User *U : param->users()) {
          if (isa<CastInst>(U))
            paramValues.push_back(cast<Value>(U));
        }
        // Check for alloca spill pattern: param → store to alloca → load
        for (User *U : param->users()) {
          auto *SI = dyn_cast<StoreInst>(U);
          if (!SI || SI->getValueOperand() != param) continue;
          Value *allocaPtr = SI->getPointerOperand();
          if (!isa<AllocaInst>(allocaPtr)) continue;
          // Collect all loads from this alloca
          for (User *AU : allocaPtr->users()) {
            if (auto *LI = dyn_cast<LoadInst>(AU))
              paramValues.push_back(LI);
          }
        }
        bool traced = false;
        for (Value *PV : paramValues) {
          for (User *U : PV->users()) {
            auto *PSI = dyn_cast<StoreInst>(U);
            if (!PSI || PSI->getValueOperand() != PV) continue;
            std::string sName;
            unsigned fIdx = 0;
            Type *fieldTy = nullptr;
            if (getFieldKeyFromPointerOperand(PSI->getPointerOperand(), sName, fIdx, fieldTy)) {
              funcFieldStores[canonArgFunc].insert({sName, fIdx});
              callbackStores++;
              traced = true;
            }
          }
        }
        if (traced)
          fieldTraceOK.insert({CB, i});
      }
    }
  }

  // Completeness audit: the field filter may only reject a target if every
  // escape of its address was classified above. Walk each function's users;
  // any unclassified escape marks the function incomplete and the filter
  // falls back to always-accept for it.
  auto scannedFn = [&](const Function *PF) {
    return PF && !PF->isDeclaration() && !PF->isIntrinsic() && !PF->empty() &&
           (!Ctx->AllocFuncs.count(PF) || summaryInvokeKeepsBody(Ctx, PF)) &&
           !Ctx->ContainerFuncs.count(PF) && !shouldSkipFunction(PF);
  };
  size_t incompleteMarked = 0;
  for (Function &F : *M) {
    Function *canonF = getFuncDef(&F);
    if (funcFieldStoresIncomplete.count(canonF))
      continue;
    bool incomplete = false;
    SmallVector<const Value *, 16> vals;
    SmallPtrSet<const Value *, 32> seenV;
    vals.push_back(&F);
    while (!vals.empty() && !incomplete) {
      const Value *V = vals.pop_back_val();
      if (!seenV.insert(V).second)
        continue;
      for (const Use &U : V->uses()) {
        const User *Usr = U.getUser();
        if (const auto *C = dyn_cast<Constant>(Usr)) {
          if (isa<GlobalVariable>(C) || isa<GlobalAlias>(C))
            continue; // initializer: recorded by processInitializer or keyless
          if (const auto *CE = dyn_cast<ConstantExpr>(C)) {
            if (CE->getOpcode() == Instruction::PtrToInt) { incomplete = true; break; }
          }
          vals.push_back(C); // aggregates / cast / gep exprs: follow users
          continue;
        }
        const auto *I = dyn_cast<Instruction>(Usr);
        if (!I) { incomplete = true; break; }
        if (const auto *CB2 = dyn_cast<const CallBase>(I)) {
          if (CB2->isCallee(&U))
            continue; // direct call, no address flow
          if (CB2->isArgOperand(&U) && scannedFn(I->getFunction()) &&
              fieldTraceOK.count({CB2, CB2->getArgOperandNo(&U)}))
            continue; // one-level callback trace succeeded for this use
          incomplete = true; break;
        }
        if (const auto *SI2 = dyn_cast<StoreInst>(I)) {
          std::string sN; unsigned fI = 0; Type *fT = nullptr;
          if (SI2->getValueOperand() == V && scannedFn(I->getFunction()) &&
              getFieldKeyFromPointerOperand(SI2->getPointerOperand(), sN, fI, fT))
            continue; // classified as a direct field store above
          incomplete = true; break;
        }
        if (isa<CastInst>(I)) { vals.push_back(I); continue; }
        if (isa<CmpInst>(I)) continue; // comparison: no flow
        incomplete = true; break;      // phi/select/return/ptrtoint/...
      }
    }
    if (incomplete) {
      funcFieldStoresIncomplete.insert(canonF);
      incompleteMarked++;
    }
  }
  CG_LOG("FieldStore completeness [" << M->getModuleIdentifier() << "]: "
         << incompleteMarked << " functions marked incomplete (filter off)\n");

  CG_LOG("FieldStore IR [" << M->getModuleIdentifier() << "]: "
         << directStores << " direct, " << callbackStores << " callback, "
         << copyAliases << " copy-aliases, "
         << funcFieldStores.size() << " functions total, "
         << fieldAliasMap.size() << " alias roots\n");
}

// ---- Global union-find dedup ----

NodeIndex CallGraphPass::globalFind(NodeIndex n) {
  // getValueNodeForConstant lazily creates nodes (e.g. for ConstantExpr GEPs
  // and vector-of-pointer constants) after globalUFParent was sized. Extend
  // both arrays on demand so new nodes start as their own roots with rank 0.
  if (n >= globalUFParent.size()) {
    size_t old = globalUFParent.size();
    globalUFParent.resize(n + 1);
    globalUFRank.resize(n + 1, 0);
    std::iota(globalUFParent.begin() + old, globalUFParent.end(), (NodeIndex)old);
  }
  NodeIndex root = n;
  while (globalUFParent[root] != root)
    root = globalUFParent[root];
  // Path compression
  while (globalUFParent[n] != root) {
    NodeIndex parent = globalUFParent[n];
    globalUFParent[n] = root;
    n = parent;
  }
  return root;
}

bool CallGraphPass::globalUnion(NodeIndex a, NodeIndex b) {
  if (a == AndersNodeFactory::InvalidIndex || b == AndersNodeFactory::InvalidIndex)
    return false;
  NodeIndex ra = globalFind(a);
  NodeIndex rb = globalFind(b);
  if (ra == rb)
    return false;

  if (globalUFRank[ra] < globalUFRank[rb])
    std::swap(ra, rb);
  globalUFParent[rb] = ra;
  if (globalUFRank[ra] == globalUFRank[rb])
    globalUFRank[ra]++;
  return true;
}

bool CallGraphPass::globalDedupScanFunction(const Function *F) {
  if (!F)
    return false;

  bool anyChanged = false;
  bool changed = false;
  do {
    changed = false;
    for (const Instruction &I : instructions(F)) {
      if (isa<BitCastInst>(&I) || isa<AddrSpaceCastInst>(&I)) {
        if (!I.getType()->isPointerTy())
          continue;
        Value *src = I.getOperand(0);
        if (!src->getType()->isPointerTy())
          continue;
        NodeIndex srcNode = NF.getValueNodeFor(src);
        NodeIndex dstNode = NF.getValueNodeFor(&I);
        if (srcNode != AndersNodeFactory::InvalidIndex &&
            dstNode != AndersNodeFactory::InvalidIndex)
          changed |= globalUnion(srcNode, dstNode);
        continue;
      }

      if (const auto *GEP = dyn_cast<GetElementPtrInst>(&I)) {
        if (!GEP->getType()->isPointerTy() || !isZeroOffsetGEP(GEP))
          continue;
        const Value *base = GEP->getPointerOperand();
        NodeIndex baseNode = NF.getValueNodeFor(base);
        NodeIndex gepNode = NF.getValueNodeFor(GEP);
        if (baseNode != AndersNodeFactory::InvalidIndex &&
            gepNode != AndersNodeFactory::InvalidIndex)
          changed |= globalUnion(baseNode, gepNode);
        continue;
      }

      if (const auto *PHI = dyn_cast<PHINode>(&I)) {
        if (!PHI->getType()->isPointerTy())
          continue;
        NodeIndex dstNode = NF.getValueNodeFor(PHI);
        if (dstNode == AndersNodeFactory::InvalidIndex)
          continue;

        NodeIndex classRep = AndersNodeFactory::InvalidIndex;
        bool allSame = true;
        for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; i++) {
          Value *src = PHI->getIncomingValue(i);
          if (shouldSkipValue(src)) {
            allSame = false;
            break;
          }
          NodeIndex srcNode = NF.getValueNodeFor(src);
          if (srcNode == AndersNodeFactory::InvalidIndex) {
            allSame = false;
            break;
          }
          NodeIndex srcRoot = globalFind(srcNode);
          if (classRep == AndersNodeFactory::InvalidIndex)
            classRep = srcRoot;
          else if (classRep != srcRoot) {
            allSame = false;
            break;
          }
        }
        if (allSame && classRep != AndersNodeFactory::InvalidIndex)
          changed |= globalUnion(dstNode, classRep);
        continue;
      }

      if (const auto *Sel = dyn_cast<SelectInst>(&I)) {
        if (!Sel->getType()->isPointerTy())
          continue;
        const Value *tVal = Sel->getTrueValue();
        const Value *fVal = Sel->getFalseValue();
        if (shouldSkipValue(tVal) || shouldSkipValue(fVal))
          continue;
        NodeIndex tNode = NF.getValueNodeFor(tVal);
        NodeIndex fNode = NF.getValueNodeFor(fVal);
        NodeIndex dstNode = NF.getValueNodeFor(Sel);
        if (tNode != AndersNodeFactory::InvalidIndex &&
            fNode != AndersNodeFactory::InvalidIndex &&
            dstNode != AndersNodeFactory::InvalidIndex &&
            globalFind(tNode) == globalFind(fNode))
          changed |= globalUnion(dstNode, tNode);
      }
    }
    anyChanged |= changed;
  } while (changed);
  return anyChanged;
}

// Merge value nodes that denote the same access path, across functions:
//   - GEPs with all-constant indices on the same base class and the same
//     accumulated byte offset compute the same address.
//   - Loads through the same pointer class read the same abstract cell
//     (flow-insensitively their only inflow is that cell's deref node).
// Both are pure-copy equivalences: merging them changes no points-to facts,
// it only removes duplicate registers from the constraint graph.
bool CallGraphPass::globalDedupScanAccessPaths() {
  struct GepKey {
    NodeIndex baseRoot;
    int64_t offset;
    bool operator==(const GepKey &o) const {
      return baseRoot == o.baseRoot && offset == o.offset;
    }
  };
  struct GepKeyHash {
    size_t operator()(const GepKey &k) const {
      return std::hash<uint64_t>()((uint64_t)k.baseRoot * 0x9E3779B97F4A7C15ULL ^
                                   (uint64_t)k.offset);
    }
  };

  std::unordered_map<GepKey, NodeIndex, GepKeyHash> gepReps;
  std::unordered_map<NodeIndex, NodeIndex> loadReps;
  bool changed = false;

  for (auto &[M, _] : Ctx->Modules) {
    const DataLayout &DL = M->getDataLayout();
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;

      for (const Instruction &I : instructions(F)) {
        if (const auto *GEP = dyn_cast<GetElementPtrInst>(&I)) {
          if (!GEP->getType()->isPointerTy())
            continue;
          NodeIndex baseNode = NF.getValueNodeFor(GEP->getPointerOperand());
          NodeIndex gepNode = NF.getValueNodeFor(GEP);
          if (baseNode == AndersNodeFactory::InvalidIndex ||
              gepNode == AndersNodeFactory::InvalidIndex)
            continue;
          APInt Off(DL.getIndexTypeSizeInBits(GEP->getType()), 0);
          if (!GEP->accumulateConstantOffset(DL, Off))
            continue;
          GepKey key{globalFind(baseNode), Off.getSExtValue()};
          auto [it, inserted] = gepReps.emplace(key, gepNode);
          if (!inserted)
            changed |= globalUnion(it->second, gepNode);
          continue;
        }

        if (const auto *LI = dyn_cast<LoadInst>(&I)) {
          if (!containsPointerType(LI->getType()))
            continue;
          NodeIndex ptrNode = NF.getValueNodeFor(LI->getPointerOperand());
          NodeIndex valNode = NF.getValueNodeFor(LI);
          if (ptrNode == AndersNodeFactory::InvalidIndex ||
              valNode == AndersNodeFactory::InvalidIndex)
            continue;
          auto [it, inserted] = loadReps.emplace(globalFind(ptrNode), valNode);
          if (!inserted)
            changed |= globalUnion(it->second, valNode);
          continue;
        }
      }
    }
  }

  return changed;
}

// Resolve a CallBase to its callee definition, or nullptr if unresolvable.
const Function *CallGraphPass::resolveDirectCallee(const CallBase *CS) {
  const Function *CF = CS->getCalledFunction();
  if (!CF) {
    Value *CO = CS->getCalledOperand()->stripPointerCastsAndAliases();
    if (auto *CE = dyn_cast<ConstantExpr>(CO)) {
      switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: {
          GEPOperator *GEP = dyn_cast<GEPOperator>(CE);
          CO = GEP->getPointerOperand()->stripPointerCastsAndAliases();
          break;
        }
        case Instruction::BitCast:
          CO = CE->getOperand(0);
          break;
        default:
          return nullptr;
      }
    }
    CF = dyn_cast<Function>(CO);
  }
  if (!CF)
    return nullptr;

  // Resolve to definition
  auto it = Ctx->Funcs.find(CF->getGUID());
  if (it != Ctx->Funcs.end())
    CF = it->second;

  if (CF->isIntrinsic() || CF->empty())
    return nullptr;
  if (Ctx->AllocFuncs.count(CF) || Ctx->ContainerFuncs.count(CF))
    return nullptr;
  if (shouldSkipFunction(CF))
    return nullptr;

  return CF;
}

void CallGraphPass::globalDedupScanCallEdges(
    const Function *F,
    const DenseSet<const Function *> &singleCallsiteCallees) {
  if (!F || F->isDeclaration() || F->isIntrinsic() || F->empty())
    return;

  for (const Instruction &I : instructions(F)) {
    const CallBase *CS = dyn_cast<CallBase>(&I);
    if (!CS || CS->isInlineAsm())
      continue;

    if (Ctx->AllocSites.count(CS))
      continue;

    const Function *CF = resolveDirectCallee(CS);
    if (!CF)
      continue;

    // Only merge for callees with exactly 1 callsite
    if (!singleCallsiteCallees.count(CF))
      continue;

    // Summarized callees: the summary REPLACES callsite arg wiring
    // (drain semantics). A single-callsite actual<->formal pre-merge
    // makes the actual and formal one union-find node, silently
    // defeating the drain (found via the t_chain2 wrapper lift: the
    // lifted registration stayed pooled through the merged node).
    if (Ctx->FuncSummaries.count(CF) ||
        Ctx->FuncSummaries.count(getFuncDef(const_cast<Function *>(CF))))
      continue;

    // Merge pointer args: fixed actual→formal, variadic tail→vararg node
    unsigned numArgs = CS->arg_size();
    unsigned numFormals = CF->arg_size();
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!containsPointerType(arg->getType()))
        continue;
      if (shouldSkipValue(arg))
        continue;
      // Function/global actuals are identity barriers (same discipline as
      // preSolveCopyFieldMerge): their value node is shared across every
      // use, so unioning it with a formal fuses the identity class into
      // the callee — for flows-to, a fn origin fused with an fptr-operand
      // formal can leave the class edge-less (the actual->formal a-edge
      // becomes a self-loop), so it is never minted and the target is
      // underivable ANYWHERE (5.18 GT FNs: tcp_splice_data_recv,
      // direct_splice_actor). The plain a-edge from wireCallArgs carries
      // the flow instead.
      if (isa<GlobalValue>(arg->stripPointerCasts()))
        continue;
      NodeIndex argNode = NF.getValueNodeFor(arg);
      if (argNode == AndersNodeFactory::InvalidIndex)
        continue;
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = NF.getValueNodeFor(farg);
      if (formalNode != AndersNodeFactory::InvalidIndex)
        globalUnion(argNode, formalNode);
    }
    if (CF->isVarArg() &&
        !(CFLPrintfVarargSink && printfVarargSinkCallsite(CS, CF))) {
      NodeIndex varargNode = NF.getVarargNodeFor(CF);
      if (varargNode == AndersNodeFactory::InvalidIndex)
        continue;
      for (unsigned i = numFormals; i < numArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!containsPointerType(arg->getType()))
          continue;
        if (shouldSkipValue(arg))
          continue;
        if (isa<GlobalValue>(arg->stripPointerCasts()))
          continue; // identity barrier — see fixed-arg loop above
        NodeIndex argNode = NF.getValueNodeFor(arg);
        if (argNode != AndersNodeFactory::InvalidIndex)
          globalUnion(argNode, varargNode);
      }
    }

    // Merge return: returnNode → callsite
    if (containsPointerType(CF->getReturnType())) {
      NodeIndex retNode = NF.getReturnNodeFor(CF);
      NodeIndex callNode = NF.getValueNodeFor(CS);
      if (retNode != AndersNodeFactory::InvalidIndex &&
          callNode != AndersNodeFactory::InvalidIndex)
        globalUnion(retNode, callNode);
    }
  }
}

void CallGraphPass::globalDedupFinalize() {
  canonicalNodeMap.clear();
  canonicalClassMembers.clear();

  size_t mergedNodes = 0;
  for (NodeIndex i = 0; i < globalUFParent.size(); i++) {
    NodeIndex root = globalFind(i);
    if (root != i) {
      canonicalNodeMap[i] = root;
      mergedNodes++;
    }
    canonicalClassMembers[root].insert(i);
  }

  CG_LOG("Global dedup: " << globalUFParent.size() << " nodes, "
         << mergedNodes << " merged, "
         << canonicalClassMembers.size() << " equivalence classes\n");
}

void CallGraphPass::runGlobalDedup() {
  const size_t numNodes = NF.getNumNodes();
  globalUFParent.resize(numNodes);
  std::iota(globalUFParent.begin(), globalUFParent.end(), 0);
  globalUFRank.assign(numNodes, 0);

  // Intra-procedural copy merges + cross-function access-path merges.
  // Iterate to a fixpoint: access-path unions (same-offset GEPs, same-cell
  // loads) can enable further phi/select merges and vice versa. Unions are
  // monotone, so stopping at the cap only forgoes optimization, never
  // soundness.
  {
    constexpr unsigned kMaxDedupRounds = 8;
    unsigned round = 0;
    bool anyChanged = true;
    while (anyChanged && round++ < kMaxDedupRounds) {
      anyChanged = false;
      for (auto &[M, _] : Ctx->Modules) {
        for (Function &F : *M) {
          if (F.isDeclaration() || F.isIntrinsic() || F.empty())
            continue;
          if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
            continue;
          if (shouldSkipFunction(&F))
            continue;
          anyChanged |= globalDedupScanFunction(&F);
        }
      }
      anyChanged |= globalDedupScanAccessPaths();
    }
    CG_LOG("Global dedup: copy/access-path merges converged in "
           << round << " round(s)\n");
  }

  // Count direct callsites per callee to find single-callsite functions
  DenseMap<const Function *, unsigned> callsiteCount;
  for (auto &[M, _] : Ctx->Modules) {
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      for (const Instruction &I : instructions(F)) {
        const CallBase *CS = dyn_cast<CallBase>(&I);
        if (!CS || CS->isInlineAsm())
          continue;
        if (Ctx->AllocSites.count(CS))
          continue;
        const Function *CF = resolveDirectCallee(CS);
        if (CF)
          callsiteCount[CF]++;
      }
    }
  }

  DenseSet<const Function *> singleCallsiteCallees;
  size_t totalCallees = 0, multiCallees = 0;
  for (auto &[CF, Count] : callsiteCount) {
    totalCallees++;
    if (Count == 1)
      singleCallsiteCallees.insert(CF);
    else
      multiCallees++;
  }
  CG_LOG("Global dedup inter-proc: " << totalCallees << " callees, "
         << singleCallsiteCallees.size() << " single-callsite, "
         << multiCallees << " multi-callsite (skipped)\n");

  // Inter-procedural merges (only for single-callsite functions)
  for (auto &[M, _] : Ctx->Modules) {
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      globalDedupScanCallEdges(&F, singleCallsiteCallees);
    }
  }

  globalDedupFinalize();

  // Free UF vectors
  globalUFParent.clear();
  globalUFParent.shrink_to_fit();
  globalUFRank.clear();
  globalUFRank.shrink_to_fit();
}

// ---- --cfl-reachable: reachability-driven body processing -------------
// A flows-to graph assumes every instruction executes: a body's sources
// (function and global addresses it passes as arguments, its allocation
// sites, its literals) enter the graph whether or not the function is
// ever called. Under the closed-world premise a function no call
// reaches never runs, so its body is processed only once it is reached:
// from an entry by direct calls, by indirect calls as they resolve
// (wiring), or by summary callback bindings. Bodies processed after the
// first solve enter the next solve as edge deltas, like wiring edges.
static boost::unordered_flat_set<const llvm::Function *> g_reachSeen;
static boost::unordered_flat_set<const llvm::Function *> g_reachProcessed;
static std::vector<llvm::Function *> g_reachWork;
static size_t g_reachBodies = 0, g_reachSeeds = 0, g_reachSkippedFilter = 0;

void CallGraphPass::reachFunction(Function *F0) {
  if (!CFLReachable || !F0) return;
  auto push = [&](const Function *CF) {
    if (!CF) return;
    Function *F = getFuncDef(const_cast<Function *>(CF));
    if (!F || F->isDeclaration()) return;
    if (g_reachSeen.insert(F).second) g_reachWork.push_back(F);
  };
  push(F0);
  while (!g_reachWork.empty()) {
    Function *F = g_reachWork.back();
    g_reachWork.pop_back();
    if (F->isIntrinsic() || F->empty()) continue;
    if ((Ctx->AllocFuncs.count(F) && !summaryInvokeKeepsBody(Ctx, F)) ||
        Ctx->ContainerFuncs.count(F) || shouldSkipFunction(F)) {
      g_reachSkippedFilter++;
      continue; // summarized: no body, same as the eager loop
    }
    if (!g_reachProcessed.insert(F).second) continue;
    const DataLayout *savedDL = curDL;
    curDL = &F->getParent()->getDataLayout();
    runOnFunction(F);
    curDL = savedDL;
    g_reachBodies++;
    for (auto II = inst_begin(*F), IE = inst_end(*F); II != IE; ++II) {
      const auto *CB = dyn_cast<CallBase>(&*II);
      if (!CB) continue;
      if (const Function *CF = CB->getCalledFunction()) {
        push(CF);
      } else if (const auto *SV = dyn_cast<Function>(
                     CB->getCalledOperand()->stripPointerCastsAndAliases())) {
        push(SV);
      }
      // Summary bindings made while processing the body (INVOKE with a
      // constant callback, DISPATCH re-attribution) are callees too.
      auto cit = Ctx->Callees.find(CB);
      if (cit != Ctx->Callees.end())
        for (const Function *T : cit->second) push(T);
      // Escape to the outside: a function handed to an external callee
      // (a declaration with no definition in the corpus) may be called
      // from there with arguments we never see. Constants through
      // select/phi/cast chains are found here; a callback that reaches
      // an external argument only through memory is not (ledgered by
      // the extern-bound census).
      const Function *CF2 = CB->getCalledFunction();
      if (CF2 && getFuncDef(const_cast<Function *>(CF2))->isDeclaration()) {
        SmallVector<const Value *, 8> work;
        boost::unordered_flat_set<const Value *> seenV;
        for (const Use &U : CB->args()) work.push_back(U.get());
        while (!work.empty()) {
          const Value *V = work.pop_back_val()->stripPointerCasts();
          if (!seenV.insert(V).second) continue;
          if (const auto *FV = dyn_cast<Function>(V)) {
            push(FV);
          } else if (const auto *SI = dyn_cast<SelectInst>(V)) {
            work.push_back(SI->getTrueValue());
            work.push_back(SI->getFalseValue());
          } else if (const auto *PN = dyn_cast<PHINode>(V)) {
            for (const Value *IV : PN->incoming_values()) work.push_back(IV);
          } else if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
            for (const Use &U : CE->operands()) work.push_back(U.get());
          } else if (const auto *CA = dyn_cast<ConstantAggregate>(V)) {
            for (const Use &U : CA->operands()) work.push_back(U.get());
          }
        }
      }
    }
  }
}

void CallGraphPass::seedReachable() {
  std::vector<std::string> names;
  if (!CFLEntryList.empty()) {
    std::ifstream ifs(CFLEntryList);
    if (!ifs) {
      errs() << "ERROR: --cfl-entry-list: cannot open " << CFLEntryList << "\n";
      exit(1);
    }
    std::string line;
    while (std::getline(ifs, line)) {
      StringRef s = StringRef(line).trim();
      if (!s.empty() && s[0] != '#') names.push_back(s.str());
    }
  } else {
    names.push_back("main");
  }
  for (const std::string &nm : names) {
    bool found = false;
    for (auto &[Mod, _] : Ctx->Modules)
      if (Function *F = Mod->getFunction(nm)) {
        if (F->isDeclaration()) continue;
        found = true;
        g_reachSeeds++;
        reachFunction(F);
      }
    if (!found)
      WARNING("--cfl-reachable: entry '" << nm << "' has no definition\n");
  }
  // Static constructors and destructors run without a call in the IR.
  for (auto &[Mod, _] : Ctx->Modules)
    for (const char *gn : {"llvm.global_ctors", "llvm.global_dtors"}) {
      const GlobalVariable *GV = Mod->getNamedGlobal(gn);
      if (!GV || !GV->hasInitializer()) continue;
      const auto *arr = dyn_cast<ConstantArray>(GV->getInitializer());
      if (!arr) continue;
      for (const Use &U : arr->operands()) {
        const auto *st = dyn_cast<ConstantStruct>(U.get());
        if (!st || st->getNumOperands() < 2) continue;
        if (const auto *F = dyn_cast<Function>(
                st->getOperand(1)->stripPointerCasts())) {
          g_reachSeeds++;
          reachFunction(const_cast<Function *>(F));
        }
      }
    }
  CG_LOG("Reach: " << g_reachSeeds << " entries seeded, " << g_reachBodies
         << " bodies processed by direct reachability, "
         << g_reachSkippedFilter << " summarized callees skipped\n");
}

void CallGraphPass::reachLedger() {
  if (!CFLReachable) return;
  size_t defined = 0, unreachedAT = 0;
  std::vector<StringRef> sample;
  for (auto &[Mod, _] : Ctx->Modules)
    for (Function &F : *Mod) {
      if (F.isDeclaration() || F.isIntrinsic()) continue;
      defined++;
      if (Ctx->AddressTakenFuncs.count(&F) && !g_reachProcessed.count(&F) &&
          !g_reachSeen.count(&F)) {
        unreachedAT++;
        if (sample.size() < 40) sample.push_back(F.getName());
      }
    }
  CG_LOG("Reach: LEDGER " << g_reachBodies << " bodies processed of "
         << defined << " defined; " << unreachedAT
         << " address-taken functions never reached (candidates for a "
         << "missing entry if any should run)\n");
  if (VerboseLevel >= 2)
    for (StringRef n : sample) errs() << "Reach:   unreached " << n << "\n";
}
