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


#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/FormatVariadic.h>
#include <llvm/Support/JSON.h>

#include <vector>
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <numeric>
#include <set>
#include <thread>
#include <unordered_map>
#include <unordered_set>

#include "CallGraph.h"
#include "Annotation.h"
#include "LLMClient.h"
#include "VSnapshot.h"

#include "gracfl/include/solvers/Solver.hpp"

#define CG_LOG(stmt) KA_LOG(2, "CallGraph: " << stmt)
#define CG_DEBUG(stmt) KA_LOG(3, "CallGraph: " << stmt)

using namespace llvm;

namespace {
struct EdgeKey {
  uint from;
  uint to;
  uint label;

  bool operator==(const EdgeKey &Other) const {
    return from == Other.from && to == Other.to && label == Other.label;
  }
};

struct EdgeKeyHash {
  size_t operator()(const EdgeKey &K) const {
    size_t H = static_cast<size_t>(K.from);
    H ^= static_cast<size_t>(K.to) + 0x9e3779b97f4a7c15ULL + (H << 6) + (H >> 2);
    H ^= static_cast<size_t>(K.label) + 0x9e3779b97f4a7c15ULL + (H << 6) + (H >> 2);
    return H;
  }
};

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
    case Intrinsic::dbg_assign:
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
      return true;
    default:
      return false;
  }
}

} // namespace

// Helper to check if we should skip creating edges for a value
static bool shouldSkipValue(const Value *V) {
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
static bool containsPointerType(Type *T) {
  if (T->isPointerTy()) return true;
  if (auto *VT = dyn_cast<VectorType>(T))
    return VT->getElementType()->isPointerTy();
  return false;
}

// Helper to check if we should skip creating edges for a function call
static bool shouldSkipFunction(const Function *F) {
  if (!F || !F->hasName())
    return false;

  StringRef name = F->getName();

  // Skip kernel utility functions
  if (isFreeFn(name) || isKernelUtilityFn(name))
    return true;

  return false;
}

static unsigned detectPhysicalCoreCount() {
  if (const char *override = std::getenv("KACFL_THREADS")) {
    char *end = nullptr;
    long value = std::strtol(override, &end, 10);
    if (end != override && value > 0)
      return static_cast<unsigned>(value);
  }

  std::ifstream cpuinfo("/proc/cpuinfo");
  if (cpuinfo.is_open()) {
    std::set<std::pair<int, int>> physicalCores;
    int physicalId = -1;
    int coreId = -1;
    std::string line;

    auto flushProcessor = [&]() {
      if (coreId >= 0) {
        if (physicalId < 0)
          physicalId = 0;
        physicalCores.emplace(physicalId, coreId);
      }
      physicalId = -1;
      coreId = -1;
    };

    while (std::getline(cpuinfo, line)) {
      if (line.empty()) {
        flushProcessor();
        continue;
      }

      const size_t colon = line.find(':');
      if (colon == std::string::npos)
        continue;

      std::string key = line.substr(0, colon);
      std::string value = line.substr(colon + 1);
      auto ltrim = [](std::string &s) {
        const size_t pos = s.find_first_not_of(" \t");
        s.erase(0, pos == std::string::npos ? s.size() : pos);
      };
      auto rtrim = [](std::string &s) {
        const size_t pos = s.find_last_not_of(" \t");
        if (pos == std::string::npos)
          s.clear();
        else
          s.erase(pos + 1);
      };
      ltrim(key);
      rtrim(key);
      ltrim(value);
      rtrim(value);

      if (key == "physical id") {
        physicalId = std::atoi(value.c_str());
      } else if (key == "core id") {
        coreId = std::atoi(value.c_str());
      }
    }
    flushProcessor();

    if (!physicalCores.empty())
      return static_cast<unsigned>(physicalCores.size());
  }

  const unsigned logical = std::thread::hardware_concurrency();
  return logical > 0 ? logical : 1;
}

CallGraphPass::CallGraphPass(GlobalContext *Ctx_, LLMClient *LLMClient_)
    : IterativeModulePass(Ctx_, "CallGraph"),
      NF(Ctx->nodeFactory),
      EB(Ctx->edgeBuilder),
      LLM(LLMClient_),
      cflThreads(detectPhysicalCoreCount()),
      cflSolvedInputEdgeCount(0),
      cflForceRebuild(true),
      iteration(0) {}

Function* CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

// Strip LLVM's numeric suffix (e.g., ".0", ".123") from struct names.
// When linking multiple modules, LLVM appends these suffixes to avoid
// name collisions, but they represent the same C struct type.
static StringRef stripStructNameSuffix(StringRef Name) {
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

  return false;
}

bool CallGraphPass::handleCall(const CallBase *CS, const Function *CF) {
  if (CF->isIntrinsic()) {
    // handle intrinsic functions
    return false;
  }

  // Skip utility functions to reduce edge explosion
  if (shouldSkipFunction(CF)) {
    CG_DEBUG("Skipping utility function: " << CF->getName() << "\n");
    return false;
  }

  // assumes CF is the function definition
  if (CF->empty()) {
    // external function, nothing to do
    WARNING("Call: " << CF->getName() << " is empty!\n");
    if (CF->getName() == "memcpy" || CF->getName() == "memmove")
      handleMemcpy(CS);
    return false;
  }
  // CG_DEBUG("Call: " << *CS << " -> " << CF->getName() << "\n");

  // handle args
  unsigned numArgs = CS->arg_size();
  if (CF->isVarArg()) {
    NodeIndex formalNode = getCanonicalNode(NF.getVarargNodeFor(CF));
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      if (shouldSkipValue(arg)) {
        CG_DEBUG("Skipping compiler-introduced argument: " << *arg << "\n");
        continue;
      }
      NodeIndex argNode = getRepNodeForValue(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      addAssignmentEdge(argNode, formalNode);
    }
  } else {
    // Only match up to the number of formal parameters; extra actual
    // arguments at the callsite are ignored (permitted by permissive matching).
    unsigned numFormals = CF->arg_size();
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      if (shouldSkipValue(arg)) {
        CG_DEBUG("Skipping compiler-introduced argument: " << *arg << "\n");
        continue;
      }
      NodeIndex argNode = getRepNodeForValue(arg);
      // assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      if (argNode == AndersNodeFactory::InvalidIndex) {
        argNode = NF.createValueNode(arg);
        argNode = getCanonicalNode(argNode);
        CG_DEBUG("Create value node " << argNode << " for Arg " << *arg << "\n");
      }
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = getRepNodeForValue(farg);
      assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
      addAssignmentEdge(argNode, formalNode);
    }
  }

  // handle return
  if (CF->getReturnType()->isPointerTy()) {
    NodeIndex retNode = getCanonicalNode(NF.getReturnNodeFor(CF));
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    // The callsite may not have a value node if it discards the return value
    // (e.g., void-typed callsite matched via permissive isCompatible)
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      addAssignmentEdge(retNode, callNode);
  }

  return false;
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
  if (CF->isVarArg()) {
    NodeIndex formalNode = getCanonicalNode(NF.getVarargNodeFor(CF));
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      NodeIndex argNode = getRepNodeForValue(arg);
      if (argNode == AndersNodeFactory::InvalidIndex) {
        WARNING("VarArg: actual (" << i << ") " << *arg << " node not found!\n");
        continue;
      }
      EB.removeAssignmentEdges(getCanonicalNode(argNode), getCanonicalNode(formalNode));
    }
  } else {
    // Only iterate over the minimum of actual and formal args
    unsigned minArgs = std::min(numArgs, numFormals);
    for (unsigned i = 0; i < minArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue; // skip non-pointer args
      NodeIndex argNode = getRepNodeForValue(arg);
      assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      Value *farg = CF->getArg(i);
      NodeIndex formalNode = getRepNodeForValue(farg);
      assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
      EB.removeAssignmentEdges(getCanonicalNode(argNode), getCanonicalNode(formalNode));
    }
  }

  // handle return
  if (CF->getReturnType()->isPointerTy()) {
    NodeIndex retNode = getCanonicalNode(NF.getReturnNodeFor(CF));
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = getRepNodeForValue(CS);
    if (callNode != AndersNodeFactory::InvalidIndex)
      EB.removeAssignmentEdges(getCanonicalNode(retNode), getCanonicalNode(callNode));
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
  return getCanonicalNode(n);
}

NodeIndex CallGraphPass::getRepDerefNode(NodeIndex ptrNode) {
  if (ptrNode == AndersNodeFactory::InvalidIndex)
    return AndersNodeFactory::InvalidIndex;

  NodeIndex canonical = getCanonicalNode(ptrNode);
  NodeIndex derefNode = NF.getDereferenceNodeFor(canonical);
  if (derefNode == AndersNodeFactory::InvalidIndex) {
    derefNode = NF.createDereferenceNode(canonical);
    CG_DEBUG("Create deref node " << derefNode << " for canonical node " << canonical << "\n");
    EB.addDereferenceEdges(canonical, derefNode);
  }

  return derefNode;
}

void CallGraphPass::addAssignmentEdge(NodeIndex src, NodeIndex dst) {
  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex)
    return;
  NodeIndex s = getCanonicalNode(src);
  NodeIndex d = getCanonicalNode(dst);
  if (s == d) return;
  EB.addAssignmentEdges(s, d);
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
    if (!containsPointerType(rv->getType())) {
      // XXX only consider pointer type
      return;
    }

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(rv)) {
      CG_DEBUG("Skipping return value: " << *rv << "\n");
      return;
    }

    NodeIndex rvNode = CGP.getRepNodeForValue(rv);
    assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
    NodeIndex RT = CGP.NF.getReturnNodeFor(F);
    assert(RT != AndersNodeFactory::InvalidIndex && "Return node not found!");
    CGP.addAssignmentEdge(rvNode, RT);
  }
}

void CallGraphPass::InstHandler::visitCallBase(CallBase &CS) {
  if (CS.isInlineAsm()) return; // FIXME handle inline assembly
  if (CGP.Ctx->AllocSites.count(&CS)) {
    // record allocation sites and create heap object node
    NodeIndex valNode = CGP.getRepNodeForValue(&CS);
    CGP.AllocSites.insert(valNode);
    NodeIndex heapObj = CGP.NF.createOpaqueObjectNode(&CS, true);
    CGP.EB.addDereferenceEdges(valNode, heapObj);
    CG_DEBUG("Create heap obj node " << heapObj << " for " << CS << "\n");
    return; // skip allocation sites
  }

  // Check for function pointer cycles
  if (!CS.getCalledFunction()) {
    Value *CO = CS.getCalledOperand()->stripPointerCastsAndAliases();
    if (auto *Load = dyn_cast<LoadInst>(CO)) {
      CG_DEBUG("Indirect call through loaded function pointer: " << *Load->getPointerOperand() << "\n");
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
      CGP.Ctx->IndirectCallInsts.insert(&CS);
    }
  }
}

void CallGraphPass::InstHandler::visitAllocaInst(AllocaInst &I) {
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(&I, slotRep))
    return;

  // create a deref node for base ptr of alloca
  NodeIndex ptrNode = CGP.getRepNodeForValue(&I);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find alloca node");
  (void)CGP.getRepDerefNode(ptrNode);
}

void CallGraphPass::InstHandler::visitLoadInst(LoadInst &I) {
  if (!containsPointerType(I.getType())) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex valNode = CGP.getRepNodeForValue(&I);
  assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find load value node");

  Value *ptr = I.getOperand(0);
  NodeIndex slotRep;
  if (CGP.resolveSummarizedAllocaSlot(ptr, slotRep)) {
    CGP.localAllocaLoadVals[slotRep].push_back(valNode);
    return;
  }
  NodeIndex ptrNode = CGP.getRepNodeForValue(ptr);
  assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find load ptr node");

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  CGP.addAssignmentEdge(derefNode, valNode);
}

void CallGraphPass::InstHandler::visitStoreInst(StoreInst &I) {
  Value *val = I.getOperand(0);
  if (!containsPointerType(val->getType())) {
    // XXX only consider pointer type
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

  NodeIndex derefNode = CGP.getRepDerefNode(ptrNode);

  CGP.addAssignmentEdge(valNode, derefNode);

  // Record struct field store for field-aware indirect call filtering.
  // Strip pointer casts (bitcasts) to see through patterns like:
  //   %gep = getelementptr %struct, %ptr, 0, 7
  //   %bc  = bitcast %gep to <other_type>*
  //   store %val, %bc
  if (auto *GEP = dyn_cast<GEPOperator>(ptr->stripPointerCasts())) {
    std::string sName;
    unsigned fIdx;
    if (CGP.getGEPStructField(GEP, sName, fIdx))
      CGP.fieldStoreRecords.push_back({valNode, sName, fIdx});
  }
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

void CallGraphPass::InstHandler::visitPHINode(PHINode &PHI) {
  if (!containsPointerType(PHI.getType())) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&PHI);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find phi dst node");
  for (unsigned i = 0, e = PHI.getNumIncomingValues(); i != e; ++i) {
    Value *src = PHI.getIncomingValue(i);

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in PHI: " << *src << "\n");
      continue;
    }

    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
    // if (srcNode == AndersNodeFactory::InvalidIndex) {
    //   srcNode = CGP.NF.createValueNode(src);
    //   CG_DEBUG("Create value node " << srcNode << " for PHI src " << *src << "\n");
    // }
    CGP.addAssignmentEdge(srcNode, dstNode);
  }
}

void CallGraphPass::InstHandler::visitSelectInst(SelectInst &I) {
  if (!containsPointerType(I.getType())) {
    // XXX only consider pointer type
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find select dst node");
  // NodeIndex dstNode = CGP.NF.createValueNode(&I);
  for (unsigned i = 1; i < I.getNumOperands(); i++) {
    Value *src = I.getOperand(i);

    // Skip nullptr and compiler-introduced values
    if (shouldSkipValue(src)) {
      CG_DEBUG("Skipping value in Select: " << *src << "\n");
      continue;
    }

    NodeIndex srcNode = CGP.getRepNodeForValue(src);
    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node");
    // if (srcNode == AndersNodeFactory::InvalidIndex) {
    //   srcNode = CGP.NF.createValueNode(src);
    //   CG_DEBUG("Create value node " << srcNode << " for select src " << *src << "\n");
    // }
    CGP.addAssignmentEdge(srcNode, dstNode);
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
    WARNING("IntToPtr: src node not found: " << I << "\n");
    return;
  }
  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    WARNING("IntToPtr: dst node not found: " << I << "\n");
    return;
  }
  CG_DEBUG("IntToPtr: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.addAssignmentEdge(srcNode, dstNode);
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
  CGP.addAssignmentEdge(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitBinaryOperator(BinaryOperator &I) {
  if (!I.getType()->isIntegerTy())
    return;

  // Check if exactly one operand is pointer-derived and the other is constant.
  NodeIndex srcNode = AndersNodeFactory::InvalidIndex;
  bool otherIsConst = false;
  for (unsigned i = 0; i < 2; i++) {
    NodeIndex n = CGP.getRepNodeForValue(I.getOperand(i));
    if (n != AndersNodeFactory::InvalidIndex && !CGP.NF.isSpecialNode(n)) {
      srcNode = n;
      otherIsConst = isa<Constant>(I.getOperand(1 - i));
    }
  }
  if (srcNode == AndersNodeFactory::InvalidIndex)
    return;

  if (!otherIsConst) {
    WARNING("BinOp on pointer-derived integer with non-constant operand: " << I << "\n");
    return;
  }

  NodeIndex dstNode = CGP.getRepNodeForValue(&I);
  if (dstNode == AndersNodeFactory::InvalidIndex) {
    dstNode = CGP.getCanonicalNode(CGP.NF.createValueNode(&I));
    CG_DEBUG("BinOp: created value node " << dstNode << " for " << I << "\n");
  }
  CG_DEBUG("BinOp: " << srcNode << " -> " << dstNode << " for " << I << "\n");
  CGP.addAssignmentEdge(srcNode, dstNode);
}

void CallGraphPass::InstHandler::visitVAArgInst(VAArgInst &I) {
  if (!I.getType()->isPointerTy())
    return;

  NodeIndex valNode = CGP.NF.getValueNodeFor(&I);
  if (valNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: result node not found: " << I << "\n");
    return;
  }

  Function *F = I.getParent()->getParent();
  NodeIndex varargNode = CGP.NF.getVarargNodeFor(F);
  if (varargNode == AndersNodeFactory::InvalidIndex) {
    WARNING("VAArg: vararg node not found for function: " << F->getName() << "\n");
    return;
  }

  CG_DEBUG("VAArg: " << F->getName() << ": vararg node " << varargNode
           << " -> val node " << valNode << " for " << I << "\n");
  CGP.addAssignmentEdge(varargNode, valNode);
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

// Process global variable initializer in field-insensitive way
void CallGraphPass::processInitializer(NodeIndex ptrNode, Constant *init,
                                        const std::string &enclosingStruct,
                                        int enclosingFieldIdx) {
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

  if (isa<GlobalVariable>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &globalvar: add assignment edges globalvar_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    // Record field store if enclosing struct is known
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      fieldStoreRecords.push_back({valNode, enclosingStruct, (unsigned)enclosingFieldIdx});
    CG_DEBUG("add CFL assignment edges for global variable " << cast<GlobalVariable>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (isa<Function>(init)) {
    NodeIndex valNode = NF.getValueNodeFor(init);
    if (valNode == AndersNodeFactory::InvalidIndex) {
      valNode = NF.createValueNode(init);
    }
    // ptr = &function: add assignment edges function_val -> ptr
    EB.addAssignmentEdges(valNode, ptrNode);
    // Record direct function store into struct field
    if (!enclosingStruct.empty() && enclosingFieldIdx >= 0)
      funcFieldStores[cast<Function>(init)].insert({enclosingStruct, (unsigned)enclosingFieldIdx});
    CG_DEBUG("add CFL assignment edges for function " << cast<Function>(init)->getName() << " -> " << ptrNode << "\n");
  } else if (ConstantArray *CA = dyn_cast<ConstantArray>(init)) {
    // Field-insensitive: all array elements assign to the same ptr
    for (unsigned i = 0; i != CA->getNumOperands(); ++i) {
      processInitializer(ptrNode, CA->getOperand(i), enclosingStruct, enclosingFieldIdx);
    }
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(init)) {
    // Field-insensitive: all struct fields assign to the same ptr
    StructType *STy = CS->getType();
    for (unsigned i = 0; i != CS->getNumOperands(); ++i) {
      std::string curStruct = enclosingStruct;
      int curField = enclosingFieldIdx;
      if (STy && !STy->isLiteral() && STy->hasName() &&
          !LLVM_STRING_STARTS_WITH(STy->getStructName(), "union")) {
        curStruct = stripStructNameSuffix(STy->getStructName()).str();
        curField = i;
      }
      processInitializer(ptrNode, CS->getOperand(i), curStruct, curField);
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
        // Field-insensitive: get the base pointer with casts stripped
        const GEPOperator *GEPOp = cast<GEPOperator>(CE);
        const Value* basePtr = GEPOp->getPointerOperand()->stripPointerCasts();
        NodeIndex baseNode = NF.getValueNodeFor(basePtr);
        if (baseNode == AndersNodeFactory::InvalidIndex) {
          baseNode = NF.createValueNode(basePtr);
        }
        // ptr = base_ptr: add assignment edges base_ptr -> ptr
        EB.addAssignmentEdges(baseNode, ptrNode);
        // Check if GEP accesses a struct field, update enclosing info
        std::string gepStruct;
        unsigned gepField;
        if (getGEPStructField(GEPOp, gepStruct, gepField))
          fieldStoreRecords.push_back({baseNode, gepStruct, gepField});
        break;
      }
      case Instruction::BitCast: {
        // BitCast: process the operand directly
        processInitializer(ptrNode, CE->getOperand(0), enclosingStruct, enclosingFieldIdx);
        break;
      }
      case Instruction::IntToPtr: {
        // ptr = (ptr)int: add assignment edges constantInt -> ptr
        // EB.addAssignmentEdges(NF.getConstantIntNode(), ptrNode);
        break;
      }
      default:
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

bool CallGraphPass::doInitialization(Module *M) {
  if (iteration == 0 && M == Ctx->Modules.front().first) {
    canonicalNodeMap.clear();
    canonicalClassMembers.clear();
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

    // collect address-taken functions
    if (F.hasAddressTaken()) {
      Ctx->AddressTakenFuncs.insert(&F);

      // only add fval -> fobj edge in call graph analysis?
      // create a value node for function pointer
      NodeIndex valNode = NF.createValueNode(&F);
      (void)valNode;
    }

    // Populate AllocFuncs for all functions matching known allocator names,
    // regardless of whether they are declarations or definitions
    {
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
      NF.createValueNode(itr.second);
    }
    for (auto const &itr: Ctx->ExtFuncs) {
      if (!itr.second->getReturnType()->isVoidTy())
        NF.createReturnNode(itr.second);
    }
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee mapping
  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty() ||
        Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
      continue;

    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      // map callsite to possible callees
      if (CallBase *CB = dyn_cast<CallBase>(&*i)) {
        if (CB->isInlineAsm())
          continue;
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
    // compare callees found by CFL and type matching
    size_t total = 0, match = 0;
    for (auto &it : calleeByType) {
      const CallBase *CS = it.first;
      FuncSet &TS = it.second;
      FuncSet &FS = Ctx->Callees[CS];
      total += TS.size();
      for (const Function *F : TS) {
        if (FS.find(F) != FS.end()) {
          match++;
        } else {
          // not found by CFL
          WARNING("Callee by type not found by CFL: " << F->getName() << " for " << *CS << "\n");
        }
      }
    }
    CG_LOG("Callee by type: total " << total << ", match by CFL " << match << "\n");
    // check if all address-taken functions are used in indirect calls
    size_t used = 0;
    for (const Function *F : Ctx->AddressTakenFuncs) {
      bool found = false;
      for (auto &it : Ctx->Callees) {
        FuncSet &FS = it.second;
        if (FS.find(F) != FS.end()) {
          found = true;
          break;
        }
      }
      if (found) {
        used++;
      } else {
        WARNING("Address-taken function not used in indirect calls: " << F->getName() << "\n");
        // print all users
        for (auto *U : F->users()) {
          if (!isa<Function>(U)) // skip personality
            errs() << "  User: " << *U << "\n";
        }
      }
    }
    CG_LOG("Address-taken functions: total " << Ctx->AddressTakenFuncs.size() << ", used " << used << "\n");
  }

  return false;
}

bool CallGraphPass::findCustomAllocators(const cfl_result_t &outputCFLGraph) {
  bool foundNewAlloc = false;
  FuncSet newAllocFuncs;
  std::vector<NodeIndex> memberNodes;
  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  for (auto *F : Ctx->CandidateAllocFuncs) {
    // get return value
    NodeIndex retNode;
    if (useDense) {
      retNode = getDenseID(NF.getReturnNodeFor(F));
    } else {
      retNode = getCanonicalNode(NF.getReturnNodeFor(F));
    }
    if (retNode == AndersNodeFactory::InvalidIndex ||
        (useDense && retNode == UINT32_MAX))
      continue;
    assert(retNode < outputCFLGraph.size() && "Return node out of CFL graph range");
    auto &cflSet = outputCFLGraph[retNode][EB.getLabelV()]; // find the alias set
    std::unordered_set<NodeIndex> seenRoots;
    for (auto idx : cflSet) {
      // Map back to original node if using dense mapping
      NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
      NodeIndex root = getCanonicalNode(origIdx);
      if (!seenRoots.insert(root).second)
        continue;
      bool reachesAllocSite = false;
      collectCanonicalMembers(root, memberNodes);
      for (NodeIndex member : memberNodes) {
        NodeIndex canonicalMember = getCanonicalNode(member);
        if (AllocSites.count(member) || AllocSites.count(canonicalMember)) {
          reachesAllocSite = true;
          break;
        }
      }
      if (reachesAllocSite) {
        // if return value is from a known allocation site
        CG_LOG("Custom allocator " << F->getName() << " return value from alloc site: " << idx << "\n");
        Ctx->AllocFuncs.insert(F);
        newAllocFuncs.insert(F);
        foundNewAlloc = true;
        // update edge
        for (auto const& U : F->users()) {
          if (const CallBase *CI = dyn_cast<CallBase>(U)) {
            if (CI->getCalledFunction() == F) {
              NodeIndex callNode = getCanonicalNode(NF.getValueNodeFor(CI));
              assert(callNode != AndersNodeFactory::InvalidIndex && "CallBase node not found for candidate alloc func!");
              Ctx->AllocSites.insert(CI);
              AllocSites.insert(callNode);
              // create heap object node
              NodeIndex heapObj = NF.createOpaqueObjectNode(CI, true);
              EB.addDereferenceEdges(callNode, heapObj);
              // remove call edges
              removeCallEdges(CI, F);
              CG_LOG("Update custom allocator call: " << *CI << "\n");
            }
          }
        }
        break;
      }
    }
  }

  if (foundNewAlloc) {
    // remove confirmed allocators from candidate set
    for (auto *F : newAllocFuncs) {
      Ctx->CandidateAllocFuncs.erase(F);
    }
  }

  return foundNewAlloc;
}

void CallGraphPass::buildFieldStoreMap(const cfl_result_t &outputCFLGraph) {
  unsigned labelV = EB.getLabelV();
  size_t funcFieldPairs = 0;
  std::vector<NodeIndex> memberNodes;
  const bool useDense = CFLGlobalDedup && !origToDense.empty();

  for (const auto &rec : fieldStoreRecords) {
    // For each store record, query the CFL V-relation to find which
    // function value nodes V-reach the stored value node
    NodeIndex valNode;
    if (useDense) {
      valNode = getDenseID(rec.valNode);
      if (valNode == UINT32_MAX) continue;
    } else {
      valNode = getCanonicalNode(rec.valNode);
    }
    assert(valNode < outputCFLGraph.size() && "Field-store node out of CFL graph range");
    auto &cflSet = outputCFLGraph[valNode][labelV];
    std::unordered_set<NodeIndex> seenRoots;
    for (auto idx : cflSet) {
      NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
      NodeIndex root = getCanonicalNode(origIdx);
      if (!seenRoots.insert(root).second)
        continue;
      collectCanonicalMembers(root, memberNodes);
      for (NodeIndex member : memberNodes) {
        if (NF.isSpecialNode(member))
          continue;
        const Value *CV = NF.getValueForNode(member);
        if (!CV)
          continue;
        const Function *F = dyn_cast<Function>(CV);
        if (!F)
          continue;
        if (funcFieldStores[F].insert({rec.structName, rec.fieldIdx}).second)
          funcFieldPairs++;
      }
    }
  }

  CG_LOG("FieldStore map: " << fieldStoreRecords.size() << " records, "
         << funcFieldPairs << " function-field pairs, "
         << funcFieldStores.size() << " distinct functions\n");
}

bool CallGraphPass::handleIndirectCall(const cfl_result_t &outputCFLGraph) {
  // resolve indirect calls
  bool Changed = false;
  std::vector<NodeIndex> memberNodes;
  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  for (auto *CS : Ctx->IndirectCallInsts) {
    CG_DEBUG("Handle indirect CallSite: " << *CS << " in function "
        << CS->getFunction()->getName() << "\n");
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    NodeIndex fptrNode;
    if (useDense) {
      fptrNode = getDenseID(NF.getValueNodeFor(fptr));
      if (fptrNode == UINT32_MAX) {
        WARNING("FuncPtr for " << *CS << " dense node not found!\n");
        continue;
      }
    } else {
      fptrNode = getCanonicalNode(NF.getValueNodeFor(fptr));
      if (fptrNode == AndersNodeFactory::InvalidIndex) {
        WARNING("FuncPtr for " << *CS << " node not found!\n");
        continue;
      }
    }
    assert(fptrNode < outputCFLGraph.size() && "Func-ptr node out of CFL graph range");

    // Extract call-site struct field info: trace through LoadInst → GEP
    std::string callSiteStruct;
    unsigned callSiteFieldIdx = 0;
    bool hasCallSiteField = false;
    if (auto *Load = dyn_cast<LoadInst>(fptr)) {
      Value *loadPtr = Load->getPointerOperand()->stripPointerCasts();
      if (auto *GEP = dyn_cast<GEPOperator>(loadPtr)) {
        hasCallSiteField = getGEPStructField(GEP, callSiteStruct, callSiteFieldIdx);
      }
    }

    auto &cflSet = outputCFLGraph[fptrNode][EB.getLabelV()];
    CG_DEBUG("  fptr node " << fptrNode << " V-set size: " << cflSet.size() << "\n");
    std::unordered_set<const Function *> seenFuncs;
    std::unordered_set<NodeIndex> seenRoots;
    for (auto idx : cflSet) {
      NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
      NodeIndex root = getCanonicalNode(origIdx);
      if (!seenRoots.insert(root).second)
        continue;
      collectCanonicalMembers(root, memberNodes);
      for (NodeIndex member : memberNodes) {
        if (NF.isSpecialNode(member)) {
          WARNING("Indirect Call: " << *CS << " callee is a special node: " << member << "\n");
          continue;
        }
        // Return nodes and vararg nodes also store Function* as their value,
        // but they represent the return value / vararg slot, not the function
        // pointer itself. Skip them — only true value nodes are function ptrs.
        if (NF.isReturnNode(member))
          continue;
        if (NF.isVarargNode(member))
          continue;

        const Value *CV = NF.getValueForNode(member);
        if (CV == NULL)
          continue;

        const Function *CF = dyn_cast<Function>(CV);
        if (CF == NULL)
          continue;
        if (!seenFuncs.insert(CF).second)
          continue;

        // due to field insensitivity, we may have FPs, do a type match
        if (!isCompatible(CS, CF)) {
          continue;
        }
        // Struct-field-aware filtering:
        // If we know the call site loads from a specific struct field,
        // and we have positive evidence of which fields this function is
        // stored into, reject if none match.
        if (hasCallSiteField) {
          auto it = funcFieldStores.find(CF);
          if (it != funcFieldStores.end()) {
            const auto &fieldSet = it->second;
            if (fieldSet.find({callSiteStruct, callSiteFieldIdx}) == fieldSet.end()) {
              CG_LOG("FieldFilter: reject " << CF->getName()
                     << " for " << callSiteStruct << " field " << callSiteFieldIdx << "\n");
              continue;
            }
          }
          // If function has no entries in funcFieldStores, keep it (conservative)
        }
        if (Ctx->Callees[CS].insert(CF).second) {
          // if new callee added, we need to rerun
          Changed = true;
          CG_LOG("Handle indirect target: " << CF->getName() << "\n");
          if (Ctx->ContainerFuncs.count(CF))
            handleContainerCall(CS, CF);
          else
            handleCall(CS, CF);
        }
      }
    }
  }

  return Changed;
}

// ---- Global union-find dedup ----

NodeIndex CallGraphPass::globalFind(NodeIndex n) {
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

void CallGraphPass::globalDedupScanFunction(const Function *F) {
  if (!F)
    return;

  bool changed = false;
  do {
    changed = false;
    for (const Instruction &I : instructions(F)) {
      if (const auto *BC = dyn_cast<BitCastInst>(&I)) {
        if (!BC->getType()->isPointerTy())
          continue;
        Value *src = BC->getOperand(0);
        if (!src->getType()->isPointerTy())
          continue;
        NodeIndex srcNode = NF.getValueNodeFor(src);
        NodeIndex dstNode = NF.getValueNodeFor(BC);
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
  } while (changed);
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

    // Merge pointer args: actual → formal
    unsigned numArgs = CS->arg_size();
    if (CF->isVarArg()) {
      NodeIndex formalNode = NF.getVarargNodeFor(CF);
      if (formalNode == AndersNodeFactory::InvalidIndex)
        continue;
      for (unsigned i = 0; i < numArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!arg->getType()->isPointerTy())
          continue;
        if (shouldSkipValue(arg))
          continue;
        NodeIndex argNode = NF.getValueNodeFor(arg);
        if (argNode != AndersNodeFactory::InvalidIndex)
          globalUnion(argNode, formalNode);
      }
    } else {
      unsigned numFormals = CF->arg_size();
      unsigned minArgs = std::min(numArgs, numFormals);
      for (unsigned i = 0; i < minArgs; i++) {
        Value *arg = CS->getArgOperand(i);
        if (!arg->getType()->isPointerTy())
          continue;
        if (shouldSkipValue(arg))
          continue;
        NodeIndex argNode = NF.getValueNodeFor(arg);
        if (argNode == AndersNodeFactory::InvalidIndex)
          continue;
        Value *farg = CF->getArg(i);
        NodeIndex formalNode = NF.getValueNodeFor(farg);
        if (formalNode != AndersNodeFactory::InvalidIndex)
          globalUnion(argNode, formalNode);
      }
    }

    // Merge return: returnNode → callsite
    if (CF->getReturnType()->isPointerTy()) {
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

  // Intra-procedural copy merges
  for (auto &[M, _] : Ctx->Modules) {
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (Ctx->AllocFuncs.count(&F) || Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      globalDedupScanFunction(&F);
    }
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

void CallGraphPass::buildDenseMapping() {
  const auto &rawEdges = EB.getEdges();
  origToDense.assign(NF.getNumNodes(), UINT32_MAX);
  denseToOrig.clear();
  numDenseNodes = 0;

  // Assign dense IDs to nodes appearing in edges
  for (const auto &E : rawEdges) {
    if (origToDense[E.from] == UINT32_MAX) {
      origToDense[E.from] = numDenseNodes;
      denseToOrig.push_back(E.from);
      numDenseNodes++;
    }
    if (origToDense[E.to] == UINT32_MAX) {
      origToDense[E.to] = numDenseNodes;
      denseToOrig.push_back(E.to);
      numDenseNodes++;
    }
  }

  // Remap + dedup
  std::unordered_set<EdgeKey, EdgeKeyHash> seen;
  seen.reserve(rawEdges.size());
  denseEdges.clear();
  denseEdges.reserve(rawEdges.size());
  for (const auto &E : rawEdges) {
    uint32_t from = origToDense[E.from];
    uint32_t to = origToDense[E.to];
    if (from == to) continue; // self-loop
    EdgeKey key{from, to, E.label};
    if (seen.insert(key).second)
      denseEdges.emplace_back(from, to, E.label);
  }

  CG_LOG("Dense mapping: " << NF.getNumNodes() << " orig nodes -> "
         << numDenseNodes << " dense nodes, "
         << rawEdges.size() << " raw edges -> "
         << denseEdges.size() << " dense edges\n");
}

uint32_t CallGraphPass::getDenseID(NodeIndex origNode) const {
  NodeIndex canonical = getCanonicalNode(origNode);
  if (canonical < origToDense.size())
    return origToDense[canonical];
  return UINT32_MAX;
}

bool CallGraphPass::doModulePass(Module *M) {
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());

  // process global initializers and functions, only the first iteration
  if (iteration == 0) {
    // Pre-size edge vector on first module to avoid repeated reallocations.
    // Estimate ~4 edges per instruction (each add{Assignment,Dereference}Edges
    // emits 2 edges, and most instructions trigger at least one call).
    if (M == Ctx->Modules.front().first) {
      size_t totalInsts = 0;
      for (auto &[Mod, _] : Ctx->Modules)
        for (Function &F : *Mod)
          totalInsts += F.getInstructionCount();
      EB.reserve(totalInsts * 4);

      // Run global dedup on first module (all nodes exist from doInitialization)
      if (CFLGlobalDedup)
        runGlobalDedup();
    }

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
        EB.addDereferenceEdges(valNode, deref);
        CG_DEBUG("Processing initializer for GV " << GV.getName() << "\n");
        auto init = GV.getInitializer();
        processInitializer(deref, init);
      }
    }

    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty() ||
          Ctx->AllocFuncs.count(&F) ||
          Ctx->ContainerFuncs.count(&F))
        continue;
      if (shouldSkipFunction(&F))
        continue;
      runOnFunction(&F);
    }
  }

  bool Changed = false;
  if (M == Ctx->Modules.back().first) {
    // Analyze edge and cycle patterns before CFL solving
    CG_LOG("Analyzing constraint graph structure...\n");
    std::vector<std::pair<NodeIndex, size_t>> topNodes;
    EB.analyzeHighDegreeNodes(1000, 20, &topNodes);

    // Examine top nodes
    if (!topNodes.empty()) {
      CG_LOG("Examining top " << topNodes.size() << " high-degree nodes:\n");
      for (const auto& [nodeId, degree] : topNodes) {
        NF.dumpNode(nodeId);
      }
    }

    // Build dense mapping if global dedup is active
    if (CFLGlobalDedup)
      buildDenseMapping();

    // solve CFL constraints after processing the last module
    CG_LOG("Using " << cflThreads << " threads for FWGramParallel\n");
    const auto &inputEdges = EB.getEdges();
    const size_t inputEdgeCount = inputEdges.size();
    const auto *Grammar = EB.getGrammar();
    const std::vector<gracfl::Edge> *solverInputEdges = CFLGlobalDedup ? &denseEdges : &inputEdges;
    const size_t solverInputEdgeCount = solverInputEdges->size();

    if (VerboseLevel >= 2 && Grammar) {
      std::vector<size_t> rawLabelCounts(Grammar->getLabelSize(), 0);
      std::unordered_set<EdgeKey, EdgeKeyHash> uniqueInputEdges;
      uniqueInputEdges.reserve(inputEdgeCount + (inputEdgeCount >> 1) + 1);

      for (const auto &E : inputEdges) {
        if (E.label < rawLabelCounts.size())
          rawLabelCounts[E.label]++;
        uniqueInputEdges.insert(EdgeKey{E.from, E.to, E.label});
      }

      const size_t uniqueInputEdgeCount = uniqueInputEdges.size();
      CG_LOG("CFL Input Edges: raw=" << inputEdgeCount
             << ", unique=" << uniqueInputEdgeCount
             << ", duplicates=" << (inputEdgeCount - uniqueInputEdgeCount) << "\n");

      std::vector<std::pair<uint, size_t>> nonZeroLabels;
      nonZeroLabels.reserve(rawLabelCounts.size());
      for (uint L = 0; L < rawLabelCounts.size(); L++) {
        if (rawLabelCounts[L] > 0)
          nonZeroLabels.emplace_back(L, rawLabelCounts[L]);
      }
      std::sort(nonZeroLabels.begin(), nonZeroLabels.end(),
                [](const auto &A, const auto &B) { return A.second > B.second; });

      const auto &idToSymbol = Grammar->getIDToSymbolMap();
      const size_t toReport = std::min<size_t>(8, nonZeroLabels.size());
      CG_LOG("CFL Input Label Distribution (top " << toReport << "/"
             << nonZeroLabels.size() << "):\n");
      for (size_t i = 0; i < toReport; i++) {
        const auto [Label, Count] = nonZeroLabels[i];
        auto It = idToSymbol.find(Label);
        StringRef LabelName = (It != idToSymbol.end()) ? StringRef(It->second) : StringRef("unknown");
        CG_LOG("  " << LabelName << " (" << Label << "): " << Count << "\n");
      }
    }

    bool rebuildSolver = false;
    if (!cflSolver || cflForceRebuild || cflSolvedInputEdgeCount > solverInputEdgeCount) {
      rebuildSolver = true;
    } else {
      // If new edges reference nodes beyond the existing solver graph,
      // rebuild with a resized graph.
      const size_t nodeCount = cflSolver->getNodeCount();
      const size_t beginCheck = cflSolvedInputEdgeCount;
      for (size_t i = beginCheck; i < solverInputEdgeCount; i++) {
        const auto &E = (*solverInputEdges)[i];
        if (E.from >= nodeCount || E.to >= nodeCount) {
          rebuildSolver = true;
          break;
        }
      }
    }

    size_t incrementalAdded = 0;
    if (rebuildSolver) {
      cflSolver = std::make_unique<gracfl::SolverFWGramParallel>(*solverInputEdges, *EB.getGrammar(), cflThreads);
      cflSolvedInputEdgeCount = solverInputEdgeCount;
      cflForceRebuild = false;
      CG_LOG("CFL Mode: full rebuild\n");
    } else if (solverInputEdgeCount > cflSolvedInputEdgeCount) {
      const size_t rawNewEdges = solverInputEdgeCount - cflSolvedInputEdgeCount;
      incrementalAdded = cflSolver->addInputEdges(*solverInputEdges, cflSolvedInputEdgeCount);
      cflSolvedInputEdgeCount = solverInputEdgeCount;
      CG_LOG("CFL Mode: incremental resume with " << incrementalAdded
             << " new frontier edges (" << rawNewEdges
             << " raw additions)\n");
    } else {
      CG_LOG("CFL Mode: reusing cached fixed-point (no new input edges)\n");
    }

    if (rebuildSolver || incrementalAdded > 0) {
      auto initEdges = cflSolver->getEdgeCount();
      CG_LOG("CFL Init Edges: " << initEdges << "\n");
      cflSolver->runCFL();
      auto finalEdges = cflSolver->getEdgeCount();
      CG_LOG("CFL Final Edges: " << finalEdges << "\n");
    }

    const auto &outputCFLGraph = cflSolver->getReachability();

    if (VerboseLevel >= 2 && Grammar && !outputCFLGraph.empty()) {
      std::vector<unsigned long long> finalLabelCounts(outputCFLGraph[0].size(), 0);
      for (const auto &PerNode : outputCFLGraph) {
        for (size_t L = 0; L < PerNode.size(); L++)
          finalLabelCounts[L] += static_cast<unsigned long long>(PerNode[L].size());
      }

      std::vector<std::pair<uint, unsigned long long>> nonZeroLabels;
      nonZeroLabels.reserve(finalLabelCounts.size());
      for (uint L = 0; L < finalLabelCounts.size(); L++) {
        if (finalLabelCounts[L] > 0)
          nonZeroLabels.emplace_back(L, finalLabelCounts[L]);
      }
      std::sort(nonZeroLabels.begin(), nonZeroLabels.end(),
                [](const auto &A, const auto &B) { return A.second > B.second; });

      const auto &idToSymbol = Grammar->getIDToSymbolMap();
      const size_t toReport = std::min<size_t>(10, nonZeroLabels.size());
      CG_LOG("CFL Final Label Distribution (top " << toReport << "/"
             << nonZeroLabels.size() << "):\n");
      for (size_t i = 0; i < toReport; i++) {
        const auto [Label, Count] = nonZeroLabels[i];
        auto It = idToSymbol.find(Label);
        StringRef LabelName = (It != idToSymbol.end()) ? StringRef(It->second) : StringRef("unknown");
        CG_LOG("  " << LabelName << " (" << Label << "): " << Count << "\n");
      }

      if (EB.getLabelV() < finalLabelCounts.size()) {
        CG_LOG("CFL Final V edges: " << finalLabelCounts[EB.getLabelV()] << "\n");
      }
      if (EB.getLabelM() < finalLabelCounts.size()) {
        CG_LOG("CFL Final M edges: " << finalLabelCounts[EB.getLabelM()] << "\n");
      }
    }

    // handle custom allocators
    const bool allocatorRewritten = findCustomAllocators(outputCFLGraph);
    if (allocatorRewritten) {
      // custom allocator discovery may rewrite/remove call edges;
      // trigger a full rebuild on the next iteration.
      cflForceRebuild = true;
      cflSolvedInputEdgeCount = 0;
    }
    Changed |= allocatorRewritten;

    // build field-store map for struct-field-aware filtering
    buildFieldStoreMap(outputCFLGraph);

    // parse results and update call edges
    Changed |= handleIndirectCall(outputCFLGraph);

    iteration++;
  }

  return Changed;
}

// debug
void CallGraphPass::dumpFuncPtrs(raw_ostream &OS) {
  for (FuncPtrMap::iterator i = Ctx->FuncPtrs.begin(),
       e = Ctx->FuncPtrs.end(); i != e; ++i) {
    if (i->second.empty())
      continue;
    OS << i->first << "\n";
    FuncSet &v = i->second;
    for (FuncSet::iterator j = v.begin(), ej = v.end();
         j != ej; ++j) {
      OS << "  " << ((*j)->hasInternalLinkage() ? "f" : "F")
         << " " << (*j)->getName().str() << "\n";
    }
  }
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

  // Collect all functions that appear in Callees or Callers
  DenseSet<const Function *> AllFuncs;
  for (auto &[CS, FS] : Ctx->Callees) {
    const Function *Caller = CS->getFunction();
    if (Caller && !Caller->isDeclaration() && !Caller->isIntrinsic())
      AllFuncs.insert(Caller);
    for (const Function *F : FS) {
      if (F && (!F->isIntrinsic() || isImportantIntrinsic(F)))
        AllFuncs.insert(F);
    }
  }
  for (auto &[F, CIS] : Ctx->Callers) {
    if (F && !F->isDeclaration() && !F->isIntrinsic())
      AllFuncs.insert(F);
  }

  json::Object Functions;
  size_t totalEdges = 0, directEdges = 0, indirectEdges = 0;

  for (const Function *F : AllFuncs) {
    if (F->isIntrinsic() && !isImportantIntrinsic(F))
      continue;
    if (F->isDeclaration() && !isImportantIntrinsic(F))
      continue;

    std::string FuncID = getFuncId(F);
    std::string SrcFile = getFuncSourceFile(F);
    auto [LineStart, LineEnd] = getFuncLineRange(F);

    json::Object FuncObj;
    FuncObj["file"] = SrcFile;
    if (LineStart > 0)
      FuncObj["line_start"] = static_cast<int64_t>(LineStart);
    if (LineEnd > 0)
      FuncObj["line_end"] = static_cast<int64_t>(LineEnd);
    FuncObj["linkage"] = F->hasExternalLinkage() ? "external" : "internal";

    // Build callees array by iterating call instructions in this function
    json::Array CalleesArr;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        const CallBase *CI = dyn_cast<CallBase>(&I);
        if (!CI || CI->isInlineAsm())
          continue;

        auto it = Ctx->Callees.find(CI);
        if (it == Ctx->Callees.end())
          continue;

        bool isDirect = (CI->getCalledFunction() != nullptr);
        unsigned line = getCallLine(CI);

        for (const Function *Callee : it->second) {
          if (Callee->isIntrinsic() && !isImportantIntrinsic(Callee))
            continue;
          json::Object Edge;
          Edge["callee"] = getFuncId(Callee);
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
    FuncObj["callees"] = std::move(CalleesArr);

    // Build callers array
    json::Array CallersArr;
    auto callerIt = Ctx->Callers.find(F);
    if (callerIt != Ctx->Callers.end()) {
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

void CallGraphPass::dumpVSnapshot(StringRef Path) {
  const cfl_result_t *GraphPtr = nullptr;
  std::unique_ptr<gracfl::SolverFWGramParallel> TmpSolver;
  if (cflSolver) {
    GraphPtr = &cflSolver->getReachability();
  } else {
    TmpSolver = std::make_unique<gracfl::SolverFWGramParallel>(EB.getEdges(), *EB.getGrammar(), cflThreads);
    TmpSolver->runCFL();
    GraphPtr = &TmpSolver->getReachability();
  }
  if (!GraphPtr || GraphPtr->empty()) {
    WARNING("VSnapshot: empty CFL graph, skip export to " << Path << "\n");
    return;
  }

  const auto &Graph = *GraphPtr;
  const uint32_t LabelV = EB.getLabelV();
  if (Graph[0].size() <= LabelV) {
    WARNING("VSnapshot: V label index " << LabelV << " is out of range\n");
    return;
  }

  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  const uint32_t NodeCount = NF.getNumNodes();

  if (!useDense && Graph.size() < NodeCount) {
    WARNING("VSnapshot: CFL graph node count " << Graph.size()
            << " is smaller than NodeFactory node count " << NodeCount << "\n");
    return;
  }

  std::unordered_map<NodeIndex, uint32_t> RootToDense;
  RootToDense.reserve(NodeCount);
  std::vector<uint32_t> NodeToRepDense(NodeCount, 0);
  std::vector<uint32_t> RepToNode;
  RepToNode.reserve(NodeCount);
  std::vector<std::vector<uint32_t>> MembersByRep;
  MembersByRep.reserve(NodeCount);
  for (uint32_t N = 0; N < NodeCount; N++) {
    NodeIndex Root = getCanonicalNode(N);
    auto It = RootToDense.find(Root);
    uint32_t Dense = 0;
    if (It == RootToDense.end()) {
      Dense = static_cast<uint32_t>(RepToNode.size());
      RootToDense.emplace(Root, Dense);
      RepToNode.push_back(Root);
      MembersByRep.emplace_back();
    } else {
      Dense = It->second;
    }
    NodeToRepDense[N] = Dense;
    MembersByRep[Dense].push_back(N);
  }
  const uint32_t RepCount = static_cast<uint32_t>(RepToNode.size());

  std::vector<VSnapshotNamedEntry> NamedEntries;
  NamedEntries.reserve(NodeCount / 8 + 32);
  for (uint32_t N = 0; N < NodeCount; N++) {
    const Value *V = NF.getValueForNode(N);
    if (!V)
      continue;

    VSnapshotNamedEntry E;
    E.node = N;

    if (NF.isReturnNode(N)) {
      const Function *F = dyn_cast<Function>(V);
      if (!F)
        continue;
      E.kind = 6; // return node
      E.name = ("ret:" + F->getName()).str();
      NamedEntries.push_back(std::move(E));
      continue;
    }
    if (NF.isVarargNode(N)) {
      const Function *F = dyn_cast<Function>(V);
      if (!F)
        continue;
      E.kind = 7; // vararg node
      E.name = ("vararg:" + F->getName()).str();
      NamedEntries.push_back(std::move(E));
      continue;
    }

    if (const Function *F = dyn_cast<Function>(V)) {
      E.kind = 1;
      E.name = F->getName().str();
    } else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(V)) {
      E.kind = 2;
      E.name = GV->getName().str();
    } else if (const Argument *A = dyn_cast<Argument>(V)) {
      E.kind = 3;
      const Function *F = A->getParent();
      std::string FName = F ? F->getName().str() : std::string("<unknown>");
      if (A->hasName())
        E.name = FName + "::arg:" + A->getName().str();
      else
        E.name = FName + "::arg#" + std::to_string(A->getArgNo());
    } else if (const Instruction *I = dyn_cast<Instruction>(V)) {
      if (!I->hasName())
        continue;
      E.kind = 4;
      const Function *F = I->getFunction();
      std::string FName = F ? F->getName().str() : std::string("<unknown>");
      E.name = FName + "::%" + I->getName().str();
    } else if (V->hasName()) {
      E.kind = 5;
      E.name = V->getName().str();
    } else {
      continue;
    }

    if (!E.name.empty())
      NamedEntries.push_back(std::move(E));
  }

  std::sort(NamedEntries.begin(), NamedEntries.end(),
            [](const VSnapshotNamedEntry &A, const VSnapshotNamedEntry &B) {
              if (A.name != B.name)
                return A.name < B.name;
              if (A.kind != B.kind)
                return A.kind < B.kind;
              return A.node < B.node;
            });

  json::Object MetaObj;
  MetaObj["tool"] = "kanalyzer";
  MetaObj["snapshot_type"] = "V-relation";
  MetaObj["version"] = static_cast<int64_t>(VSnapshotData::kVersion);
  MetaObj["label_v"] = static_cast<int64_t>(LabelV);
  MetaObj["global_dedup"] = static_cast<bool>(CFLGlobalDedup);
  MetaObj["local_alloca_summary"] = static_cast<bool>(CFLLocalAllocaSummary);
  MetaObj["node_count"] = static_cast<int64_t>(NodeCount);
  MetaObj["rep_count"] = static_cast<int64_t>(RepCount);

  VSnapshotData Data;
  Data.labelV = LabelV;
  Data.flags = 0;
  Data.metadataJson = formatv("{0}", json::Value(std::move(MetaObj))).str();
  Data.nodeToRep = std::move(NodeToRepDense);
  Data.repToNode = std::move(RepToNode);
  Data.namedEntries = std::move(NamedEntries);

  std::string ErrMsg;
  uint64_t EdgeCount = 0;
  auto RowProvider = [&](uint32_t Rep, std::vector<uint32_t> &RowOut) {
    std::unordered_set<uint32_t> Dsts;
    for (uint32_t Member : MembersByRep[Rep]) {
      if (useDense) {
        // Map original node → dense CFL graph index
        uint32_t denseIdx = (Member < origToDense.size()) ? origToDense[Member] : UINT32_MAX;
        if (denseIdx == UINT32_MAX || denseIdx >= Graph.size())
          continue;
        const auto &VSet = Graph[denseIdx][LabelV];
        Dsts.reserve(Dsts.size() + VSet.size());
        for (NodeIndex D : VSet) {
          // Map dense result back to original node, then to rep
          if (D >= denseToOrig.size()) continue;
          NodeIndex origD = denseToOrig[D];
          if (origD >= NodeCount) continue;
          Dsts.insert(Data.nodeToRep[origD]);
        }
      } else {
        assert(Member < Graph.size() && "member node out of CFL graph range");
        const auto &VSet = Graph[Member][LabelV];
        Dsts.reserve(Dsts.size() + VSet.size());
        for (NodeIndex D : VSet) {
          if (D >= NodeCount)
            continue;
          Dsts.insert(Data.nodeToRep[D]);
        }
      }
    }
    RowOut.assign(Dsts.begin(), Dsts.end());
    EdgeCount += RowOut.size();
  };

  if (!saveVSnapshotWithRowProvider(Path, Data, RowProvider, &ErrMsg)) {
    WARNING("VSnapshot: failed to export " << Path << ": " << ErrMsg << "\n");
    return;
  }
  CG_LOG("Exported V snapshot to " << Path
         << ": nodes=" << Data.nodeToRep.size()
         << ", reps=" << Data.repToNode.size()
         << ", V-edges=" << EdgeCount
         << ", names=" << Data.namedEntries.size() << "\n");
}

void CallGraphPass::dumpGlobals(raw_ostream &OS) {
  CG_LOG("\n[dumpGlobals]\n");
  const bool useDense = CFLGlobalDedup && !origToDense.empty();
  const auto &solverEdges = useDense ? denseEdges : EB.getEdges();
  auto solver = std::make_unique<gracfl::SolverFWGramParallel>(solverEdges, *EB.getGrammar(), cflThreads);
  solver->runCFL();
  const auto &outputCFLGraph = solver->getReachability();
  for (auto &it : Ctx->Gobjs) {
    Value *GV = it.second;
    NodeIndex valNode;
    if (useDense) {
      valNode = getDenseID(NF.getValueNodeFor(GV));
      if (valNode == UINT32_MAX) continue;
    } else {
      valNode = getCanonicalNode(NF.getValueNodeFor(GV));
    }
    if (valNode != AndersNodeFactory::InvalidIndex) {
      assert(valNode < outputCFLGraph.size() && "Global node out of CFL graph range");
      auto &cflSect = outputCFLGraph[valNode][EB.getLabelV()];
      if (cflSect.empty())
        continue;
      CG_DEBUG("GlobalVar: " << GV->getName() << " : " << valNode << " ->\n");
      for (auto idx : cflSect) {
        NodeIndex origIdx = useDense ? denseToOrig[idx] : idx;
        if (origIdx == valNode)
          continue;
        if (NF.isSpecialNode(origIdx)) {
          CG_DEBUG("\tSpecialNode: " << origIdx << "\n");
          continue;
        }
        const Value *CV = NF.getValueForNode(origIdx);
        if (CV == NULL) {
          CG_DEBUG("\tNoValue: " << origIdx << "\n");
          continue;
        }
        CG_DEBUG("\t" << *CV << " : " << origIdx << "\n");
      }
    }
  }
  CG_LOG("\n[End of dumpGlobals]\n");
}
