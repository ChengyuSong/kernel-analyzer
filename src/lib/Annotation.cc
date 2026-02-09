/*
 * Annotation utility functions
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 *
 * For licensing details see LICENSE
 */


#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Constants.h>
#include <llvm/Pass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/Transforms/Utils/Local.h>
#include "llvm/Support/DJB.h"

#include "Annotation.h"
#include "Flags.h"
#include "Common.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

using namespace llvm;

// static inline bool needAnnotation(Value *V) {
//   if (PointerType *PTy = dyn_cast<PointerType>(V->getType())) {
//     Type *Ty = PTy->getElementType();
//     return (Ty->isIntegerTy() || isFunctionPointer(Ty));
//   }
//   return false;
// }

//
// Functions will be included under 2 criteria:
// 1. primitive allocators, e.g., kmalloc
// 2. wrapper allocator that does not directly
//    return the results from primitive allocator,
//    e.g., devres_alloc
//
// flag stores the arg number of the flag operand
// size stores the arg number of the size operand
//
bool isAllocFn(StringRef name, int *size, int *flag) {

  // user space
  // malloc/new
  if (name.equals("malloc") ||
    name.equals("_Znwj") ||
    name.equals("_ZnwjRKSt9nothrow_t") ||
    name.equals("_Znwm") ||
    name.equals("_ZnwmRKSt9nothrow_t") ||
    name.equals("_Znaj") ||
    name.equals("_ZnajRKSt9nothrow_t") ||
    name.equals("_Znam") ||
    name.equals("_ZnamRKSt9nothrow_t")) {
    *size = 0;
    *flag = -1;
    return true;
  }

  // Core slab allocators - basic kmalloc family
  // don't handle variable length yet
  if (name.equals("kmalloc_array") ||
    name.equals("kcalloc") ||
    name.equals("kmalloc_array_node") ||
    name.equals("kcalloc_node") ||
    name.equals("krealloc_array"))
    return false;

  if (LLVM_STRING_STARTS_WITH(name, "kmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "__kmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "kzalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // kmem_cache_alloc family
  if (LLVM_STRING_STARTS_WITH(name, "kmem_cache_alloc") ||
    name.equals("kmem_cache_zalloc")) {
    *size = -1;
    *flag = 1;
    return true;
  }

  // kvmalloc family (hybrid kmalloc/vmalloc)
  if (LLVM_STRING_STARTS_WITH(name, "kvmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "kvzalloc") ||
    name.equals("kvrealloc") ||
    name.equals("kvcalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // vmalloc family
  if (LLVM_STRING_STARTS_WITH(name, "vmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "vzalloc") ||
    LLVM_STRING_STARTS_WITH(name, "__vmalloc") ||
    name.equals("vcalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // kmemdup
  if (name.equals("kmemdup")) {
    *size = 1;
    *flag = 2;
    return true;
  }

  if (name.equals("kstrndup") ||
      name.equals("kstrdup"))
    return false;

  if (name.equals("krealloc") ||
    name.equals("__krealloc")) {
    *size = 1;
    *flag = 2;
    return true;
  }

  // Device-managed allocators (devm_*)
  if (LLVM_STRING_STARTS_WITH(name, "devm_kmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "devm_kzalloc") ||
    name.equals("devm_krealloc") ||
    name.equals("devm_kmemdup") ||
    name.equals("alloc_dr") ||
    name.equals("__devres_alloc") ||
    name.equals("devres_alloc")) {
    *size = 1;
    *flag = 2;
    return true;
  }

  // DRM-managed allocators (drmm_*)
  if (LLVM_STRING_STARTS_WITH(name, "drmm_kmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "drmm_kzalloc")) {
    *size = 1;
    *flag = 2;
    return true;
  }

  // Page allocators
  if (name.equals("alloc_pages") ||
    name.equals("alloc_pages_node") ||
    name.equals("alloc_pages_mpol") ||
    name.equals("alloc_page") ||
    name.equals("alloc_page_vma") ||
    name.equals("__get_free_pages") ||
    name.equals("__get_free_page") ||
    name.equals("__get_dma_pages")) {
    *size = -1;
    *flag = 0;
    return true;
  }

  // DMA allocators
  if (name.equals("dma_alloc_attrs") ||
    name.equals("dma_alloc_coherent") ||
    name.equals("dma_alloc_noncoherent") ||
    name.equals("dma_alloc_wc") ||
    name.equals("dma_alloc_from_global_coherent")) {
    *size = 1;
    *flag = 2;
    return true;
  }

  // Memory pool allocators
  if (name.equals("mempool_alloc")) {
    *size = -1;
    *flag = 1;
    return false;
  }

  if (name.equals("mempool_alloc_slab") ||
    name.equals("mempool_kmalloc")) {
    *size = -1;
    *flag = 0;
    return true;
  }

  if (name.equals("mempool_alloc_pages"))
    return false;

  // Bio/block allocators
  if (name.equals("bio_alloc") ||
    name.equals("bio_kmalloc")) {
    *size = -1;
    *flag = 0;
    return true;
  }

  if (name.equals("bio_alloc_bioset")) {
    *size = -1;
    *flag = 0;
    return true;
  }

  // Networking allocators
  if (name.equals("sk_prot_alloc")) {
    *size = -1;
    *flag = 1;
    return true;
  }

  if (name.equals("sk_alloc")) {
    *size = -1;
    *flag = 2;
    return true;
  }

  if (name.equals("sock_kmalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  if (name.equals("__netdev_alloc_skb") ||
    name.equals("__dev_alloc_page") ||
    name.equals("dev_alloc_page")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // Filesystem-specific wrappers
  // F2FS
  if (LLVM_STRING_STARTS_WITH(name, "f2fs_kmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "f2fs_kzalloc") ||
    LLVM_STRING_STARTS_WITH(name, "f2fs_kvmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "f2fs_kvzalloc") ||
    name.equals("f2fs_kmem_cache_alloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // Bcachefs
  if (name.equals("bch2_trans_kmalloc") ||
    name.equals("__bch2_trans_kmalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // NTFS
  if (name.equals("__ntfs_malloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // BPF allocators
  if (name.equals("bpf_map_kzalloc") ||
    name.equals("bpf_map_kvcalloc") ||
    name.equals("bpf_map_kmalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // KUnit test allocators
  if (LLVM_STRING_STARTS_WITH(name, "kunit_kmalloc") ||
    LLVM_STRING_STARTS_WITH(name, "kunit_kzalloc") ||
    name.equals("kunit_kcalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // Per-CPU allocators
  if (name.equals("alloc_percpu") ||
    name.equals("__alloc_percpu") ||
    name.equals("__alloc_percpu_gfp")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // KASAN/KFENCE instrumented
  if (name.equals("__kfence_alloc") ||
    name.equals("kfence_alloc") ||
    name.equals("__kasan_kmalloc") ||
    name.equals("__kasan_slab_alloc") ||
    name.equals("kasan_kmalloc_large")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // Driver-specific allocators
  if (name.equals("flexcop_device_kmalloc") ||
    name.equals("tasdevice_kzalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // Crypto allocators
  if (name.equals("jent_kvzalloc") ||
    name.equals("jent_zalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  // Architecture-specific
  if (name.equals("uml_kmalloc")) {
    *size = 0;
    *flag = 1;
    return true;
  }

  return false;
}

bool isFreeFn(StringRef name) {
  // Core slab/kmalloc free functions
  if (name.equals("kfree") ||
      name.equals("kfree_sensitive") ||
      name.equals("kzfree")) {
    return true;
  }

  // kvmalloc free
  if (name.equals("kvfree")) {
    return true;
  }

  // vmalloc free
  if (name.equals("vfree") ||
      name.equals("vfree_atomic")) {
    return true;
  }

  // Cache free
  if (name.equals("kmem_cache_free")) {
    return true;
  }

  // Device-managed free (typically auto-freed, but can be explicit)
  if (name.equals("devm_kfree")) {
    return true;
  }

  // DRM-managed free
  if (name.equals("drmm_kfree")) {
    return true;
  }

  // Page free
  if (name.equals("__free_pages") ||
      name.equals("free_pages") ||
      name.equals("free_page") ||
      name.equals("put_page") ||
      name.equals("__free_page")) {
    return true;
  }

  // DMA free
  if (name.equals("dma_free_coherent") ||
      name.equals("dma_free_attrs") ||
      name.equals("dma_free_noncoherent") ||
      name.equals("dma_free_wc")) {
    return true;
  }

  // Memory pool free
  if (name.equals("mempool_free")) {
    return true;
  }

  // Bio/block free
  if (name.equals("bio_put") ||
      name.equals("bio_free")) {
    return true;
  }

  // Networking free
  if (name.equals("sock_kfree_s") ||
      name.equals("kfree_skb") ||
      name.equals("__kfree_skb") ||
      name.equals("consume_skb") ||
      name.equals("kfree_skb_reason") ||
      name.equals("__kfree_skb_defer") ||
      name.equals("dev_kfree_skb") ||
      name.equals("dev_kfree_skb_any") ||
      name.equals("dev_kfree_skb_irq")) {
    return true;
  }

  // Per-CPU free
  if (name.equals("free_percpu")) {
    return true;
  }

  // KUnit test free
  if (name.equals("kunit_kfree")) {
    return true;
  }

  // Filesystem-specific free
  if (LLVM_STRING_STARTS_WITH(name, "f2fs_kfree") ||
      LLVM_STRING_STARTS_WITH(name, "f2fs_kvfree")) {
    return true;
  }

  // BPF free
  if (name.equals("bpf_map_kfree") ||
      name.equals("bpf_map_kvfree")) {
    return true;
  }

  // Crypto free
  if (name.equals("jent_zfree") ||
      name.equals("jent_kvzfree")) {
    return true;
  }

  // String free
  if (name.equals("kfree_const")) {
    return true;
  }

  // RCU-based free (deferred)
  if (name.equals("kfree_rcu") ||
      name.equals("kvfree_rcu")) {
    return true;
  }

  return false;
}

bool isEntryFn(StringRef name) {
  if (name.equals("main") ||
    LLVM_STRING_STARTS_WITH(name, "do_syscall_") ||
    LLVM_STRING_ENDS_WITH(name, "do_softirq") ||
    name.equals("start_kernel") ||
    name.equals("init") ||
    name.equals("module_init") ||
    name.equals("module_exit") ||
    name.equals("init_module") ||
    name.equals("cleanup_module") ||
    name.equals("do_init_module") ||
    name.equals("do_cleanup_module") ||
    name.equals("do_one_initcall") ||
    name.equals("do_one_initcall_sync"))
    return true;
  else return false;
}

bool isExitFn(StringRef name) {
  if (name.equals("exit") ||
    name.equals("_exit") ||
    name.equals("_Exit") ||
    name.equals("exit_group") ||
    name.equals("panic") ||
    name.equals("BUG") ||
    name.equals("BUG_ON"))
    return true;
  else return false;
}

bool isPrintFn(StringRef name) {
  if (name.find("print") != StringRef::npos ||
    name.find("dump") != StringRef::npos ||
    name.find("log") != StringRef::npos ||
    name.find("warn") != StringRef::npos ||
    name.find("info") != StringRef::npos ||
    name.find("msg") != StringRef::npos ||
    name.find("trace") != StringRef::npos ||
    name.find("report") != StringRef::npos ||
    name.find("show") != StringRef::npos ||
    name.find("display") != StringRef::npos ||
    name.find("dmsg") != StringRef::npos)
    return true;
  else return false;
}

bool isKernelUtilityFn(StringRef name) {
  // Common kernel utility functions that create high-degree nodes
  // These functions don't contribute to meaningful points-to analysis

  // Printing and debug functions
  if (name.equals("_printk") ||
      name.equals("printk") ||
      name.equals("__warn_printk") ||
      name.equals("seq_printf"))
    return true;

  // Lock/unlock operations (just synchronization, no data flow)
  if (name.equals("mutex_lock") ||
      name.equals("mutex_unlock") ||
      name.equals("mutex_lock_nested") ||
      LLVM_STRING_STARTS_WITH(name, "_raw_spin_") ||
      LLVM_STRING_STARTS_WITH(name, "_raw_read_") ||
      LLVM_STRING_STARTS_WITH(name, "_raw_write_") ||
      name.equals("spin_lock") ||
      name.equals("spin_unlock"))
    return true;

  // RCU and lockdep (debug/validation, no data flow)
  if (LLVM_STRING_STARTS_WITH(name, "lockdep_") ||
      LLVM_STRING_STARTS_WITH(name, "lock_") ||
      LLVM_STRING_STARTS_WITH(name, "rcu_"))
    return true;

  // String operations (utility, high fan-out)
  if (name.equals("strlen") ||
      name.equals("strcmp") ||
      name.equals("strncmp") ||
      name.equals("strcpy") ||
      name.equals("strncpy"))
    return true;

  // Reference counting (just increment/decrement)
  if (LLVM_STRING_STARTS_WITH(name, "refcount_") ||
      LLVM_STRING_STARTS_WITH(name, "atomic_") ||
      LLVM_STRING_STARTS_WITH(name, "atomic64_"))
    return true;

  return false;
}

bool isCompilerIntroducedValue(const Value *V) {
  if (!V || !V->hasName())
    return false;

  StringRef name = V->getName();

  // LLVM compiler-introduced globals
  if (name.equals("llvm.compiler.used") ||
      name.equals("llvm.used") ||
      name.equals("llvm.global_ctors") ||
      name.equals("llvm.global_dtors") ||
      LLVM_STRING_STARTS_WITH(name, "llvm."))
    return true;

  return false;
}

std::string getStoreId(StoreInst *SI) {
  StringRef Id = getLoadStoreId(SI);
  if (!Id.empty())
    return Id.str();

  std::string Anno;
  LLVMContext &VMCtx = SI->getContext();
  Module *M = SI->getParent()->getParent()->getParent();
  Value *V = SI->getPointerOperand();
  Anno = getAnnotation(V, M);
  if (Anno.empty())
    return Anno;

  MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, Anno));
  SI->setMetadata(MD_ID, MD);
  return Anno;
}

std::string getLoadId(LoadInst *LI) {
  StringRef Id = getLoadStoreId(LI);
  if (!Id.empty())
    return Id.str();

  std::string Anno;
  LLVMContext &VMCtx = LI->getContext();
  Module *M = LI->getParent()->getParent()->getParent();
  Value *V = LI->getPointerOperand();
  Anno = getAnnotation(V, M);
  if (Anno.empty())
    return Anno;

  MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, Anno));
  LI->setMetadata(MD_ID, MD);
  return Anno;
}

std::string getStructId(Value *PVal, User::op_iterator &IS, User::op_iterator &IE, Module *M) {

//  Type *PTy = PVal->getType();
  StructType *STy = nullptr;
//   for (++IE; IS != IE; ++IS) {
//     if (!CT) break;
//     if ((STy = dyn_cast<StructType>(CT))) break;
//     if (!CT->indexValid(*IS)) break;
//     PTy = CT->getTypeAtIndex(*IS);
//   }

  if (STy && !STy->isOpaque() && !STy->isLiteral()) {
    std::string out;
    raw_string_ostream rso(out);

    std::string structName = STy->getStructName().str();
    if (structName.find("struct.anon") == 0) {
      structName = getScopeName(STy, M);
      structName = getAnonStructId(PVal, M, structName);
    } else if (structName.find("struct.hlist_") == 0||
      !structName.compare("struct.list_head") ||
      !structName.compare("struct.atomic_t") ||
      !structName.compare("struct.atomic64_t")) {
      structName = getAnonStructId(PVal, M, "");
      if (structName.empty())
        return "";
    }

    rso << structName;
    for (; IS != IE; ++IS) {
      rso << ",";
      ConstantInt *Idx = dyn_cast<ConstantInt>(*IS);
      if (Idx)
        rso << Idx->getZExtValue();
      else
        (*IS)->printAsOperand(rso);
    }
    return rso.str();
  }
  return "";
}

std::string getAnonStructId(Value *V, Module *M, StringRef Prefix) {
  
  SmallPtrSet<Value*, 4> Visited;
  SmallVector<Value*, 4> WorkList;

  Visited.insert(V);
  WorkList.push_back(V);

  while (!WorkList.empty()) {
    Value *v = WorkList.pop_back_val();

    // only handle GEP and cast
    User::op_iterator is, ie; // GEP indices
    Value *PVal = NULL;       // Pointer operand in the GEP
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(v)) {
      // GEP instruction
      is = GEP->idx_begin();
      ie = GEP->idx_end() - 1;
      PVal = GEP->getPointerOperand();
    } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(v)) {
      // constant GEP expression
      if (CE->getOpcode() == Instruction::GetElementPtr) {
        is = CE->op_begin() + 1;
        ie = CE->op_end() - 1;
        PVal = CE->getOperand(0);
      } else if (CE->isCast()) {
        if (Visited.insert(CE->getOperand(0)).second)
          WorkList.push_back(CE->getOperand(0));
        continue;
      }
    }

    // id is in the form of struct.[name].[offset]
    if (PVal) {
      // prefer global over struct
      if (GlobalValue *GV = dyn_cast<GlobalValue>(PVal)) {
        return getVarId(GV);
      }

      std::string structId = getStructId(PVal, is, ie, M);
      if (!structId.empty())
        return structId;
    }

    if (CastInst *CI = dyn_cast<CastInst>(v)) {
      if (Visited.insert(CI->getOperand(0)).second)
        WorkList.push_back(CI->getOperand(0));
      continue;
    }

#if 0
    if (AllocaInst *AI = dyn_cast<AllocaInst>(v)) {
      return getVarId(AI);
    }

    if (GlobalVariable *GV = dyn_cast<GlobalVariable>(v)) {
      return getVarId(GV);
    }

    Type *Ty = v->getType();
    while (Ty->isPointerTy())
      Ty = Ty->getContainedType(0);
    if (StructType *STy = dyn_cast<StructType>(Ty)) {
      if (!LLVM_STRING_STARTS_WITH(STy->getStructName(), "struct.anon")) {
        return STy->getStructName();
      }
    }
#endif

    //WARNING("Invalid anon struct value " << *v << "\n");
    break;
  }

  return Prefix.str();
}

std::string getAnnotation(Value *V, Module *M) {

  SmallPtrSet<Value*, 16> Visited;
  SmallVector<Value*, 8> WorkList;

  Visited.insert(V);
  WorkList.push_back(V);

  while (!WorkList.empty()) {
    Value *v = WorkList.pop_back_val();

    if (GlobalVariable *GV = dyn_cast<GlobalVariable>(v))
      return getVarId(GV);

    if (Argument *A = dyn_cast<Argument>(v))
      return getArgId(A);

    User::op_iterator is, ie; // GEP indices
    Value *PVal = NULL;       // Pointer operand in the GEP
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(v)) {
      // GEP instruction
      is = GEP->idx_begin();
      ie = GEP->idx_end() - 1;
      PVal = GEP->getPointerOperand();
    } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(v)) {
      // constant GEP expression
      if (CE->getOpcode() == Instruction::GetElementPtr) {
        is = CE->op_begin() + 1;
        ie = CE->op_end() - 1;
        PVal = CE->getOperand(0);
      } else if (CE->isCast()) {
        if (Visited.insert(CE->getOperand(0)).second)
          WorkList.push_back(CE->getOperand(0));
        continue;
      }
    }

    // id is in the form of struct.[name].[offset]
    if (PVal) {
      std::string structId = getStructId(PVal, is, ie, M);
      if (!structId.empty()) {
        return structId;
      } else {
        if (Visited.insert(PVal).second)
          WorkList.push_back(PVal);
        //Instruction *i = cast<Instruction>(v);
        //Function *f = i->getParent()->getParent();
        //errs() << "Unsupported GEP: " << f->getName() << "::" << *i << "\n";
        //errs() << "\t Pointer: " << *PVal << "\n";
        continue;
      }
    }

    if (AllocaInst *AI = dyn_cast<AllocaInst>(v)) {
      return getVarId(AI);
    }

    if (CastInst *CI = dyn_cast<CastInst>(v)) {
      if (Visited.insert(CI->getOperand(0)).second)
        WorkList.push_back(CI->getOperand(0));
      continue;
    }

    if (CallInst *CI = dyn_cast<CallInst>(v)) {
      Value *CV = CI->getOperand(0);
      // handle simple cast expr
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(CV)) {
        if (CE->isCast())
          CV = CE->getOperand(0);
      }
      Function *F = dyn_cast<Function>(CV);
      if (F != NULL) {
        // check for alloc function
        StringRef name = F->getName();
        if (isAllocFn(name)) {
          // return the loc
          std::string loc;
          raw_string_ostream rso(loc);
          const DebugLoc &LOC = CI->getDebugLoc();
          LOC.print(rso);
          return rso.str();
        } else
          return getRetId(F);
      }
    }

    if (LoadInst *LI = dyn_cast<LoadInst>(v)) {
      Value *S = LI->getPointerOperand();
      if (Visited.insert(S).second)
        WorkList.push_back(S);
      continue;
    }

    if (PHINode *PHI = dyn_cast<PHINode>(v)) {
      for (unsigned i = 0, e = PHI->getNumIncomingValues(); i < e; ++i) {
        if (Visited.insert(PHI->getIncomingValue(i)).second)
          WorkList.push_back(PHI->getIncomingValue(i));
      }
      continue;
    }

    if (SelectInst *SEI = dyn_cast<SelectInst>(v)) {
      if (Visited.insert(SEI->getTrueValue()).second)
        WorkList.push_back(SEI->getTrueValue());
      if (Visited.insert(SEI->getFalseValue()).second)
        WorkList.push_back(SEI->getFalseValue());
      continue;
    }

    if (BinaryOperator *BO = dyn_cast<BinaryOperator>(v)) {
      // only when one of the operand is a constant int
      if (isa<ConstantInt>(BO->getOperand(1))) {
        if (Visited.insert(BO->getOperand(0)).second)
          WorkList.push_back(BO->getOperand(0));
        continue;
      }

      if (isa<ConstantInt>(BO->getOperand(0))) {
        if (Visited.insert(BO->getOperand(1)).second)
          WorkList.push_back(BO->getOperand(1));
        continue;
      }
    }

    //WARNING("Unsupported annotation source: " << *v << "\n");
  }
  return std::string();
}

static inline void getInsDebugLoc(const Instruction *I, StringRef &Filename,
                                  unsigned &Line, unsigned &Col) {
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename();
    Col = Loc->getColumn();
    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Col = oDILoc->getColumn();
        Filename = oDILoc->getFilename();
      }
    }
  }
}


static inline void getBBDebugLoc(const BasicBlock *BB, std::string &Filename, unsigned &Line, unsigned &Col) {
  std::string bb_name("");
  StringRef filename;
  unsigned line = 0;
  unsigned col = 0;
  for (auto &I : *BB) {
    getInsDebugLoc(&I, filename, line, col);
    if (filename.empty() || line == 0 || LLVM_STRING_STARTS_WITH(filename, "/usr/"))
      continue;
    std::size_t found = filename.find_last_of("/\\");
    if (found != std::string::npos)
      filename = filename.substr(found + 1);
    Filename = filename.str();
    Line = line;
    Col = col;
    break;
  }
}

uint32_t getBasicBlockId(const BasicBlock *BB) {
  static uint32_t unamed = 0;
  std::string bb_name_with_col("");
  std::string filename;
  unsigned line = 0;
  unsigned col = 0;
  getBBDebugLoc(BB, filename, line, col);
  if (!filename.empty() && line != 0 ) {
    bb_name_with_col = filename + ":" + std::to_string(line) + ":" + std::to_string(col);
  } else {
    filename = BB->getParent()->getParent()->getSourceFileName();
    std::size_t found = filename.find_last_of("/\\");
    if (found != std::string::npos)
      filename = filename.substr(found + 1);
    bb_name_with_col = filename + ":unamed:" + std::to_string(unamed++);
  }
  return djbHash(bb_name_with_col);
}
