#ifndef _GLOBAL_H
#define _GLOBAL_H

#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/CommandLine.h>

#include <map>
#include <unordered_map>
#include <deque>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>

#include <boost/unordered/unordered_flat_map.hpp>

#include "Common.h"
#include "StructAnalyzer.h"
#include "NodeFactory.h"
#include "ConstraintGraph.h"

typedef std::vector< std::pair<llvm::Module*, llvm::StringRef> > ModuleList;

// Fn-ptr slot census (CallGraph.cc): every (deepest named struct, byte
// offset) observed to HOLD a function, from global initializers and
// direct fn-constant stores. Shared by --cfl-dump-fnptr-offsets and
// the --cfl-field-buckets-auto Z_P selector.
void kaCollectFnPtrOffsets(
    ModuleList &modules,
    llvm::function_ref<void(llvm::StringRef, uint64_t, llvm::StringRef)>
        sink);
typedef std::unordered_map<llvm::Module*, llvm::StringRef> ModuleMap;

typedef llvm::SmallPtrSet<const llvm::CallBase*, 8> CallInstSet;
typedef llvm::SmallPtrSet<const llvm::Function*, 8> FuncSet;
typedef std::unordered_map<NodeIndex, FuncSet> FuncPtrMap;

typedef llvm::DenseMap<const llvm::Function*, CallInstSet> CallerMap;
typedef llvm::DenseMap<const llvm::CallBase*, FuncSet> CalleeMap;
typedef llvm::DenseMap<const llvm::Function*, const llvm::ReturnInst*> RetSiteMap;


class GlobalContext {
private:
  // pass specific data
  std::map<std::string, void*> PassData;

public:
  bool add(std::string name, void* data) {
    if (PassData.find(name) != PassData.end())
      return false;

    PassData[name] = data;
    return true;
  }

  void* get(std::string name) {
    std::map<std::string, void*>::iterator itr;

    itr = PassData.find(name);
    if (itr != PassData.end())
      return itr->second;
    else
      return nullptr;
  }

  // StructAnalyzer
  StructAnalyzer structAnalyzer;

  // Map global object name to object definition
  GObjMap Gobjs;

  // Map external global object name to a single declaration
  GObjMap ExtGobjs;

  // Map global function name to function defination
  FuncMap Funcs;

  // Map external global function name to a single declaration
  FuncMap ExtFuncs;

  // Map function signature to function definition
  std::unordered_map<size_t, FuncSet> FuncSigs;

  // Map function pointers to possible assignments
  FuncPtrMap FuncPtrs;

  // functions whose addresses are taken
  FuncSet AddressTakenFuncs;

  // Functions implicitly called as global constructors/destructors
  FuncSet CtorDtorFuncs;

  // allocation functions
  FuncSet AllocFuncs;
  FuncSet CandidateAllocFuncs;

  // container function summaries
  struct ContainerFuncInfo {
    int containerArg;           // index of the container object parameter
    std::vector<int> storeArgs; // indices of value params stored INTO container
    bool loadReturn;            // true if return value is loaded FROM container
  };
  std::unordered_map<const llvm::Function*, ContainerFuncInfo> ContainerFuncs;

  // Transfer-summary vocabulary (--func-summaries): callsite-applied
  // atoms replacing the hardcoded isAllocFn table. A summary applied at
  // a callsite is a zero-cost infinite clone (per-callsite identity for
  // FRESH; no shared-formal/ret mixing). File is the authoritative,
  // checked-in artifact of the proposer+confirmer loop.
  struct SummaryAtom {
    enum Kind {
      Fresh, // per-callsite heap object identity (via AllocFuncs paths)
      Cpy,   // shift-preserving cell copy: deref(src) -> deref(dst)
      Alias, // dst value aliases src value (interior/identity return)
      Store, // *container <- value
      Load,  // dst value <- *container
      Move,  // *dst@off <- *src@off (field-to-field cell move)
      FreshSub, // a fresh anonymous sub-object stored into *dst
      Invoke, // pair-correlated dispatch: fn at arg[dst] will be called
              // with arg[src] bound to its formal [aux] (C interface
              // polymorphism: (fn,data) registration pairs)
      ChainReg, // keyed pair-channel REGISTRATION (notifier shape):
                // key = chain-head global at arg[dst]; callback read
                // from the constant initializer of the block global at
                // arg[src], byte offset [off]; the block binds to the
                // callback's formal [fk]
      ChainCall, // keyed pair-channel DISPATCH: key at arg[dst]; the
                // dispatch value at arg[src] binds to each registered
                // callback's formal [fk]. Registration x dispatch pairs
                // are wired per key at finalize (static_call precedent)
      MoveX, // Move + wildcard shift on the DESTINATION: an interior-
             // of-loaded value stored into a cell (skb_put tail
             // advance). fx loop on dst absorbs the unknown delta
      Store2, // value into **src-base@dstByteOff (2nd level wildcard):
              // deref-of-deref chain at apply (nla_put memcpy class)
      Move2,  // *src@srcByteOff content into **dst-base@dstByteOff
      Load2,  // ret <- **src@srcByteOff (2nd level wildcard)
      LoadX, // LD + wildcard shift on the RESULT: ret = interior of
             // the pointer loaded from *src@srcByteOff (skb_put class:
             // loaded_ptr + delta). Result gets an fx self-loop —
             // covers any delta; exact at FI (solved-summary only)
      Dispatch // container dispatch (2026-09-16): the indirect call(s)
               // inside function [siteFn] (default: the summarized
               // callee) take their callee from ref (dst, fnLevel,
               // dstByteOff) and their argument [aux] from ref (src,
               // valLevel, srcByteOff); refs are argN (level 0),
               // *argN@off (level 1), **argN@off (level 2: the pointer
               // in *argN@0, then field off). The site keeps its own
               // identity for the answer (GT sites inside the body).
    } kind;
    int dst = -1; // arg index, or -1 = callsite return value
    int src = -1; // arg index (Cpy/Alias src; Store: value; Load: container)
    int dstByteOff = 0; // Store/Move: byte offset within *dst
    int srcByteOff = 0; // Load/Move: byte offset within *src container
    int aux = 0;  // Invoke: callee formal index receiving src
    int off = -1; // ChainReg: byte offset of the fn inside *arg[src]
    int fk = -1;  // ChainReg/ChainCall: callback formal index
    const llvm::GlobalValue *gsrc = nullptr; // Store: global-value source;
                                             // ChainReg: derived key global
                                             // (generated atoms only)
    // Global-container refs (v2.2b, per-run adopted atoms only —
    // pointer identity, never serialized: internal-linkage globals
    // would be name-ambiguous across TUs). When set, they replace the
    // corresponding arg ref: gdst = container/dst side (Store/Move
    // target, byte at dstByteOff), gsrc2 = source side (Move/Load
    // container or Store/Alias address-of-global value, byte at
    // srcByteOff).
    const llvm::GlobalValue *gdst = nullptr;
    const llvm::GlobalValue *gsrc2 = nullptr;
    std::string gsym; // ChainReg: key global by symbol name (file syntax
                      // CHAINREG(@sym,...) for external-linkage heads)
    int fnLevel = 0;  // Dispatch: deref depth of the callee ref
    int valLevel = 0; // Dispatch: deref depth of the value ref
    bool exact2 = false; // Store2/Load2 from the file: level-2 offset is
                         // exact (field of the pointed-to object), not
                         // the generated wildcard
    int innerOff = 0;    // exact Store2/Load2: the first dereference's field
                         // (**argN@inner@outer: the table/array pointer in
                         // field `inner`, then element/field `outer`)
    std::string siteFn; // Dispatch: function holding the icall site(s)
  };
  struct FuncSummary {
    std::vector<SummaryAtom> atoms;
    bool fresh = false; // has a Fresh atom
    bool body = false;  // BODY: the body is analyzed too (its own calls)
    bool none = false;  // explicit NONE: no summary, stop matching
    bool noop = false;  // NOOP: call transfers nothing, body skipped
                        // (free/printk/lock entry points — replaces the
                        // hardcoded isFreeFn/isKernelUtilityFn lists
                        // when the file is loaded; task #44 follow-up)
    // FREE(argN): a deallocator of argN. Its body's stores through the
    // freed pointer, and of it (a pool's free list), are invisible: the
    // object is dead after the call (a read is undefined behavior), and a
    // reuse of the block is a new object (FRESH). Premise: the block stays
    // in the program's own pool, not released to the underlying allocator.
    // Not a transfer atom: call sites wire the body as usual.
    int freeArg = -1;
    // POOL: a member of an allocator family that is not itself an
    // allocator (pool setup, introspection, range tests): no transfer
    // meaning, the call is wired as usual; its accesses count as the
    // family's in the pool-closure check (plan 3.38).
    bool pool = false;
    bool externOnly = false; // '@scope extern' block: applies only to
                        // functions WITHOUT a body in the corpus. A
                        // libc-derived entry must never replace a
                        // same-named in-corpus definition (5.18: 'sort
                        // NOOP' cut the comparator flow of lib/sort.c,
                        // 'sem_init NOOP' erased ipc/sem.c's registration
                        // of sysvipc_sem_proc_show; 10 GT misses).
  };
  // Ordered specs (first match wins; trailing '*' = prefix match) and
  // the per-Function resolution filled during doInitialization.
  std::vector<std::pair<std::string, FuncSummary>> SummarySpecs;
  // Summaries GENERATED by the body confirmer (--cfl-confirm-fresh):
  // deque for stable addresses (FuncSummaries holds pointers).
  std::deque<FuncSummary> OwnedSummaries;
  std::unordered_map<const llvm::Function*, const FuncSummary*> FuncSummaries;

  // Map a callsite to all potential callee functions.
  CalleeMap Callees;

  // Map a function to all potential caller instructions.
  CallerMap Callers;

  // Indirect call instructions
  CallInstSet IndirectCallInsts;

  // Allocation sites
  CallInstSet AllocSites;

  // Return sites
  RetSiteMap RetSites;

  // A factory object that knows how to manage AndersNodes
  AndersNodeFactory nodeFactory;

  // Global init point-to graph

  // Constraint graph built from IR (src/lib/ConstraintGraph.h)
  ConstraintGraph constraintGraph;

  ModuleList Modules;

  ModuleMap ModuleMaps;
  std::set<std::string> InvolvedModules;
};

class IterativeModulePass {
protected:
  GlobalContext *Ctx;
  const char *ID;
  unsigned long Iteration;
public:
  IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
    : Ctx(Ctx_), ID(ID_) { }

  // run on each module before iterative pass
  virtual bool doInitialization(llvm::Module *M)
    { return true; }

  // run on each module after iterative pass
  virtual bool doFinalization(llvm::Module *M)
    { return true; }

  // iterative pass
  virtual bool doModulePass(llvm::Module *M)
    { return false; }

  virtual void run(ModuleList &modules);
};

#endif
