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
#include "CFLEdgeBuilder.h"

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

typedef boost::unordered_flat_map<std::size_t, AndersPtsSet> PtsGraph;
typedef boost::unordered_flat_map<llvm::Instruction*, PtsGraph> NodeToPtsGraph;

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
      ChainCall // keyed pair-channel DISPATCH: key at arg[dst]; the
                // dispatch value at arg[src] binds to each registered
                // callback's formal [fk]. Registration x dispatch pairs
                // are wired per key at finalize (static_call precedent)
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
    std::string gsym; // ChainReg: key global by symbol name (file syntax
                      // CHAINREG(@sym,...) for external-linkage heads)
  };
  struct FuncSummary {
    std::vector<SummaryAtom> atoms;
    bool fresh = false; // has a Fresh atom
    bool none = false;  // explicit NONE: no summary, stop matching
    bool noop = false;  // NOOP: call transfers nothing, body skipped
                        // (free/printk/lock entry points — replaces the
                        // hardcoded isFreeFn/isKernelUtilityFn lists
                        // when the file is loaded; task #44 follow-up)
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
  PtsGraph GlobalInitPtsGraph;

  // CFL edge builder
  CFLEdgeBuilder edgeBuilder;

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

// Default P2 grammar for CFL-reachability analysis
static const std::vector<std::string> DefaultP2Grammar = {
  "M DV d",
  "DV -d V",
  "V MAM AMs",
  "MAM MAs Mq",
  "Mq",
  "Mq M",
  "MAs",
  "MAs MAs MA",
  "MA Mq -a",
  "AMs",
  "AMs AMs AM",
  "AM a Mq"
};

// Field-sensitive extension: shift-indexed valley grammar over Z_P u {T}.
// Field steps are residues mod P (P = numBuckets): a GEP of byte offset k
// emits terminal f<r> with r = k mod P; signed offsets fold into the
// residue, so container_of's negative steps compose correctly with
// positive ones (down 8 then down 8 matches flat down 16 when 8+8 ≡ 16).
// fx is the absorbing unknown-shift element T (variable-offset fallback).
//
// Chain nonterminals, indexed by net shift c:
//   Dn<c> ::= eps(c=0) | Dn<a> DS<b>    with c = (a+b) mod P; T absorbs
//   Up<c> ::= eps(c=0) | US<b> Up<a>
//   DS0 ::= a | M ; DS<r> ::= f<r> ; DSX ::= fx     (down steps)
//   US0 ::= -a | M ; US<r> ::= -f<r> ; USX ::= -fx  (up steps)
// Valley assembly — only net-zero and unknown are ever consumed:
//   V  ::= Up<a> Dn<a>  for every a  (exact shifts agree = same position)
//   VX ::= UpX Dn<b> | Up<a> DnX | UpX DnX          (unknown may be zero)
//   M  ::= -d V d | -d VX d
// V keeps its name so every existing consumer (presolve V-SCC, snapshots,
// resolution) works unchanged. Exact-mismatch pairs (a != b) get NO rule:
// provably different positions never alias.
inline std::vector<std::string> buildP2GrammarWithFields(unsigned numBuckets) {
  if (numBuckets == 0)
    return DefaultP2Grammar;
  const unsigned P = numBuckets;
  std::vector<std::string> g = {
    "M DV d",
    "DV -d V",
    "Mq",
    "Mq M",
    "DVX -d VX",
    "M DVX d",
  };
  auto n = [](const char *base, unsigned i) {
    return std::string(base) + std::to_string(i);
  };
  g.push_back("DS0 a");
  g.push_back("DS0 M");
  g.push_back("US0 -a");
  g.push_back("US0 M");
  g.push_back("DSX fx");
  g.push_back("USX -fx");
  for (unsigned r = 0; r < P; r++) {
    g.push_back(n("DS", r) + " f" + std::to_string(r));
    g.push_back(n("US", r) + " -f" + std::to_string(r));
  }
  g.push_back("Dn0");
  g.push_back("Up0");
  for (unsigned a = 0; a < P; a++)
    for (unsigned b = 0; b < P; b++) {
      unsigned c = (a + b) % P;
      g.push_back(n("Dn", c) + " " + n("Dn", a) + " " + n("DS", b));
      g.push_back(n("Up", c) + " " + n("US", b) + " " + n("Up", a));
    }
  for (unsigned a = 0; a < P; a++) {
    g.push_back("DnX " + n("Dn", a) + " DSX");
    g.push_back("DnX DnX " + n("DS", a));
    g.push_back("UpX USX " + n("Up", a));
    g.push_back("UpX " + n("US", a) + " UpX");
  }
  g.push_back("DnX DnX DSX");
  g.push_back("UpX USX UpX");
  for (unsigned a = 0; a < P; a++) {
    g.push_back("V " + n("Up", a) + " " + n("Dn", a));
    g.push_back("VX UpX " + n("Dn", a));
    g.push_back("VX " + n("Up", a) + " DnX");
  }
  g.push_back("VX UpX DnX");
  return g;
}

#endif
