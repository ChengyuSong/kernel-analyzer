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

// Field-sensitive extension: K bucketed field-offset terminal pairs f<i>/-f<i>
// plus a wildcard pair fx/-fx. A matched field step
//   Fld ::= -f<i> V f<i>
// relates two field pointers computed at the same (bucketed) offset from
// value-aliasing bases -- the exact analogue of M ::= -d V d for dereference.
// The wildcard fx matches any bucket on the other side; a fx/-fx self-loop on
// a node soundly absorbs field steps of arbitrary offset and nesting depth
// (used as the conservative fallback for unknown-offset accesses).
inline std::vector<std::string> buildP2GrammarWithFields(unsigned numBuckets) {
  std::vector<std::string> g = DefaultP2Grammar;
  if (numBuckets == 0)
    return g;
  g.push_back("Mq Fld");
  g.push_back("FVx -fx V");
  g.push_back("Fld FVx fx");
  for (unsigned i = 0; i < numBuckets; i++) {
    std::string fi = "f" + std::to_string(i);
    std::string FVi = "FV" + std::to_string(i);
    g.push_back(FVi + " -" + fi + " V");
    g.push_back("Fld " + FVi + " " + fi);
    g.push_back("Fld " + FVi + " fx");
    g.push_back("Fld FVx " + fi);
  }
  return g;
}

#endif
