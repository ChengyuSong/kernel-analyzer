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

  // Map function pointers to possible assignments
  FuncPtrMap FuncPtrs;

  // functions whose addresses are taken
  FuncSet AddressTakenFuncs;

  // Map a callsite to all potential callee functions.
  CalleeMap Callees;

  // Map a function to all potential caller instructions.
  CallerMap Callers;

  // Indirect call instructions
  std::vector<CallInst*> IndirectCallInsts;

  // Allocation sites
  CallInstSet AllocSites;

  // Return sites
  RetSiteMap RetSites;

  // A factory object that knows how to manage AndersNodes
  AndersNodeFactory nodeFactory;

  // Global init point-to graph
  PtsGraph GlobalInitPtsGraph;

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
