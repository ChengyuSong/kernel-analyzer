#progma once

#include "Global.h"

class ModuleDumpPass : public IterativeModulePass {
public:
  ModuleDumpPass(GlobalContext *Ctx_)
      : IterativeModulePass(Ctx_, "ModuleDump") {}

  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  void dumpConfig(llvm::raw_ostream &OS);  
};
