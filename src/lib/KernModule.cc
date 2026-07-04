/*
 * This is an assistant pass for UCSAN, aiming to automate the generation of
 * analysis scope for kernel modules without another static analysis.
 *
 * Copyrigth (C) 2025 Chengyu Song
 *
 * For licensing details see LICENSE
 */

 #include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/Support/Debug.h>

#include "Annotation.h"
#include "KernModule.h"

using namespace llvm;

bool ModuleDumpPass::doInitialization(Module *M) {
  Diag << "[" << ID << "] Initializing " << M->getName() << "\n";
  return false;
}