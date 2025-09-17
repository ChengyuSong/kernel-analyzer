#ifndef POINTTO_H
#define POINTTO_H

#include <unordered_map>

#include "Global.h"
#include "NodeFactory.h"

void populateNodeFactory(GlobalContext &GlobalCtx);
NodeIndex createNodeForTypedVal(const Value *v, const Type *type, bool isHeap,
    AndersNodeFactory &nodeFactory, StructAnalyzer &structAnalyzer);
NodeIndex createNodeForHeapObject(const Instruction *I, int SizeArg, int FlagArg,
    AndersNodeFactory &nodeFactory, StructAnalyzer &structAnalyzer);

int64_t getGEPOffset(const llvm::Value* value, const llvm::DataLayout* dataLayout);
unsigned offsetToFieldNum(const llvm::Type* type, int64_t offset, const llvm::DataLayout* dataLayout,
    StructAnalyzer &structAnalyzer, llvm::Module* module);

NodeIndex extendObjectSize(NodeIndex oldObj, const StructType* stType, AndersNodeFactory &nodeFactory,
    StructAnalyzer &structAnalyzer, PtsGraph &ptsGraph);

#endif
