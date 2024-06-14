/*
 * Helper functions for point-to analysis
 *
 * Copyright (C) 2019 - 2024 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>

#include "Common.h"
#include "Annotation.h"
#include "PointTo.h"
#include "StructAnalyzer.h"

#define PT_LOG(stmt) KA_LOG(2, "Point2: " << stmt)

using namespace llvm;

static NodeIndex processStruct(const Value* v, const StructType* stType, bool isHeap,
                               AndersNodeFactory &nodeFactory,
                               StructAnalyzer &structAnalyzer) {

  if (stType->isOpaque()) {
    errs() << "Opaque struct type ";
    stType->print(errs());
    errs() << "\n";

    // we don't know how the struct looks like
    return nodeFactory.createObjectNode(v, stType, false, isHeap);
  }

  // Sanity check
  assert(stType != NULL && "structType is NULL");

  const StructInfo* stInfo = structAnalyzer.getStructInfo(stType, nodeFactory.getModule());
  assert(stInfo != NULL && "structInfoMap should have info for all structs!");

  // Empty struct has only one pointer that points to nothing
  if (stInfo->isEmpty())
    return nodeFactory.getNullObjectNode();

  // Non-empty structs: create one pointer and one target for each field
  unsigned stSize = stInfo->getExpandedSize();

  // We construct a target variable for each field
  // A better approach is to collect all constant GEP instructions and
  // construct variables only if they are used. We want to do the simplest thing first
  NodeIndex obj = nodeFactory.getObjectNodeFor(v);
  if (obj == AndersNodeFactory::InvalidIndex) { // avoid re-creating nodes
    obj = nodeFactory.createObjectNode(v, stType, stInfo->isFieldUnion(0), isHeap);
    for (unsigned i = 1; i < stSize; ++i)
      nodeFactory.createObjectNode(obj, i, stInfo->isFieldUnion(i), isHeap);
  }

  return obj;
}

NodeIndex createNodeForTypedVal(const Value *v, const Type *type, bool isHeap,
                                AndersNodeFactory &nodeFactory,
                                StructAnalyzer &structAnalyzer) {

  // An array is considered a single variable of its type.
  while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
    type = arrayType->getElementType();

  // Now construct the memory object variable
  // It depends on whether the type of this variable is a struct or not
  NodeIndex obj = AndersNodeFactory::InvalidIndex;
  if (const StructType *structType = dyn_cast<StructType>(type)) {
    // check if the struct is a union
    if (!structType->isLiteral() && structType->getStructName().startswith("union"))
      obj = nodeFactory.createObjectNode(v, type, true, isHeap);
    else
      obj = processStruct(v, structType, isHeap, nodeFactory, structAnalyzer);
  } else {
    obj = nodeFactory.createObjectNode(v, type, false, isHeap);
  }

  return obj;
}

static inline const Type* getBetterType(const Type* oldType, const Type* newType) {
  if (oldType == NULL)
    return newType;
  if (oldType == newType)
    return newType;
  // collapse array type
  while (const ArrayType *arrayType = dyn_cast<ArrayType>(oldType))
    oldType = arrayType->getElementType();
  while (const ArrayType *arrayType = dyn_cast<ArrayType>(newType))
    newType = arrayType->getElementType();

  if (newType->isSingleValueType()) {
    if (oldType->isSingleValueType())
      return oldType->getPrimitiveSizeInBits() < newType->getPrimitiveSizeInBits() ? newType : oldType;
    else return oldType; // oldType is aggregate type,  prefer
  } else {
    if (oldType->isSingleValueType())
      return newType; // newType is aggregate type, prefer
    // else both struct, prefer non-literal struct
    const StructType *oldST = dyn_cast<StructType>(oldType);
    const StructType *newST = dyn_cast<StructType>(newType);
    assert(oldST != NULL && newST != NULL && "Non-struct type should have been handled");
    if (oldST->isLiteral() && !newST->isLiteral())
      return newType;
    else return oldType;
  }

  llvm_unreachable("Unhandled type comparison");
}

static const Type* getUsedType(const Value* GV, const Type* initType) {
  SmallVector<const Value*, 4> worklist(GV->user_begin(), GV->user_end());
  SmallPtrSet<const Value*, 4> visited;
  const Type* bestTy = initType;
  while (!worklist.empty()) {
    const Value *V = worklist.pop_back_val();
    if (!visited.insert(V).second)
      continue;
    if (const LoadInst *LI = dyn_cast<LoadInst>(V)) {
      bestTy = getBetterType(bestTy, LI->getType());
    } else if (const GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
      bestTy = getBetterType(bestTy, GEP->getSourceElementType());
    } else if (const BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
      worklist.insert(worklist.end(), BC->user_begin(), BC->user_end());
    } else if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
      if (CE->getOpcode() == Instruction::GetElementPtr) {
        auto GEP = cast<GEPOperator>(CE);
        bestTy = getBetterType(bestTy, GEP->getSourceElementType());
      } else if (CE->getOpcode() == Instruction::BitCast) {
        worklist.insert(worklist.end(), CE->user_begin(), CE->user_end());
      }
    } else if (isa<ConstantAggregate>(V)) {
      // ignore initializer
    } else {
      WARNING("Unhandled user of value " << GV->getName() << ": " << *V << "\n");
    }
  }

  return bestTy;
}

static void createNodeForGlobals(Module *M, AndersNodeFactory &nodeFactory,
                                 StructAnalyzer &structAnalyzer,
                                 PtsGraph &ptsGraph) {

  for (auto const& GV: M->globals()) {
    if (GV.isDeclaration())
      continue;

    NodeIndex valNode = nodeFactory.createValueNode(&GV);
    const Constant *init = GV.getInitializer();
    if (init) {
      // defined global variables should have initializers
      const Type *type = init->getType();
      // XXX: the type of the initializer could be tricky
      if (const StructType *ST = dyn_cast<StructType>(type)) {
        if (ST->isLiteral()) {
          // if the initializer is a literal struct, try to see if the global
          // has been used in a more friendly type
          const Type *usedType = getUsedType(&GV, type);
          if (usedType != type) {
            PT_LOG("Using used type " << *usedType << " instead of init type " << *type << " for global " << GV.getName() << "\n");
            type = usedType;
          }
        }
      }
      NodeIndex objNode = createNodeForTypedVal(&GV, type, false, nodeFactory, structAnalyzer);
      ptsGraph[valNode].insert(objNode);
      PT_LOG("Created node " << objNode << " for global " << GV.getName() << "\n");
    } else {
      WARNING("GV:" << GV.getName() << ", no initializer\n");
    }
  }

  for (auto const& F: *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty()) {
      continue;
    }

    // Create return node
    Type *retType = F.getReturnType();
    if (!retType->isVoidTy()) {
      // FIXME: handle potential aggregate return type
      // createNodeForTypedVal(&F, retType, false, nodeFactory, structAnalyzer);
      assert(!retType->isAggregateType() && "Aggregate return type not supported");
      nodeFactory.createReturnNode(&F);
    }

    // Create vararg node
    if (F.getFunctionType()->isVarArg())
      nodeFactory.createVarargNode(&F);

    // Add nodes for all formal arguments.
    for (auto const &A : F.args()) {
      // FIXME: handle potential aggregate argument type
      // createNodeForTypedVal(&A, A.getType(), false, nodeFactory, structAnalyzer);
      assert(!A.getType()->isAggregateType() && "Aggregate argument type not supported");
      nodeFactory.createValueNode(&A);
    }

    NodeIndex fobj = nodeFactory.createObjectNode(&F);
    PT_LOG("Created node " << fobj << " for function " << F.getName() << "\n");
  }
}

static NodeIndex createNodeForHeapObject(const Instruction *I, int SizeArg, int FlagArg,
                                    AndersNodeFactory &nodeFactory, StructAnalyzer &structAnalyzer) {

#if 1 //LLVM_VERSION_MAJOR > 13
  // Assuming opaque pointer type
  // We don't know what it points to, so we create an opaque object node
  return nodeFactory.createOpaqueObjectNode(I, true);
#else
  const Type* elemType = pType->getElementType();

  // TODO: using casting is not the best way, consider sizeof
  if (elemType->isIntegerTy(8)) {
    // Check all the users of inst
    // TODO: use a working list to handle load/store
    for (auto U: I->users()) {
      if (const CastInst *CI = dyn_cast<CastInst>(U)) {
        pType = dyn_cast<PointerType>(CI->getType());
        if (!pType) continue;
        elemType = pType->getElementType();
        break;
      }
    }
  }

  unsigned maxSize = 0;
  uint64_t allocSize = 1;
  const StructInfo* stInfo = nullptr;
  bool isUnion = false;
  while (const ArrayType* arrayType = dyn_cast<ArrayType>(elemType)) {
    allocSize *= arrayType->getNumElements();
    elemType = arrayType->getElementType();
  }
  if (allocSize == 0) allocSize = 1;

  if (const StructType* structType = dyn_cast<StructType>(elemType)) {
    stInfo = structAnalyzer.getStructInfo(structType, nodeFactory.getModule());
    assert(stInfo != nullptr && "structInfoMap should have info for all structs!");
    if (!structType->isLiteral() && structType->getStructName().startswith("union"))
      isUnion = true;
    maxSize = stInfo->getExpandedSize();
    allocSize *= stInfo->getAllocSize();
  }

  // if size arg exists
  if (SizeArg >= 0) {
    const Value *SV = I->getOperand(SizeArg);
    if (const ConstantInt *size = dyn_cast<ConstantInt>(SV)) {
      uint64_t zext_size = size->getZExtValue();
      if (zext_size > allocSize) {
        assert(zext_size < (uint64_t)UINT_MAX);
        maxSize = zext_size;
      }
    }
  } else {
    // FIXME: kmem_cache_alloc
  }

  if (maxSize == 0) maxSize = StructInfo::getMaxStructSize();

  // Create the first heap node
  NodeIndex obj = nodeFactory.getObjectNodeFor(I);
  if (obj == AndersNodeFactory::InvalidIndex) {
    obj = nodeFactory.createObjectNode(I, isUnion, true);
    for (unsigned i = 1; i < maxSize; ++i) {
      isUnion = (stInfo && i < stInfo->getExpandedSize()) ? stInfo->isFieldUnion(i) : false;
      nodeFactory.createObjectNode(obj, i, isUnion, true);
    }
  }
#endif
}

static void processInitializer(NodeIndex obj, const Type *objTy, Constant *init,
                               AndersNodeFactory &nodeFactory,
                               PtsGraph &ptsGraph) {

  assert(obj != AndersNodeFactory::InvalidIndex && "Invalid node index for global object");

  // collapse array type
  while (const ArrayType *arrayType = dyn_cast<ArrayType>(objTy))
    objTy = arrayType->getElementType();

  // look for global values in the initializer
  if (ConstantArray *CA = dyn_cast<ConstantArray>(init)) {
    // array, always collapse, process element by element
    for (unsigned i = 0; i != CA->getNumOperands(); ++i)
      processInitializer(obj, objTy, CA->getOperand(i), nodeFactory, ptsGraph);
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(init)) {
    // handle struct type specially, could be tricky because of type mismatch
    // GV could be allocated using the used type (see createNodeForGlobals)
    const StructType *CSTy = CS->getType();
    if (CSTy != objTy) {
      // type mismatch
      PT_LOG("Initializer type mismatch for " << *CS << " vs " << *objTy << "\n");
      assert(CSTy->isLiteral() && "Non-literal struct type mismatch");
      const StructType *STy = dyn_cast<StructType>(objTy);
      auto dataLayout = nodeFactory.getDataLayout();
      auto objSize = dataLayout->getTypeAllocSize(const_cast<Type*>(objTy));
      for (unsigned i = 0, j = 0; i != CSTy->getNumElements(); ++i) {
        // XXX try a heuristic
        Type *elemTy = CSTy->getElementType(i);
        auto elemSize = dataLayout->getTypeAllocSize(elemTy);
        if (elemSize % objSize == 0) {
          // element size is a multiple of object size, use base type
          processInitializer(obj, objTy, CS->getOperand(i), nodeFactory, ptsGraph);
        } else {
          // we could be looking at a sub-field
          assert(STy != NULL && "Struct initializer for non-struct type");
          NodeIndex field = nodeFactory.getOffsetObjectNode(obj, j);
          assert(field != AndersNodeFactory::InvalidIndex && "Invalid node index for field");
          processInitializer(field, STy->getElementType(j), CS->getOperand(i), nodeFactory, ptsGraph);
          // advance to next field if not array type
          if (!elemTy->isArrayTy()) ++j;
        }
      }
    } else {
      // type match, process field by field
      for (unsigned i = 0; i != CSTy->getNumElements(); ++i) {
        const Type* elemTy = CSTy->getElementType(i);
        // collapse array type before processing
        while (const ArrayType *arrayType = dyn_cast<ArrayType>(elemTy))
          elemTy = arrayType->getElementType();
        NodeIndex field = nodeFactory.getOffsetObjectNode(obj, i);
        assert(field != AndersNodeFactory::InvalidIndex && "Invalid node index for field");
        processInitializer(field, elemTy, CS->getOperand(i), nodeFactory, ptsGraph);
      }
    }
  } else if (ConstantVector *CV = dyn_cast<ConstantVector>(init)) {
    // FIXME: handle vector type
    // for (unsigned i = 0; i != CV->getNumOperands(); ++i)
    //   processInitializer(obj, objTy, CV->getOperand(i), nodeFactory, ptsGraph);
    WARNING("Unhandled vector initializer: " << *init << "\n");
  } else if (ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(init)) {
    // zero initializer
    Type *Ty = CAZ->getType();
    if (isa<ArrayType>(Ty) || isa<VectorType>(Ty)) {
      // array or vector, process element only once
      processInitializer(obj, objTy, CAZ->getSequentialElement(), nodeFactory, ptsGraph);
    } else {
      StructType *CSTy = dyn_cast<StructType>(Ty);
      assert(CSTy != NULL && "Invalid zero initializer type");
      // assert(!CSTy->isLiteral() && "Zero initializer cannot be literal?");
      assert(CSTy == objTy && "Zero initializer type mismatch");
      // struct, process field by field
      for (unsigned i = 0; i != CSTy->getNumElements(); ++i) {
        Type *elemTy = CSTy->getElementType(i);
        Constant *elem = CAZ->getStructElement(i);
        // collapse array type before processing
        while (const ArrayType *arrayType = dyn_cast<ArrayType>(elemTy)) {
          elemTy = arrayType->getElementType();
          elem = cast<ConstantAggregateZero>(elem)->getSequentialElement();
        }
        NodeIndex field = nodeFactory.getOffsetObjectNode(obj, i);
        processInitializer(field, elemTy, elem, nodeFactory, ptsGraph);
      }
    }
  } else {
    // non-aggregate initializer
    assert(objTy->isSingleValueType() && "Single value initializer for non single value type");
    if (isa<ConstantPointerNull>(init)) {
      ptsGraph[obj].insert(nodeFactory.getNullObjectNode());
    } else if (isa<GlobalVariable>(init)) {
      NodeIndex objNode = nodeFactory.getObjectNodeFor(init); // already handles name to def mapping
      assert(objNode != AndersNodeFactory::InvalidIndex && "Invalid node index for global variable");
      ptsGraph[obj].insert(objNode);
    } else if (isa<Function>(init)) {
      NodeIndex objNode = nodeFactory.getObjectNodeFor(init); // already handles name to def mapping
      assert(objNode != AndersNodeFactory::InvalidIndex && "Invalid node index for function");
      ptsGraph[obj].insert(objNode);
    } else if (isa<ConstantExpr>(init)) {
      ConstantExpr *CE = cast<ConstantExpr>(init);
      switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: {
          NodeIndex field = nodeFactory.getObjectNodeForConstant(CE);
          assert(!AndersNodeFactory::isSpecialNode(field) && "Invalid node index for field");
          ptsGraph[obj].insert(field);
          break;
        }
        case Instruction::BitCast: {
          // BitCast, process the operand
          processInitializer(obj, objTy, CE->getOperand(0), nodeFactory, ptsGraph);
          break;
        }
        // case Instruction::IntToPtr: {
        //   // IntToPtr, do nothing
        //   break;
        // }
        default:
          WARNING("Unhandled constant expression initializer: " << *init << "\n");
      }
    }
  }
}

void populateNodeFactory(GlobalContext &GlobalCtx) {

  AndersNodeFactory &nodeFactory = GlobalCtx.nodeFactory;
  StructAnalyzer &structAnalyzer = GlobalCtx.structAnalyzer;

  nodeFactory.setStructAnalyzer(&structAnalyzer);
  nodeFactory.setGobjMap(&GlobalCtx.Gobjs);
  nodeFactory.setExtGobjMap(&GlobalCtx.ExtGobjs);
  nodeFactory.setFuncMap(&GlobalCtx.Funcs);
  nodeFactory.setExtFuncMap(&GlobalCtx.ExtFuncs);

  PtsGraph &ptsGraph = GlobalCtx.GlobalInitPtsGraph;

  // universal ptr points to universal obj
  ptsGraph[nodeFactory.getUniversalPtrNode()].insert(nodeFactory.getUniversalObjNode());
  // universal obj points to universal obj
  ptsGraph[nodeFactory.getUniversalObjNode()].insert(nodeFactory.getUniversalObjNode());
  // null ptr points to null obj
  ptsGraph[nodeFactory.getNullPtrNode()].insert(nodeFactory.getNullObjectNode());
  // null obj points to nothing, so empty
  ptsGraph[nodeFactory.getNullObjectNode()].clear();

  for (auto i = GlobalCtx.Modules.begin(), e = GlobalCtx.Modules.end(); i != e; ++i) {
    Module *M = i->first;
    nodeFactory.setDataLayout(&(M->getDataLayout()));
    nodeFactory.setModule(M);

    PT_LOG("Creating nodes for module " << M->getModuleIdentifier() << "\n");

    // Create obj nodes for global variables and functions
    createNodeForGlobals(M, nodeFactory, structAnalyzer, ptsGraph);

    for (auto const& F: *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
    
      int size, flag;
      if (isAllocFn(F.getName(), &size, &flag))
        continue;
    
      // Scan the function body
      for (auto itr = inst_begin(&F), ite = inst_end(&F); itr != ite; ++itr) {
        const Instruction *I = &*itr;
        // First, create a value node for each instruction
        NodeIndex valNode = nodeFactory.createValueNode(I);

        // Next, handle allocators
        switch (I->getOpcode()) {
          case Instruction::Ret: {
            const ReturnInst *RI = cast<ReturnInst>(I);
            GlobalCtx.RetSites[&F] = RI;
            break;
          }
          case Instruction::Alloca: {
            Type *Ty = cast<AllocaInst>(I)->getAllocatedType();
            NodeIndex obj = createNodeForTypedVal(I, Ty, false, nodeFactory, structAnalyzer);
            ptsGraph[valNode].insert(obj);
            break;
          }
          case Instruction::Call: {
            const CallInst *CI = dyn_cast<CallInst>(I);
            if (Function *CF = CI->getCalledFunction()) {
              if (isAllocFn(CF->getName(), &size, &flag)) {
                NodeIndex obj = createNodeForHeapObject(CI, size, flag, nodeFactory, structAnalyzer);
                ptsGraph[valNode].insert(obj);
                GlobalCtx.AllocSites.insert(CI);
              }
            }
            break;
          }
        }
      }
    }
  }

  // Create object nodes for external global variables and functions
  for (auto const &itr: GlobalCtx.ExtGobjs) {
    auto node = nodeFactory.createObjectNode(itr.second);
    PT_LOG("Creating node " << node << " for external global " << itr.second->getName() << "\n");
  }
  for (auto const &itr: GlobalCtx.ExtFuncs) {
    auto node = nodeFactory.createObjectNode(itr.second);
    PT_LOG("Creating node " << node << " for external function " << itr.second->getName() << "\n");
  }

  // iterate again to process global initializers
  // collecting point2 information for global values
  for (auto i = GlobalCtx.Modules.begin(), e = GlobalCtx.Modules.end(); i != e; ++i) {
    Module *M = i->first;
    nodeFactory.setDataLayout(&(M->getDataLayout()));
    nodeFactory.setModule(M);

    for (auto &GV: M->globals()) {
      if (GV.hasInitializer()) {
        NodeIndex obj = nodeFactory.getObjectNodeFor(&GV);
        const Type *Ty = nodeFactory.getObjectType(obj);
        //PT_LOG("Processing initializer for global " << GV.getName() << " type " << *Ty << " with " << *GV.getInitializer() << "\n");
        processInitializer(obj, Ty, GV.getInitializer(), nodeFactory, ptsGraph);
      }
    }
  }
}

int64_t getGEPOffset(const Value* value, const DataLayout* dataLayout) {
  // Assume this function always receives GEP value
  //errs()<<"Inside getGEPOffset:\n";
  const GEPOperator* gepValue = dyn_cast<GEPOperator>(value);
  assert(gepValue != NULL && "getGEPOffset receives a non-gep value!");
  assert(dataLayout != NULL && "getGEPOffset receives a NULL dataLayout!");

  int64_t offset = 0;
  const Value* baseValue = gepValue->getPointerOperand()->stripPointerCasts();
  // If we have yet another nested GEP const expr, accumulate its offset
  // The reason why we don't accumulate nested GEP instruction's offset is
  // that we aren't required to. Also, it is impossible to do that because
  // we are not sure if the indices of a GEP instruction contains all-consts or not.
  if (const ConstantExpr* cexp = dyn_cast<ConstantExpr>(baseValue))
    if (cexp->getOpcode() == Instruction::GetElementPtr) {
      offset += getGEPOffset(cexp, dataLayout);
    }
  Type* ptrTy = gepValue->getSourceElementType();
    
  SmallVector<Value*, 4> indexOps(gepValue->op_begin() + 1, gepValue->op_end());
  // Make sure all indices are constants
  for (unsigned i = 0, e = indexOps.size(); i != e; ++i) {
    if (!isa<ConstantInt>(indexOps[i]))
      indexOps[i] = ConstantInt::get(Type::getInt32Ty(ptrTy->getContext()), 0);
  }
  offset += dataLayout->getIndexedOffsetInType(ptrTy, indexOps);

  return offset;
}

unsigned offsetToFieldNum(const Type* type, int64_t off, const DataLayout* dataLayout,
                          StructAnalyzer &structAnalyzer, Module* module) {

  assert(dataLayout != nullptr && "DataLayout is NULL when calling offsetToFieldNum!");
  if (off < 0)
    return 0;

  unsigned ret = 0;
  Type* elemType = const_cast<Type*>(type);
  if (elemType->isStructTy()) {
    StructType* stType = cast<StructType>(elemType);
    if (!stType->isLiteral() && stType->getName().startswith("union"))
      return ret;
    if (!stType->isLiteral() && stType->getName().startswith("union"))
      return ret;
    if (stType->isOpaque())
      return ret;
  }

  auto offset = off;
  while (offset > 0) {
    //errs()<<"offset: "<<offset<<"\n";
    // Collapse array type
    while(const ArrayType *arrayType= dyn_cast<ArrayType>(elemType))
      elemType = arrayType->getElementType();

    if (elemType->isStructTy()) {
      StructType* stType = cast<StructType>(elemType);

      const StructInfo* stInfo = structAnalyzer.getStructInfo(stType, module);
      assert(stInfo != NULL && "structInfoMap should have info for all structs!");
      stType = const_cast<StructType*>(stInfo->getRealType());

      const StructLayout* stLayout = stInfo->getDataLayout()->getStructLayout(stType);
      uint64_t allocSize = stInfo->getDataLayout()->getTypeAllocSize(stType);
      PT_LOG("allocSize = " << allocSize << ", offset = " << off << "\n");
      if (!allocSize)
        return 0;

      // since we have collapsed arrays, we want the offset into individual element
      offset %= allocSize;
      unsigned idx = stLayout->getElementContainingOffset(offset);
      if (!stType->isLiteral() && stType->getName().startswith("union")) {
        offset -= stInfo->getDataLayout()->getTypeAllocSize(stType);
        if (offset <= 0)
          break;
      }
      ret += stInfo->getOffset(idx);

      if (!stType->isLiteral() && stType->getName().startswith("union")) {
        offset -= stInfo->getDataLayout()->getTypeAllocSize(stType);
      } else {
        offset -= stLayout->getElementOffset(idx);
      }
      elemType = stType->getElementType(idx);
    } else {
      //errs() << "elemType: " << *elemType<< "\n";
      offset %= dataLayout->getTypeAllocSize(elemType);
      if (offset != 0) {
        errs() << "Warning: GEP into the middle of a field. This usually occurs when union is used. Since partial alias is not supported, correctness is not guanranteed here.\n";
        break;
      }
    }
  }

  return ret;
}

// given the old object node, old size, and the new object node
// replace all point-to info to the new node
// including the value to object node mapping
static void updateObjectNode(NodeIndex oldObj, NodeIndex newObj,
                             AndersNodeFactory &nodeFactory,PtsGraph &ptsGraph) {
  unsigned offset = nodeFactory.getObjectOffset(oldObj);
  NodeIndex baseObj = nodeFactory.getOffsetObjectNode(oldObj, -(int)offset);
  unsigned size = nodeFactory.getObjectSize(oldObj);

  // well, really expensive op
  // use explicit iterator for updating
  for (auto itr = ptsGraph.begin(), end = ptsGraph.end(); itr != end; ++itr) {
    AndersPtsSet temp = itr->second; // make a copy
    // in case modification will break iteration
    for (auto obj = temp.find_first(), end = temp.getSize(); obj < end;
         obj = temp.find_next(obj)) {
      if (obj >= baseObj && obj < (baseObj + size)) {
        itr->second.reset(obj);
        itr->second.insert(newObj + (obj - baseObj));
      }
    }
  }
}

// given old object node and new struct info, extend the object size
// return the new object node
NodeIndex extendObjectSize(NodeIndex oldObj, const StructType* stType,
                           AndersNodeFactory &nodeFactory,
                           StructAnalyzer &structAnalyzer,
                           PtsGraph &ptsGraph) {
  // FIXME: assuming oldObj is the base
  assert(nodeFactory.getObjectOffset(oldObj) == 0);
  bool isHeap = nodeFactory.isHeapObject(oldObj);

  const Value *val = nodeFactory.getValueForNode(oldObj);
  assert(val != NULL && "Failed to find value of node");
  NodeIndex valNode = nodeFactory.getValueNodeFor(val);

  // before creating new obj, remove the old ptr->obj
  auto itr = ptsGraph.find(valNode);
  assert(itr != ptsGraph.end() && itr->second.has(oldObj) && "Failed to find old obj in ptsGraph");
  itr->second.reset(oldObj);
  nodeFactory.removeNodeForObject(val);

  // create new obj
  NodeIndex newObj = processStruct(val, stType, isHeap, nodeFactory, structAnalyzer);

  // update ptr2set
  updateObjectNode(oldObj, newObj, nodeFactory, ptsGraph);

  return newObj;
}
