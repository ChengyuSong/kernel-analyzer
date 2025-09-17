/*
 * Andersen NodeFactory
 *
 * Copyright (C) 2015 Jia Chen
 * Copyright (C) 2015 - 2024 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/FileSystem.h>

#include <limits>
#include <sstream>

#include "NodeFactory.h"
#include "Common.h"
#include "PointTo.h"

#define AA_LOG(stmt) KA_LOG(2, "AA: " << stmt)

using namespace llvm;

const unsigned AndersNodeFactory::InvalidIndex = std::numeric_limits<unsigned int>::max();

AndersNodeFactory::AndersNodeFactory() {
    // Note that we can't use std::vector::emplace_back() here because AndersNode's constructors are private hence std::vector cannot see it

    // Node #0 is always the universal ptr: the ptr that we don't know anything about.
    nodes.emplace_back(AndersNode(AndersNode::VALUE_NODE, 0));
    // Node #1 is always the universal obj: the obj that we don't know anything about.
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, 1));
    // Node #2 always represents the null pointer.
    nodes.emplace_back(AndersNode(AndersNode::VALUE_NODE, 2));
    // Node #3 is the object that null pointer points to
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, 3));
    // Node #4 is the constaint int obj
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, 4));

    assert(nodes.size() == 5);
}

NodeIndex AndersNodeFactory::createValueNode(const Value* val) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::VALUE_NODE, nextIdx, val));
    if (val != nullptr) {
        if (valueNodeMap.count(val))
            return valueNodeMap[val];
        valueNodeMap[val] = nextIdx;
    }

    return nextIdx;
}

NodeIndex AndersNodeFactory::createOpaqueObjectNode(const Value* val, const bool heap) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, nextIdx, val, NULL, 0, false, heap, true));
    if (val != nullptr) {
        if (objNodeMap.count(val))
            return objNodeMap[val];
        objNodeMap[val] = nextIdx;
    }

    return nextIdx;
}

NodeIndex AndersNodeFactory::createObjectNode(const Value* val, const Type* ty, const bool uniono, const bool heap) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, nextIdx, val, ty, 0, uniono, heap));
    if (val != nullptr) {
        if (objNodeMap.count(val))
            return objNodeMap[val];
        objNodeMap[val] = nextIdx;
    }

    return nextIdx;
}

NodeIndex AndersNodeFactory::createObjectNode(const NodeIndex base, const unsigned offset, const bool uniono, const bool heap) {
    assert(offset != 0);

    unsigned nextIdx = nodes.size();
    assert(nextIdx == base + offset);
    const Value *val = getValueForNode(base);
    const Type *ty = getObjectType(base);
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, nextIdx, val, ty, offset, uniono, heap));

    return nextIdx;
}

NodeIndex AndersNodeFactory::createReturnNode(const llvm::Function* f) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::VALUE_NODE, nextIdx, f));

    assert(!returnMap.count(f) && "Trying to insert two mappings to returnMap!");
    returnMap[f] = nextIdx;

    return nextIdx;
}

NodeIndex AndersNodeFactory::createVarargNode(const llvm::Function* f) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, nextIdx, f));

    assert(!varargMap.count(f) && "Trying to insert two mappings to varargMap!");
    varargMap[f] = nextIdx;

    return nextIdx;
}

NodeIndex AndersNodeFactory::createDereferenceNode(const NodeIndex ptr) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::DEREF_NODE, nextIdx));
    if (ptr != InvalidIndex) {
        if (derefMap.count(ptr))
            return derefMap[ptr];
        derefMap[ptr] = nextIdx;
    }
    return nextIdx;
}

NodeIndex AndersNodeFactory::getValueNodeFor(const Value* val) {
    if (const Constant* c = dyn_cast<Constant>(val))
        if (!isa<GlobalValue>(c))
            return getValueNodeForConstant(c);

    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(val)) {
        auto GID = globalVar->getGUID();
        auto itr = gobjMap->find(GID);
        if (itr != gobjMap->end()) {
            auto obj = itr->second;
            val = obj;
        } else if (extGobjMap->find(GID) != extGobjMap->end()) {
            // XXX: return universal ptr?
            return getUniversalPtrNode();
        }
    }
    // else if (const Function *func = dyn_cast<Function>(val)) {
    //     auto itr = funcMap->find(func->getGUID());
    //     if (itr != funcMap->end())
    //         val = itr->second;
    // }

    auto itr = valueNodeMap.find(val);
    if (itr == valueNodeMap.end()) {
        return InvalidIndex;
    } else {
        return itr->second;
    }
}

NodeIndex AndersNodeFactory::getValueNodeForConstant(const llvm::Constant* c) {
    if (!isa<PointerType>(c->getType()))
        return ConstantIntIndex;

    if (isa<ConstantPointerNull>(c) || isa<UndefValue>(c))
        return NullPtrIndex;
    else if (const GlobalValue* gv = dyn_cast<GlobalValue>(c))
        return getValueNodeFor(gv);
    else if (const ConstantExpr* ce = dyn_cast<ConstantExpr>(c)) {
        switch (ce->getOpcode()){
            case Instruction::GetElementPtr:
            {
                NodeIndex baseNode = getValueNodeForConstant(ce->getOperand(0));
                assert(baseNode != InvalidIndex && "missing base val node for gep");

                if (baseNode == NullObjectIndex)
                    return NullPtrIndex;

                if (baseNode == UniversalObjIndex) {
                    errs() << "GEP CE, universal obj " << *(ce->getOperand(0)) << "\n";
                    return UniversalPtrIndex;
                }

                unsigned fieldNum = constGEPtoFieldNum(ce);
                if (fieldNum == 0)
                    return baseNode;

                auto mapKey = std::make_pair(baseNode, fieldNum);
                auto itr = gepMap.find(mapKey);
                if (itr == gepMap.end()) {
                    NodeIndex gepIndex = createValueNode(ce);
                    gepMap.insert(std::make_pair(mapKey, gepIndex));
                    gepNodeMap[gepIndex] = mapKey;
                    return gepIndex;
                } else {
                    return itr->second;
                }
            }
            case Instruction::BitCast:
            {
                NodeIndex srcNode = getValueNodeFor(ce->getOperand(0));
                if (srcNode == NullObjectIndex)
                    return NullPtrIndex;

                if (srcNode == UniversalObjIndex) {
                    errs() << "GEP CE, universal obj " << *(ce->getOperand(0)) << "\n";
                    return UniversalPtrIndex;
                }

                return srcNode;
            }
            case Instruction::IntToPtr:
                // FIXME
                return NullPtrIndex;
            case Instruction::PtrToInt:
                // FIXME
                return NullPtrIndex;
            default:
                errs() << "Constant Expr not yet handled: " << *ce << "\n";
                llvm_unreachable(0);
        }
    } else if (isa<BlockAddress>(c)) {
        // FIXME return NULL now
        return NullPtrIndex;
    }

    errs() << "Unknown constant pointer: " << *c << "\n";
    llvm_unreachable("Unknown constant pointer!");
    return InvalidIndex;
}

NodeIndex AndersNodeFactory::getObjectNodeFor(const Value* val) {
    if (const Constant* c = dyn_cast<const Constant>(val))
        if(!isa<GlobalValue>(c))
            return getObjectNodeForConstant(c);

    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(val)) {
        auto GID = globalVar->getGUID();
        auto itr = gobjMap->find(GID);
        if (itr != gobjMap->end()) {
            val = itr->second;
        } else {
            itr = extGobjMap->find(GID);
            if (itr != extGobjMap->end())
                val = itr->second;
        }
    } else if (const Function *func = dyn_cast<Function>(val)) {
        auto FID = func->getGUID();
        auto itr = funcMap->find(FID);
        if (itr != funcMap->end()) {
            val = itr->second;
        } else {
            itr = extFuncMap->find(FID);
            if (itr != extFuncMap->end())
                val = itr->second;
        }
    }

    auto itr = objNodeMap.find(val);
    if (itr == objNodeMap.end())
        return InvalidIndex;
    else
        return itr->second;
}

NodeIndex AndersNodeFactory::getObjectNodeForConstant(const llvm::Constant* c) {
    if(!isa<PointerType>(c->getType()))
        return getUniversalPtrNode();

    if (isa<ConstantPointerNull>(c))
        return NullObjectIndex;
    else if (const GlobalValue* gv = dyn_cast<GlobalValue>(c))
        return getObjectNodeFor(gv);
    else if (const ConstantExpr* ce = dyn_cast<ConstantExpr>(c)) {
        switch (ce->getOpcode()) {
            case Instruction::GetElementPtr:
            {
                NodeIndex baseNode = getObjectNodeForConstant(ce->getOperand(0));
                assert(baseNode != InvalidIndex && "missing base obj node for gep");
                if (baseNode == NullObjectIndex || baseNode == UniversalObjIndex)
                    return baseNode;

                return getOffsetObjectNode(baseNode, constGEPtoFieldNum(ce));
            }
            case Instruction::IntToPtr:
                // FIXME
                return NullObjectIndex;
            case Instruction::PtrToInt:
                // FIXME
                return NullObjectIndex;
            case Instruction::BitCast:
                return getObjectNodeForConstant(ce->getOperand(0));
            default:
                errs() << "Constant Expr not yet handled: " << *ce << "\n";
                llvm_unreachable(0);
        }
    } else if (isa<BlockAddress>(c)) {
        // FIXME return NULL now
        return NullObjectIndex;
    }

    errs() << "Unknown constant pointer: " << *c << "\n";
    llvm_unreachable("Unknown constant pointer!");
    return InvalidIndex;
}

NodeIndex AndersNodeFactory::getReturnNodeFor(const llvm::Function* f) {
    auto FID = f->getGUID();
    auto rf = funcMap->find(FID);
    if (rf != funcMap->end())
        f = rf->second;
    else if (extFuncMap->find(FID) != extFuncMap->end())
        // XXX: return universal ptr?
        return getUniversalPtrNode();
    auto itr = returnMap.find(f);
    if (itr == returnMap.end())
        return InvalidIndex;
    else
        return itr->second;
}

NodeIndex AndersNodeFactory::getVarargNodeFor(const llvm::Function* f) {
    auto itr = varargMap.find(f);
    if (itr == varargMap.end())
        return InvalidIndex;
    else
        return itr->second;
}

NodeIndex AndersNodeFactory::getDereferenceNodeFor(const NodeIndex ptr) {
    auto itr = derefMap.find(ptr);
    if (itr == derefMap.end())
        return InvalidIndex;
    else
        return itr->second;
}

unsigned AndersNodeFactory::constGEPtoFieldNum(const llvm::ConstantExpr* expr) const {
    const GEPOperator* GEP = dyn_cast<GEPOperator>(expr);
    assert(GEP != NULL && "constGEPtoFieldNum receives a non-gep value!");

    // we assume the base pointer has already been recursively processed
    // so there is no need to strip
    unsigned ret = 0;
    const Type* elemTy = GEP->getSourceElementType();
    const Type* ptrTy = GEP->getPointerOperand()->getType();

    auto idx = GEP->idx_begin();
    if (ptrTy->isPointerTy()) {
        ConstantInt *CI = dyn_cast<ConstantInt>(*idx);
        assert(CI != NULL && "GEP ptr index is not a constant int!");
        if (!CI->isZero()) {
            if (elemTy->isIntegerTy(8)) {
                AA_LOG("const gep expr with non-zero index into ptr: " << *expr << "\n");
                // char*, offset = index
                assert(GEP->getNumIndices() == 1 && "char* should have only one index!");
                int64_t offset = CI->getSExtValue();
                assert(offset >= 0 && "constexpr char* offset should be non-negative!");
                auto ptr = dyn_cast<GlobalVariable>(GEP->getPointerOperand()->stripPointerCasts());
                assert(ptr && "const gep expr ptr should be a global variable!");
                auto GID = ptr->getGUID();
                auto itr = gobjMap->find(GID);
                if (itr != gobjMap->end()) {
                    ptr = itr->second;
                } else {
                    itr = extGobjMap->find(GID);
                    if (itr != extGobjMap->end())
                        ptr = itr->second;
                }
                auto itr2 = objNodeMap.find(ptr);
                assert(itr2 != objNodeMap.end() && "const gep expr ptr should have a node!");
                const Type *ATy = nodes[itr2->second].getAllocationType();
                return offsetToFieldNum(ATy, offset, dataLayout, *structAnalyzer, module);
            } else {
                // slow path, convert to byte offset then back to field number
                int64_t offset = getGEPOffset(GEP, dataLayout);
                // assert(offset >= 0 && "constexpr gep offset should be non-negative!");
                if (offset < 0) {
                    AA_LOG("Negative offset " << offset << " for GEP: " << *expr << "\n");
                    // FIXME: return 0 for now
                    return 0;
                }
                return offsetToFieldNum(elemTy, offset, dataLayout, *structAnalyzer, module);
            }
        } // else
        idx++;
    }

    // fast path, without converting to byte offset then back to field number
    while (idx != GEP->idx_end()) {
        if (const ArrayType *arrayType = dyn_cast<ArrayType>(elemTy)) {
            // array has been collapsed
            elemTy = arrayType->getElementType();
        } else if (const StructType *structType = dyn_cast<StructType>(elemTy)) {
            ConstantInt *CI = dyn_cast<ConstantInt>(*idx);
            assert(CI != NULL && "GEP struct index is not a constant int!");
            unsigned index = CI->getZExtValue();

            const StructInfo* stInfo = structAnalyzer->getStructInfo(structType, module);
            assert(stInfo != NULL && "structInfoMap should have info for all structs!");

            if (index >= stInfo->getSize()) {
                // index is out of bounds, likely due to union
                WARNING("Field index " << index << " is out of bounds, size = "
                        << stInfo->getSize() << " for GEP: " << *expr << "\n");
                // FIXME: we don't record anything about unions, so just return
                break;
            }
            ret += stInfo->getOffset(index);

            elemTy = structType->getElementType(index);
        } else if (const VectorType *vectorType = dyn_cast<VectorType>(elemTy)) {
            elemTy = vectorType->getElementType();
        } else {
            assert(false && "Unhandled GEP element type!");
        }
        idx++;
    }

    return ret;
}

void AndersNodeFactory::mergeNode(NodeIndex n0, NodeIndex n1) {
    assert(n0 < nodes.size() && n1 < nodes.size());
    nodes[n1].mergeTarget = n0;
}

NodeIndex AndersNodeFactory::getMergeTarget(NodeIndex n) {
    assert(n < nodes.size());
    NodeIndex ret = nodes[n].mergeTarget;
    if (ret != n)
    {
        std::vector<NodeIndex> path(1, n);
        while (ret != nodes[ret].mergeTarget)
        {
            path.push_back(ret);
            ret = nodes[ret].mergeTarget;
        }
        for (auto idx: path)
            nodes[idx].mergeTarget = ret;
    }
    assert(ret < nodes.size());
    return ret;
}

NodeIndex AndersNodeFactory::getMergeTarget(NodeIndex n) const {
    assert (n < nodes.size());
    NodeIndex ret = nodes[n].mergeTarget;
    while (ret != nodes[ret].mergeTarget)
        ret = nodes[ret].mergeTarget;
    return ret;
}

void AndersNodeFactory::setNodeAsTainted(NodeIndex i) {
    assert(nodes.at(i).type == AndersNode::OBJ_NODE);
    taintedNodes.insert(i);
}

static void dumpLocation(const Value *val) {
    FUNCTION_TIMER();

    if (!val)
        return;

    if (const Instruction *inst = dyn_cast<Instruction>(val)) {
        DebugLoc loc = inst->getDebugLoc();
        if (isa<AllocaInst>(inst)) {
            std::string a;
            raw_string_ostream ao(a);
            inst->getType()->print(ao);
            ao << " %" << inst->getName();
            for (auto const& i : *(inst->getParent())) {
                if (const CallInst *ci = dyn_cast<CallInst>(&i)) {
                    Function *f = ci->getCalledFunction();
                    if (f != nullptr && !f->getName().compare("llvm.dbg.value")) {
                        std::string m;
                        raw_string_ostream mo(m);
                        ci->getOperand(0)->print(mo);
                        if (ao.str() == mo.str()) {
                            loc = ci->getDebugLoc();
                            break;
                        }
                    }
                }
            }
        }
        AA_LOG("\tsrc> ");
        const Function *F = inst->getParent()->getParent();
        if (F && F->hasName())
            AA_LOG(" (" << F->getName() << ") ");
        if (VerboseLevel >= 2)
            loc.print(errs());
        AA_LOG("\n");
    }
}

void AndersNodeFactory::dumpNode(NodeIndex idx) const {

    const AndersNode& n = nodes.at(idx);

    if (n.type == AndersNode::VALUE_NODE)
        AA_LOG("V ");
    else if (n.type == AndersNode::OBJ_NODE)
        AA_LOG("O ");
    else if (n.type == AndersNode::DEREF_NODE)
        AA_LOG("D ");
    else
        assert(false && "Wrong type number!");
    AA_LOG("#" << n.idx << "\t");

    // Dump node value info.
    const Value* val = n.getValue();
    if (val == nullptr) {
        NodeIndex offset = n.getOffset();
        if (offset == 0)
           AA_LOG("nullptr>");
        else
        {
            NodeIndex baseIdx = n.getIndex() - offset;
            const Value* base = nodes.at(baseIdx).getValue();
            assert(base != nullptr);

            AA_LOG("field [" << offset << "] of ");

            Type *BaseTy = base->getType();
            if (BaseTy && VerboseLevel >= 2)
                BaseTy->print(errs());

            if (base->hasName())
                AA_LOG(" : " << base->getName());
        }
    }
    else if (isa<Function>(val))
        AA_LOG("f> " << val->getName());
    else
        AA_LOG("v> " << *val);
    AA_LOG("\n");

    // Dump source loc info if possible.
    dumpLocation(val);
}

void AndersNodeFactory::dumpNode(NodeIndex idx,
                                 std::map<NodeIndex, AndersPtsSet>& ptsGraph,
                                 std::set<NodeIndex>& dumped, bool dumpDep) const {

    dumpNode(idx);
    dumped.insert(idx);

    // Dump ptr set info.
    dumpNodePtrSetInfo(idx, ptsGraph, dumped, dumpDep);
}

static unsigned ptrMax;
static unsigned long ptrTotal;
static unsigned long ptrNumber;

void AndersNodeFactory::dumpNodePtrSetInfo(
        NodeIndex index, std::map<NodeIndex, AndersPtsSet>& ptsGraph,
        std::set<NodeIndex>& dumped, bool dumpDep) const {

    FUNCTION_TIMER();

    NodeIndex rep = getMergeTarget(index);
    if (rep != index)
        AA_LOG("\tmerge> " << index << " -> " << rep << "\n");

    auto ptsItr = ptsGraph.find(rep);
    if (ptsItr != ptsGraph.end()) {
        unsigned size = ptsItr->second.getSize();
        // if (index != 0 && ptsItr->second.has(getUniversalObjNode()))
        //     outs() << "-1\n";
        // else
        //     outs() << size <<"\n";
        if (size > ptrMax)
            ptrMax = size;

        ptrTotal += size;
        ptrNumber++;

        // AA_LOG("\tptrs> ");
        // for (auto v: ptsItr->second)
        //     AA_LOG(v << " ");
        // AA_LOG("\n");

        // if (dumpDep) {
        //     // Since we may not dump all the nodes
        //     // this is necessary for dumping the dependents
        //     for (auto v: ptsItr->second) {
        //         if (!dumped.count(v))
        //             dumpNode(v, ptsGraph, dumped, dumpDep);
        //     }
        // }
    }
}

void AndersNodeFactory::dumpNodeInfo(
        std::map<NodeIndex, AndersPtsSet>& ptsGraph,
        std::set<const Value*>* inclusion) const {
    FUNCTION_TIMER();
    std::set<NodeIndex> dumped;
    bool dumpDep = inclusion ? true : false;
    ptrMax = 0;
    ptrTotal = ptrNumber = 0;

    AA_LOG("\n----- Print AndersNodeFactory Info -----\n");
    for (auto const& node: nodes)
    {
        // Dump node ordinal info.
        NodeIndex index = node.getIndex();
        const Value* val = node.getValue();

        // Only dump the requested value if provided
        if (inclusion != nullptr && !inclusion->count(val))
            continue;

        // Do not re-dump
        if (dumped.count(index))
            continue;

        dumpNode(index, ptsGraph, dumped, dumpDep);
    }

    AA_LOG("\nReturn Map:\n");
    for (auto const& mapping: returnMap)
        AA_LOG(mapping.first->getName() << "  -->>  [Node #" << mapping.second << "]\n");

    AA_LOG("\nVararg Map:\n");
    for (auto const& mapping: varargMap)
        AA_LOG(mapping.first->getName() << "  -->>  [Node #" << mapping.second << "]\n");
    AA_LOG("----- End of Print -----\n");

    errs() << "\nStatistic Info:\n";
    errs() << "ptrMax = " << ptrMax << "\n";
    errs() << "ptrTotal = " << ptrTotal << "\n";
    errs() << "ptrNumber = " << ptrNumber << "\n";
}

void AndersNodeFactory::dumpRepInfo() const {
    errs() << "\n----- Print Node Merge Info -----\n";
    for (NodeIndex i = 0, e = nodes.size(); i < e; ++i) {
        NodeIndex rep = getMergeTarget(i);
        if (rep != i)
            errs() << i << " -> " << rep << "\n";
    }
    errs() << "----- End of Print -----\n";
}
