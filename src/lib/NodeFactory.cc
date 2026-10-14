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
#include "Flags.h"
#include <sstream>

#include "NodeFactory.h"
#include "Common.h"

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

const GlobalVariable* AndersNodeFactory::canonicalizeGlobal(
    const GlobalVariable* gv) const {
    if (!gv)
        return gv;
    uint64_t gid = gv->getGUID();
    if (gobjMap) {
        auto it = gobjMap->find(gid);
        if (it != gobjMap->end())
            return it->second;
    }
    if (extGobjMap) {
        auto it = extGobjMap->find(gid);
        if (it != extGobjMap->end())
            return it->second;
    }
    return gv;
}

const Function* AndersNodeFactory::canonicalizeFunction(
    const Function* f) const {
    if (!f)
        return f;
    uint64_t fid = f->getGUID();
    if (funcMap) {
        auto it = funcMap->find(fid);
        if (it != funcMap->end())
            return it->second;
    }
    if (extFuncMap) {
        auto it = extFuncMap->find(fid);
        if (it != extFuncMap->end())
            return it->second;
    }
    return f;
}

const Value* AndersNodeFactory::canonicalizeValueKey(const Value* v) const {
    if (v == nullptr)
        return nullptr; // anonymous nodes (e.g., synthetic field pointers)
    if (const auto *arg = dyn_cast<Argument>(v)) {
        const Function *parent = arg->getParent();
        const Function *canonParent = canonicalizeFunction(parent);
        if (canonParent && arg->getArgNo() < canonParent->arg_size())
            return canonParent->getArg(arg->getArgNo());
        return v;
    }
    if (const auto *ga = dyn_cast<GlobalAlias>(v))
        return canonicalizeValueKey(ga->getAliasee()->stripPointerCasts());
    if (const auto *gv = dyn_cast<GlobalVariable>(v))
        return canonicalizeGlobal(gv);
    if (const auto *f = dyn_cast<Function>(v))
        return canonicalizeFunction(f);
    return v;
}

NodeIndex AndersNodeFactory::createValueNode(const Value* val) {
    val = canonicalizeValueKey(val);
    if (val != nullptr) {
        auto it = valueNodeMap.find(val);
        if (it != valueNodeMap.end())
            return it->second;
    }

    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::VALUE_NODE, nextIdx, val));
    if (val != nullptr)
        valueNodeMap[val] = nextIdx;

    return nextIdx;
}

NodeIndex AndersNodeFactory::createOpaqueObjectNode(const Value* val, const bool heap) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, nextIdx, val, heap, /*opaque=*/true));
    if (val != nullptr) {
        if (objNodeMap.count(val))
            return objNodeMap[val];
        objNodeMap[val] = nextIdx;
    }

    return nextIdx;
}

NodeIndex AndersNodeFactory::createReturnNode(const llvm::Function* f) {
    f = canonicalizeFunction(f);
    auto existing = returnMap.find(f);
    if (existing != returnMap.end())
        return existing->second;

    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::VALUE_NODE, nextIdx, f));

    returnMap[f] = nextIdx;

    return nextIdx;
}

NodeIndex AndersNodeFactory::createVarargNode(const llvm::Function* f) {
    f = canonicalizeFunction(f);
    auto existing = varargMap.find(f);
    if (existing != varargMap.end())
        return existing->second;

    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::OBJ_NODE, nextIdx, f));

    varargMap[f] = nextIdx;

    return nextIdx;
}

uint32_t AndersNodeFactory::internCellName(const std::string &name) {
    auto [it, ins] = cellNameIds.try_emplace(name, (uint32_t)cellNames.size());
    if (ins)
        cellNames.push_back(name);
    return it->second;
}

NodeIndex AndersNodeFactory::getCellNode(NodeIndex origin, uint32_t name) {
    assert(origin != InvalidIndex && name < cellNames.size() && "a cell has an origin and a name");
    const uint64_t key = ((uint64_t)origin << 32) | name;
    auto it = cellMap.find(key);
    if (it != cellMap.end())
        return it->second;
    const unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::CELL_NODE, nextIdx));
    nodes.back().cellOrigin = origin;
    nodes.back().cellName = name;
    cellMap.emplace(key, nextIdx);
    return nextIdx;
}

NodeIndex AndersNodeFactory::createDereferenceNode(const NodeIndex ptr) {
    unsigned nextIdx = nodes.size();
    nodes.emplace_back(AndersNode(AndersNode::DEREF_NODE, nextIdx));
    if (ptr != InvalidIndex) {
        if (derefMap.count(ptr))
            return derefMap[ptr];
        derefMap[ptr] = nextIdx;
        derefParentMap[nextIdx] = ptr;
    }
    return nextIdx;
}

NodeIndex AndersNodeFactory::getValueNodeFor(const Value* val) {
    if (const Constant* c = dyn_cast<Constant>(val))
        if (!isa<GlobalValue>(c))
            return getValueNodeForConstant(c);

    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(val)) {
        auto GID = globalVar->getGUID();
        if (gobjMap) {
            auto itr = gobjMap->find(GID);
            if (itr != gobjMap->end()) {
                val = itr->second;
            } else if (extGobjMap && extGobjMap->find(GID) != extGobjMap->end()) {
                if (extGobjOverrides.count(GID))
                    val = extGobjMap->find(GID)->second; // own identity
                else {
                    uniExtGobjHits++;
                    return getUniversalPtrNode();
                }
            }
        } else if (extGobjMap && extGobjMap->find(GID) != extGobjMap->end()) {
            if (extGobjOverrides.count(GID))
                val = extGobjMap->find(GID)->second; // own identity
            else {
                uniExtGobjHits++;
                return getUniversalPtrNode();
            }
        }
    }
    val = canonicalizeValueKey(val);

    auto itr = valueNodeMap.find(val);
    if (itr == valueNodeMap.end()) {
        return InvalidIndex;
    } else {
        return itr->second;
    }
}

// Single ptrtoint leaf of a folded integer/inttoptr constant chain: the
// chain computes an address DERIVED from exactly one pointer (percpu
// rebasing, tagged pointers in static initializers, address-as-integer
// laundering). Two leaves = a pointer DIFFERENCE (PREL32 table entries,
// ".long fn - .") — NOT a pointer; the LinkerArrays/offset_to_ptr
// machinery owns those, so return null and leave them untouched.
static const Constant* singlePtrToIntBase(const Constant* c,
                                          unsigned depth = 0) {
    if (depth > 8)
        return nullptr;
    const auto *ce = dyn_cast<ConstantExpr>(c);
    if (!ce)
        return nullptr;
    switch (ce->getOpcode()) {
        case Instruction::PtrToInt:
            return cast<Constant>(ce->getOperand(0));
        case Instruction::IntToPtr: // nested round trip
        case Instruction::Trunc:
        case Instruction::ZExt:
        case Instruction::SExt:
        case Instruction::BitCast:
            return singlePtrToIntBase(cast<Constant>(ce->getOperand(0)),
                                      depth + 1);
        case Instruction::Add:
        case Instruction::Sub:
        case Instruction::Or: {
            const Constant *l =
                singlePtrToIntBase(cast<Constant>(ce->getOperand(0)), depth + 1);
            const Constant *r =
                singlePtrToIntBase(cast<Constant>(ce->getOperand(1)), depth + 1);
            if (l && r)
                return nullptr; // pointer difference: no single identity
            return l ? l : r;
        }
        default:
            return nullptr;
    }
}

// Percpu gate for the constant-level rebased-pointer identity
// (narrowed 2026-08-12): only .data..percpu-section globals get their
// identity carried through folded ptrtoint chains — the GT-demanded
// population. Broad application multiplied the km closure ~3.8x.
bool AndersNodeFactory::percpuPtiBase(const llvm::Constant* base) const {
    const auto *gv = dyn_cast<GlobalVariable>(base->stripPointerCasts());
    if (!gv)
        return false;
    if (const GlobalVariable *cg = canonicalizeGlobal(gv))
        return cg->getSection().contains("percpu");
    return gv->getSection().contains("percpu");
}

NodeIndex AndersNodeFactory::getValueNodeForConstant(const llvm::Constant* c) {
    // Accept pointer types and vector-of-pointer types (e.g., <2 x ptr>)
    Type *cTy = c->getType();
    bool isPtr = isa<PointerType>(cTy);
    if (!isPtr) {
        if (auto *VT = dyn_cast<VectorType>(cTy))
            isPtr = VT->getElementType()->isPointerTy();
    }
    if (!isPtr) {
        // Integer constant DERIVED from one pointer (folded ptrtoint
        // chain): carry the base's identity instead of dropping to the
        // inert int node — closes the address-as-integer laundering hole
        // (store i64 ptrtoint(@gv) ... load ... inttoptr).
        // --cfl-cells (Fable 2026-10-13): a constant integer is not a
        // carrier, and a ptrtoint constant is a value node of its object.
        // The shared constant-int node must never hold a fact (a nameless
        // hub every integer constant reads: the kernel's ERR_PTR arms read
        // every ptrtoint-constant pointer stored anywhere).
        if (const Constant *base = singlePtrToIntBase(c))
            if (CFLCells || percpuPtiBase(base)) {
                if (CFLCells) ptrToIntConstants.insert(c);
                return getValueNodeFor(base);
            }
        return ConstantIntIndex;
    }

    if (isa<ConstantPointerNull>(c) || isa<UndefValue>(c) ||
        isa<ConstantAggregateZero>(c))
        return NullPtrIndex;
    // Vector-of-pointer constants: look up or create a collapsed value node
    if (isa<VectorType>(cTy)) {
        auto itr = valueNodeMap.find(c);
        if (itr != valueNodeMap.end())
            return itr->second;
        return createValueNode(c);
    }
    if (const GlobalValue* gv = dyn_cast<GlobalValue>(c))
        return getValueNodeFor(gv);
    else if (const ConstantExpr* ce = dyn_cast<ConstantExpr>(c)) {
        switch (ce->getOpcode()){
            case Instruction::GetElementPtr:
            {
                NodeIndex baseNode = getValueNodeForConstant(ce->getOperand(0));
                assert(baseNode != InvalidIndex && "missing base val node for gep");

                if (baseNode == NullObjectIndex)
                    return NullPtrIndex;
                // The IntToPtr case resolves pure-integer addresses
                // (LIST_POISON1/2, ERR_PTR, MMIO/fixmap) to the null
                // POINTER value — GEP arithmetic on such a sentinel is
                // still the same object-less sentinel. Typed-pointer
                // (LLVM-14) kernel IR folds poison+offset into exactly
                // this shape; without the guard it fell through to the
                // field mapper (negative-offset assert, 2026-08-18).
                if (baseNode == NullPtrIndex)
                    return NullPtrIndex;

                if (baseNode == UniversalObjIndex) {
                    errs() << "GEP CE, universal obj " << *(ce->getOperand(0)) << "\n";
                    return UniversalPtrIndex;
                }

                // GEP off an absolute integer address (inttoptr CE that
                // is not a rebased real pointer) is still an absolute
                // address: LIST_POISON1/2 + folded arithmetic in
                // typed-pointer (LLVM-14) kernel IR reach here. Sentinels
                // carry no flows; field numbers are meaningless on them.
                if (baseNode == ConstantIntIndex)
                    return ConstantIntIndex;

                // The address is the base plus a byte offset: equal
                // addresses share one value node (cells are named by byte
                // offset, plan 3.26).
                const auto *GEP = cast<GEPOperator>(ce);
                APInt off(dataLayout->getIndexTypeSizeInBits(GEP->getType()), 0);
                const bool constOff = GEP->accumulateConstantOffset(*dataLayout, off);
                assert(constOff && "a constant GEP expression has constant indices");
                (void)constOff;
                if (off.isZero())
                    return baseNode;
                const auto mapKey = std::make_pair(baseNode, off.getSExtValue());
                auto itr = gepMap.find(mapKey);
                if (itr != gepMap.end())
                    return itr->second;
                const NodeIndex gepIndex = createValueNode(ce);
                gepMap.emplace(mapKey, gepIndex);
                return gepIndex;
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
            case Instruction::IntToPtr: {
                // Rebased-pointer rule at the constant level (mirrors
                // visitIntToPtrInst): a folded inttoptr whose integer
                // chain has exactly one ptrtoint(p) IS a pointer into
                // p's object. Pure-integer addresses (MMIO/fixmap/
                // ERR_PTR-style) have no IR object: null.
                if (const Constant *base =
                        singlePtrToIntBase(cast<Constant>(ce->getOperand(0))))
                    if (CFLCells || percpuPtiBase(base)) {
                        if (CFLCells) ptrToIntConstants.insert(c);
                        return getValueNodeFor(base);
                    }
                if (CFLCells) absoluteAddresses.insert(c);
                return NullPtrIndex;
            }
            case Instruction::PtrToInt:
                // Integer-typed: unreachable through the isPtr gate
                // except by recursion; identity handled by
                // singlePtrToIntBase at both entry points.
                return NullPtrIndex;
            default:
                errs() << "Constant Expr not yet handled: " << *ce << "\n";
                llvm_unreachable(0);
        }
    } else if (isa<BlockAddress>(c)) {
        // Computed-goto label: give it its own identity instead of
        // conflating with null, so jump-table slots hold a distinct
        // value (never a function origin — cannot smear the callgraph).
        return createValueNode(c); // createValueNode dedups via valueNodeMap
    }

    errs() << "Unknown constant pointer: " << *c << "\n";
    llvm_unreachable("Unknown constant pointer!");
    return InvalidIndex;
}

NodeIndex AndersNodeFactory::getReturnNodeFor(const llvm::Function* f) {
    uint64_t fid = f->getGUID();
    f = canonicalizeFunction(f);
    auto itr = returnMap.find(f);
    if (itr != returnMap.end())
        return itr->second;
    if (extFuncMap && extFuncMap->find(fid) != extFuncMap->end()) {
        uniOtherHits++; // extern-fn return conflates in universal
        return getUniversalPtrNode();
    }
    return InvalidIndex;
}

NodeIndex AndersNodeFactory::getVarargNodeFor(const llvm::Function* f) {
    f = canonicalizeFunction(f);
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

    const AndersNode *n = &nodes.at(idx);

    if (n->type == AndersNode::VALUE_NODE)
        AA_LOG("V ");
    else if (n->type == AndersNode::OBJ_NODE)
        AA_LOG("O ");
    else if (n->type == AndersNode::DEREF_NODE)
        AA_LOG("D ");
    else if (n->type == AndersNode::CELL_NODE)
        AA_LOG("C ");
    else
        assert(false && "Wrong type number!");
    AA_LOG("#" << n->idx << "\t");

    if (n->type == AndersNode::DEREF_NODE) {
        // idx is the value in derefMap, find the corresponding ptr
        for (auto const& p: derefMap) {
            if (p.second == idx) {
                AA_LOG("of Node #" << p.first << ", ");
                n = &nodes.at(p.first);
                break;
            }
        }
    }

    // A cell: its name, then its object.
    if (n->type == AndersNode::CELL_NODE) {
        AA_LOG("cell " << cellNames.at(n->cellName) << " of #" << n->cellOrigin << ", ");
        n = &nodes.at(n->cellOrigin);
    }

    // Dump node value info.
    const Value* val = n->getValue();
    if (val == nullptr) {
        AA_LOG("nullptr>");
    }
    else if (isa<Function>(val))
        AA_LOG("f> " << val->getName());
    else if (isa<GlobalValue>(val))
        AA_LOG("g> " << val->getName());
    else if (const Argument *arg = dyn_cast<Argument>(val))
        AA_LOG("a> " << *arg << " of " << arg->getParent()->getName());
    else
        AA_LOG("v> " << *val);
    AA_LOG("\n");

    // Dump source loc info if possible.
    dumpLocation(val);
}
