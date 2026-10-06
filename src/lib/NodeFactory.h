#ifndef ANDERSEN_NODEFACTORY_H
#define ANDERSEN_NODEFACTORY_H

#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/Analysis/ValueTracking.h>

#include "StructAnalyzer.h"

#include <map>
#include <unordered_set>
#include <vector>
#include <set>

#include <boost/unordered/unordered_flat_map.hpp>

//List propagation: propagate callee's arg lists to caller's arg lists
//#define ListProp

// AndersNode class - This class is used to represent a node in the constraint graph.
// Due to various optimizations, it is not always the case that there is always a mapping from a Node to a Value.
// (In particular, we add artificial Node's that represent the set of pointed-to variables shared for each location equivalent Node.
// Ordinary clients are not allowed to create AndersNode objects. To guarantee index consistency,
// AndersNodes (and its subclasses) instances should only be created through AndersNodeFactory.
typedef unsigned NodeIndex;
typedef boost::unordered_flat_map<uint64_t, llvm::Function*> FuncMap;
typedef boost::unordered_flat_map<uint64_t, llvm::GlobalVariable*> GObjMap;

class AndersNode {
public:
    enum AndersNodeType {
        VALUE_NODE,
        OBJ_NODE,
        DEREF_NODE,
        // A memory cell (plan 3.26): one location of an object, keyed by a
        // name (a field as label+byte offset, a union slot, a key value, a
        // byte offset of an unlabeled object). Its content is (origin, name):
        // the origin is the object node of the allocation, global, stack slot
        // or function; the name is an id of the factory's cell-name table.
        CELL_NODE
    };
private:
    AndersNodeType type;
    NodeIndex idx;
    const llvm::Value* value;
    bool isHeapNode;
    bool isOpaqueObj;
    NodeIndex cellOrigin = ~0u; // CELL_NODE: the object node it is a cell of
    uint32_t cellName = ~0u;    // CELL_NODE: id in the cell-name table

    AndersNode(AndersNodeType t, unsigned i, const llvm::Value* v = nullptr,
               bool heap = false, bool opaque = false)
            : type(t), idx(i), value(v), isHeapNode(heap), isOpaqueObj(opaque) {}

public:
    NodeIndex getIndex() const { return idx; }
    const llvm::Value* getValue() const { return value; }
    bool isHeap() const { return isHeapNode; }
    bool isOpaque() const { return isOpaqueObj; }

    friend class AndersNodeFactory;
};

// This is the factory class of AndersNode
// It use a vectors to hold all Nodes in the program
// Since vectors may invalidate all element pointers/iterators when resizing,
// it is impossible to return AndersNode* in public interfaces (they may get invalidated).
// Therefore, we use plain integers to represent nodes for public functions like createXXX and getXXX.
// This is ugly, but it is efficient.
class AndersNodeFactory {
public:

    // The largest unsigned int is reserved for invalid index
    static const unsigned InvalidIndex;
private:
    llvm::Module* module;
    // The datalayout info
    const llvm::DataLayout* dataLayout;
    // The struct info
    StructAnalyzer* structAnalyzer;
    // Global Object info
    const GObjMap* gobjMap;
    const GObjMap* extGobjMap;
    // Function info
    const FuncMap* funcMap;
    const FuncMap* extFuncMap;

    // The set of nodes
    std::vector<AndersNode> nodes;

    // Some special indices
    std::unordered_set<uint64_t> extGobjOverrides;
    uint64_t uniExtGobjHits = 0, uniOtherHits = 0;
    static const NodeIndex UniversalPtrIndex = 0;
    static const NodeIndex UniversalObjIndex = 1;
    static const NodeIndex NullPtrIndex = 2;
    static const NodeIndex NullObjectIndex = 3;
    static const NodeIndex ConstantIntIndex = 4;

    // valueNodeMap - This map indicates the AndersNode* that a particular Value* corresponds to
    boost::unordered_flat_map<const llvm::Value*, NodeIndex> valueNodeMap;

    // ObjectNodes - This map contains entries for each memory object in the program: globals, alloca's and mallocs.
    // We are able to represent them as llvm::Value* because we're modeling the heap with the simplest allocation-site approach
    boost::unordered_flat_map<const llvm::Value*, NodeIndex> objNodeMap;

    // returnMap - This map contains an entry for each function in the
    // program that returns a ptr.
    boost::unordered_flat_map<const llvm::Function*, NodeIndex> returnMap;

    // varargMap - This map contains the entry used to represent all pointers
    // passed through the varargs portion of a function call for a particular
    // function.  An entry is not present in this map for functions that do not
    // take variable arguments.
    boost::unordered_flat_map<const llvm::Function*, NodeIndex> varargMap;

    // Cells (plan 3.26): (origin object node, name id) -> cell node, minted
    // lazily; names are interned key strings.
    boost::unordered_flat_map<uint64_t, NodeIndex> cellMap;
    std::vector<std::string> cellNames;
    boost::unordered_flat_map<std::string, uint32_t> cellNameIds;

    // derefMap - This map caches the deref-relations across value nodes.
    boost::unordered_flat_map<const NodeIndex, NodeIndex> derefMap;
    // derefParentMap - the inverse: a dereference node's pointer.
    boost::unordered_flat_map<NodeIndex, NodeIndex> derefParentMap;

    // gepMap - constant GEP expressions: (base value node, byte offset) ->
    // the value node of the address, so equal addresses share one node.
    boost::unordered_flat_map<std::pair<NodeIndex, int64_t>, NodeIndex,
                              boost::hash<std::pair<NodeIndex, int64_t>>> gepMap;
    const llvm::GlobalVariable* canonicalizeGlobal(const llvm::GlobalVariable* gv) const;
    bool percpuPtiBase(const llvm::Constant* base) const;
    const llvm::Function* canonicalizeFunction(const llvm::Function* f) const;
    const llvm::Value* canonicalizeValueKey(const llvm::Value* v) const;
public:
    AndersNodeFactory();

    void setModule(llvm::Module* m) { module = m; }
    llvm::Module* getModule() const { return module; }
    void setDataLayout(const llvm::DataLayout* d) { dataLayout = d; }
    const llvm::DataLayout* getDataLayout() const { return dataLayout; }
    void setStructAnalyzer(StructAnalyzer* s) { structAnalyzer = s; }
    void setGobjMap(const GObjMap* m) { gobjMap = m; }
    void setExtGobjMap(const GObjMap* m) { extGobjMap = m; }
    void setFuncMap(const FuncMap* m) { funcMap = m; }
    void setExtFuncMap(const FuncMap* m) { extFuncMap = m; }

    // Factory methods
    NodeIndex createValueNode(const llvm::Value* val = NULL);
    NodeIndex createOpaqueObjectNode(const llvm::Value* val = NULL,
        const bool heap = false);
    NodeIndex createReturnNode(const llvm::Function* f);
    NodeIndex createVarargNode(const llvm::Function* f);
    NodeIndex createDereferenceNode(const NodeIndex ptr);

    // Cells (plan 3.26). A name is any key the program fixes for a location:
    // "struct.T+off" (a field: the object's label and a byte offset),
    // "+k" (byte k of an unlabeled object), "...#v" (refined by a key).
    uint32_t internCellName(const std::string &name);
    const std::string &cellNameString(uint32_t name) const { return cellNames.at(name); }
    // The cell of `origin` named `name`, created on first use.
    NodeIndex getCellNode(NodeIndex origin, uint32_t name);
    bool isCellNode(NodeIndex i) const {
        return nodes.at(i).type == AndersNode::CELL_NODE;
    }
    NodeIndex getCellOrigin(NodeIndex cell) const {
        assert(isCellNode(cell) && "not a cell");
        return nodes.at(cell).cellOrigin;
    }
    uint32_t getCellName(NodeIndex cell) const {
        assert(isCellNode(cell) && "not a cell");
        return nodes.at(cell).cellName;
    }
    size_t numCells() const { return cellMap.size(); }

    // Map lookup interfaces (return NULL if value not found)
    NodeIndex getValueNodeFor(const llvm::Value* val);
    NodeIndex getValueNodeForConstant(const llvm::Constant* c);
    NodeIndex getReturnNodeFor(const llvm::Function* f);
    NodeIndex getVarargNodeFor(const llvm::Function* f);
    NodeIndex getDereferenceNodeFor(const NodeIndex ptr);
    // The pointer a dereference node was created for (InvalidIndex for
    // one created without a pointer).
    NodeIndex getDerefParent(NodeIndex deref) const {
        auto it = derefParentMap.find(deref);
        return it == derefParentMap.end() ? InvalidIndex : it->second;
    }
    const boost::unordered_flat_map<const NodeIndex, NodeIndex> &
    getDerefMap() const { return derefMap; }

    // Node classification: distinguish function value nodes from
    // return/vararg nodes (all three store Function* as their value)
    bool isReturnNode(NodeIndex i) const {
        const llvm::Value *v = nodes.at(i).getValue();
        if (!v) return false;
        const auto *f = llvm::dyn_cast<llvm::Function>(v);
        if (!f) return false;
        auto it = returnMap.find(f);
        return it != returnMap.end() && it->second == i;
    }
    bool isVarargNode(NodeIndex i) const {
        const llvm::Value *v = nodes.at(i).getValue();
        if (!v) return false;
        const auto *f = llvm::dyn_cast<llvm::Function>(v);
        if (!f) return false;
        auto it = varargMap.find(f);
        return it != varargMap.end() && it->second == i;
    }

    // Pointer arithmetic
    const bool isObjectNode(NodeIndex i) const {
        return (nodes.at(i).type == AndersNode::OBJ_NODE);
    }
    const bool isValueNode(NodeIndex i) const {
        return (nodes.at(i).type == AndersNode::VALUE_NODE);
    }
    const bool isDereferenceNode(NodeIndex i) const {
        return (nodes.at(i).type == AndersNode::DEREF_NODE);
    }
    const bool isHeapObject (NodeIndex i) const {
        return nodes.at(i).isHeap();
    }
    const bool isOpaqueObject(NodeIndex i) const {
        return nodes.at(i).isOpaque();
    }

    // Special node getters
    NodeIndex getUniversalPtrNode() const { return UniversalPtrIndex; }
    // Linker-array bounds symbols (task #22): undefined externs whose
    // contents ARE known (closed world: the linker concatenates the
    // enumerated section members). Overridden GUIDs bypass the
    // universal-ptr fallback and resolve to their own value node, so
    // wiring members into deref(bounds) reaches exactly the reads of
    // that array instead of the universal unknown-memory hub.
    void addExtGobjOverride(uint64_t guid) { extGobjOverrides.insert(guid); }
    // universal-fallback exposure counters (no silent conflation)
    void getUniversalLedger(uint64_t &extGobj, uint64_t &other) const {
        extGobj = uniExtGobjHits; other = uniOtherHits;
    }
    bool isExtGobjOverride(uint64_t guid) const {
        return extGobjOverrides.count(guid) != 0;
    }
    NodeIndex getUniversalObjNode() const { return UniversalObjIndex; }
    NodeIndex getNullPtrNode() const { return NullPtrIndex; }
    NodeIndex getNullObjectNode() const { return NullObjectIndex; }
    NodeIndex getConstantIntNode() const { return ConstantIntIndex; }
    static bool isSpecialNode(NodeIndex i) {
        return i <= ConstantIntIndex;
    }

    // Value getters
    // The IR value a node stands for; a dereference or a cell has none
    // (its pointer: getDerefParent; its object: getCellOrigin).
    const llvm::Value* getValueForNode(NodeIndex i) const {
        return nodes.at(i).getValue();
    }

    // Size getters
    unsigned getNumNodes() const { return nodes.size(); }


    // For debugging purpose
    void dumpNode(NodeIndex) const;
};

#endif
