#ifndef KA_NAMED_CELLS_H
#define KA_NAMED_CELLS_H

// Access names for named cells (docs/plan-named-cells.md Part B,
// docs/named-cells-design.md; model proof/lean/CompositionalCFL/
// NamedCells.lean).
//
// The name of a scalar memory access is the innermost NAMED struct type
// that contains the accessed leaf field, with the leaf's byte offset in
// it. Array elements fold onto element 0 (every element of an array
// field shares one name) and literal structs are transparent. One
// descent computes it for both sides: from a GEP chain (loads, stores)
// and from a struct type and offset (initializer slots), so a store and
// a load of the same field get the same name by whichever path they
// reached it.
//
// A union inside a named struct is one slot of that struct: an access in
// it is named by the struct and its byte offset (every member at those
// bytes shares the plane), unless a struct-typed member of the union
// overlaps the access (a `struct T *` into the union names its accesses
// T+off, which would then miss the slot's).
//
// An access gets no name (`Unnamed`) when its address expression has no
// struct type, an offset leaves the struct it indexes, a leaf is crossed
// or padding is hit, a union with a struct member over the bytes (or a
// union outside any named struct) lies on the path, or the chain casts the
// position to a struct type the enclosing layout does not have there
// (punning between unrelated structs).

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>

#include <boost/unordered/unordered_flat_map.hpp>
#include <boost/unordered/unordered_flat_set.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace ka {

// The C struct tag a DIType names, through typedefs, qualifiers and
// (with ThroughPtr) one pointer level — an anonymous struct by its
// nearest typedef, which is how clang names its IR type; "" if the type
// is no struct.
llvm::StringRef diStructName(const llvm::DIType *T, bool ThroughPtr);

class AccessNames {
public:
  // Name ids. 0 is a cell's own node (every plane); 1 is the plane of
  // writes that carry no name; 2 is the plane of content from outside
  // the program (roots minted on cells), read under every name; access
  // names start at FirstName.
  static constexpr uint32_t Original = 0;
  static constexpr uint32_t Unnamed = 1;
  static constexpr uint32_t Identity = 2;
  static constexpr uint32_t FirstName = 3;

  enum Why : unsigned {
    NoStruct,   // no struct type on the address expression
    OutOfRange, // offset outside the struct (or into a flexible tail)
    Straddle,   // access crosses a leaf, or lands in padding
    Union,      // a union on the path
    Pun,        // chain casts to a struct the layout does not have there
    NumWhy
  };
  static const char *whyName(Why W);

  AccessNames();

  // Pointers a module indexes as two struct types neither of which sits
  // at offset 0 of the other (a cast between unrelated structs on one
  // base: punning). Every access through such a base is Unnamed. Call
  // once per module before naming its accesses.
  void scanBases(const llvm::Module &M);

  // Where an address points: the innermost named struct and the byte
  // offset in it (array elements folded). When the access has no name
  // because the position is tainted (a union, a pun, or a variable step
  // out of a struct), `open` lists every named struct the chain shows
  // it may lie in; with no struct at all (`S` null, `open` empty) the
  // address is untyped.
  struct Position {
    llvm::StructType *S = nullptr;
    int64_t off = 0;
    bool tainted = false;
    Why why = NoStruct;
    llvm::SmallVector<llvm::StructType *, 2> open;
    // A struct only debug info still describes (the optimizer dropped its
    // IR type): its composite and C tag, `off` bytes in. Set only when S
    // is not.
    const llvm::DICompositeType *DIS = nullptr;
    llvm::StringRef DITag;
    const llvm::Module *M = nullptr;
    // An anonymous struct on the chain with no named struct around it.
    bool anonOnly = false;
  };
  Position position(const llvm::Value *Ptr, const llvm::DataLayout &DL);
  // Every leaf name of S (nested named structs by their own names,
  // arrays folded, nothing inside unions).
  const llvm::SmallVector<uint32_t, 8> &leavesOf(llvm::StructType *S,
                                                  const llvm::DataLayout &DL);

  // Name of a `Size`-byte access through address `Ptr`, or Unnamed.
  uint32_t ofAccess(const llvm::Value *Ptr, uint64_t Size,
                    const llvm::DataLayout &DL);
  // Name of load or store `I` (its address and size): from the GEP chain,
  // else from its struct-path TBAA tag (the base struct and the offset in
  // it, which clang emits for every field access and which survives the
  // byte GEPs instcombine leaves at -O2/-O3).
  uint32_t ofMemAccess(const llvm::Instruction &I, const llvm::Value *Ptr,
                       uint64_t Size, const llvm::DataLayout &DL);
  // Names of the lanes of a vector-of-pointers access (empty unless
  // every lane has one): the -O3 vectorizer's paired field copies.
  llvm::SmallVector<uint32_t, 4> ofLanes(const llvm::Value *Ptr,
                                         llvm::VectorType *VT,
                                         const llvm::DataLayout &DL);
  // The named IR struct a C struct tag denotes in module M.
  llvm::StructType *structByTag(const llvm::Module *M, llvm::StringRef Tag);
  // The debug-info composite of the named struct with C tag Tag, or null.
  const llvm::DICompositeType *diStruct(llvm::StringRef Tag) const {
    auto It = DIStruct.find(Tag.str());
    return It == DIStruct.end() ? nullptr : It->second;
  }
  // The struct an untyped base pointer is declared to point to: a formal
  // by its subprogram's parameter type, any other value by the variable
  // a dbg.value describes it as. The IR type when the module still has
  // it, else the debug-info composite.
  struct BaseType {
    llvm::StructType *S = nullptr;
    const llvm::DICompositeType *C = nullptr;
    llvm::StringRef Tag;
  };
  BaseType baseStruct(const llvm::Value *P);
  // ofSlot for a debug-info-only struct: descend its members (handing
  // over to the IR type of any member struct the module still has); a
  // leaf of a debug-info-only struct is named "struct.<tag>+<offset>",
  // as its IR type would have been.
  uint32_t ofDISlot(const llvm::Module *M, const llvm::DICompositeType *C,
                    llvm::StringRef Tag, uint64_t Off, uint64_t Size,
                    const llvm::DataLayout &DL);
  // Name of a `Size`-byte access at position P (IR or debug info).
  uint32_t ofPosition(const Position &P, uint64_t Size,
                      const llvm::DataLayout &DL);
  uint64_t namedByTBAA = 0;
  // Unnamed because the only struct around the access is anonymous
  // (counted among NoStruct).
  uint64_t anonOnly = 0;
  // Name of a `Size`-byte access at byte `Off` of named struct `S`, or
  // Unnamed. The descent ofAccess ends with.
  uint32_t ofSlot(llvm::StructType *S, uint64_t Off, uint64_t Size,
                  const llvm::DataLayout &DL);

  const std::string &str(uint32_t Id) const { return Names[Id]; }
  // The id of a name built outside the descent (a union key,
  // "struct.S+off#v"; --cfl-union-keys).
  uint32_t keyName(const std::string &S) { return intern(S); }
  uint32_t size() const { return (uint32_t)Names.size(); }
  // Unnamed results by reason (counted per query).
  uint64_t unnamedBy[NumWhy] = {};

private:
  uint32_t miss(Why W) {
    unnamedBy[W]++;
    return Unnamed;
  }
  uint32_t intern(std::string S);
  // The union slot name for bytes [Rel, Rel+Size) of the union at byte
  // Base of named struct S, or Unnamed when a struct-typed member of the
  // union (debug info: the IR keeps only its largest member) overlaps them.
  uint32_t unionSlot(llvm::StructType *S, uint64_t Base, uint64_t Rel,
                     uint64_t Size);
  // Debug-info composites of named structs, by C tag (scanBases).
  boost::unordered_flat_map<std::string, const llvm::DICompositeType *> DIStruct;
  std::vector<std::string> Names;
  boost::unordered_flat_map<std::string, uint32_t> Ids;
  boost::unordered_flat_set<const llvm::Value *> PunnedBases;
  boost::unordered_flat_map<llvm::StructType *, llvm::SmallVector<uint32_t, 8>>
      Leaves;
  // Per module: C struct tag (TBAA type name) -> named IR struct.
  boost::unordered_flat_map<const llvm::Module *,
                            boost::unordered_flat_map<std::string, llvm::StructType *>>
      ByTag;
  boost::unordered_flat_map<const llvm::Value *, BaseType> BaseOf;
};

} // namespace ka

#endif
