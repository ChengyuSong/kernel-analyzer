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
// An access gets no name (`Unnamed`) when its address expression has no
// struct type, an offset leaves the struct it indexes, a leaf is crossed
// or padding is hit, a union lies on the path, or the chain casts the
// position to a struct type the enclosing layout does not have there
// (punning between unrelated structs).

#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>

#include <boost/unordered/unordered_flat_map.hpp>
#include <boost/unordered/unordered_flat_set.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace ka {

class AccessNames {
public:
  // Name ids. 0 is a cell's own node (every plane); 1 is the plane of
  // writes that carry no name; access names start at 2.
  static constexpr uint32_t Original = 0;
  static constexpr uint32_t Unnamed = 1;

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

  // Name of a `Size`-byte access through address `Ptr`, or Unnamed.
  uint32_t ofAccess(const llvm::Value *Ptr, uint64_t Size,
                    const llvm::DataLayout &DL);
  // Name of a `Size`-byte access at byte `Off` of named struct `S`, or
  // Unnamed. The descent ofAccess ends with.
  uint32_t ofSlot(llvm::StructType *S, uint64_t Off, uint64_t Size,
                  const llvm::DataLayout &DL);

  const std::string &str(uint32_t Id) const { return Names[Id]; }
  uint32_t size() const { return (uint32_t)Names.size(); }
  // Unnamed results by reason (counted per query).
  uint64_t unnamedBy[NumWhy] = {};

private:
  uint32_t miss(Why W) {
    unnamedBy[W]++;
    return Unnamed;
  }
  uint32_t intern(std::string S);
  std::vector<std::string> Names;
  boost::unordered_flat_map<std::string, uint32_t> Ids;
  boost::unordered_flat_set<const llvm::Value *> PunnedBases;
};

} // namespace ka

#endif
