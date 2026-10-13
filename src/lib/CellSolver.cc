/*
 * Copyright (C) 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

// CellSolver.cc: the cell solver (--cfl-cells, plan 3.26).
//
// Facts are cells (origin, name). An origin is a function, a global, a
// stack slot or an allocation site. A name is a byte offset in the
// origin's object, read through the object's label: the layout of its IR
// type (globals, stack slots) or of the struct its typed writes declare
// (heap). The layout folds every array element onto element 0, and a
// labeled heap object is an array of its label. An unlabeled object's
// name is its raw byte offset. Two more names per object: `*`, any offset
// (unknown arithmetic), and `out`, an address outside the object, which no
// legal access dereferences.
//
// Values flow by inclusion. A dereference node of the constraint graph is
// a per-pointer hub, never a cell: a load through pointer p reads every
// cell p holds, a store through p writes every cell p holds. No two cells
// are ever unified, so a cell's content is exactly what the program
// writes into that (origin, name).
//
// A member step of struct S on a labeled object checks that S starts at
// the address's offset in the object's layout; a mismatch is counted (rule
// (b): a pun or a bug in the program) and the step still uses the cell the
// address carries.

#include "CallGraphInternal.h"
#include "SCC.h"
#include <llvm/ADT/BitVector.h>
#include <deque>
#include <numeric>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DebugInfo.h>

using namespace llvm;

namespace {

// A set of fact ids: sorted while small, a bit vector once large.
class Facts {
  SmallVector<uint32_t, 4> S;
  BitVector D;
  size_t N = 0;
  bool dense = false;

public:
  bool set(uint32_t f) {
    if (dense) {
      if (f >= D.size()) D.resize(std::max<size_t>(f + 1, D.size() * 2));
      if (D.test(f)) return false;
      D.set(f);
      N++;
      return true;
    }
    auto it = std::lower_bound(S.begin(), S.end(), f);
    if (it != S.end() && *it == f) return false;
    S.insert(it, f);
    N++;
    if (S.size() > 64) {
      D.resize(std::max<uint32_t>(S.back() + 1, 1024));
      for (uint32_t x : S) D.set(x);
      S.clear();
      S = SmallVector<uint32_t, 4>();
      dense = true;
    }
    return true;
  }
  size_t count() const { return N; }
  template <class Fn> void forEach(Fn fn) const {
    if (dense)
      for (unsigned f : D.set_bits()) fn(f);
    else
      for (uint32_t f : S) fn(f);
  }
  bool test(uint32_t f) const {
    if (dense) return f < D.size() && D.test(f);
    return std::binary_search(S.begin(), S.end(), f);
  }
};

// Offsets one folded offset or one strided step may stand for before the
// step yields the object's any-offset cell (counted).
constexpr size_t kExpandCap = 1 << 16;
// A field edge out of a node: its target, label, and for an edge on a
// cycle (a pointer walk) the gcd of the steps around the cycle.
struct FieldEdge {
  uint32_t dst, li;
  int64_t walk; // 0: not on a cycle
};
// A member of a (possibly unified) cell: an object and its offset there.
using Member = std::pair<uint32_t, int64_t>;

enum class CellKind : uint8_t { Func, Off, Any, Out };

struct Cell {
  uint32_t obj;
  CellKind kind;
  int64_t off;     // Off: the folded offset
  uint32_t name;   // Off: interned "label+off" ("+off" unlabeled)
  uint32_t store;  // solver node a store writes (Off, Any)
  uint32_t load;   // solver node a load reads (Off, Any)
  NodeIndex node;  // the factory's cell node
  // Off: an address made by a variable index (some element of the arrays
  // its offset lies in, the offset being element 0's), not an exact one.
  bool folded = false;
};

// A member's offset carries the folded flag in a high bit.
constexpr int64_t kFoldedBit = (int64_t)1 << 62;
inline int64_t encOff(int64_t off, bool folded) {
  return folded ? (off | kFoldedBit) : off;
}
inline int64_t decOff(int64_t e) { return e & ~kFoldedBit; }


struct Obj {
  NodeIndex origin;
  const Function *fn = nullptr;
  Type *layout = nullptr; // null: unlabeled
  bool repeats = false;   // an array of `layout` of unknown length
  // A heap block allocated as sizeof(T) + extra: T followed by trailing
  // data, not an array of T. The trailing data is an object of its own
  // (`(Fts3Table *)&p[1]` starts one), minted on first use: unknown until
  // its first typed use, possibly header+tail itself.
  bool tail = false;
  uint32_t tailObj = UINT32_MAX;  // the trailing object, once used
  uint32_t parentObj = UINT32_MAX; // for a trailing object: the header's
  int64_t base = 0;               // offset in the allocation (trailing objects)
  int64_t size = 0;       // layout's allocation size
  std::string label;
  // Address facts by (offset << 1 | folded), and the content cells (one
  // solver node per folded offset: arrays are one element) they share.
  boost::unordered_flat_map<int64_t, uint32_t> offCells;
  // A content cell is a (write side, read side) pair of solver nodes: one
  // node, except in a keyed union slot (--cfl-union-keys=tag), where the
  // unkeyed writes land in U, a key's reads see U and its own writes (K),
  // and an unkeyed read sees everything (P).
  boost::unordered_flat_map<int64_t, std::pair<uint32_t, uint32_t>> content;
  boost::unordered_flat_map<uint64_t, uint32_t> keyed; // (c, key) -> K
  // Copies out of a keyed union slot (src c -> dst object, dst c): a key
  // made here later is copied to the same key there.
  std::vector<std::tuple<int64_t, uint32_t, int64_t>> copyOut;
  // Learned during the solve: a layout from the first typed access at
  // offset 0 of an unlabeled object.
  bool learnedLayout = false;
  // An unlabeled object is unnamed (its cells named ?#o by raw offset)
  // until its first typed write labels it (plan 3.53, rule 1: bytes is
  // not a label). A variable byte index into it is its any-offset cell.
  // A trailing object folded back into its header when the header became
  // an array (a T-stride access): its addresses are the header's, fwdOff
  // bytes on.
  uint32_t fwd = UINT32_MAX;
  int64_t fwdOff = 0;
  // The trailing object is there because the size said nothing (not
  // because it said T plus data): it never takes a label of its own.
  bool tailUnsized = false;
  // Used as bytes while unlabeled: a variable byte access, or a side of a
  // byte copy (plan 3.53 rule 1 (ii)). Its layout is its first typed use,
  // so a later struct write does not label it: a rule (b) row.
  bool byteAccessed = false;
  // Its debug-info identity, when the linked IR merged its struct away
  // under the layout's name (block_header as struct.my_devt): names its
  // cells; the layout (offsets) stays the IR type's.
  std::string ident;
  // An unlabeled object is an array of unknown element: a variable index
  // of stride s says its element is s bytes (content folds modulo it).
  int64_t period = 0;
  uint32_t func = UINT32_MAX;
  // Its content nodes (by folded offset, for the any and residue cells),
  // its any-offset cell (reads and writes exactly those) and outside cell.
  std::vector<std::tuple<int64_t, uint32_t, uint32_t>> loadNodes; // c, U, P
  uint32_t any = UINT32_MAX, out = UINT32_MAX;
};

// The folded offset of byte `off` inside one instance of T: every array
// element is element 0. Offsets in padding or past T stay as they are.
int64_t foldIn(Type *T, int64_t off, const DataLayout &DL) {
  if (off < 0) return off;
  if (auto *ST = dyn_cast<StructType>(T)) {
    if (ST->isOpaque()) return off;
    const StructLayout *SL = DL.getStructLayout(ST);
    if ((uint64_t)off >= SL->getSizeInBytes()) return off;
    unsigned i = SL->getElementContainingOffset(off);
    int64_t eo = (int64_t)SL->getElementOffset(i);
    Type *E = ST->getElementType(i);
    if (off - eo >= (int64_t)DL.getTypeAllocSize(E)) return off; // padding
    return eo + foldIn(E, off - eo, DL);
  }
  Type *E = nullptr;
  uint64_t n = 0;
  if (auto *AT = dyn_cast<ArrayType>(T)) {
    E = AT->getElementType(); n = AT->getNumElements();
  } else if (auto *VT = dyn_cast<FixedVectorType>(T)) {
    E = VT->getElementType(); n = VT->getNumElements();
  }
  if (E) {
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0 || off >= e * (int64_t)n) return off;
    return foldIn(E, off % e, DL);
  }
  return off;
}

// A byte copy's (source object, destination object, source key,
// destination key) pair, visited once per copied region.
struct SeenKey {
  uint32_t so, dob;
  int64_t sk, dk;
  bool operator==(const SeenKey &o) const {
    return so == o.so && dob == o.dob && sk == o.sk && dk == o.dk;
  }
};
struct SeenKeyHash {
  size_t operator()(const SeenKey &k) const {
    uint64_t h = (uint64_t)k.so * 0x9E3779B97F4A7C15ull ^ k.dob;
    h = (h ^ (uint64_t)k.sk) * 0xBF58476D1CE4E5B9ull;
    return (size_t)((h ^ (uint64_t)k.dk) * 0x94D049BB133111EBull);
  }
};

// Where foldIn's key repeats around byte `off` of one instance of T: the
// outermost array containing it, as (element size, array end); every
// element folds to element 0, so the key is periodic with the element size
// up to the array's end. {0, 0} outside any array.
std::pair<int64_t, int64_t> foldPeriod(Type *T, int64_t off, const DataLayout &DL) {
  int64_t base = 0;
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return {0, 0};
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return {0, 0};
      unsigned i = SL->getElementContainingOffset(off);
      const int64_t eo = (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      if (off - eo >= (int64_t)DL.getTypeAllocSize(T)) return {0, 0}; // padding
      base += eo;
      off -= eo;
      continue;
    }
    Type *E = nullptr;
    uint64_t n = 0;
    if (auto *AT = dyn_cast<ArrayType>(T)) {
      E = AT->getElementType(); n = AT->getNumElements();
    } else if (auto *VT = dyn_cast<FixedVectorType>(T)) {
      E = VT->getElementType(); n = VT->getNumElements();
    }
    if (!E) return {0, 0};
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0 || off >= e * (int64_t)n) return {0, 0};
    return {e, base + e * (int64_t)n};
  }
  return {0, 0};
}

// "function file:line" of an instruction (reports).
std::string instLoc(const Instruction *I) {
  if (!I) return "?";
  std::string s = I->getFunction()->getName().str();
  if (const DILocation *L = I->getDebugLoc())
    s += " " + L->getFilename().str() + ":" + std::to_string(L->getLine());
  return s;
}

// The outermost struct that starts at offset `off` of T (through nested
// members and array elements), or null.
StructType *structAt(Type *T, int64_t off, const DataLayout &DL) {
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return nullptr;
      if (off == 0) return ST;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return nullptr;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return nullptr;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return nullptr;
    off %= e;
    T = E;
  }
  return nullptr;
}

// Does a struct named like S start at offset `off` of T (through nested
// members and array elements)?
bool structStartsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL,
                    const StructType *Same = nullptr) {
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->hasName() && stripStructNameSuffix(ST->getName()) == S)
        return true;
      // Layout-identical types are one type to -O3 (it indexes a
      // TermOffsetCtx as a SnippetIter): the same struct here.
      if (Same && ST != Same && !ST->isOpaque() &&
          ST->isLayoutIdentical(const_cast<StructType *>(Same)))
        return true;
      if (ST->isOpaque()) return false;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return false;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return false;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return false;
    off %= e;
    T = E;
  }
  return false;
}

// Is `off` (folded) the first byte of a scalar member of T?
// The scalar leaf that starts at offset `off` of T (through members and
// array elements), or null.
Type *leafAt(Type *T, int64_t off, const DataLayout &DL) {
  for (int depth = 0; depth < 64 && T; depth++) {
    if (off < 0) return nullptr;
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return nullptr;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return nullptr;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return off == 0 ? T : nullptr;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return nullptr;
    off %= e;
    T = E;
  }
  return nullptr;
}

// diDeclaredStruct, only for a struct the linked IR merged away under
// another name (block_header read as struct.my_devt), else "".
std::string diMergedIdent(const Value *P, bool pointee) {
  const std::string name = diDeclaredStruct(P, pointee);
  if (name.empty()) return "";
  P = P->stripPointerCasts();
  const auto *I = dyn_cast<Instruction>(P);
  const Module *M = I ? I->getModule() : isa<Argument>(P) ? cast<Argument>(P)->getParent()->getParent()
                                                         : cast<GlobalValue>(P)->getParent();
  return StructType::getTypeByName(M->getContext(), name) ? "" : name;
}

// Strip typedefs and qualifiers.
const DIType *diStrip(const DIType *T) {
  for (int i = 0; i < 16 && T; i++) {
    const auto *D = dyn_cast<DIDerivedType>(T);
    if (!D) break;
    const auto tag = D->getTag();
    if (tag != dwarf::DW_TAG_typedef && tag != dwarf::DW_TAG_const_type &&
        tag != dwarf::DW_TAG_volatile_type && tag != dwarf::DW_TAG_restrict_type)
      break;
    T = D->getBaseType();
  }
  return T;
}
// A pointer type's pointee as a key ("char", "Fts3Expr", "ptr", "fn").
std::string diPointeeKey(const DIType *T) {
  T = diStrip(T);
  const auto *D = dyn_cast_or_null<DIDerivedType>(T);
  if (!D || D->getTag() != dwarf::DW_TAG_pointer_type) return "";
  const DIType *P = diStrip(D->getBaseType());
  if (!P) return "char"; // void *: character-like, as char * and u8 *
  if (const auto *Q = dyn_cast<DIDerivedType>(P))
    if (Q->getTag() == dwarf::DW_TAG_pointer_type) return "ptr";
  if (isa<DISubroutineType>(P)) return "fn";
  if (const auto *B = dyn_cast<DIBasicType>(P))
    return B->getSizeInBits() == 8 ? "char"
           : (B->getEncoding() == dwarf::DW_ATE_float ? "f" : "i") +
                 std::to_string(B->getSizeInBits());
  return P->getName().empty() ? "?" : P->getName().str();
}
// The debug type of the member at byte `off` of composite C (through
// embedded structs and array elements).
const DIType *diMemberAt(const DIType *T, uint64_t off) {
  for (int depth = 0; depth < 32 && T; depth++) {
    T = diStrip(T);
    const auto *C = dyn_cast_or_null<DICompositeType>(T);
    if (!C) return off == 0 ? T : nullptr;
    if (C->getTag() == dwarf::DW_TAG_array_type) {
      const DIType *E = diStrip(C->getBaseType());
      const uint64_t es = E ? E->getSizeInBits() / 8 : 0;
      if (!es) return nullptr;
      off %= es;
      T = E;
      continue;
    }
    const DIDerivedType *hit = nullptr;
    for (const DINode *N : C->getElements())
      if (const auto *M = dyn_cast<DIDerivedType>(N))
        if (M->getTag() == dwarf::DW_TAG_member) {
          const uint64_t mo = M->getOffsetInBits() / 8, ms = M->getSizeInBits() / 8;
          if (off >= mo && off < mo + std::max<uint64_t>(ms, 1)) { hit = M; break; }
        }
    if (!hit) return nullptr;
    off -= hit->getOffsetInBits() / 8;
    T = hit->getBaseType();
  }
  return nullptr;
}

bool leafStart(Type *T, int64_t off, const DataLayout &DL) {
  for (int depth = 0; depth < 64; depth++) {
    if (off < 0) return false;
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return off == 0;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return false;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      if (off >= (int64_t)DL.getTypeAllocSize(T)) return false; // padding
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return off == 0;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return off == 0;
    off %= e;
    T = E;
  }
  return false;
}

// Does offset `off` of T lie inside an array of i8 (a char buffer, at any
// nesting)? Its cell is then the byte array i8[], like an untyped buffer.
bool inByteArray(Type *T, int64_t off, const DataLayout &DL) {
  for (int depth = 0; depth < 64 && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return false;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return false;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return false;
    if (E->isIntegerTy(8)) return true;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return false;
    off %= e;
    T = E;
  }
  return false;
}

// Every struct enclosing offset `off` of T, with the offset inside it,
// outermost first: the views a pointer to that address has (a field of an
// embedded struct is that struct's field; offset 0 of a struct is the
// struct itself, and its first member).
void structChain(Type *T, int64_t off, const DataLayout &DL,
                 std::vector<std::string> &out) {
  out.clear();
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->hasName())
        out.push_back(stripStructNameSuffix(ST->getName()).str() + "+" +
                      std::to_string(off));
      if (ST->isOpaque()) return;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return;
    off %= e;
    T = E;
  }
}

// Is offset `off` of T inside an array (at any depth) whose element is
// `esz` bytes?
bool inArrayOfSize(Type *T, int64_t off, int64_t esz, const DataLayout &DL) {
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) return false;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) return false;
      unsigned i = SL->getElementContainingOffset(off);
      off -= (int64_t)SL->getElementOffset(i);
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) return false;
    const int64_t e = (int64_t)DL.getTypeAllocSize(E);
    if (e == 0) return false;
    if (e == esz) return true;
    off %= e;
    T = E;
  }
  return false;
}

// The element of the innermost array holding offset `off` of T: its start
// (absolute) and size. False when `off` lies in no array.
bool innermostArray(Type *T, int64_t off, const DataLayout &DL, int64_t &b,
                    int64_t &e) {
  bool found = false;
  int64_t base = 0;
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) break;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) break;
      unsigned i = SL->getElementContainingOffset(off);
      const int64_t eo = (int64_t)SL->getElementOffset(i);
      base += eo;
      off -= eo;
      T = ST->getElementType(i);
      continue;
    }
    Type *E = nullptr;
    if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
    else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
    if (!E) break;
    const int64_t esz = (int64_t)DL.getTypeAllocSize(E);
    if (esz == 0) break;
    found = true;
    b = base + (off / esz) * esz;
    e = esz;
    base = b;
    off %= esz;
    T = E;
  }
  return found;
}

// The innermost array holding offset `off` of T: its span [lo, hi)
// (absolute) and element size. False when `off` lies in no array.
bool innermostArraySpan(Type *T, int64_t off, const DataLayout &DL, int64_t &lo,
                        int64_t &hi, int64_t &esz) {
  bool found = false;
  int64_t base = 0;
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (ST->isOpaque()) break;
      const StructLayout *SL = DL.getStructLayout(ST);
      if ((uint64_t)off >= SL->getSizeInBytes()) break;
      unsigned i = SL->getElementContainingOffset(off);
      const int64_t eo = (int64_t)SL->getElementOffset(i);
      base += eo;
      off -= eo;
      T = ST->getElementType(i);
      continue;
    }
    auto *AT = dyn_cast<ArrayType>(T);
    if (!AT) break;
    const int64_t e = (int64_t)DL.getTypeAllocSize(AT->getElementType());
    if (e == 0) break;
    found = true;
    lo = base;
    hi = base + (int64_t)AT->getNumElements() * e;
    esz = e;
    base += (off / e) * e;
    off %= e;
    T = AT->getElementType();
  }
  return found;
}

// An allocation size's source: through casts, and at -O0 a local slot that
// never escapes (its only users are direct loads and exactly one store: no
// call can write it through its address) forwards the stored value
// (sqlite3: nByte = sizeof(Fts3SegReader) + (nElem+1)*sizeof(Fts3HashElem
// *); malloc(nByte)).
const Value *sizeThrough(const Value *V) {
  for (int d = 0; d < 8; d++) {
    if (const auto *CI = dyn_cast<CastInst>(V)) { V = CI->getOperand(0); continue; }
    if (const auto *L = dyn_cast<LoadInst>(V))
      if (const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
        const StoreInst *only = nullptr;
        bool ok = true, several = false;
        for (const User *U : S->users()) {
          if (isa<LoadInst>(U)) continue;
          const auto *SI = dyn_cast<StoreInst>(U);
          if (!SI || SI->getPointerOperand() != S || SI->getValueOperand() == S) {
            ok = false;
            break;
          }
          several |= only != nullptr;
          only = SI;
        }
        if (ok && only && !several) { V = only->getValueOperand(); continue; }
        // A slot stored several times (fts3InitVtab reuses nByte): the
        // store before the load in its block reaches it.
        if (ok && several) {
          const StoreInst *last = nullptr;
          for (const Instruction *I = L->getPrevNode(); I && !last; I = I->getPrevNode())
            if (const auto *SI = dyn_cast<StoreInst>(I))
              if (SI->getPointerOperand() == S) last = SI;
          if (last) { V = last->getValueOperand(); continue; }
        }
      }
    break;
  }
  return V;
}

// Is size expression X a multiple of sz: a constant multiple (nonzero: a
// size, not a flag), or a product (or shift) with one?
bool isMultipleOf(const Value *X, uint64_t sz, bool nonzero = false) {
  X = sizeThrough(X);
  if (const auto *B = dyn_cast<BinaryOperator>(X)) {
    if (B->getOpcode() == Instruction::Mul)
      for (const Value *Op : B->operands())
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(Op)))
          return (!nonzero || K->getZExtValue()) && K->getZExtValue() % sz == 0;
    if (B->getOpcode() == Instruction::Shl)
      if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(B->getOperand(1))))
        return K->getZExtValue() < 63 && (1ULL << K->getZExtValue()) % sz == 0;
  }
  if (const auto *K = dyn_cast<ConstantInt>(X))
    return (!nonzero || K->getZExtValue()) && K->getZExtValue() % sz == 0;
  return false;
}

// Does an allocation call's size argument say "a T followed by trailing
// data": a constant larger than T and not a multiple of it, or a sum (any
// depth: -O3 chains `sizeof(T) + 8*n + 40*m + k`) with a constant term of
// at least sizeof(T) and some other term that is not a multiple of it
// (`n*sizeof(T) + sizeof(T)` is an array of n+1)?
bool headerPlusTail(const CallBase *C, uint64_t sz) {
  auto lookThrough = sizeThrough;
  auto multipleOf = [&](const Value *X) { return isMultipleOf(X, sz); };
  for (const Use &A : C->args()) {
    const Value *V = lookThrough(A.get());
    if (!V->getType()->isIntegerTy()) continue;
    if (const auto *K = dyn_cast<ConstantInt>(V)) {
      const uint64_t k = K->getZExtValue();
      if (k > sz && k % sz != 0) return true;
      continue;
    }
    std::vector<const Value *> terms, work{V};
    while (!work.empty() && terms.size() < 32) {
      const Value *X = lookThrough(work.back());
      work.pop_back();
      const auto *B = dyn_cast<BinaryOperator>(X);
      if (B && B->getOpcode() == Instruction::Add) {
        work.push_back(B->getOperand(0));
        work.push_back(B->getOperand(1));
      } else {
        terms.push_back(X);
      }
    }
    if (terms.size() < 2) continue;
    bool header = false, other = false;
    for (const Value *T : terms) {
      const auto *K = dyn_cast<ConstantInt>(T);
      // A constant term is a header size only when it is positive: the -O3
      // sum `nsymz * 16 + (len - 8 * nsymz - 8) + 1` carries -8, which read
      // unsigned (2^64 - 8) was "a header" at every offset.
      if (K && !K->isNegative() && K->getZExtValue() >= sz) header = true;
      else if (!multipleOf(T)) other = true;
    }
    if (header && other) return true;
  }
  return false;
}

// Does an allocation call allocate exactly sz bytes (its integer
// arguments all constants, multiplying to sz: malloc(64), calloc(1, 64))?
// Then it is one T, not an array of T.
bool exactlyOne(const CallBase *C, uint64_t sz) {
  uint64_t prod = 1;
  bool any = false;
  for (const Use &A : C->args()) {
    const Value *V = A.get();
    while (const auto *CI = dyn_cast<CastInst>(V)) V = CI->getOperand(0);
    if (!V->getType()->isIntegerTy()) continue;
    const auto *K = dyn_cast<ConstantInt>(V);
    if (!K) return false;
    prod *= K->getZExtValue();
    any = true;
  }
  return any && prod == sz;
}

// Does an allocation call's size say "an array of T": an integer argument
// that is a multiple of sizeof(T) (calloc(n, sizeof T), malloc(n * sizeof
// T), realloc(p, k * sizeof T))?
bool sizeIsMultiple(const CallBase *C, uint64_t sz) {
  for (const Use &A : C->args())
    if (A.get()->getType()->isIntegerTy() && isMultipleOf(A.get(), sz, true)) return true;
  return false;
}

std::string typeLabel(Type *T) {
  while (auto *AT = dyn_cast<ArrayType>(T)) T = AT->getElementType();
  if (auto *ST = dyn_cast<StructType>(T))
    if (ST->hasName()) return stripStructNameSuffix(ST->getName()).str();
  std::string s;
  raw_string_ostream os(s);
  T->print(os);
  return os.str();
}

} // namespace

bool CallGraphPass::runCellResolution() {
  using Clock = std::chrono::steady_clock;
  const auto t0 = Clock::now();
  const DataLayout &DL = Ctx->Modules.front().first->getDataLayout();

  // The kernel's answer-level channels (static_call tables, tracepoint
  // keys) live in the cluster solver's resolution; refuse their inputs.
  for (const CallBase *CS : Ctx->IndirectCallInsts)
    if (const Function *CF = CS->getCalledFunction())
      assert(!CF->getName().starts_with("__SCT__") &&
             !CF->getName().starts_with("__traceiter_") &&
             "--cfl-cells does not model static_call or tracepoint dispatch");

  // ---- Solver nodes: graph nodes keep their factory index; cells and
  // store collectors are numbered after them. ----
  const uint32_t G = NF.getNumNodes();
  uint32_t numNodes = G;
  std::vector<Facts> pts;
  std::vector<std::vector<uint32_t>> pend; // added, not yet propagated
  std::vector<std::vector<uint32_t>> succ;
  std::vector<char> inWL;
  // Copy cycles collapse into one solver node (mutual flow: equal sets,
  // so the merge loses nothing; cells stay distinct facts). The
  // representative inherits every constraint of its members.
  std::vector<uint32_t> repOf;
  std::vector<std::vector<uint32_t>> hubsOf; // pointer -> its hubs
  std::vector<std::vector<FieldEdge>> fieldOut;
  std::vector<char> anyLoop;
  // Per node: the fact it holds under each name (unification by name).
  std::vector<boost::unordered_flat_map<uint32_t, uint32_t>> byName;
  // --cfl-cell-one-label: the one (merged) cell a node points to.
  std::vector<uint32_t> oneCell;
  std::vector<std::vector<uint32_t>> copiesAt; // byte copies a node is in
  std::vector<char> unionView; // a union slot's U or P: holds every member
  auto grow = [&](uint32_t n) {
    if (n <= pts.size()) return;
    size_t cap = std::max<size_t>(n, pts.size() * 3 / 2);
    const size_t old = repOf.size();
    pts.resize(cap); pend.resize(cap); succ.resize(cap); inWL.resize(cap, 0);
    hubsOf.resize(cap); fieldOut.resize(cap); anyLoop.resize(cap, 0);
    byName.resize(cap);
    oneCell.resize(cap, UINT32_MAX);
    copiesAt.resize(cap);
    unionView.resize(cap, 0);
    repOf.resize(cap);
    for (size_t i = old; i < cap; i++) repOf[i] = i;
  };
  grow(G);
  auto find = [&](uint32_t n) {
    while (repOf[n] != n) n = repOf[n] = repOf[repOf[n]];
    return n;
  };
  auto newNode = [&]() { grow(numNodes + 1); return numNodes++; };
  std::vector<uint32_t> worklist;
  auto push = [&](uint32_t n) {
    if (!inWL[n]) { inWL[n] = 1; worklist.push_back(n); }
  };
  std::function<uint32_t(uint32_t)> canonFact; // the fact union-find
  // --cfl-cell-why: the first cause of each (node, fact) arrival and of
  // each dynamic edge. node/fact: where the fact came from (EDGE: the
  // edge's source; STEP/WALK/ANY/HUB: the pointer and its fact); COPY:
  // node = the byte copy, fact = its source cell, extra = its destination
  // cell.
  enum WhyKind : uint8_t { W_OTHER, W_EDGE, W_STEP, W_WALK, W_ANY, W_HUB, W_COPY, W_DISPATCH };
  struct Why { uint32_t node = UINT32_MAX, fact = UINT32_MAX, extra = UINT32_MAX;
               WhyKind kind = W_OTHER; uint32_t t = 0; };
  uint32_t whyClock = 0; // pops, for the order of first arrivals
  const bool recordWhy = !CFLCellWhy.empty();
  // Causes are tracked (curWhy) for --cfl-cell-why and the soup profiler;
  // only --cfl-cell-why records them per fact.
  const bool trackWhy = recordWhy || CFLCellSoupProfile;
  std::function<void(uint32_t, uint32_t)> soupArrive; // set once cells exist
  // --cfl-cell-leak-census: the arrival hook and the merge hook (a merged
  // node keeps its members' leaks); set once cells exist.
  std::function<void(uint32_t, uint32_t)> leakArrive, leakMerge;
  std::function<void(uint32_t)> leakRefold; // an object's cells were renamed
  if (CFLCellLeakCensus && !CFLCellSoupProfile) {
    errs() << "Cells: --cfl-cell-leak-census reports at the soup profiler's stop "
           << "point; it needs --cfl-cell-soup-profile\n";
    exit(1);
  }
  bool soupStop = false;
  const bool whyStopAtAny = StringRef(CFLCellWhy).starts_with("any:");
  bool whyAnyArrived = false;
  std::function<bool(uint32_t)> whyIsAny = [](uint32_t) { return false; }; // set once cells exist
  // Only facts of the queried object are recorded (an exploding iteration
  // has far too many facts to record them all); set once objs exist.
  std::function<bool(uint32_t)> whyWanted = [](uint32_t) { return true; };
  Why curWhy;
  boost::unordered_flat_map<uint64_t, Why> factWhy, edgeWhy;
  // --cfl-cell-receivers holder guards: a guarded node's facts are held
  // until admitted (guardHold); guardIdx[n] = the guard, UINT32_MAX none.
  std::vector<uint32_t> guardIdx;
  bool admitting = false;
  std::function<void(uint32_t, uint32_t, uint32_t)> guardHold;
  auto add = [&](uint32_t n, uint32_t f) {
    n = find(n);
    if (canonFact) f = canonFact(f);
    if (n < guardIdx.size() && guardIdx[n] != UINT32_MAX && !admitting) {
      guardHold(guardIdx[n], n, f);
      return;
    }
    if (pts[n].set(f)) {
      if (soupArrive) soupArrive(n, f);
      if (leakArrive) leakArrive(n, f);
      if (recordWhy && whyWanted(f)) {
        Why w = curWhy;
        w.t = whyClock;
        factWhy.try_emplace((uint64_t)n << 32 | f, w);
        // any:OBJ: stop at the first arrival of OBJ's any-offset cell.
        if (whyStopAtAny && whyIsAny(f)) whyAnyArrived = true;
      }
      pend[n].push_back(f);
      push(n);
    }
  };
  boost::unordered_flat_set<uint64_t> edgeSet;
  size_t dynEdges = 0;
  auto addEdge = [&](uint32_t a, uint32_t b) {
    a = find(a);
    b = find(b);
    if (a == b || !edgeSet.insert((uint64_t)a << 32 | b).second) return;
    succ[a].push_back(b);
    if (!trackWhy) {
      pts[a].forEach([&](uint32_t f) { add(b, f); });
      return;
    }
    // A byte copy's content edges are not recorded (a copy makes millions
    // of edges); the chain names them "static copy or byte copy".
    if (recordWhy && curWhy.kind != W_COPY) edgeWhy.try_emplace((uint64_t)a << 32 | b, curWhy);
    const Why saved = curWhy;
    pts[a].forEach([&](uint32_t f) {
      curWhy = {a, f, UINT32_MAX, W_EDGE};
      add(b, f);
    });
    curWhy = saved;
  };

  // ---- Static constraints ----
  auto canon = [&](NodeIndex n) -> uint32_t {
    uint32_t c = getCanonicalNode(n);
    assert(c < G && "edge endpoint created after the solve began");
    return c;
  };
  // ---- Method entries (plan 3.54) ----
  // A method formal whose reads are keyed by its entry test is split:
  // every entry other than a test dispatch (the static edges: direct
  // calls and wired call sites; a dispatch through any other site)
  // arrives at its other-entry node Ao, which feeds the formal. An object
  // that ever arrives at Ao is "other": the formal's entry-keyed reads
  // also read it unkeyed (the read's entry hub); an object that entered
  // only through test dispatches is read through the admitted keys alone.
  struct EntryF {
    uint32_t A = UINT32_MAX, Ao = UINT32_MAX;
    bool poisoned = false; // every object reads unkeyed (no split, or merged)
    std::string why;
    boost::unordered_flat_set<uint32_t> other; // objects that entered other than by a test
    // Plan 3.54 (b): object -> the terms it entered with (formal indices:
    // a test entry of this formal is its own index; a channel brings the
    // caller's terms), and the formals it was passed on to.
    boost::unordered_flat_map<uint32_t, std::vector<uint32_t>> terms, subs;
    // object -> (entry hub, fact, read) where its cells are read: linked
    // per term it gains, and unkeyed once it enters otherwise.
    boost::unordered_flat_map<uint32_t, std::vector<std::array<uint32_t, 3>>> held;
    size_t testEntries = 0, otherEntries = 0, chanEntries = 0, flushed = 0, termLinks = 0;
  };
  std::vector<EntryF> entryF(taggedEntryFormals.size());
  boost::unordered_flat_map<uint32_t, uint32_t> entryOfA, entryOfAo;
  boost::unordered_flat_map<uint32_t, uint32_t> entryOfKey; // hub key -> entry read (taggedEntryReadList)
  for (uint32_t j = 0; j < taggedEntryReadList.size(); j++)
    entryOfKey[NF.internCellName(taggedEntryHubKey(taggedEntryReadList[j]))] = j;
  std::function<void(uint32_t, const std::string &)> entryPoison;
  std::function<void(uint32_t, uint32_t)> entryOtherFn, entryTestFn;
  std::function<void(uint32_t, uint32_t)> entryMergedFn;
  std::function<void(uint32_t, uint32_t, uint32_t)> chanArriveFn;
  std::function<void(uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t)> termLinkFn;
  for (uint32_t fi = 0; fi < entryF.size(); fi++) {
    const auto &E = taggedEntryFormals[fi];
    EntryF &ef = entryF[fi];
    const NodeIndex fv = NF.getValueNodeFor(E.M->getArg(E.k));
    if (fv == AndersNodeFactory::InvalidIndex) {
      ef.poisoned = true;
      ef.why = "the formal has no node";
      continue;
    }
    const uint32_t A = canon(fv);
    if (auto it = entryOfA.find(A); it != entryOfA.end()) {
      ef.poisoned = entryF[it->second].poisoned = true;
      ef.why = entryF[it->second].why = "the formal shares its node with another method's formal";
      continue;
    }
    ef.A = A;
    ef.Ao = newNode();
    entryOfA[A] = fi;
    entryOfAo[ef.Ao] = fi;
  }
  // Until the solve's hubs exist nothing waits: poisoning is the flag
  // (reassigned with the flush below).
  entryPoison = [&](uint32_t fi, const std::string &why) {
    if (!entryF[fi].poisoned) entryF[fi].poisoned = true, entryF[fi].why = why;
  };
  // Plan 3.54 (b): a channel (caller formal X -> callee formal Y) is a node
  // feeding Y's formal; objects arriving there take X's state for them.
  // A call's argument k into Y is a channel when the call passes X's
  // object on (taggedEntryChannels) with every F Y's reads read unwritten.
  boost::unordered_flat_map<uint64_t, uint32_t> chanNodeOf;               // (X, Y) -> node
  // A static channel's source (a call argument's node, by its current
  // representative) -> the channel nodes its pops feed.
  boost::unordered_flat_map<uint32_t, std::vector<uint32_t>> chanFrom;
  boost::unordered_flat_map<uint32_t, std::pair<uint32_t, uint32_t>> chanOfNode; // node -> (X, Y)
  auto chanNode = [&](uint32_t fx, uint32_t fy) {
    auto [it, ins] = chanNodeOf.try_emplace((uint64_t)fx << 32 | fy, 0);
    if (ins) {
      it->second = newNode();
      chanOfNode[it->second] = {fx, fy};
      addEdge(it->second, entryF[fy].A);
    }
    return it->second;
  };
  auto chanValid = [&](const TaggedChannel &ch, uint32_t fy) {
    const auto &EX = taggedEntryFormals[ch.from], &EY = taggedEntryFormals[fy];
    if (EX.S != EY.S || entryF[ch.from].A == UINT32_MAX) return false;
    for (int64_t F : EY.Fs)
      if (!ch.Fs.count(F)) return false;
    return true;
  };
  auto chanFor = [&](const CallBase *CS, unsigned k, uint32_t fy) -> int64_t {
    if (!CS) return -1;
    auto cit = taggedEntryChannels.find(CS);
    if (cit == taggedEntryChannels.end()) return -1;
    for (const TaggedChannel &ch : cit->second)
      if (ch.k == k && chanValid(ch, fy)) return ch.from;
    return -1;
  };
  // A static edge's source as a call argument: its channel, if every call
  // argument with that node is one (from one caller formal), else none.
  struct ActualChan { int64_t fx = -1; std::vector<const TaggedChannel *> chs; bool mixed = false; };
  boost::unordered_flat_map<uint32_t, ActualChan> actualChan;
  if (!entryF.empty() && !taggedEntryChannels.empty())
    for (auto &[M, _] : Ctx->Modules)
      for (Function &Fn : *M)
        for (Instruction &I : instructions(Fn)) {
          const auto *CS = dyn_cast<CallBase>(&I);
          if (!CS || isa<IntrinsicInst>(CS)) continue;
          auto cit = taggedEntryChannels.find(CS);
          for (unsigned k = 0; k < CS->arg_size(); k++) {
            // A constant is never a channel's actual (that is the receiver's
            // identity, a load or an argument), and its node, with no copy
            // edge into it, shares no class with one; asking the factory for
            // it could mint a node after the graph was fixed.
            if (!CS->getArgOperand(k)->getType()->isPointerTy() || isa<Constant>(CS->getArgOperand(k))) continue;
            const NodeIndex vn = NF.getValueNodeFor(CS->getArgOperand(k));
            if (vn == AndersNodeFactory::InvalidIndex) continue;
            ActualChan &ac = actualChan[canon(vn)];
            const TaggedChannel *ch = nullptr;
            if (cit != taggedEntryChannels.end())
              for (const TaggedChannel &c : cit->second)
                if (c.k == k) ch = &c;
            if (!ch || (ac.fx >= 0 && ac.fx != (int64_t)ch->from)) { ac.mixed = true; continue; }
            ac.fx = ch->from;
            ac.chs.push_back(ch);
          }
        }
  auto staticChan = [&](uint32_t a, uint32_t fy) -> int64_t {
    auto it = actualChan.find(a);
    if (it == actualChan.end() || it->second.mixed || it->second.fx < 0) return -1;
    for (const TaggedChannel *ch : it->second.chs)
      if (!chanValid(*ch, fy)) return -1;
    return it->second.fx;
  };
  std::vector<char> isHub(G, 0), inGraph(G, 0);
  size_t graphFieldEdges = 0;
  for (const GraphEdge &E : Graph.edges())
    if (E.kind == EdgeKind::Deref) {
      const uint32_t p = canon(E.from), h = canon(E.to);
      inGraph[p] = inGraph[h] = 1;
      if (std::find(hubsOf[p].begin(), hubsOf[p].end(), h) == hubsOf[p].end())
        hubsOf[p].push_back(h);
      isHub[h] = 1;
    }
  std::vector<uint32_t> storeHub(G, UINT32_MAX);
  size_t staticCopies = 0, stores = 0;
  // Leak census: a store collector's hub and the value nodes stored.
  boost::unordered_flat_map<uint32_t, uint32_t> leakCollHub;
  boost::unordered_flat_map<uint32_t, std::vector<uint32_t>> leakCollIn;
  // Leak census: the IR stores each store collector stands for (indexed
  // before any merge), and the load results a hub feeds (factory nodes, before
  // presolve merged them).
  boost::unordered_flat_map<uint32_t, std::vector<NodeIndex>> leakHubLoads;
  boost::unordered_flat_map<uint32_t, std::vector<const StoreInst *>> leakCollStores;
  for (const GraphEdge &E : Graph.edges()) {
    switch (E.kind) {
    case EdgeKind::Copy: {
      const uint32_t a = canon(E.from), b = canon(E.to);
      inGraph[a] = inGraph[b] = 1;
      if (isHub[b]) { // a store: into the cells the hub's pointers hold
        if (storeHub[b] == UINT32_MAX) storeHub[b] = newNode();
        addEdge(a, storeHub[b]);
        if (CFLCellLeakCensus) {
          leakCollHub.try_emplace(storeHub[b], b);
          leakCollIn[storeHub[b]].push_back(a);
        }
        stores++;
      } else {
        uint32_t to = b;
        bool hooked = false;
        if (!entryOfA.empty())
          if (auto eit = entryOfA.find(b); eit != entryOfA.end()) { // plan 3.54
            const int64_t fx = staticChan(a, eit->second);
            if (fx < 0)
              to = entryF[eit->second].Ao;
            else {
              // A channel (3.54 (b)): a transfer the pops of a make, not a
              // copy edge, so channels close no cycle for the collapse to
              // merge; into the caller's own formal, nothing (the argument
              // is the formal's own value: its facts are there).
              hooked = true;
              if ((uint32_t)fx != eit->second) {
                const uint32_t cn = chanNode((uint32_t)fx, eit->second);
                auto &v = chanFrom[a];
                if (std::find(v.begin(), v.end(), cn) == v.end()) v.push_back(cn);
              }
            }
          }
        if (!hooked) addEdge(a, to);
        if (CFLCellLeakCensus && isHub[a]) leakHubLoads[a].push_back(E.to);
        staticCopies++;
      }
      break;
    }
    case EdgeKind::FieldAny:
      assert(canon(E.from) == canon(E.to) && "field-any edges are loops");
      anyLoop[canon(E.from)] = 1;
      inGraph[canon(E.from)] = 1;
      break;
    case EdgeKind::Field:
      graphFieldEdges++;
      break;
    case EdgeKind::Deref:
      break;
    }
  }
  assert(graphFieldEdges == lazyFEdges.size() &&
         "every field edge carries an exact label");
  for (EntryF &ef : entryF)
    if (ef.Ao != UINT32_MAX) addEdge(ef.Ao, ef.A);
  // Static edges as inserted (staticCopies and stores count attempts,
  // self-loops and duplicates included).
  const size_t staticEdges = edgeSet.size();
  struct ByteCopy { uint32_t src, dst; int64_t len; const Instruction *at; };
  std::vector<ByteCopy> copies;
  for (auto &[sN, dN, len, at] : byteCopies) {
    const uint32_t a = canon(sN), b = canon(dN);
    inGraph[a] = inGraph[b] = 1;
    copiesAt[a].push_back(copies.size());
    if (b != a) copiesAt[b].push_back(copies.size());
    copies.push_back({a, b, len, at});
  }
  for (auto &[f, t, li] : lazyFEdges) {
    const uint32_t a = canon(f), b = canon(t);
    inGraph[a] = inGraph[b] = 1;
    assert(!isHub[b] && "a field address is never a dereference");
    if (a != b || lazyLabels[li].off != 0 || lazyLabels[li].stride != 0)
      fieldOut[a].push_back({b, li, 0});
  }

  // Watched stores (plan 3.51 ruling B): by the solver node of the store's
  // root pointer; a fact landing there is checked against the keyed tags
  // its write covers (watchCheck, set once objects exist). Facts on an
  // object not yet typed wait for its layout (watchPending).
  boost::unordered_flat_map<uint32_t, std::vector<uint32_t>> watchAt;
  boost::unordered_flat_map<uint32_t, std::vector<std::pair<uint32_t, uint32_t>>> watchPending;
  boost::unordered_flat_set<uint64_t> watchSeen;
  // Keyed accesses (--cfl-union-keys=tag) through an object not yet
  // labeled wait for its label (whether the cell is a keyed slot is the
  // label's to say): (hub, fact) by object. Linked keyed once it is
  // labeled; at the fixpoint, those still waiting link unkeyed and the
  // solve goes on.
  boost::unordered_flat_map<uint32_t, std::vector<std::pair<uint32_t, uint32_t>>> keyedWait;
  std::function<void(uint32_t, uint32_t)> linkHubFn; // set once linkHub exists
  size_t keyedWaits = 0, keyedFlushed = 0;
  std::function<void(uint32_t, uint32_t)> watchCheck;
  // Alias assumptions (plan 3.51): an entry on a node is the identity side
  // of assumption idx (off: the field) or an access of access set idx
  // (off: its constant offset, var: unknown).
  struct AsmEntry { uint32_t idx; bool idSide; int64_t off; bool var; uint32_t acc = UINT32_MAX; };
  boost::unordered_flat_map<uint32_t, std::vector<AsmEntry>> asmAt;
  std::function<void(const AsmEntry &, uint32_t)> asmCheck;
  // Merging solver nodes: the representative inherits every constraint
  // and re-propagates every fact (members brought facts the others'
  // successors and constraints have not seen).
  auto absorb = [&](uint32_t r, uint32_t m) {
    if (!entryOfA.empty()) // plan 3.54: a split node merged with another: no split
      for (uint32_t x : {r, m}) {
        if (auto it = entryOfA.find(x); it != entryOfA.end()) entryPoison(it->second, "the formal merged in a cycle");
        if (auto it = entryOfAo.find(x); it != entryOfAo.end()) entryPoison(it->second, "the formal merged in a cycle");
        if (auto it = chanOfNode.find(x); it != chanOfNode.end())
          entryPoison(it->second.second, "a channel into the formal merged in a cycle");
      }
    if (!chanFrom.empty()) // plan 3.54 (b): a channel source merged: the class feeds its channels
      if (auto it = chanFrom.find(m); it != chanFrom.end()) {
        std::vector<uint32_t> cs = std::move(it->second);
        chanFrom.erase(it);
        auto &v = chanFrom[r];
        for (uint32_t cn : cs)
          if (std::find(v.begin(), v.end(), cn) == v.end()) v.push_back(cn);
        // (finalize re-pends every fact of r: its next pop sends them all)
      }
    repOf[m] = r;
    if (leakMerge) leakMerge(r, m);
    if (!asmAt.empty())
      if (auto ait = asmAt.find(m); ait != asmAt.end()) {
        std::vector<AsmEntry> es = std::move(ait->second);
        asmAt.erase(ait);
        auto &ra = asmAt[r];
        ra.insert(ra.end(), es.begin(), es.end());
      }
    if (!watchAt.empty())
      if (auto wit = watchAt.find(m); wit != watchAt.end()) {
        std::vector<uint32_t> ws = std::move(wit->second);
        watchAt.erase(wit);
        auto &rw = watchAt[r];
        rw.insert(rw.end(), ws.begin(), ws.end());
      }
    pts[m].forEach([&](uint32_t f) { pts[r].set(f); });
    pts[m] = Facts();
    pend[m].clear();
    succ[r].insert(succ[r].end(), succ[m].begin(), succ[m].end());
    succ[m].clear();
    hubsOf[r].insert(hubsOf[r].end(), hubsOf[m].begin(), hubsOf[m].end());
    hubsOf[m].clear();
    fieldOut[r].insert(fieldOut[r].end(), fieldOut[m].begin(),
                       fieldOut[m].end());
    fieldOut[m].clear();
    anyLoop[r] |= anyLoop[m];
    byName[m] = {}; // the rep re-runs every fact (finalize)
    copiesAt[r].insert(copiesAt[r].end(), copiesAt[m].begin(), copiesAt[m].end());
    copiesAt[m].clear();
    oneCell[m] = UINT32_MAX;
  };
  size_t finalizes = 0, refacts = 0;
  auto finalize = [&](uint32_t r) {
    finalizes++;
    refacts += pts[r].count();
    std::vector<uint32_t> &S = succ[r];
    for (uint32_t &v : S) v = find(v);
    std::sort(S.begin(), S.end());
    S.erase(std::unique(S.begin(), S.end()), S.end());
    S.erase(std::remove(S.begin(), S.end(), r), S.end());
    for (uint32_t v : S) edgeSet.insert((uint64_t)r << 32 | v);
    pend[r].clear();
    pts[r].forEach([&](uint32_t f) { pend[r].push_back(f); });
    if (!pend[r].empty()) push(r);
  };
  auto mergeNodes = [&](uint32_t a, uint32_t b) {
    a = find(a);
    b = find(b);
    if (a == b) return;
    if (b < a) std::swap(a, b);
    absorb(a, b);
    finalize(a);
  };

  // Collapse the copy cycles of the current graph (static edges and the
  // hub edges added so far).
  size_t collapses = 0, collapsedNodes = 0, walkEdges = 0;
  double collapseSecs = 0;
  std::vector<std::vector<uint32_t>> bigCycles; // the largest per collapse (report)
  // Edges inside each big cycle, recorded before the merge erases them.
  std::vector<std::vector<std::pair<uint32_t, uint32_t>>> bigCycleEdges;
  // Cycles with offset (plan 3.49; Pearce's positive-weight cycles): the
  // copy+field SCCs whose steps have a nonzero gcd (pointer walks).
  struct PwcComp { size_t size = 0, typed = 0, untyped = 0; bool cls = false; int64_t g = 0; uint32_t rep = 0; };
  std::vector<PwcComp> pwcComps;
  std::vector<uint8_t> inPwc;
  auto collapseCycles = [&]() {
    const auto tc = Clock::now();
    collapses++;
    std::vector<std::vector<uint32_t>> sccs;
    ka::tarjanSCC(
        numNodes, [&](uint32_t u) { return find(u) != u; },
        [&](uint32_t u) { return succ[u].size(); },
        [&](uint32_t u, size_t i) -> uint32_t {
          const uint32_t v = find(succ[u][i]);
          return v == u ? ka::kNoNode : v;
        },
        [&](const std::vector<uint32_t> &members) {
          if (members.size() > 1) sccs.push_back(members);
        });
    if (VerboseLevel >= 2 && !sccs.empty()) {
      auto big = std::max_element(sccs.begin(), sccs.end(), [](auto &a, auto &b) {
        return a.size() < b.size();
      });
      if (big->size() >= 50) {
        bigCycles.push_back(*big);
        std::set<uint32_t> in(big->begin(), big->end());
        std::vector<std::pair<uint32_t, uint32_t>> es;
        for (uint32_t m : *big)
          for (uint32_t v : succ[m])
            if (in.count(find(v)) && find(v) != m) es.push_back({m, find(v)});
        bigCycleEdges.push_back(std::move(es));
      }
    }
    for (auto &M : sccs) {
      const uint32_t r = *std::min_element(M.begin(), M.end());
      for (uint32_t m : M)
        if (m != r && find(m) == m) {
          absorb(find(r), m);
          collapsedNodes++;
        }
    }
    for (auto &M : sccs) finalize(find(M[0]));
    {
      // Field edges on a cycle (copy and field edges together) are
      // pointer walks: a step along one yields the object's any-offset
      // cell (the walk reaches every offset) instead of one address per
      // turn. Flagged in the label's top bit.
      std::vector<uint32_t> comp(numNodes, UINT32_MAX), compSize;
      uint32_t nc = 0;
      ka::tarjanSCC(
          numNodes, [&](uint32_t u) { return find(u) != u; },
          [&](uint32_t u) { return succ[u].size() + fieldOut[u].size(); },
          [&](uint32_t u, size_t i) -> uint32_t {
            const uint32_t v = i < succ[u].size()
                                   ? find(succ[u][i])
                                   : find(fieldOut[u][i - succ[u].size()].dst);
            return v == u ? ka::kNoNode : v;
          },
          [&](const std::vector<uint32_t> &members) {
            for (uint32_t w : members) comp[w] = nc;
            compSize.push_back(members.size());
            nc++;
          });
      std::map<std::string, size_t> walk;
      size_t onCycle = 0, selfLoops = 0;
      // The steps around a cycle reach offsets congruent modulo the gcd
      // of all of them.
      std::vector<int64_t> compGcd(nc, 0);
      auto stepOf = [&](const LazyLabel &L) -> int64_t {
        const int64_t o = L.off < 0 ? -L.off : L.off;
        return L.stride ? std::gcd((int64_t)L.stride, o) : o;
      };
      for (uint32_t u = 0; u < numNodes; u++) {
        if (find(u) != u) continue;
        for (FieldEdge &e : fieldOut[u]) {
          const uint32_t v = find(e.dst);
          if (v != u && comp[v] != comp[u]) continue;
          compGcd[comp[u]] = std::gcd(compGcd[comp[u]], stepOf(lazyLabels[e.li]));
        }
      }
      std::map<uint32_t, PwcComp> pwcBy;
      for (uint32_t u = 0; u < numNodes; u++) {
        if (find(u) != u) continue;
        for (FieldEdge &e : fieldOut[u]) {
          const uint32_t v = find(e.dst);
          if (v != u && comp[v] != comp[u]) continue;
          const int64_t g = compGcd[comp[u]];
          if (g == 0) continue; // offset-free cycle
          e.walk = g;
          onCycle++;
          selfLoops += v == u;
          walk["step " + std::to_string(g)]++;
          PwcComp &P = pwcBy[comp[u]];
          P.size = compSize[comp[u]];
          P.g = g;
          P.rep = u;
          const LazyLabel &L = lazyLabels[e.li];
          (L.ty ? P.typed : P.untyped)++;
          if (L.ty && L.ty->hasName() && L.ty->getName().starts_with("class.")) P.cls = true;
        }
      }
      pwcComps.clear();
      inPwc.assign(numNodes, 0);
      for (auto &[c, P] : pwcBy) pwcComps.push_back(P);
      for (uint32_t u = 0; u < numNodes; u++)
        if (find(u) == u && comp[u] != UINT32_MAX && pwcBy.count(comp[u])) inPwc[u] = 1;
      if (VerboseLevel >= 2 && !pwcComps.empty()) {
        size_t t = 0, un = 0, mx = 0, cl = 0;
        for (const PwcComp &P : pwcComps) {
          (P.typed && P.untyped ? mx : P.typed ? t : un)++;
          cl += P.cls;
        }
        CG_LOG("Cells: pwc: " << pwcComps.size() << " (typed " << t << ", untyped " << un
               << ", mixed " << mx << "; through a C++ class step " << cl << ")\n");
      }
      std::vector<std::pair<size_t, std::string>> top;
      for (auto &[k, c] : walk) top.push_back({c, k});
      std::sort(top.rbegin(), top.rend());
      std::string line;
      for (size_t i = 0; i < top.size() && i < 12; i++)
        line += " " + top[i].second + "=" + std::to_string(top[i].first);
      walkEdges = onCycle;
      if (VerboseLevel >= 2)
      CG_LOG("Cells: field edges on cycles " << onCycle << " (" << selfLoops
             << " self-loops):" << line << "\n");
    }
    collapseSecs += std::chrono::duration<double>(Clock::now() - tc).count();
  };
  if (CFLCellLeakCensus)
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (Instruction &I : instructions(F))
          if (auto *SI = dyn_cast<StoreInst>(&I)) {
            if (NF.getValueNodeFor(SI->getValueOperand()) == AndersNodeFactory::InvalidIndex) continue;
            const NodeIndex pn = NF.getValueNodeFor(SI->getPointerOperand());
            if (pn == AndersNodeFactory::InvalidIndex || pn >= G) continue;
            const uint32_t c = getCanonicalNode(pn);
            if (c >= G) continue;
            for (uint32_t h : hubsOf[c])
              if (storeHub[h] != UINT32_MAX) leakCollStores[storeHub[h]].push_back(SI);
          }
  collapseCycles(); // static cycles, before any fact moves

  // ---- Objects and cells ----
  // A deque: objects are minted during the solve (trailing objects, gaps,
  // byte tails) while callers hold references to others.
  std::deque<Obj> objs;
  std::vector<Cell> cells;
  std::vector<uint32_t> factRep; // cells unified by name
  // A unified cell's member objects (all at its offset); the steps
  // (target node, label) and walks (target node) applied to it, replayed
  // for a member that joins later.
  std::vector<std::vector<Member>> memb;
  std::vector<std::vector<uint32_t>> anyDst; // field-any loops: any cells
  std::vector<std::vector<FieldEdge>> walkDst;
  std::vector<std::vector<uint64_t>> stepDst;
  size_t cappedMints = 0, outMints = 0;
  auto internName = [&](const std::string &s) { return NF.internCellName(s); };
  auto findFact = [&](uint32_t f) {
    while (factRep[f] != f) f = factRep[f] = factRep[factRep[f]];
    return f;
  };
  canonFact = findFact;
  auto newCell = [&](Cell C) {
    cells.push_back(C);
    factRep.push_back(cells.size() - 1);
    memb.push_back({{C.obj, encOff(C.off, C.folded)}});
    anyDst.emplace_back();
    walkDst.emplace_back();
    stepDst.emplace_back();
    return (uint32_t)cells.size() - 1;
  };
  // Leak census: the cell a content node (U, P, a key's K) or an
  // any-offset node stands for (kLeakAny).
  constexpr int64_t kLeakAny = std::numeric_limits<int64_t>::min();
  boost::unordered_flat_map<uint32_t, std::pair<uint32_t, int64_t>> leakCellOf;
  // The any-offset cell writes every content cell and reads them all.
  auto linkAny = [&](uint32_t a, uint32_t storeNode, uint32_t loadNode) {
    addEdge(cells[a].store, storeNode);
    addEdge(loadNode, cells[a].load);
  };
  // Why an any-offset cell was made (verbose, --cfl-cell-trace-obj).
  std::string anyCause = "?";
  uint32_t anyCauseNode = UINT32_MAX;
  std::function<void(uint32_t)> noteAnyCause;
  std::function<uint32_t(uint32_t)> anyOf;
  anyOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].any != UINT32_MAX) return objs[o].any;
    if (objs[o].fwd != UINT32_MAX) return anyOf(objs[o].fwd); // folded into its header
    if (noteAnyCause) noteAnyCause(o);
    const uint32_t w = newNode(), r = newNode();
    const uint32_t f = newCell({o, CellKind::Any, 0, UINT32_MAX, w, r,
                                NF.getCellNode(objs[o].origin, internName("*"))});
    objs[o].any = f;
    if (CFLCellLeakCensus) {
      leakCellOf.emplace(w, std::make_pair(o, kLeakAny));
      leakCellOf.emplace(r, std::make_pair(o, kLeakAny));
    }
    addEdge(w, r);
    for (auto &[c, u, pn] : objs[o].loadNodes) linkAny(f, u, pn);
    return f;
  };
  // Interior cells (a labeled object's offset inside a scalar member),
  // by the step that minted them (verbose census).
  std::map<std::string, size_t> interiorBy;
  std::string mintCause = "seed";
  // The cause a minting operation sets for its extent; the previous one
  // comes back on exit, so no cell is credited to a stale step.
  struct MintCause {
    std::string *v = nullptr, old;
    MintCause(std::string &cur, std::string c, bool on) {
      if (!on) return;
      v = &cur;
      old = std::move(cur);
      cur = std::move(c);
    }
    ~MintCause() { if (v) *v = std::move(old); }
  };
  size_t interiorCells = 0, beyondLabel = 0, leftObject = 0;
  // The content cell of folded offset c of object o, made on first use.
  // The content cell an offset of object o lands in: folded through its
  // layout (arrays are one element), or, unlabeled, one cell for bytes,
  // the offset modulo the learned element size, else the raw offset.
  auto contentKey = [&](const Obj &O, int64_t off) -> int64_t {
    if (!O.layout)
      return O.period ? ((off % O.period) + O.period) % O.period : off;
    assert(!(O.tail && off >= O.size) && "trailing offsets route to the tail object");
    off = ((off % O.size) + O.size) % O.size; // an array of one or more
    return foldIn(O.layout, off, DL);
  };
  // Keyed union slots by struct ("struct.S" -> offset, size).
  std::map<std::string, std::vector<std::pair<uint64_t, uint64_t>>> slotsOf;
  for (auto &[S, off, size] : cellUnionSlots) slotsOf["struct." + S].push_back({off, size});
  std::vector<std::string> slotChain;
  auto inUnionSlot = [&](const Obj &O, int64_t c) {
    if (slotsOf.empty() || !O.layout) return false;
    structChain(O.layout, c, DL, slotChain);
    for (const std::string &e : slotChain) {
      const size_t plus = e.rfind('+');
      auto it = slotsOf.find(e.substr(0, plus));
      if (it == slotsOf.end()) continue;
      const uint64_t rel = std::stoull(e.substr(plus + 1));
      for (auto [off, size] : it->second)
        if (rel >= off && rel < off + size) return true;
    }
    return false;
  };
  size_t splitCells = 0, keyedCells = 0, lateSplits = 0;
  size_t trailingArrays = 0; // trailing objects of a header taken as arrays of unknown extent
  auto contentOf = [&](uint32_t o, int64_t c) -> std::pair<uint32_t, uint32_t> {
    auto it = objs[o].content.find(c);
    if (it != objs[o].content.end()) return it->second;
    const uint32_t u = newNode();
    uint32_t pn = u;
    if (inUnionSlot(objs[o], c)) { // write side U, read side P = U + keys
      pn = newNode();
      addEdge(u, pn);
      unionView[u] = unionView[pn] = 1;
      splitCells++;
    }
    objs[o].content.emplace(c, std::make_pair(u, pn));
    objs[o].loadNodes.push_back({c, u, pn});
    if (CFLCellLeakCensus) {
      leakCellOf.emplace(u, std::make_pair(o, c));
      leakCellOf.emplace(pn, std::make_pair(o, c));
    }
    if (objs[o].any != UINT32_MAX) linkAny(objs[o].any, u, pn);
    if (objs[o].layout && !leafStart(objs[o].layout, c, DL)) {
      interiorCells++;
      interiorBy[mintCause]++;
    }
    return std::make_pair(u, pn);
  };
  // Tagged-field slots flipped to unkeyed during the solve (plan 3.51):
  // (struct label, F offset). Their keyed cells feed the unkeyed side, so
  // every read of the slot sees every write.
  std::set<std::pair<std::string, int64_t>> taggedFlipped;
  std::vector<std::string> taggedFlipAt;
  std::map<std::string, std::vector<size_t>> tagPairsOf; // struct -> pairs
  for (size_t i = 0; i < taggedPairs.size(); i++) tagPairsOf[taggedPairs[i].S].push_back(i);
  std::vector<std::string> tagChain;
  // Is content c of object o a flipped slot (in any struct nested there)?
  auto flippedAt = [&](uint32_t o, int64_t c) {
    if (taggedFlipped.empty() || !objs[o].layout) return false;
    structChain(objs[o].layout, c, DL, tagChain);
    for (const std::string &e : tagChain) {
      const size_t plus = e.rfind('+');
      if (taggedFlipped.count({e.substr(0, plus), std::stoll(e.substr(plus + 1))})) return true;
    }
    return false;
  };
  // A write the census did not name reached pair pi's tag: every keyed
  // cell of its slot (in every object it is nested in) feeds the slot's
  // unkeyed side, so every read sees every write (monotone).
  auto flipPair = [&](size_t pi, const std::string &why) {
    const TaggedPair &tp = taggedPairs[pi];
    if (!taggedFlipped.insert({tp.S, tp.F}).second) return;
    MintCause mc(mintCause, "tag flip", VerboseLevel >= 2);
    if (taggedFlipAt.size() < 20)
      taggedFlipAt.push_back(tp.S + "+" + std::to_string(tp.F) + " by +" + std::to_string(tp.D) + ": " + why);
    for (uint32_t o2 = 0; o2 < objs.size(); o2++) {
      if (!objs[o2].layout || objs[o2].keyed.empty()) continue;
      for (auto &[kk, n] : objs[o2].keyed) {
        const int64_t c = (int64_t)(uint32_t)(kk >> 32);
        if (flippedAt(o2, c)) addEdge(n, contentOf(o2, c).first);
      }
    }
  };
  // The tagged pairs whose tag bytes positions [lo, hi) of object o cover
  // (all: anywhere in o); each is flipped.
  std::map<Type *, bool> tagNests;
  auto tagNestsIn = [&](Type *L) { // does a keyed pair's struct lie in L?
    auto [nit, ins] = tagNests.try_emplace(L, false);
    if (ins && L->isSized())
      structCover(L, 0, (int64_t)DL.getTypeAllocSize(L), DL, [&](StructType *ST, int64_t, int64_t) {
        nit->second |= tagPairsOf.count(stripStructNameSuffix(ST->getName()).str()) != 0;
      });
    return nit->second;
  };
  // (Positions past a header are the trailing object's: the caller's.)
  auto flipCovered = [&](uint32_t o, int64_t lo, int64_t hi, bool all, const Instruction *at) {
    const Obj &O = objs[o];
    if (!O.layout || O.size <= 0 || !tagNestsIn(O.layout)) return;
    const int64_t sz = O.size;
    int64_t a = 0, b = sz;
    if (!all && hi - lo < sz) {
      a = O.repeats ? ((lo % sz) + sz) % sz : std::max<int64_t>(lo, 0);
      b = a + (hi - lo);
    }
    auto visit = [&](StructType *ST, int64_t l, int64_t h) {
      auto it = tagPairsOf.find(stripStructNameSuffix(ST->getName()).str());
      if (it == tagPairsOf.end()) return;
      for (size_t pi : it->second) {
        const TaggedPair &tp = taggedPairs[pi];
        if (l < tp.D + tp.Dsize && tp.D < h && !taggedFlipped.count({tp.S, tp.F}))
          flipPair(pi, "watched store at " + instLoc(at) + " (" + objs[o].label + ")");
      }
    };
    structCover(O.layout, a, std::min(b, sz), DL, visit);
    if (b > sz && O.repeats) structCover(O.layout, 0, b - sz, DL, visit);
  };
  // The cell of key k in content (o, c): its unkeyed writes and its own.
  std::function<uint32_t(uint32_t, int64_t, uint32_t)> keyedOf;
  keyedOf = [&](uint32_t o, int64_t c, uint32_t k) -> uint32_t {
    const auto [u, pn] = contentOf(o, c);
    if (u == pn) return u; // not a keyed slot: the key adds nothing
    const uint64_t kk = ((uint64_t)(uint32_t)c << 32) | k;
    auto it = objs[o].keyed.find(kk);
    if (it != objs[o].keyed.end()) return it->second;
    const uint32_t n = newNode();
    addEdge(u, n);
    addEdge(n, pn);
    if (flippedAt(o, c)) addEdge(n, u);
    objs[o].keyed.emplace(kk, n);
    if (CFLCellLeakCensus) leakCellOf.emplace(n, std::make_pair(o, c));
    keyedCells++;
    // Copies out of this slot carry the key along.
    for (size_t i = 0; i < objs[o].copyOut.size(); i++) {
      const auto [sc, od, dc] = objs[o].copyOut[i];
      if (sc == c) addEdge(n, keyedOf(od, dc, k));
    }
    return n;
  };
  auto cellName = [&](uint32_t o, int64_t c) -> std::string {
    const Obj &O = objs[o];
    if (!O.layout)
      return "?#" + std::to_string(o);
    if (O.label == "i8" || inByteArray(O.layout, c, DL))
      return "i8[]";
    return (O.ident.empty() ? O.label : O.ident) + "+" + std::to_string(c);
  };
  // The address fact (o, off): exact, or folded (off is element 0's).
  // The trailing object of header+tail object o, minted on first use.
  size_t tailMinted = 0, tailMoved = 0;
  auto tailOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].tailObj != UINT32_MAX) return objs[o].tailObj;
    Obj T;
    T.origin = objs[o].origin;
    T.parentObj = o;
    T.base = objs[o].base + objs[o].size;
    objs.push_back(std::move(T));
    objs[o].tailObj = objs.size() - 1;
    tailMinted++;
    return objs[o].tailObj;
  };
  // Byte `off` of object o, through trailing objects: (object, offset).
  auto locate = [&](uint32_t o, int64_t off) -> std::pair<uint32_t, int64_t> {
    while (objs[o].fwd != UINT32_MAX) {
      off += objs[o].fwdOff;
      o = objs[o].fwd;
    }
    while (objs[o].tail && off >= objs[o].size) {
      off -= objs[o].size;
      o = tailOf(o);
    }
    return {o, off};
  };
  auto mintOff = [&](uint32_t o, int64_t off, bool folded) -> uint32_t {
    Obj &O = objs[o];
    const int64_t key = off * 2 + (folded ? 1 : 0);
    auto it = O.offCells.find(key);
    if (it != O.offCells.end()) return findFact(it->second);
    if (!O.layout && O.content.size() >= CFLCellCap &&
        !O.content.count(off)) {
      anyCause = "cap";
      cappedMints++;
      return anyOf(o);
    }
    const int64_t c = contentKey(O, off);
    const uint32_t nm = internName(cellName(o, c));
    const auto [cu, cp] = contentOf(o, c);
    Cell C{o, CellKind::Off, off, nm, cu, cp, NF.getCellNode(objs[o].origin, nm)};
    C.folded = folded;
    const uint32_t f = newCell(C);
    objs[o].offCells.emplace(key, f);
    return f;
  };
  auto outOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].out != UINT32_MAX) return objs[o].out;
    const uint32_t f = newCell({o, CellKind::Out, 0, UINT32_MAX, UINT32_MAX, UINT32_MAX,
                                NF.getCellNode(objs[o].origin, internName("out"))});
    objs[o].out = f;
    outMints++;
    return f;
  };
  // The cells one step of object o's offset `off` along label li reaches.
  std::function<const std::vector<uint32_t> &(uint32_t, int64_t, uint32_t)>
      stepOne;
  std::function<void(uint32_t, int64_t, uint32_t, int64_t, uint32_t)> walkOne;
  // The fact applyStep is stepping, and its node (one-label reports).
  uint32_t curStepFact = UINT32_MAX, curStepNode = UINT32_MAX, curStepDst = UINT32_MAX;
  uint32_t curStepLi = UINT32_MAX; // the label of the step or walk being applied
  std::map<std::string, size_t> cloneCandidates, otherMeets; // one-label
  std::set<std::tuple<uint32_t, uint32_t, uint32_t>> seenConflict;
  size_t conflicts = 0;
  std::function<void(uint32_t, uint32_t, const StructType *, const char *)>
      reportTypedStep;
  // --cfl-cell-one-label: a conflict matters only inside the icall cone
  // (nodes whose facts can reach an indirect call's callee operand); one
  // outside waits here until the cone grows to it, else stays unreported.
  // kind 0: two names at a node; 1: a step of another struct; 2: a copy
  // between unrelated structs.
  struct PendingConflict {
    int kind;
    uint32_t n, a, f;
    const StructType *S;
    std::string why;
    uint64_t pop;
  };
  std::vector<PendingConflict> pendingConf;
  boost::unordered_flat_map<uint64_t, int8_t> compatMemo;
  // Stop mode reports one conflict: a node's first is enough; the rest
  // are counted.
  boost::unordered_flat_set<uint32_t> pendingNodes;
  size_t pendingDup = 0;
  auto pend1 = [&](PendingConflict P) {
    if (CFLCellOneLabelMax <= 1 && !pendingNodes.insert(P.n).second) {
      pendingDup++;
      return;
    }
    pendingConf.push_back(std::move(P));
  };
  uint32_t curCopyDst = UINT32_MAX, curCopySrcFact = UINT32_MAX;
  // Per byte copy: cell pairs, content edges, source and destination
  // objects met (the copy report).
  struct CopyStat {
    size_t pairs = 0, edges = 0;
    boost::unordered_flat_set<uint32_t> srcObjs, dstObjs;
  };
  std::vector<CopyStat> copyStat;
  uint32_t curCopy = UINT32_MAX;
  // Leak census: a byte copy's content edges (source, destination node).
  boost::unordered_flat_map<uint64_t, uint32_t> leakCopyEdge;
  struct { uint32_t ci = UINT32_MAX, fs, os, od; } firstMismatch;
  uint64_t pops = 0; // worklist pops (the solve's clock)
  // Two cells of one name a node holds become one cell: their content
  // nodes merge, and each side's steps and walks are replayed for the
  // other side's member objects.
  size_t factMerges = 0;
  auto mergeFacts = [&](uint32_t a, uint32_t b) {
    a = findFact(a);
    b = findFact(b);
    if (a == b) return a;
    assert(cells[a].kind == CellKind::Off && cells[b].kind == CellKind::Off &&
           "only offset cells merge");
    factRep[b] = a;
    factMerges++;
    mergeNodes(cells[a].store, cells[b].store);
    // stepOne, walkOne and anyOf may mint (growing these vectors): copies.
    const std::vector<Member> ma = memb[a], mb = memb[b];
    const std::vector<uint32_t> xa = anyDst[a], xb = anyDst[b];
    const std::vector<FieldEdge> wa = walkDst[a], wb = walkDst[b];
    const std::vector<uint64_t> sa = stepDst[a], sb = stepDst[b];
    auto replay = [&](const std::vector<uint64_t> &S,
                      const std::vector<FieldEdge> &W,
                      const std::vector<uint32_t> &X,
                      const std::vector<Member> &M) {
      curStepFact = UINT32_MAX; // a replay: no step to attribute
      for (uint64_t dl : S)
        for (auto [o, off] : M) {
          const std::vector<uint32_t> R = stepOne(o, off, (uint32_t)dl);
          for (uint32_t f2 : R) add((uint32_t)(dl >> 32), f2);
        }
      for (const FieldEdge &e : W)
        for (auto [o, off] : M) walkOne(o, off, e.li, e.walk, e.dst);
      for (uint32_t d : X) {
        anyCause = "merge with a fact in the field-any loop";
        anyCauseNode = d;
        for (auto [o, off] : M) add(d, anyOf(o));
      }
    };
    replay(sa, wa, xa, mb);
    replay(sb, wb, xb, ma);
    memb[a].insert(memb[a].end(), mb.begin(), mb.end());
    anyDst[a].insert(anyDst[a].end(), xb.begin(), xb.end());
    walkDst[a].insert(walkDst[a].end(), wb.begin(), wb.end());
    stepDst[a].insert(stepDst[a].end(), sb.begin(), sb.end());
    memb[b] = {};
    anyDst[b] = {};
    walkDst[b] = {};
    stepDst[b] = {};
    if (entryMergedFn) entryMergedFn(a, b); // plan 3.54: the merged cell's objects
    return a;
  };
  // The exact address of byte `off` of object o (a heap array is one
  // element: offsets reduce modulo its size).
  auto cellAt = [&](uint32_t o, int64_t off) -> uint32_t {
    std::tie(o, off) = locate(o, off);
    Obj &O = objs[o];
    if (!O.layout) {
      // An unlabeled array of learned element size: the address reduces
      // modulo the element, as a heap object modulo its struct.
      if (O.period) return mintOff(o, ((off % O.period) + O.period) % O.period, false);
      return off < 0 ? outOf(o) : mintOff(o, off, false);
    }
    // Every object is an array (a single object an array of one), arrays
    // are one element and a step never leaves its array: offsets reduce
    // modulo the object, and inside it fold to element 0 (&a[4] is &a[0]).
    // Leaving a non-array object (one past the end of a single struct) is
    // undefined behavior if dereferenced: counted.
    if (off >= O.size || off < 0) {
      // An array of T (heap) wraps; a byte offset past a single object is
      // outside it (one past the end, never dereferenced legally). Index
      // steps (p[k], p++) never get here: they stay in their array.
      if (!O.repeats) { leftObject++; return outOf(o); }
      beyondLabel++;
      off = ((off % O.size) + O.size) % O.size;
    }
    return mintOff(o, foldIn(O.layout, off, DL), false);
  };
  // The address of byte `off` as an element of the byte array holding it
  // (provenance, plan 3.43: it cannot leave the array); the exact address
  // elsewhere. Both share the content cell.
  auto cellAtArr = [&](uint32_t o, int64_t off) -> uint32_t {
    std::tie(o, off) = locate(o, off);
    const Obj &O = objs[o];
    if (!O.layout || O.tail) return cellAt(o, off);
    const int64_t pos = O.repeats ? ((off % O.size) + O.size) % O.size : off;
    int64_t lo = 0, hi = 0, esz = 0;
    if (pos < 0 || pos >= O.size || !innermostArraySpan(O.layout, pos, DL, lo, hi, esz) ||
        esz != 1 || hi - lo <= 1)
      return cellAt(o, off);
    return mintOff(o, foldIn(O.layout, pos, DL), true);
  };

  // Learned folding: a typed access at offset 0 of an unlabeled object
  // gives it a layout. Existing cells re-fold (merge) at the next safe
  // point; folding only merges, so the cells minted before it stay sound.
  std::vector<uint32_t> refoldQueue;
  // --cfl-cell-one-label: nodes an object's facts passed while unknown.
  // Unknown objects' facts that passed a node unchecked: object -> (node,
  // fact), re-presented there once the object is typed.
  boost::unordered_flat_map<uint32_t, std::vector<std::pair<uint32_t, uint32_t>>> passedBy;
  size_t layoutsLearned = 0, refoldMerges = 0, periodsLearned = 0,
         tailObjects = 0;
  auto requestPeriod = [&](uint32_t o, int64_t s) {
    Obj &O = objs[o];
    if (O.layout || O.fn || s <= 0) return;
    const int64_t p = O.period ? std::gcd(O.period, s) : s;
    if (p == O.period) return;
    if (!O.period) periodsLearned++;
    O.period = p;
    refoldQueue.push_back(o);
  };
  std::function<void(uint32_t, StructType *)> noteLayoutCause; // --cfl-cell-trace-obj
  std::string layoutCopyFrom; // the byte copy giving its effective type (trace)
  uint32_t layoutCopySrc = UINT32_MAX; // its source object
  // An allocation whose constant size k is larger than struct S (and not a
  // multiple): the structs of exactly k bytes that start with S. Then S is
  // the first member of a container (C inheritance: code that writes only
  // `pub`), not a header before trailing data. *n = how many there are.
  size_t heapContainerRelabeled = 0, heapContainerAmbiguous = 0;
  // Objects whose debug-info identity differs from the IR struct the
  // linker kept: (IR label, identity) -> count.
  std::map<std::pair<std::string, std::string>, size_t> identPairs;
  auto noteIdent = [&](Obj &O, const std::string &id) {
    if (id.empty() || id == O.label) return;
    O.ident = id;
    identPairs[{O.label, id}]++;
  };
  auto containerOfSize = [&](const CallBase *C, const StructType *S, int64_t sz,
                             size_t &n) -> StructType * {
    n = 0;
    uint64_t k = 0;
    for (const Use &A : C->args())
      if (const auto *K = dyn_cast<ConstantInt>(A.get()))
        if (K->getZExtValue() > (uint64_t)sz && K->getZExtValue() % sz) k = K->getZExtValue();
    if (!k) return nullptr;
    const StructInfo *SI =
        Ctx->structAnalyzer.getStructInfo(S, const_cast<Module *>(C->getModule()));
    if (!SI) return nullptr;
    StructType *one = nullptr;
    for (auto &[ct, offs] : SI->getContainers())
      if (offs.count(0) && ct->isSized() && DL.getTypeAllocSize(const_cast<StructType *>(ct)) == k) {
        n++;
        one = const_cast<StructType *>(ct);
      }
    return n == 1 ? one : nullptr;
  };
  // The extent a label covers (plan 3.53, rule 1): a T at the start, and
  // what the allocation's size says of the rest. A constant or a multiple
  // of T's size is an array of T; one T exactly is one; T plus trailing
  // data, or a size that says nothing (a wrapper's argument, a length read
  // from input), is a header followed by an unknown trailing object, until
  // a T-stride access makes it an array (extendToArray).
  size_t extentArrays = 0, extentOne = 0, extentHeader = 0, extentUnknown = 0,
         arraysExtended = 0, extendRefused = 0, readStepsSkipped = 0, varByteAny = 0,
         tailIndexAny = 0;
  auto setExtent = [&](Obj &O, const Value *V) {
    O.tail = false;
    O.repeats = false;
    const auto *C = dyn_cast_or_null<CallBase>(V);
    const uint64_t at = (uint64_t)(O.base + O.size);
    if (C && headerPlusTail(C, at)) { O.tail = true; extentHeader++; tailObjects++; }
    else if (C && exactlyOne(C, at)) extentOne++;
    else if (C && sizeIsMultiple(C, at)) { O.repeats = true; extentArrays++; }
    else { O.tail = true; O.tailUnsized = true; extentUnknown++; }
  };
  // The extension of a header+tail object into an array of its T (defined
  // with the steps; a label request on an unsized tail makes it).
  std::function<void(uint32_t)> extendToArrayFn;
  std::function<std::string(uint32_t)> nodeDescFn; // set once nodeDesc exists
  std::function<std::string(const Obj &)> describeFn; // set once describe exists
  size_t bytesWritesRefused = 0;
  std::map<std::string, size_t> bytesWritesBy; // writing site | struct
  size_t tailWritesFolded = 0;
  std::map<std::pair<std::string, std::string>, size_t> tailFoldPairs;
  auto requestLayout = [&](uint32_t o, StructType *S) {
    Obj &O = objs[o];
    if (O.layout || O.fn || !S || S->isOpaque() || !S->isSized()) return;
    // One label per allocation: the unknown data after a T (an allocation
    // whose size said nothing) takes no label of its own. A write of T
    // there makes it an array of T; a write of another struct is a rule (b)
    // row (the object was laid out by its first typed write).
    // The data after a T taking the T itself is the next element, whatever
    // the size said (a sized header+tail too: bfd_zalloc(abfd,
    // nsymz * sizeof (carsym) + stringsize + 1) walked by carsym++): an
    // array of T, never a chain of trailing objects.
    if (O.parentObj != UINT32_MAX && objs[O.parentObj].tailObj == o &&
        S == objs[O.parentObj].layout) {
      extendToArrayFn(O.parentObj); // a T written at a T stride: an array of T
      return;
    }
    if (O.parentObj != UINT32_MAX && objs[O.parentObj].tailUnsized &&
        objs[O.parentObj].tailObj == o) {
      const uint32_t p = O.parentObj;
      // Another struct written into the data after a T: reported (rule
      // (b)), not admitted; the write flows to the raw cell.
      tailWritesFolded++;
      tailFoldPairs[{objs[p].label, typeLabel(S)}]++;
      return;
    }
    int64_t sz = (int64_t)DL.getTypeAllocSize(S);
    if (sz <= 0) return;
    // The first member of a container its allocation size names: learn the
    // container; with several such containers, learn nothing yet (a later
    // step names the type).
    if (O.base == 0)
      if (const auto *C = dyn_cast_or_null<CallBase>(NF.getValueForNode(O.origin))) {
        size_t n = 0;
        if (StructType *CT = containerOfSize(C, S, sz, n)) {
          S = CT;
          sz = (int64_t)DL.getTypeAllocSize(S);
          heapContainerRelabeled++;
        } else if (n > 1) {
          heapContainerAmbiguous++;
          return;
        }
      }
    // An object used as bytes keeps that first use: a struct written into
    // it is reported (rule (b)), not admitted as its layout. The write
    // still flows: the step yields the raw cell (or the any-offset cell).
    if (O.byteAccessed) {
      bytesWritesRefused++;
      const std::string site =
          !layoutCopyFrom.empty() ? "copy at " + layoutCopyFrom.substr(0, layoutCopyFrom.find(" from "))
          : curStepDst != UINT32_MAX ? nodeDescFn(curStepDst).substr(0, 120) : std::string("?");
      bytesWritesBy[site + " | " + typeLabel(S)]++;
      return;
    }
    O.layout = S;
    O.size = sz;
    O.label = typeLabel(S);
    O.learnedLayout = true;
    // Its identity: a copy's source's; a written step's pointer's declared
    // pointee (debug info) where the IR merged that struct away.
    if (layoutCopySrc != UINT32_MAX) {
      if (objs[layoutCopySrc].label == O.label) noteIdent(O, objs[layoutCopySrc].ident);
    } else if (curStepDst < G) {
      if (const auto *GEP = dyn_cast_or_null<GEPOperator>(NF.getValueForNode(curStepDst)))
        noteIdent(O, diMergedIdent(GEP->getPointerOperand(), true));
    }
    setExtent(O, NF.getValueForNode(O.origin));
    if (O.parentObj != UINT32_MAX) trailingArrays += O.repeats;
    layoutsLearned++;
    if (noteLayoutCause) noteLayoutCause(o, S);
    refoldQueue.push_back(o);
  };
  auto canonOff = contentKey;
  auto refold = [&](uint32_t o) {
    MintCause mc(mintCause, "refold", VerboseLevel >= 2);
    // Header+tail: what lay past the header (minted while the object was
    // unknown) moves to the trailing object.
    if (objs[o].tail) {
      const int64_t sz = objs[o].size;
      std::vector<std::tuple<int64_t, uint32_t, uint32_t>> keep, moved;
      for (auto &x : objs[o].loadNodes)
        (std::get<0>(x) >= sz ? moved : keep).push_back(x);
      objs[o].loadNodes = std::move(keep);
      for (auto &[c, u, pn] : moved) {
        const auto [t, c2] = locate(o, c);
        const auto [u2, p2] = contentOf(t, contentKey(objs[t], c2));
        mergeNodes(u2, u);
        mergeNodes(p2, pn);
      }
      std::vector<std::tuple<int64_t, bool, uint32_t>> past;
      for (auto &[key, f] : objs[o].offCells)
        if ((key >> 1) >= sz) past.push_back({key >> 1, (key & 1) != 0, findFact(f)});
      for (auto &[off, bit, f] : past) {
        objs[o].offCells.erase(off * 2 + (bit ? 1 : 0));
        const auto [t, off2] = locate(o, off);
        for (Member &mb : memb[f])
          if (mb.first == o && decOff(mb.second) == off)
            mb = {t, encOff(off2, (mb.second & kFoldedBit) != 0)};
        if (cells[f].obj == o) {
          cells[f].obj = t;
          cells[f].off = off2;
          cells[f].name = internName(cellName(t, contentKey(objs[t], off2)));
        }
        auto it = objs[t].offCells.find(off2 * 2 + (bit ? 1 : 0));
        if (it == objs[t].offCells.end()) objs[t].offCells[off2 * 2 + (bit ? 1 : 0)] = f;
        else it->second = mergeFacts(findFact(it->second), f);
        tailMoved++;
        refoldQueue.push_back(t); // folds them as the trailing object reads
      }
    }
    // Content cells merge by their new folded offset.
    std::map<int64_t, std::vector<std::pair<uint32_t, uint32_t>>> byC;
    for (auto &[c, u, pn] : objs[o].loadNodes)
      byC[canonOff(objs[o], c)].push_back({u, pn});
    objs[o].content.clear();
    objs[o].loadNodes.clear();
    for (auto &[c, ns] : byC) {
      for (size_t i = 1; i < ns.size(); i++) {
        mergeNodes(ns[0].first, ns[i].first);
        mergeNodes(ns[0].second, ns[i].second);
      }
      objs[o].content.emplace(c, ns[0]);
      objs[o].loadNodes.push_back({c, ns[0].first, ns[0].second});
    }
    // Exact addresses reduce modulo the element; equal ones become one.
    std::map<std::pair<int64_t, bool>, std::vector<uint32_t>> byOff;
    for (auto &[key, f] : objs[o].offCells) {
      int64_t off = key >> 1;
      const bool bit = (key & 1) != 0;
      const Obj &O = objs[o];
      assert(!(O.tail && off >= O.size) && "moved to the trailing object above");
      if (O.repeats) off = ((off % O.size) + O.size) % O.size;
      else if (!O.layout && O.period) off = ((off % O.period) + O.period) % O.period;
      byOff[{off, bit}].push_back(findFact(f));
    }
    objs[o].offCells.clear();
    for (auto &[ob, G2] : byOff) {
      const auto [off, bit] = ob;
      std::vector<uint32_t> fs = G2;
      std::sort(fs.begin(), fs.end());
      fs.erase(std::unique(fs.begin(), fs.end()), fs.end());
      const int64_t c = canonOff(objs[o], off);
      const uint32_t nm = internName(cellName(o, c));
      for (uint32_t f : fs) {
        for (Member &mb : memb[f])
          if (mb.first == o) mb.second = encOff(off, (mb.second & kFoldedBit) != 0);
        if (cells[f].obj == o) {
          cells[f].off = off;
          cells[f].name = nm;
        }
      }
      uint32_t surv = fs[0];
      for (size_t i = 1; i < fs.size(); i++) {
        surv = mergeFacts(surv, fs[i]);
        refoldMerges++;
      }
      objs[o].offCells[off * 2 + (bit ? 1 : 0)] = surv;
    }
    // A content cell minted while the object was unknown and now inside a
    // keyed slot gets its read side: P reads U and keeps every link U
    // had (what read the whole cell still does), and the object's cells
    // there read P, so keys made from now on reach their reads.
    for (auto &[c, un] : objs[o].content) {
      auto &[u, pn] = un;
      if (find(u) != find(pn) || !inUnionSlot(objs[o], c)) continue;
      const uint32_t p2 = newNode();
      const std::vector<uint32_t> outs = succ[find(u)];
      addEdge(u, p2);
      for (uint32_t x : outs) addEdge(p2, x);
      unionView[find(u)] = unionView[p2] = 1;
      for (auto &ln : objs[o].loadNodes)
        if (std::get<0>(ln) == c) std::get<2>(ln) = p2;
      for (auto &[key, f] : objs[o].offCells) {
        Cell &C = cells[findFact(f)];
        if (C.obj == o && contentKey(objs[o], key >> 1) == c && find(C.load) == find(u)) C.load = p2;
      }
      pn = p2;
      splitCells++;
      lateSplits++;
    }
    if (leakRefold) leakRefold(o);
  };
  auto drainRefolds = [&]() {
    while (!refoldQueue.empty()) {
      const uint32_t o = refoldQueue.back();
      refoldQueue.pop_back();
      refold(o);
      if (!watchPending.empty() && objs[o].layout)
        if (auto wit = watchPending.find(o); wit != watchPending.end()) {
          std::vector<std::pair<uint32_t, uint32_t>> ws = std::move(wit->second);
          watchPending.erase(wit);
          for (auto [wi, f] : ws) watchCheck(wi, findFact(f));
        }
      if (!keyedWait.empty() && objs[o].layout)
        if (auto kit = keyedWait.find(o); kit != keyedWait.end()) {
          std::vector<std::pair<uint32_t, uint32_t>> ws = std::move(kit->second);
          keyedWait.erase(kit);
          for (auto [h, f] : ws) linkHubFn(h, findFact(f));
        }
      // Typed now: its facts at the nodes it passed while unknown get the
      // one-label check (re-presented as pending; propagation is a no-op).
      auto pit = passedBy.find(o);
      if (pit == passedBy.end() || !objs[o].layout) continue;
      std::vector<std::pair<uint32_t, uint32_t>> seen = std::move(pit->second);
      passedBy.erase(pit);
      std::sort(seen.begin(), seen.end());
      seen.erase(std::unique(seen.begin(), seen.end()), seen.end());
      for (auto [m, x] : seen) {
        const uint32_t r = find(m);
        pend[r].push_back(findFact(x));
        push(r);
      }
    }
  };

  // Labels: globals and stack slots by their IR types, heap objects by the
  // struct their typed writes declare (one struct, else unlabeled).
  std::unordered_map<const Value *, std::set<std::string>> labels;
  staticLabels(labels);
  const double labelSecs =
      std::chrono::duration<double>(Clock::now() - t0).count();
  size_t heapLabeled = 0, heapUnlabeled = 0, heapConflict = 0, heapPtrArrays = 0;
  auto newObj = [&](NodeIndex origin, const Value *V) -> uint32_t {
    Obj O;
    O.origin = origin;
    if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) {
      O.layout = GV->getValueType();
    } else if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) {
      O.layout = AI->getAllocatedType();
      O.repeats = AI->isArrayAllocation();
    } else if (const auto *C = dyn_cast_or_null<CallBase>(V)) {
      auto lit = labels.find(C);
      if (!CFLCellTraceObj.empty()) {
        const Function *CF = C->getCalledFunction();
        const std::string who = C->getFunction()->getName().str() + "::call " +
                                (CF ? CF->getName().str() : std::string("?"));
        if (who.find(CFLCellTraceObj) != std::string::npos) {
          std::string ls;
          if (lit != labels.end())
            for (const std::string &l : lit->second) ls += " " + l;
          CG_LOG("Cells: SITE " << who << " at " << instLoc(C) << ": site labels {" << ls << " }\n");
        }
      }
      // Labels of one object at its start, one embedding the other at
      // offset 0 (my_memory_mgr and its first member jpeg_memory_mgr:
      // `mem->pub.f = ..`): the container is the object's type.
      if (lit != labels.end() && lit->second.size() > 1) {
        std::set<std::string> outer;
        for (const std::string &a : lit->second) {
          bool embedded = false;
          for (const std::string &b : lit->second) {
            if (a == b) continue;
            StructType *SB = StructType::getTypeByName(C->getContext(), b);
            if (SB && !SB->isOpaque() &&
                structStartsAt(SB, 0, stripStructNameSuffix(a), DL))
              embedded = true;
          }
          if (!embedded) outer.insert(a);
        }
        if (outer.size() == 1) lit->second = std::move(outer);
      }
      if (lit != labels.end() && lit->second.size() == 1 &&
          StringRef(*lit->second.begin()).starts_with("ptr[]:")) {
        // The site's variable declares an array of pointer slots (T **):
        // element = one pointer, its extent from the size below.
        O.layout = PointerType::get(C->getContext(), 0);
        O.repeats = true;
        O.ident = StringRef(*lit->second.begin()).drop_front(6).str() + "[]";
        heapLabeled++;
        heapPtrArrays++;
      } else if (lit != labels.end() && lit->second.size() == 1) {
        O.layout = StructType::getTypeByName(C->getContext(),
                                             *lit->second.begin());
        O.repeats = true;
        if (O.layout) heapLabeled++;
        else heapUnlabeled++;
      } else if (lit != labels.end() && lit->second.size() > 1) {
        heapConflict++;
      } else {
        heapUnlabeled++;
      }
    }
    if (O.layout && O.layout->isSized())
      O.size = (int64_t)DL.getTypeAllocSize(O.layout);
    if (O.size <= 0) O.layout = nullptr; // opaque or empty: unlabeled
    else O.label = typeLabel(O.layout);
    if (O.layout && (isa_and_nonnull<AllocaInst>(V) || isa_and_nonnull<GlobalVariable>(V)))
      noteIdent(O, diMergedIdent(V, false));
    // A constant size larger than the label where some struct of exactly
    // that size starts with the label: the label is the first member of a
    // container (C inheritance: the allocating code writes only `pub`),
    // not a header before trailing data. One such container: its type;
    // several (cjpeg -O3: huff and phuff encoders are both 200 bytes):
    // unlabeled, learned from the first struct step.
    if (O.layout && O.repeats)
      if (const auto *C = dyn_cast_or_null<CallBase>(V))
        if (const auto *ST = dyn_cast<StructType>(O.layout)) {
          size_t n = 0;
          if (StructType *CT = containerOfSize(C, ST, O.size, n)) {
            O.layout = CT;
            O.size = (int64_t)DL.getTypeAllocSize(CT);
            O.label = typeLabel(O.layout);
            O.repeats = false;
            heapContainerRelabeled++;
          } else if (n > 1) {
            O.layout = nullptr;
            O.size = 0;
            O.label.clear();
            heapContainerAmbiguous++;
          }
        }
    if (O.layout && O.repeats && isa_and_nonnull<CallBase>(V)) setExtent(O, V);
    objs.push_back(std::move(O));
    return objs.size() - 1;
  };

  // A stable order for the pointer-keyed sets the solve walks (a
  // SmallPtrSet iterates in pointer-hash order, so fact numbering, and the
  // pop order with it, followed the heap layout): module, function and
  // instruction position.
  std::unordered_map<const Value *, uint64_t> stableOrd;
  {
    uint64_t k = 0;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        stableOrd[&F] = k++;
        for (Instruction &I : instructions(F)) stableOrd[&I] = k++;
      }
  }
  auto stableKey = [&](const Value *V) {
    auto it = stableOrd.find(V);
    return it == stableOrd.end() ? UINT64_MAX : it->second;
  };
  std::vector<const Function *> addrTakenSorted(Ctx->AddressTakenFuncs.begin(),
                                                Ctx->AddressTakenFuncs.end());
  std::sort(addrTakenSorted.begin(), addrTakenSorted.end(), [&](const Function *a, const Function *b) {
    const uint64_t ka = stableKey(a), kb = stableKey(b);
    return ka != kb ? ka < kb : a->getName() < b->getName();
  });
  std::vector<const CallBase *> icallsSorted(Ctx->IndirectCallInsts.begin(), Ctx->IndirectCallInsts.end());
  std::sort(icallsSorted.begin(), icallsSorted.end(),
            [&](const CallBase *a, const CallBase *b) { return stableKey(a) < stableKey(b); });

  // ---- Seeds: functions and objects ----
  size_t funcSeeds = 0, objSeeds = 0;
  std::unordered_map<const Function *, uint32_t> funcFact;
  for (const Function *F : addrTakenSorted) {
    const NodeIndex vn = NF.getValueNodeFor(F);
    if (vn == AndersNodeFactory::InvalidIndex) continue;
    const uint32_t n = canon(vn);
    if (!inGraph[n]) continue;
    const Function *FD = getFuncDef(const_cast<Function *>(F));
    auto [it, ins] = funcFact.try_emplace(FD, 0);
    if (ins) {
      Obj O;
      O.origin = vn;
      O.fn = FD;
      objs.push_back(std::move(O));
      const uint32_t f = newCell({(uint32_t)objs.size() - 1, CellKind::Func, 0,
                                  UINT32_MAX, UINT32_MAX, UINT32_MAX,
                                  NF.getCellNode(vn, internName("fn"))});
      objs.back().func = f;
      it->second = f;
    }
    add(n, it->second);
    funcSeeds++;
  }
  auto isOrigin = [&](NodeIndex m) {
    if (!NF.isValueNode(m)) return false;
    if (AllocSites.count(m)) return true;
    const Value *v = NF.getValueForNode(m);
    return v && (isa<AllocaInst>(v) || isa<GlobalVariable>(v));
  };
  std::vector<NodeIndex> members;
  for (uint32_t n = 0; n < G; n++) {
    if (!inGraph[n] || getCanonicalNode(n) != n) continue;
    members.clear();
    collectCanonicalMembers(n, members);
    if (members.empty()) members.push_back(n);
    for (NodeIndex m : members) {
      const bool special = m == NF.getUniversalPtrNode() ||
                           m == NF.getUniversalObjNode();
      if (!special && !isOrigin(m)) continue;
      const uint32_t o = newObj(m, NF.getValueForNode(m));
      add(n, cellAt(o, 0));
      objSeeds++;
    }
  }
  mintCause = "other";

  // A variable index (stride s) from byte x of object o stays in the
  // innermost array holding x, arrays being one element: the same cell
  // when s is a multiple of the element, else the element's positions
  // congruent to x modulo gcd(s, element). An unlabeled object is an array
  // of s-byte elements (stride 1: bytes). An index from an address in no
  // array is undefined behavior: counted, the address stays.
  size_t indexOutsideArray = 0, indexAsOffset = 0, indexStays = 0, leafMerges = 0, byteStepUB = 0,
         byteStepStays = 0, byteStepContainer = 0, byteStepStructRel = 0,
         byteWalkStays = 0, byteWalkStructRel = 0;
  // Sampled undefined-behavior exits: (pointer node, object, position, k).
  std::vector<std::tuple<uint32_t, uint32_t, int64_t, int64_t>> byteStepUBAt;
  // An unlabeled object used as bytes (its first typed use); the leak
  // census re-reads its cells (now byte storage).
  auto markBytes = [&](uint32_t o) {
    if (objs[o].byteAccessed) return;
    objs[o].byteAccessed = true;
    if (leakRefold) leakRefold(o);
  };
  // A T followed by unknown data, accessed at a T stride, is an array of T
  // (plan 3.53, rule 1): the trailing object's cells and addresses fold
  // into the header's element (offset + sizeof T, modulo T), and it
  // forwards to the header from now on. Trailing data typed as something
  // else, or of a learned element size, stays (refused, counted).
  auto extendToArray = [&](uint32_t o) {
    const uint32_t t = objs[o].tailObj;
    if (t != UINT32_MAX && (objs[t].layout || objs[t].period || objs[t].tail ||
                            !objs[t].keyed.empty())) {
      extendRefused++;
      return;
    }
    arraysExtended++;
    if (!CFLCellTraceObj.empty() && describeFn(objs[o]).find(CFLCellTraceObj) != std::string::npos) {
      std::string lab = "?";
      if (curStepLi != UINT32_MAX) {
        const LazyLabel &L = lazyLabels[curStepLi];
        lab = (L.ty ? typeLabel(const_cast<StructType *>(L.ty)) : std::string("untyped")) +
              " stride " + std::to_string(L.stride) + " off " + std::to_string(L.off) +
              (L.arith ? " arith" : "");
      }
      CG_LOG("Cells: EXTEND " << describeFn(objs[o]) << " to an array by step [" << lab << "] at "
             << (curStepDst < G ? nodeDescFn(curStepDst).substr(0, 200) : std::string("?")) << "\n");
    }
    objs[o].tail = false;
    objs[o].tailUnsized = false;
    objs[o].repeats = true;
    objs[o].tailObj = UINT32_MAX;
    if (t != UINT32_MAX) {
      const int64_t d = objs[t].base - objs[o].base; // the header's size
      objs[t].fwd = o;
      objs[t].fwdOff = d;
      // Content: each cell of t merges with the header's cell there.
      std::vector<std::tuple<int64_t, uint32_t, uint32_t>> moved = std::move(objs[t].loadNodes);
      objs[t].loadNodes.clear();
      objs[t].content.clear();
      for (auto &[c, u, pn] : moved) {
        const auto [u2, p2] = contentOf(o, contentKey(objs[o], c + d));
        mergeNodes(u2, u);
        mergeNodes(p2, pn);
      }
      // Addresses: t's become the header's (re-folded by the refold).
      std::vector<std::pair<int64_t, uint32_t>> past(objs[t].offCells.begin(), objs[t].offCells.end());
      objs[t].offCells.clear();
      for (auto &[key, f0] : past) {
        const uint32_t f = findFact(f0);
        const int64_t off = (key >> 1) + d;
        const bool bit = (key & 1) != 0;
        for (Member &mb : memb[f])
          if (mb.first == t) mb = {o, encOff(decOff(mb.second) + d, (mb.second & kFoldedBit) != 0)};
        if (cells[f].obj == t) {
          cells[f].obj = o;
          cells[f].off = off;
        }
        auto it = objs[o].offCells.find(off * 2 + (bit ? 1 : 0));
        if (it == objs[o].offCells.end()) objs[o].offCells[off * 2 + (bit ? 1 : 0)] = f;
        else it->second = mergeFacts(findFact(it->second), f);
      }
      // Its any-offset cell reads and writes all of the array.
      if (objs[t].any != UINT32_MAX) {
        const uint32_t a = anyOf(o);
        addEdge(cells[objs[t].any].store, cells[a].store);
        addEdge(cells[a].load, cells[objs[t].any].load);
      }
    }
    refoldQueue.push_back(o);
  };
  extendToArrayFn = extendToArray;
  // arr: the result is an element address of its byte array (provenance).
  // elem: the element struct the index steps over (typed evidence).
  auto strideCells = [&](uint32_t o, int64_t x, int64_t s,
                         std::vector<uint32_t> &out, bool arr, const StructType *elem) {
    auto folded = [&](uint32_t o2, int64_t at) { return arr ? cellAtArr(o2, at) : cellAt(o2, at); };
    std::tie(o, x) = locate(o, x); // past a header: the trailing object
    if (!objs[o].layout) {
      // A variable byte index into an unlabeled object: any byte of it,
      // its any-offset cell (bytes is not a label). A wider stride: an
      // array of s-byte elements.
      if (s == 1) {
        varByteAny++;
        markBytes(o);
        out.push_back(anyOf(o));
        return;
      }
      requestPeriod(o, s);
      out.push_back(cellAt(o, x));
      return;
    }
    // A T-typed index (over elements of T) on a T followed by unknown data:
    // an array of T. A stride that only equals T's size is no evidence.
    if (objs[o].tail && !objs[o].repeats && elem && elem == objs[o].layout &&
        s % objs[o].size == 0) {
      extendToArray(o);
      std::tie(o, x) = locate(o, x);
    }
    // Still a T followed by data whose size said nothing (no T-typed
    // evidence, or the extension refused): a variable index from the T may
    // reach that data, so it reaches the data's any-offset cell too (the
    // T alone is not known to be an array of one).
    // The same for a T plus data whose size said so (the extension
    // refused): the index may still run past the T.
    const bool tailIndex = objs[o].tail && !objs[o].repeats;
    if (tailIndex) {
      tailIndexAny++;
      out.push_back(anyOf(tailOf(o)));
    }
    Obj &O = objs[o];
    const int64_t pos = ((x % O.size) + O.size) % O.size;
    int64_t b = 0, e = 0;
    if (!innermostArray(O.layout, pos, DL, b, e)) {
      // No array inside the layout holds the address: an array of the
      // layout (a heap array of T) is indexed legally; otherwise what it
      // points to is a single object (the object itself, or one embedded
      // in it), an array of one: the index stays (counted: undefined
      // behavior past element 0).
      if (!O.repeats) indexOutsideArray++;
      // A T followed by data: the index is some element, an address of
      // the implicit array (folded), so a constant step after it (`p[i -
      // 1]`) stays in the element instead of leaving the T.
      out.push_back(tailIndex ? cellAtArr(o, pos) : cellAt(o, pos));
      return;
    }
    if (s % e == 0) { out.push_back(folded(o, pos)); return; }
    const int64_t g = std::gcd(s, e), r0 = (((pos - b) % g) + g) % g;
    for (int64_t j = r0; j < e; j += g) out.push_back(folded(o, b + j));
  };

  // ---- Steps: a field edge maps each cell to the cell(s) at the new
  // offset, through every element its folded offset stands for. ----
  boost::unordered_flat_map<std::tuple<uint32_t, int64_t, uint32_t>,
                            std::vector<uint32_t>,
                            boost::hash<std::tuple<uint32_t, int64_t, uint32_t>>>
      stepMemo;
  size_t stridedUnlabeled = 0, expandCapped = 0, ruleB = 0, stepCalls = 0,
         stepOffsets = 0;
  std::map<std::pair<std::string, std::string>, size_t> ruleBPairs;
  // --cfl-cell-why: the first rule (b) step (pointer node, object, struct).
  struct { uint32_t node = UINT32_MAX, obj; const StructType *ty; } firstRuleB;
  std::vector<int64_t> actual;
  stepOne = [&](uint32_t o, int64_t eoff,
                uint32_t li) -> const std::vector<uint32_t> & {
    const auto key = std::make_tuple(o, eoff, li);
    const int64_t off = decOff(eoff);
    auto [it, ins] = stepMemo.try_emplace(key);
    if (!ins) return it->second;
    std::vector<uint32_t> res;
    stepCalls++;
    // The member's own cell at `off` (an Off cell of object o).
    const Cell C{o, CellKind::Off, off, UINT32_MAX, UINT32_MAX, UINT32_MAX, 0};
    const LazyLabel &L = lazyLabels[li];
    MintCause mc(mintCause,
                 VerboseLevel < 2 ? std::string()
                 : (L.stride ? "stride " + std::to_string(L.stride)
                             : (L.arith ? "arith +" : "member +") +
                                   std::to_string(L.off)) +
                       (objs[C.obj].repeats ? " (heap)" : ""),
                 VerboseLevel >= 2);
    switch (C.kind) {
    case CellKind::Func:
    case CellKind::Any:
    case CellKind::Out:
      llvm_unreachable("stepOne steps offset cells only");
    case CellKind::Off: {
      const Obj &O = objs[C.obj];
      if (!O.layout && L.ty && !L.stride && !L.arith && C.off == 0 && !L.writes)
        readStepsSkipped++; // a read does not label (plan 3.53, rule 1)
      if (!O.layout && L.ty && !L.stride && !L.arith && C.off == 0 && L.writes) {
        // One label per pointer: a cell merged from several objects as
        // bytes, now accessed as struct L.ty, is the conflict itself.
        if (CFLCellOneLabel && curStepFact != UINT32_MAX &&
            memb[curStepFact].size() > 1) {
          if (CFLCellOneLabelMax <= 1)
            pend1({1, curStepNode, 0, curStepFact, L.ty,
                                   "merged from several objects as bytes", pops});
          otherMeets["bytes-then-struct"]++;
        }
        requestLayout(C.obj, const_cast<StructType *>(L.ty));
      }
      if (!O.layout) {
        if (L.stride) {
          stridedUnlabeled++;
          strideCells(C.obj, C.off + L.off, (int64_t)L.stride, res, false, L.elem);
        } else {
          res.push_back(cellAt(C.obj, C.off + L.off));
        }
        break;
      }
      if (L.ty && L.stride == 0 &&
          !structStartsAt(O.layout, C.off, stripStructNameSuffix(L.ty->getName()), DL, L.ty)) {
        if (!ruleB && curStepFact != UINT32_MAX)
          firstRuleB = {curStepNode, C.obj, L.ty};
        ruleB++;
        ruleBPairs[{O.label, stripStructNameSuffix(L.ty->getName()).str()}]++;
        // One label per pointer: a pointer used as L.ty holding an object
        // of another struct is the conflict itself.
        if (CFLCellOneLabel && curStepFact != UINT32_MAX) {
          if (CFLCellOneLabelMax <= 1)
            pend1({1, curStepNode, 0, curStepFact, L.ty,
                                   "of another struct", pops});
          otherMeets["struct-mismatch"]++;
        }
      }
      // A step stays in its array (arrays are one element), so a folded
      // address steps from element 0 like any other: no expansion over the
      // elements it stands for. Leaving the array is undefined behavior.
      actual.clear();
      actual.push_back(C.off);
      stepOffsets += actual.size();
      if (!L.stride) {
        // A constant index on a pointer (p + k, p[k], element > 1 byte)
        // inside an array of that element is array indexing: it stays in
        // the array, which is one element, so the address is the same.
        // Anywhere else it is a byte offset of k elements: -O3 writes a
        // field of the struct a pointer is cast to as an index over the
        // pointer's own type (`gep sqlite3_vtab, %p, 20` for a field of
        // Fts3Table). Byte offsets (gep i8) and member steps move.
        // A folded address of a T followed by data came from a variable
        // index over T: an element of the implicit array of T.
        const bool tailElem = O.tail && (eoff & kFoldedBit) && O.size == (int64_t)L.extent;
        const bool inArray =
            (O.repeats && O.size == (int64_t)L.extent) || tailElem ||
            inArrayOfSize(O.layout, ((C.off % O.size) + O.size) % O.size,
                          (int64_t)L.extent, DL);
        const bool index = L.arith && L.extent > 1 && L.off % L.extent == 0 &&
                           (!O.tail || tailElem) && // &p[1] of a header block: its trailing data
                           inArray;
        if (L.arith && L.extent > 1 && L.off % L.extent == 0 && !O.tail && !inArray &&
            L.off != 0)
          indexAsOffset++;
        if (index && L.off != 0) indexStays++;
        // An untyped constant offset k from inside an array of bytes (n
        // elements; folded, the address stands for every element). Where
        // k moves some element to another (-n < k < n), the address stays
        // in the array. An address of the array as such (provenance: a
        // typed step into it, an index; the folded bit) cannot leave it
        // (C11 6.5.6p8): an exit is followed only to a struct start
        // (container_of), any other is undefined behavior, counted and not
        // followed. A byte address of the object (from its start or a
        // byte offset: -O3 writes fields as byte offsets) may step
        // anywhere in it: the struct-relative target too (plan 3.43).
        {
          int64_t lo = 0, hi = 0, esz = 0;
          const int64_t pos = O.repeats ? ((C.off % O.size) + O.size) % O.size : C.off;
          if (!index && !L.ty && L.off != 0 && !O.tail &&
              innermostArraySpan(O.layout, pos, DL, lo, hi, esz) && esz == 1 &&
              hi - lo > 1) {
            const int64_t n = hi - lo, k = L.off;
            const bool arr = (eoff & kFoldedBit) != 0, stays = k > -n && k < n;
            if (stays) res.push_back(arr ? cellAtArr(C.obj, C.off) : cellAt(C.obj, C.off));
            if (!arr) {
              byteStepStructRel++;
              res.push_back(cellAt(C.obj, C.off + k));
            } else if (stays) {
              byteStepStays++;
            } else {
              const int64_t to = pos + k;
              const int64_t tf = O.repeats ? ((to % O.size) + O.size) % O.size : to;
              if (tf >= 0 && tf < O.size && structAt(O.layout, tf, DL)) {
                byteStepContainer++;
                res.push_back(cellAt(C.obj, C.off + k));
              } else {
                byteStepUB++;
                if (byteStepUBAt.size() < 12) byteStepUBAt.push_back({curStepNode, C.obj, pos, k});
              }
            }
            break;
          }
        }
        for (int64_t a : actual)
          res.push_back(index ? (tailElem ? cellAtArr(C.obj, a) : cellAt(C.obj, a))
                        : L.ty && L.written ? cellAtArr(C.obj, a + L.off) // into an array member as such
                               : cellAt(C.obj, a + L.off));
        break;
      }
      // Strided: a variable index stays in its array (an element address
      // of it: as the source was, or by a written index into the array).
      for (int64_t a : actual)
        strideCells(C.obj, a + L.off, (int64_t)L.stride, res,
                    (eoff & kFoldedBit) || (L.written && L.extent > 0), L.elem);
      break;
    }
    }
    std::sort(res.begin(), res.end());
    res.erase(std::unique(res.begin(), res.end()), res.end());
    auto &slot = stepMemo[key]; // cellAt may rehash
    slot = std::move(res);
    return slot;
  };

  // The objects with the most offset cells (verbose reports).
  auto topObjects = [&](size_t k) {
    std::vector<std::pair<size_t, uint32_t>> big;
    for (uint32_t o = 0; o < objs.size(); o++)
      if (!objs[o].fn) big.push_back({objs[o].offCells.size(), o});
    std::sort(big.rbegin(), big.rend());
    for (size_t i = 0; i < big.size() && i < k; i++) {
      const Obj &O = objs[big[i].second];
      const Value *V = NF.getValueForNode(O.origin);
      std::string where = "<special>";
      if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
        where = (I->getFunction()->getName() + "::" + I->getOpcodeName()).str();
        if (const auto *CB = dyn_cast<CallBase>(I))
          if (const Function *CF = CB->getCalledFunction())
            where += " " + CF->getName().str();
      } else if (V) {
        where = V->getName().str();
      }
      CG_LOG("Cells:   object " << where << " ["
             << (O.layout ? O.label : std::string("unlabeled"))
             << (O.repeats ? " array" : "") << ", " << O.size << " B]: "
             << big[i].first << " offset cells"
             << (O.any != UINT32_MAX ? " + any" : "") << "\n");
    }
  };
  // Where the fact mass is: (node, fact) pairs by the fact's object and
  // cell kind, and how many solver nodes hold some fact of the object.
  auto describe = [&](const Obj &O) {
    const Value *V = NF.getValueForNode(O.origin);
    std::string where = "<special>";
    if (O.fn) return "fn " + O.fn->getName().str();
    if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
      where = (I->getFunction()->getName() + "::" + I->getOpcodeName()).str();
      if (const auto *CB = dyn_cast<CallBase>(I))
        if (const Function *CF = CB->getCalledFunction())
          where += " " + CF->getName().str();
    } else if (V) {
      where = V->getName().str();
    }
    return where + (O.parentObj != UINT32_MAX ? " tail@" + std::to_string(O.base) : "") +
           " [" + (O.layout ? (O.ident.empty() ? O.label : O.ident + " as " + O.label) : std::string("unlabeled")) +
           (O.repeats ? " array" : "") + "]";
  };
  describeFn = describe;
  auto massByObject = [&](size_t k) {
    std::vector<uint64_t> mass(objs.size(), 0), holders(objs.size(), 0);
    uint64_t byKind[5] = {0, 0, 0, 0, 0};
    std::vector<uint32_t> seen(objs.size(), UINT32_MAX);
    for (uint32_t m = 0; m < numNodes; m++)
      pts[m].forEach([&](uint32_t f) {
        const Cell &C = cells[f];
        mass[C.obj]++;
        byKind[(int)C.kind]++;
        if (seen[C.obj] != m) { seen[C.obj] = m; holders[C.obj]++; }
      });
    CG_LOG("Cells: mass by kind: function " << byKind[0] << ", offset "
           << byKind[1] << ", any " << byKind[2] << ", outside "
           << byKind[3] << ", residue " << byKind[4] << "\n");
    std::vector<std::pair<uint64_t, uint32_t>> top;
    for (uint32_t o = 0; o < objs.size(); o++) top.push_back({mass[o], o});
    std::sort(top.rbegin(), top.rend());
    for (size_t i = 0; i < top.size() && i < k; i++) {
      const Obj &O = objs[top[i].second];
      CG_LOG("Cells:   mass " << top[i].first << " in "
             << holders[top[i].second] << " nodes: " << describe(O) << ", "
             << O.offCells.size() << " cells\n");
    }
    if (top.empty()) return;
    // The holders of the heaviest object, by function and node kind.
    const uint32_t o0 = top[0].second;
    std::map<std::string, size_t> byFn, byKindH;
    for (uint32_t m = 0; m < numNodes; m++) {
      bool has = false;
      pts[m].forEach([&](uint32_t f) { has |= cells[f].obj == o0; });
      if (!has) continue;
      std::string fn = "<none>", kind = m < G ? "graph" : "cell/collector";
      if (m < G) {
        const Value *V = NF.getValueForNode(m);
        if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
          fn = I->getFunction()->getName().str();
          kind = I->getOpcodeName();
        } else if (const auto *A = dyn_cast_or_null<Argument>(V)) {
          fn = A->getParent()->getName().str();
          kind = "formal";
        } else if (NF.isDereferenceNode(m) || NF.isObjectNode(m)) {
          kind = "hub";
          const NodeIndex par = NF.getDerefParent(m);
          if (par != AndersNodeFactory::InvalidIndex)
            if (const auto *I = dyn_cast_or_null<Instruction>(
                    NF.getValueForNode(par)))
              fn = I->getFunction()->getName().str();
        } else if (NF.isReturnNode(m) || NF.isVarargNode(m)) {
          kind = NF.isReturnNode(m) ? "return" : "vararg";
          fn = cast<Function>(V)->getName().str();
        } else if (V) {
          kind = "value";
        }
      }
      byFn[fn]++;
      byKindH[kind]++;
    }
    std::string kl;
    for (auto &[kk, c] : byKindH) kl += " " + kk + "=" + std::to_string(c);
    CG_LOG("Cells:   holders of the heaviest object by kind:" << kl << "\n");
    std::vector<std::pair<size_t, std::string>> fns;
    for (auto &[fn, c] : byFn) fns.push_back({c, fn});
    std::sort(fns.rbegin(), fns.rend());
    std::string fl;
    for (size_t i = 0; i < fns.size() && i < 25; i++)
      fl += " " + fns[i].second + "(" + std::to_string(fns[i].first) + ")";
    CG_LOG("Cells:   ... by function (" << fns.size() << "):" << fl << "\n");
  };
  auto interiorReport = [&]() {
    std::vector<std::pair<size_t, std::string>> top;
    for (auto &[k, c] : interiorBy) top.push_back({c, k});
    std::sort(top.rbegin(), top.rend());
    std::string line;
    for (size_t i = 0; i < top.size() && i < 12; i++)
      line += " [" + top[i].second + "] " + std::to_string(top[i].first);
    CG_LOG("Cells: " << interiorCells << " interior cells (inside a scalar "
           << "member), " << beyondLabel << " heap offsets past the label "
           << "folded back; minted by:" << line << "\n");
  };
  whyIsAny = [&](uint32_t f) { return f < cells.size() && cells[f].kind == CellKind::Any; };
  if (recordWhy) {
    const std::string want = StringRef(CFLCellWhy).starts_with("any:")
                                 ? CFLCellWhy.substr(4) : std::string(CFLCellWhy);
    whyWanted = [&, want, cache = std::vector<int8_t>()](uint32_t f) mutable {
      // Several objects: alternatives separated by '|'.
      auto is = [&](uint32_t o) {
        if (o >= cache.size()) cache.resize(objs.size() + 64, -1);
        if (cache[o] < 0) {
          const std::string d = describe(objs[o]);
          bool hit = false;
          for (StringRef alt : llvm::split(StringRef(want), '|'))
            hit |= !alt.empty() && d.find(alt.str()) != std::string::npos;
          cache[o] = hit;
        }
        return cache[o] == 1;
      };
      if (f >= cells.size()) return false;
      if (is(cells[f].obj)) return true;
      for (auto [o, e] : memb[f])
        if (is(o)) return true;
      return false;
    };
  }
  // ---- Method dispatch (--cfl-cell-receivers) ----
  // A method call (*(p.path.slot))(.., p, ..) (dispatchReceiver; the graph
  // does not wire the receiver argument): each object o at p reaches the
  // receiver formal only of the methods its own path leads to (C:
  // p->f(p), p->ops->f(p); C++: p->vptr[k](p)). Level nodes per (site,
  // receiver cell, level) collect the content loaded at that level: a
  // holder arriving at a level steps to the next level's slot; a function
  // arriving at the last level gets the receiver. A site whose step at
  // some level is not a field step of the graph passes every receiver to
  // every method (the plain wiring, counted).
  // The byte offset an address adds to its base pointer (0: the pointer
  // itself), INT64_MIN when not constant; through a chain of constant
  // GEPs (a field of an embedded struct, as dispatchReceiver steps it).
  auto slotOffset = [&](const Value *Slot) -> int64_t {
    int64_t off = 0;
    const Value *X = Slot->stripPointerCasts();
    while (const auto *G = dyn_cast<GEPOperator>(X)) {
      APInt A(64, 0);
      if (!G->accumulateConstantOffset(DL, A)) return INT64_MIN;
      off += A.getSExtValue();
      X = G->getPointerOperand()->stripPointerCasts();
    }
    return off;
  };
  struct RecvSite {
    const CallBase *cs;
    unsigned k;
    uint32_t base, callee;
    // Per level: the field steps from the level's pointer to the address
    // loaded, one per GEP of the chain (empty: the pointer itself).
    std::vector<std::vector<uint32_t>> lis;
    bool all = false;          // every receiver to every method
    std::string sig;           // the path's shape (types and constant indices)
    const Value *slot0;        // the address loaded at level 0
  };
  // guard: UINT32_MAX for a call's dispatch, else the holder guard whose
  // admission this level chain decides.
  struct LevelKey { uint32_t si, f, level, guard = UINT32_MAX; };
  std::vector<RecvSite> recvSites;
  boost::unordered_flat_map<uint32_t, std::vector<uint32_t>> recvAt; // base -> sites
  boost::unordered_flat_map<uint64_t, uint32_t> recvLevel; // (site, receiver, level) -> node
  // level node -> site, receiver cell (UINT32_MAX: every receiver), level
  boost::unordered_flat_map<uint32_t, LevelKey> dispatchOf;
  size_t recvUnstepped = 0, recvNoNode = 0, recvBound = 0, recvLevels = 0;
  if (CFLCellReceivers) {
    std::vector<std::pair<const Value *, const Value *>> path;
    for (const CallBase *CS : icallsSorted) {
      const int k = dispatchReceiver(CS, &path);
      if (k < 0) continue;
      const NodeIndex bn = NF.getValueNodeFor(path[0].first),
                      cn = NF.getValueNodeFor(CS->getCalledOperand());
      if (bn == AndersNodeFactory::InvalidIndex || cn == AndersNodeFactory::InvalidIndex) {
        recvNoNode++; // no facts at p or at the callee: nothing to pass
        continue;
      }
      RecvSite R{CS, (unsigned)k, find(canon(bn)), find(canon(cn)), {}};
      R.slot0 = path[0].second;
      R.sig = std::to_string(k);
      for (auto [V, Slot] : path) {
        // The shape by byte offsets: linking renames a struct per unit.
        R.sig += "|" + std::to_string(slotOffset(Slot));
        // The addresses stepped to, the loaded one first: a chain of GEPs
        // when the field is in a struct embedded in the object.
        std::vector<const Value *> addrs{Slot};
        bool constStep = false;
        for (const Value *X = Slot->stripPointerCasts(); const auto *G = dyn_cast<GEPOperator>(X);) {
          X = G->getPointerOperand()->stripPointerCasts();
          if (X == V) break;
          constStep |= isa<Constant>(X); // a constant GEP of a global: no node to step (plain wiring)
          addrs.push_back(X);
        }
        if (constStep) {
          R.all = true;
          R.lis.push_back({});
          continue;
        }
        std::vector<uint32_t> steps;
        const Value *B = V;
        for (auto ait = addrs.rbegin(); ait != addrs.rend(); ++ait) {
          const NodeIndex vn = NF.getValueNodeFor(B), sn = NF.getValueNodeFor(*ait);
          bool stepped = vn != AndersNodeFactory::InvalidIndex &&
                         (sn == AndersNodeFactory::InvalidIndex ||
                          find(canon(sn)) == find(canon(vn)));
          if (!stepped && vn != AndersNodeFactory::InvalidIndex)
            for (const FieldEdge &e : fieldOut[find(canon(vn))])
              if (!e.walk && find(e.dst) == find(canon(sn))) {
                steps.push_back(e.li);
                stepped = true;
                break;
              }
          R.all |= !stepped;
          B = *ait;
        }
        R.lis.push_back(std::move(steps));
      }
      const uint32_t si = recvSites.size();
      recvSites.push_back(R);
      recvLevels += R.lis.size();
      if (R.all) {
        // Every receiver to every method: the callee's content, all of p.
        recvUnstepped++;
        const uint32_t P = newNode();
        dispatchOf[P] = {si, UINT32_MAX, (uint32_t)R.lis.size() - 1};
        addEdge(R.callee, P);
        continue;
      }
      recvAt[R.base].push_back(si);
    }
  }
  // Holder g at level L of site si for receiver f: g's slot content into
  // the level node.
  boost::unordered_flat_map<uint64_t, uint32_t> guardLevel; // (guard, holder, level) -> node
  auto linkLevel = [&](uint32_t si, uint32_t f, uint32_t level, uint32_t g,
                       uint32_t guard = UINT32_MAX) {
    const RecvSite &R = recvSites[si];
    const Cell &C = cells[g];
    if (C.kind == CellKind::Func || C.kind == CellKind::Out) return; // no slot
    std::vector<uint32_t> slots{g};
    for (uint32_t li : R.lis[level]) { // each field step of the level's chain
      std::vector<uint32_t> next;
      for (uint32_t c : slots) {
        const CellKind ck = cells[c].kind;
        if (ck == CellKind::Any) { next.push_back(c); continue; }
        if (ck == CellKind::Func || ck == CellKind::Out) continue; // no slot
        for (size_t i = 0; i < memb[c].size(); i++) {
          const Member mb = memb[c][i];
          const std::vector<uint32_t> &S = stepOne(mb.first, mb.second, li);
          next.insert(next.end(), S.begin(), S.end());
        }
      }
      slots.swap(next);
    }
    auto &M = guard == UINT32_MAX ? recvLevel : guardLevel;
    const uint64_t key =
        ((uint64_t)(guard == UINT32_MAX ? si : guard) << 40) ^ ((uint64_t)level << 32) ^ f;
    auto [it, ins] = M.try_emplace(key, 0);
    if (ins) {
      it->second = newNode();
      dispatchOf[it->second] = {si, f, level, guard};
      if (level == 0 && guard == UINT32_MAX) recvBound++;
    }
    const uint32_t P = it->second;
    for (uint32_t r : slots) {
      r = findFact(r);
      const CellKind k = cells[r].kind;
      if (k == CellKind::Off || k == CellKind::Any) addEdge(cells[r].load, P);
    }
  };
  auto bindReceiver = [&](uint32_t si, uint32_t f) { linkLevel(si, f, 0, f); };
  // After a cycle collapse: a site whose p merged into another node is
  // keyed by the representative, and that node's facts are dispatched.
  auto rekeyReceivers = [&]() {
    if (recvAt.empty()) return;
    recvAt.clear();
    for (uint32_t si = 0; si < recvSites.size(); si++) {
      RecvSite &R = recvSites[si];
      if (R.all || !R.cs) continue; // plain edges: merges keep them; guard pseudo sites
      const uint32_t b = find(R.base);
      const bool moved = b != R.base;
      R.base = b;
      recvAt[b].push_back(si);
      if (moved) {
        std::vector<uint32_t> fs;
        pts[b].forEach([&](uint32_t f) { fs.push_back(findFact(f)); });
        for (uint32_t f : fs) bindReceiver(si, f);
      }
    }
  };
  std::function<void(uint32_t, uint32_t, uint32_t)> guardAdmit; // guard, holder, function
  // A method first delivered by a dispatch site during the solve: its
  // holder guards are installed then (set below), not one iteration late.
  std::function<void(uint32_t, const Function *)> onDispatchTarget;
  auto dispatch = [&](uint32_t P, const std::vector<uint32_t> &dlt) {
    const LevelKey K = dispatchOf[P];
    const RecvSite &R = recvSites[K.si];
    if (K.level + 1 < R.lis.size()) { // holders: on to the next level
      for (uint32_t g : dlt) linkLevel(K.si, K.f, K.level + 1, g, K.guard);
      return;
    }
    if (K.guard != UINT32_MAX) {
      for (uint32_t F : dlt)
        if (cells[F].kind == CellKind::Func) guardAdmit(K.guard, K.f, F);
      return;
    }
    for (uint32_t F : dlt) {
      if (cells[F].kind != CellKind::Func) continue;
      const Function *Fn = objs[cells[F].obj].fn;
      if (!Fn || Fn->isDeclaration() || R.k >= Fn->arg_size()) continue;
      if (!isCompatible(R.cs, Fn)) continue; // not a target (the answers' rule)
      const NodeIndex fv = NF.getValueNodeFor(Fn->getArg(R.k));
      if (fv == AndersNodeFactory::InvalidIndex) continue;
      uint32_t formal = find(canon(fv));
      if (onDispatchTarget) onDispatchTarget(K.si, Fn);
      if (trackWhy) curWhy = {R.base, K.f, F, W_DISPATCH};
      // Plan 3.54: into a split formal, only a test site's receiver enters
      // directly (with the formal's own term); a call passing a method
      // formal's object on enters through its channel (3.54 (b)); any other
      // dispatch is an other entry.
      if (!entryOfA.empty())
        if (auto eit = entryOfA.find(canon(fv)); eit != entryOfA.end()) {
          const uint32_t fy = eit->second;
          const auto &E = taggedEntryFormals[fy];
          auto sit = taggedEntrySites.find(R.cs);
          const bool test = K.f != UINT32_MAX && R.k == E.k && sit != taggedEntrySites.end() &&
                            sit->second.first == E.S && E.Ds.count(sit->second.second);
          if (test) {
            entryF[fy].testEntries++;
            entryTestFn(fy, K.f);
          } else if (const int64_t fx = chanFor(R.cs, R.k, fy); fx >= 0) {
            if ((uint32_t)fx == fy) continue; // its own object, already at its formal
            formal = find(chanNode((uint32_t)fx, fy));
          } else
            formal = find(entryF[fy].Ao);
        }
      if (K.f == UINT32_MAX) addEdge(R.base, formal);
      else add(formal, K.f);
    }
  };
  // Holder guards: a method F reached only through dispatch sites of one
  // path shape reloads the level-1 holder from its receiver formal
  // (`entropy = (phuff_entropy_ptr) cinfo->entropy` in a method fetched
  // from cinfo->entropy->start_pass): that load yields only holders whose
  // own path leads to F. A holder is held at the load until F arrives at
  // its slot. Premise (recorded): the path is not rewritten between the
  // method's fetch and its reload in F.
  struct Guard { const Function *F; uint32_t si, node; std::vector<uint32_t> held; bool dropped = false; };
  std::vector<Guard> guards;
  boost::unordered_flat_set<uint64_t> guardAdmitted, guardSeen; // (guard, holder)
  size_t guardHeldFacts = 0, guardDropped = 0, guardRefused = 0;
  std::vector<std::string> guardRefusedAt;
  // Is V the receiver formal A of its function: A itself, or a reload of
  // a non-escaping stack slot whose only store stores A.
  auto isFormalValue = [](const Value *V, const Argument *A) {
    V = V->stripPointerCasts();
    if (V == A) return true;
    const auto *L = dyn_cast<LoadInst>(V);
    if (!L) return false;
    const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
    if (!S) return false;
    const StoreInst *only = nullptr;
    for (const User *U : S->users()) {
      if (isa<LoadInst>(U)) continue;
      const auto *SI = dyn_cast<StoreInst>(U);
      if (!SI || SI->getPointerOperand() != S || SI->getValueOperand() == S) return false;
      if (only) return false;
      only = SI;
    }
    return only && only->getValueOperand()->stripPointerCasts() == A;
  };
  auto sameSlotShape = [&](const Value *X, const Value *Y) {
    const int64_t a = slotOffset(X);
    return a != INT64_MIN && a == slotOffset(Y);
  };
  // Pointer slots a function may write, itself or through its callees
  // (direct calls and the previous iterations' resolved targets): a slot
  // is (struct name, byte offset); name "" = an untyped write at that
  // offset (any struct); allWrites = a memcpy/memset into non-local memory.
  // Bodiless functions write nothing (premise, counted). Used to check the
  // guards' premise: no write of the guarded path between the check (the
  // dispatch or the identity test) and the reload.
  struct ModSet { std::set<std::pair<std::string, int64_t>> slots; bool all = false; };
  boost::unordered_flat_map<const Function *, ModSet> modOf;
  // Premises, counted: writes into untyped memory (a byte or pointer
  // buffer, a memcpy/memset whose destination has no struct type) do not
  // hit a struct's pointer slot; bodiless functions write no slot.
  size_t modBodiless = 0, modUntypedWrites = 0;
  // The struct slots a write at Addr of Len bytes may hit: (S, off) per
  // 8-byte word, (S, -1) = some slot of S (a variable index inside S);
  // false = untyped memory (counted premise).
  auto writeSlots = [&](const Value *Addr, int64_t Len,
                        std::vector<std::pair<std::string, int64_t>> &out) {
    const Value *X = Addr->stripPointerCasts();
    const auto *G = dyn_cast<GEPOperator>(X);
    if (!G) return false;
    const auto *ST = dyn_cast<StructType>(G->getSourceElementType());
    if (!ST || !ST->hasName()) return false;
    const std::string S = stripStructNameSuffix(ST->getName()).str();
    APInt Ap(64, 0);
    if (!G->accumulateConstantOffset(DL, Ap) || Len < 0) {
      out.push_back({S, -1});
      return true;
    }
    const int64_t o = Ap.getSExtValue();
    for (int64_t w = o & ~(int64_t)7; w < o + std::max<int64_t>(Len, 1); w += 8) out.push_back({S, w});
    return true;
  };
  auto slotKey = [&](const Value *Addr, std::pair<std::string, int64_t> &key) {
    const Value *X = Addr->stripPointerCasts();
    key = {"", 0};
    if (const auto *G = dyn_cast<GEPOperator>(X)) {
      APInt Ap(64, 0);
      if (!G->accumulateConstantOffset(DL, Ap)) return false;
      key.second = Ap.getSExtValue();
      if (const auto *ST = dyn_cast<StructType>(G->getSourceElementType()))
        if (ST->hasName()) key.first = stripStructNameSuffix(ST->getName()).str();
    }
    return true;
  };
  auto slotMatches = [](const std::pair<std::string, int64_t> &w,
                        const std::pair<std::string, int64_t> &slot) {
    if (w.second == -1 || slot.second == -1) return w.first == slot.first;
    return w.second == slot.second &&
           (w.first.empty() || slot.first.empty() || w.first == slot.first);
  };
  bool modBuilt = false;
  auto buildMod = [&]() {
    if (modBuilt) return;
    modBuilt = true;
    boost::unordered_flat_map<const Function *, std::vector<const Function *>> calls;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (F.isDeclaration()) continue;
        ModSet &MS = modOf[&F];
        for (Instruction &I : instructions(F)) {
          if (const auto *SI = dyn_cast<StoreInst>(&I)) {
            const Type *VT = SI->getValueOperand()->getType();
            if (!VT->isPointerTy() && !(VT->isIntegerTy(64))) continue;
            if (isa<AllocaInst>(SI->getPointerOperand()->stripPointerCasts())) continue;
            std::pair<std::string, int64_t> k;
            std::vector<std::pair<std::string, int64_t>> ws;
            if (slotKey(SI->getPointerOperand(), k)) MS.slots.insert(k);
            else if (writeSlots(SI->getPointerOperand(), -1, ws)) MS.slots.insert(ws.begin(), ws.end());
            else modUntypedWrites++;
            continue;
          }
          const auto *CB = dyn_cast<CallBase>(&I);
          if (!CB) continue;
          if (const Function *C = CB->getCalledFunction()) {
            const StringRef N = C->getName();
            if (N.starts_with("llvm.memcpy") || N.starts_with("llvm.memmove") ||
                N.starts_with("llvm.memset") || N == "memcpy" || N == "memmove" || N == "memset") {
              const Value *D = CB->getArgOperand(0);
              if (isa<AllocaInst>(D->stripPointerCasts())) continue;
              int64_t len = -1;
              if (CB->arg_size() >= 3)
                if (const auto *CI = dyn_cast<ConstantInt>(CB->getArgOperand(2))) len = CI->getSExtValue();
              std::vector<std::pair<std::string, int64_t>> ws;
              if (writeSlots(D, len, ws)) MS.slots.insert(ws.begin(), ws.end());
              else modUntypedWrites++;
              continue;
            }
            if (C->isDeclaration()) { modBodiless++; continue; }
            calls[&F].push_back(C);
            continue;
          }
          auto cit = Ctx->Callees.find(CB);
          if (cit != Ctx->Callees.end())
            for (const Function *C : cit->second)
              if (!C->isDeclaration()) calls[&F].push_back(C);
        }
      }
    for (bool grew = true; grew;) {
      grew = false;
      for (auto &[F, cs] : calls) {
        ModSet &MS = modOf[F];
        for (const Function *C : cs) {
          const ModSet &CM = modOf[C];
          if (CM.all && !MS.all) { MS.all = true; grew = true; }
          for (const auto &k : CM.slots)
            if (MS.slots.insert(k).second) grew = true;
        }
      }
    }
  };
  auto mayWrite = [&](const Function *F, const std::pair<std::string, int64_t> &slot) {
    auto it = modOf.find(F);
    if (it == modOf.end()) return false;
    if (it->second.all) return true;
    for (const auto &w : it->second.slots)
      if (slotMatches(w, slot)) return true;
    return false;
  };
  // Does instruction K (in a function body) possibly write the slot?
  auto instWrites = [&](const Instruction &K, const std::pair<std::string, int64_t> &slot) {
    if (const auto *SI = dyn_cast<StoreInst>(&K)) {
      if (isa<AllocaInst>(SI->getPointerOperand()->stripPointerCasts())) return false;
      const Type *VT = SI->getValueOperand()->getType();
      if (!VT->isPointerTy() && !VT->isIntegerTy(64)) return false;
      std::pair<std::string, int64_t> k;
      if (slotKey(SI->getPointerOperand(), k)) return slotMatches(k, slot);
      std::vector<std::pair<std::string, int64_t>> ws;
      if (!writeSlots(SI->getPointerOperand(), -1, ws)) return false; // untyped (premise)
      for (const auto &w : ws)
        if (slotMatches(w, slot)) return true;
      return false;
    }
    const auto *CB = dyn_cast<CallBase>(&K);
    if (!CB) return false;
    if (const Function *C = CB->getCalledFunction()) {
      const StringRef N = C->getName();
      if (N.starts_with("llvm.memcpy") || N.starts_with("llvm.memmove") ||
          N.starts_with("llvm.memset") || N == "memcpy" || N == "memmove" || N == "memset") {
        const Value *D = CB->getArgOperand(0);
        if (isa<AllocaInst>(D->stripPointerCasts())) return false;
        int64_t len = -1;
        if (CB->arg_size() >= 3)
          if (const auto *CI = dyn_cast<ConstantInt>(CB->getArgOperand(2))) len = CI->getSExtValue();
        std::vector<std::pair<std::string, int64_t>> ws;
        if (!writeSlots(D, len, ws)) return false; // untyped (premise)
        for (const auto &w : ws)
          if (slotMatches(w, slot)) return true;
        return false;
      }
      return mayWrite(C, slot);
    }
    auto cit = Ctx->Callees.find(CB);
    if (cit == Ctx->Callees.end()) return false;
    for (const Function *C : cit->second)
      if (mayWrite(C, slot)) return true;
    return false;
  };
  size_t guardModFallback = 0;
  // A guard needs a node of its own: every value in the node's class is
  // the guarded value R, a no-op cast of it, or a phi of only those (global
  // dedup merges loads of one pointer class and one-input phis; a guard on
  // a shared node would filter every value of the class).
  size_t guardClassShared = 0;
  auto classOnly = [&](NodeIndex rn, const Value *R) {
    auto mit = canonicalClassMembers.find(getCanonicalNode(rn));
    if (mit == canonicalClassMembers.end()) return true; // a singleton
    for (NodeIndex m : mit->second) {
      const Value *V = NF.getValueForNode(m);
      if (!V) { guardClassShared++; return false; }
      if (V->stripPointerCasts() == R) continue;
      if (const auto *Ph = dyn_cast<PHINode>(V)) {
        bool all = true;
        for (const Value *In : Ph->incoming_values()) all &= In->stripPointerCasts() == R;
        if (all) continue;
      }
      guardClassShared++;
      return false;
    }
    return true;
  };
  // Callers of each function (the previous iterations' call graph).
  boost::unordered_flat_map<const Function *, std::vector<const CallBase *>> callers;
  boost::unordered_flat_map<const CallBase *, uint32_t> siteOf;
  boost::unordered_flat_set<const Function *> done; // guard decided for F
  // Holder guards for method F delivered by dispatch site si: every call of
  // F is a dispatch site of si's path shape (no direct call), F's writes
  // do not include the path's level-0 slot (the receivers premise,
  // checked), and each reload of that slot from the receiver formal is
  // its own node. live: during the solve (the method was just delivered);
  // the reload's node must still be empty, and a later dispatch of F with
  // another shape drops the guards (held facts released).
  boost::unordered_flat_map<const Function *, std::string> guardSig;
  size_t guardsLive = 0, guardsLiveDropped = 0;
  auto hasDirectCaller = [](const Function *F) {
    for (const User *U : F->users())
      if (const auto *CB = dyn_cast<CallBase>(U))
        if (CB->getCalledOperand()->stripPointerCasts() == F) return true;
    return false;
  };
  std::function<void(uint32_t, const Function *, bool)> tryHolderGuards =
      [&](uint32_t si, const Function *F, bool live) {
    const RecvSite &R = recvSites[si];
    if (R.all || !R.cs || R.lis.size() < 2) return;
    if (!done.insert(F).second || F->isDeclaration() || R.k >= F->arg_size()) return;
    bool uniform = !hasDirectCaller(F); // every call of F: a dispatch site of this shape
    const CallBase *breaker = nullptr;
    for (const CallBase *C : callers[F]) {
      auto sit = siteOf.find(C);
      const bool ok = sit != siteOf.end() && !recvSites[sit->second].all &&
                      recvSites[sit->second].sig == R.sig;
      if (!ok && !breaker) breaker = C;
      uniform &= ok;
    }
    if (uniform) {
      // The premise: F (and its callees) never rewrite the path's level-0
      // slot, so a reload inside F sees the holder the method came from.
      buildMod();
      std::pair<std::string, int64_t> slot0;
      if (!slotKey(R.slot0, slot0) || mayWrite(F, slot0)) {
        guardModFallback++;
        if (guardRefusedAt.size() < 400)
          guardRefusedAt.push_back(F->getName().str() + ": may write the dispatch path's slot " +
                                   slot0.first + "+" + std::to_string(slot0.second) +
                                   " (receiver premise fails; no guard)");
        return;
      }
    }
    if (!uniform) {
      guardRefused++;
      if (guardRefusedAt.size() < 400) {
        auto sit = breaker ? siteOf.find(breaker) : siteOf.end();
        guardRefusedAt.push_back(F->getName().str() + " (shape " + R.sig + "): called at " +
                                 (breaker ? instLoc(breaker) : std::string("a direct call")) +
                                 (sit == siteOf.end() ? " (not a method call)"
                                                      : " (shape " + recvSites[sit->second].sig + ")"));
      }
      return;
    }
    guardSig[F] = R.sig;
    const Argument *A = F->getArg(R.k);
    for (const Instruction &I : instructions(*F)) {
      const auto *L = dyn_cast<LoadInst>(&I);
      if (!L || !L->getType()->isPointerTy() || !sameSlotShape(L->getPointerOperand(), R.slot0))
        continue;
      const Value *B = L->getPointerOperand()->stripPointerCasts();
      if (const auto *G = dyn_cast<GEPOperator>(B)) B = G->getPointerOperand();
      if (!isFormalValue(B, A)) continue;
      const NodeIndex ln = NF.getValueNodeFor(L);
      if (ln == AndersNodeFactory::InvalidIndex) continue;
      const uint32_t n = find(canon(ln));
      if (n >= guardIdx.size() || guardIdx[n] != UINT32_MAX || !classOnly(ln, L)) continue;
      if (live && pts[n].count()) continue; // facts arrived before the method did
      guardIdx[n] = guards.size();
      guards.push_back({F, si, n, {}});
      guardsLive += live;
    }
  };
  if (CFLCellReceivers && !recvSites.empty()) {
    for (auto &[CS, FS] : Ctx->Callees)
      for (const Function *F : FS) callers[F].push_back(CS);
    for (auto &[F, cs] : callers) // stable: Callees iterates in pointer order
      std::sort(cs.begin(), cs.end(), [&](const CallBase *a, const CallBase *b) { return stableKey(a) < stableKey(b); });
    for (uint32_t si = 0; si < recvSites.size(); si++)
      if (recvSites[si].cs) siteOf[recvSites[si].cs] = si;
    guardIdx.assign(numNodes, UINT32_MAX);
    for (uint32_t si = 0; si < recvSites.size(); si++) {
      const RecvSite &R = recvSites[si];
      if (R.all || R.lis.size() < 2) continue;
      auto cit = Ctx->Callees.find(R.cs);
      if (cit == Ctx->Callees.end()) continue;
      for (const Function *F : cit->second) tryHolderGuards(si, F, false);
    }
    CG_LOG("Cells: holder guards: " << guards.size() << " reloads guarded; "
           << guardModFallback << " methods that may rewrite the path (premise checked: no guard); "
           << modBodiless << " calls of bodiless functions and " << modUntypedWrites
           << " untyped writes assumed to write no struct slot; "
           << guardClassShared << " reloads not guarded (node shared by dedup); "
           << guardRefused << " methods refused (a call of another shape):\n");
    for (const std::string &d : guardRefusedAt) CG_LOG("Cells:   refused " << d << "\n");
    onDispatchTarget = [&](uint32_t si, const Function *F) {
      const RecvSite &R = recvSites[si];
      if (R.all || !R.cs || R.lis.size() < 2) return;
      auto git = guardSig.find(F);
      if (git != guardSig.end()) {
        if (git->second.empty() || git->second == R.sig) return;
        // Another shape delivers F: its guards are void; release what they held.
        git->second.clear();
        for (Guard &Gd : guards) {
          if (Gd.F != F || Gd.dropped) continue;
          Gd.dropped = true;
          guardsLiveDropped++;
          admitting = true;
          for (uint32_t f : Gd.held) add(Gd.node, f);
          admitting = false;
        }
        return;
      }
      if (!done.count(F)) tryHolderGuards(si, F, true);
    };
  }
  // Method-identity checks (the program's own RTTI with a method pointer
  // as the tag): `if (h->slot != Fn) <never returns>` where h = B->path
  // (jdatadst.c: cinfo->dest->init_destination != init_mem_destination ->
  // ERREXIT). A reload of B->path that every path from the function's
  // entry reaches only through the test's equal edge or a store into
  // B->path (in that function) admits only the stored objects and holders
  // whose slot holds Fn. "Never returns": an unreachable, a call to a
  // noreturn function, or a call whose resolved targets all never return.
  boost::unordered_flat_map<uint32_t, uint32_t> passOf; // pass node -> guard
  size_t idTests = 0, idGuards = 0, idUngated = 0, idShared = 0;
  std::vector<std::string> idGuardAt, idTestAt;
  if (CFLCellReceivers && !guardIdx.empty()) {
    auto neverReturns = [&](const Function *F) {
      if (F->doesNotReturn()) return true;
      if (F->isDeclaration()) return false;
      for (const BasicBlock &BB : *F)
        if (isa<ReturnInst>(BB.getTerminator())) return false;
      return true;
    };
    auto deadCall = [&](const Instruction &I) {
      const auto *CB = dyn_cast<CallBase>(&I);
      if (!CB) return false;
      if (CB->doesNotReturn()) return true;
      if (const Function *C = CB->getCalledFunction()) return neverReturns(C);
      auto cit = Ctx->Callees.find(CB);
      if (cit == Ctx->Callees.end() || cit->second.empty()) return false;
      for (const Function *C : cit->second)
        if (!neverReturns(C)) return false;
      return true;
    };
    // The same base pointer anywhere in a function: one SSA value, or loads
    // of a non-escaping stack slot stored exactly once.
    auto sameBase = [](const Value *A, const Value *B) {
      A = A->stripPointerCasts();
      B = B->stripPointerCasts();
      if (A == B) return true;
      const auto *LA = dyn_cast<LoadInst>(A), *LB = dyn_cast<LoadInst>(B);
      if (!LA || !LB) return false;
      const auto *S = dyn_cast<AllocaInst>(LA->getPointerOperand()->stripPointerCasts());
      if (!S || S != LB->getPointerOperand()->stripPointerCasts()) return false;
      unsigned stores = 0;
      for (const User *U : S->users()) {
        if (isa<LoadInst>(U)) continue;
        const auto *SI = dyn_cast<StoreInst>(U);
        if (!SI || SI->getPointerOperand() != S || SI->getValueOperand() == S) return false;
        stores++;
      }
      return stores == 1;
    };
    // An address as (base, constant offset).
    auto splitAddr = [&](const Value *A, const Value *&base, int64_t &off) {
      const Value *X = A->stripPointerCasts();
      off = 0;
      if (const auto *G = dyn_cast<GEPOperator>(X)) {
        APInt Ap(64, 0);
        if (!G->accumulateConstantOffset(DL, Ap)) return false;
        off = Ap.getSExtValue();
        X = G->getPointerOperand()->stripPointerCasts();
      }
      base = X;
      return true;
    };
    auto samePath = [&](const Value *A1, const Value *A2) {
      const Value *b1, *b2;
      int64_t o1, o2;
      return splitAddr(A1, b1, o1) && splitAddr(A2, b2, o2) && o1 == o2 && sameBase(b1, b2);
    };
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        for (Instruction &I : instructions(F)) {
          const auto *C = dyn_cast<ICmpInst>(&I);
          if (!C || !C->isEquality()) continue;
          const Function *Fn = nullptr;
          const LoadInst *LM = nullptr;
          for (unsigned i = 0; i < 2; i++) {
            const Value *X = C->getOperand(i)->stripPointerCasts(),
                        *Y = C->getOperand(1 - i)->stripPointerCasts();
            if (isa<Function>(X) && isa<LoadInst>(Y)) {
              Fn = cast<Function>(X);
              LM = cast<LoadInst>(Y);
            }
          }
          if (!Fn || !LM) continue;
          const Value *Hb;
          int64_t m;
          if (!splitAddr(LM->getPointerOperand(), Hb, m)) continue;
          const auto *LH = dyn_cast<LoadInst>(Hb); // the holder: B->path
          if (!LH || !LH->getType()->isPointerTy()) continue;
          const auto *Br = dyn_cast_or_null<BranchInst>(C->getNextNode());
          if (!Br || !Br->isConditional() || Br->getCondition() != C) continue;
          idTests++;
          size_t tCand = 0, tGuard = 0, tUngated = 0, tShared = 0;
          const BasicBlock *eqSucc =
              Br->getSuccessor(C->getPredicate() == ICmpInst::ICMP_EQ ? 0 : 1);
          const Value *path = LH->getPointerOperand();
          // The slot step from the holder (none at offset 0).
          const NodeIndex hn = NF.getValueNodeFor(LH),
                          sn = NF.getValueNodeFor(LM->getPointerOperand());
          if (hn == AndersNodeFactory::InvalidIndex) continue;
          uint32_t li = UINT32_MAX;
          if (m != 0) {
            if (sn == AndersNodeFactory::InvalidIndex) continue;
            for (const FieldEdge &e : fieldOut[find(canon(hn))])
              if (!e.walk && find(e.dst) == find(canon(sn))) { li = e.li; break; }
            if (li == UINT32_MAX) continue;
          }
          // Stores into the path in F: their values pass the guard.
          std::vector<const StoreInst *> pathStores;
          for (Instruction &J : instructions(F))
            if (const auto *SI = dyn_cast<StoreInst>(&J))
              if (SI->getValueOperand()->getType()->isPointerTy() &&
                  samePath(SI->getPointerOperand(), path))
                pathStores.push_back(SI);
          // Every reload of the path gated by the test or a path store.
          for (Instruction &J : instructions(F)) {
            // A reload of the path, or the holder's SSA copy at the test's
            // equal successor (Driver: splitIdentityTests).
            const Instruction *R = nullptr;
            if (const auto *Ld = dyn_cast<LoadInst>(&J)) {
              if (Ld != LH && Ld->getType()->isPointerTy() &&
                  samePath(Ld->getPointerOperand(), path))
                R = Ld;
            } else if (const auto *Ph = dyn_cast<PHINode>(&J)) {
              if (Ph->getMetadata("ka.idcopy") && Ph->getNumIncomingValues() == 1 &&
                  Ph->getIncomingValue(0) == LH)
                R = Ph;
            }
            if (!R) continue;
            tCand++;
            // Walk from the entry with a state: gated after the test's equal
            // edge or a store into the path (its value passes), ungated again
            // at anything that may write the path (another store, a call whose
            // writes include the slot). Reaching R ungated fails.
            buildMod();
            std::pair<std::string, int64_t> pslot;
            if (!slotKey(path, pslot)) { idUngated++; tUngated++; continue; }
            bool reached = false;
            std::vector<std::pair<const BasicBlock *, bool>> work{{&F.getEntryBlock(), false}};
            boost::unordered_flat_set<uint64_t> seen;
            auto key = [](const BasicBlock *B, bool g) { return (uint64_t)(uintptr_t)B * 2 + g; };
            seen.insert(key(&F.getEntryBlock(), false));
            while (!work.empty() && !reached) {
              auto [X, gated] = work.back();
              work.pop_back();
              bool stop = false;
              for (const Instruction &K : *X) {
                if (&K == R) { if (!gated) reached = true; stop = true; break; }
                if (const auto *SI = dyn_cast<StoreInst>(&K))
                  if (std::find(pathStores.begin(), pathStores.end(), SI) != pathStores.end()) {
                    gated = true;
                    continue;
                  }
                if (deadCall(K)) { stop = true; break; }
                if (gated && instWrites(K, pslot)) gated = false;
              }
              if (stop) continue;
              const Instruction *T = X->getTerminator();
              for (unsigned k = 0; k < T->getNumSuccessors(); k++) {
                const BasicBlock *S = T->getSuccessor(k);
                const bool g = gated || (T == Br && S == eqSucc);
                if (seen.insert(key(S, g)).second) work.push_back({S, g});
              }
            }
            if (reached) { idUngated++; tUngated++; continue; }
            const NodeIndex rn = NF.getValueNodeFor(R);
            if (rn == AndersNodeFactory::InvalidIndex) continue;
            const uint32_t n = find(canon(rn));
            // The guarded value must be its own node: a node shared with
            // the tested holder (or another value) would filter them too.
            if (n == find(canon(hn))) {
              idShared++;
              tShared++;
              continue;
            }
            if (n >= guardIdx.size() || guardIdx[n] != UINT32_MAX || !classOnly(rn, R)) {
              idShared++;
              tShared++;
              continue;
            }
            tGuard++;
            // A pseudo site: level 1 steps the holder to the tested slot.
            RecvSite PS{nullptr, 0, n, n, {{}, {li}}};
            const uint32_t si = recvSites.size();
            recvSites.push_back(PS);
            const uint32_t gi = guards.size();
            guardIdx[n] = gi;
            guards.push_back({Fn, si, n, {}});
            idGuards++;
            if (idGuardAt.size() < 12)
              idGuardAt.push_back(instLoc(R) + " admits holders whose slot +" +
                                  std::to_string(m) + " holds " + Fn->getName().str());
            for (const StoreInst *SI : pathStores) {
              const NodeIndex vn = NF.getValueNodeFor(SI->getValueOperand());
              if (vn == AndersNodeFactory::InvalidIndex) continue;
              const uint32_t P = newNode();
              passOf[P] = gi;
              addEdge(find(canon(vn)), P);
            }
          }
          if (idTestAt.size() < 40)
            idTestAt.push_back(instLoc(C) + " (== " + Fn->getName().str() + "): " +
                               std::to_string(tCand) + " reloads, " + std::to_string(tGuard) +
                               " guarded, " + std::to_string(tUngated) + " reachable around, " +
                               std::to_string(tShared) + " shared");
        }
      }
    CG_LOG("Cells: method-identity tests: " << idTests << " (h->slot ==/!= function); "
           << idGuards << " reloads guarded, " << idUngated
           << " reloads reachable around the test (not guarded), " << idShared
           << " not guarded (node shared with the holder or another guard)\n");
    for (const std::string &d : idGuardAt) CG_LOG("Cells:   " << d << "\n");
    for (const std::string &d : idTestAt) CG_LOG("Cells:   identity test " << d << "\n");
  }
  guardHold = [&](uint32_t gi, uint32_t n, uint32_t f) {
    Guard &Gd = guards[gi];
    if (!guardSeen.insert((uint64_t)gi << 32 | f).second && !Gd.dropped &&
        !guardAdmitted.count((uint64_t)gi << 32 | f))
      return; // already held
    if (Gd.dropped || guardAdmitted.count((uint64_t)gi << 32 | f)) {
      admitting = true;
      add(n, f);
      admitting = false;
      return;
    }
    if (cells[f].kind == CellKind::Func || cells[f].kind == CellKind::Out) {
      Gd.held.push_back(f); // no slot: never admitted (counted)
      guardHeldFacts++;
      return;
    }
    Gd.held.push_back(f);
    guardHeldFacts++;
    linkLevel(Gd.si, f, 1, f, gi);
  };
  // A guarded node merged into another (a cycle): the guard is dropped and
  // its held facts are released (more facts, sound).
  auto dropMergedGuards = [&]() {
    for (uint32_t gi = 0; gi < guards.size(); gi++) {
      Guard &Gd = guards[gi];
      if (Gd.dropped || find(Gd.node) == Gd.node) continue;
      Gd.dropped = true;
      guardDropped++;
      admitting = true;
      for (uint32_t f : Gd.held) add(Gd.node, f);
      admitting = false;
    }
  };
  guardAdmit = [&](uint32_t gi, uint32_t f, uint32_t F) {
    Guard &Gd = guards[gi];
    if (objs[cells[F].obj].fn != Gd.F) return;
    if (!guardAdmitted.insert((uint64_t)gi << 32 | f).second) return;
    admitting = true;
    add(Gd.node, f);
    admitting = false;
  };

  // Watched stores: each root's node; a root with no node is refused
  // (no facts can tell which objects its stores write).
  size_t watchNoNode = 0;
  std::string watchNoNodeAt;
  if (!taggedPairs.empty()) {
    for (uint32_t wi = 0; wi < taggedWatches.size(); wi++) {
      const NodeIndex vn = NF.getValueNodeFor(taggedWatches[wi].root);
      if (vn == AndersNodeFactory::InvalidIndex) {
        if (!watchNoNode++) watchNoNodeAt = instLoc(taggedWatches[wi].at);
        continue;
      }
      watchAt[find(canon(vn))].push_back(wi);
    }
    if (watchNoNode)
      for (size_t pi = 0; pi < taggedPairs.size(); pi++)
        flipPair(pi, "a watched store whose root has no node, e.g. " + watchNoNodeAt);
    for (auto &[n, ws] : watchAt)
      pts[n].forEach([&](uint32_t f) { pend[n].push_back(f); push(n); });
  }
  // Alias assumptions: per assumption and per access set, the content
  // keys of each object seen on its side (-1: any position).
  std::vector<boost::unordered_flat_map<uint32_t, std::vector<int64_t>>> asmIdKeys(taggedAssumes.size()),
      asmAccKeys(taggedAccessSets.size());
  std::vector<std::vector<uint32_t>> asmPairs(taggedAssumes.size()), setAssumes(taggedAccessSets.size());
  size_t asmUsed = 0, asmFailed = 0, asmNoNode = 0;
  std::vector<char> asmFailedAt(taggedAssumes.size(), 0);
  std::vector<boost::unordered_flat_map<uint32_t, uint32_t>> asmAccFirst(taggedAccessSets.size()); // obj -> access
  std::vector<std::string> asmFailSites;
  if (!taggedPairs.empty()) {
    std::set<uint32_t> used, sets;
    for (uint32_t pi = 0; pi < taggedPairAssumes.size(); pi++)
      for (uint32_t a : taggedPairAssumes[pi]) {
        asmPairs[a].push_back(pi);
        if (used.insert(a).second) {
          setAssumes[taggedAssumes[a].accSet].push_back(a);
          sets.insert(taggedAssumes[a].accSet);
        }
      }
    asmUsed = used.size();
    auto failAll = [&](uint32_t a, const std::string &why) {
      if (!asmFailedAt[a]) { asmFailedAt[a] = 1; asmFailed++; }
      for (uint32_t pi : asmPairs[a]) flipPair(pi, why);
    };
    for (uint32_t a : used) {
      const NodeIndex vn = NF.getValueNodeFor(taggedAssumes[a].id);
      if (vn == AndersNodeFactory::InvalidIndex) {
        asmNoNode++;
        failAll(a, "alias assumption at " + taggedAssumes[a].site + ": its object has no node");
        continue;
      }
      asmAt[find(canon(vn))].push_back({a, true, taggedAssumes[a].field, false});
    }
    for (uint32_t si : sets)
      for (const TaggedAccess &A : taggedAccessSets[si]) {
        const NodeIndex bn = NF.getValueNodeFor(A.base);
        if (bn == AndersNodeFactory::InvalidIndex) {
          asmNoNode++;
          for (uint32_t a : setAssumes[si]) failAll(a, "alias assumption at " + taggedAssumes[a].site +
                                                           ": an access with no node");
          continue;
        }
        asmAt[find(canon(bn))].push_back({si, false, A.k, A.var,
                                          (uint32_t)(&A - &taggedAccessSets[si][0])});
      }
    for (auto &[n, es] : asmAt)
      pts[n].forEach([&](uint32_t f) { pend[n].push_back(f); push(n); });
  }
  asmCheck = [&](const AsmEntry &E, uint32_t f) {
    const Cell &C = cells[f];
    if (C.kind == CellKind::Func || C.kind == CellKind::Out) return;
    for (const Member &mb : memb[f]) {
      const uint32_t o = mb.first;
      int64_t key = -1;
      if (C.kind != CellKind::Any && !E.var && objs[o].layout) {
        const int64_t pos = decOff(mb.second) + E.off;
        if (!(objs[o].tail && (pos >= objs[o].size || pos < 0))) key = contentKey(objs[o], pos);
      }
      auto meets = [&](const std::vector<int64_t> &ks) {
        for (int64_t k : ks)
          if (k == key || k == -1 || key == -1) return true;
        return false;
      };
      auto fail = [&](uint32_t a) {
        std::string detail;
        if (!asmFailedAt[a]) {
          asmFailedAt[a] = 1;
          asmFailed++;
          {
            const TaggedAssume &TA = taggedAssumes[a];
            std::string acc = "?";
            if (auto it = asmAccFirst[TA.accSet].find(o); it != asmAccFirst[TA.accSet].end()) {
              const TaggedAccess &X = taggedAccessSets[TA.accSet][it->second];
              std::string v;
              raw_string_ostream os(v);
              X.base->printAsOperand(os, false);
              const auto *BI = dyn_cast<Instruction>(X.base);
              acc = os.str() + (BI ? " in " + BI->getFunction()->getName().str() : std::string()) + " +" +
                    std::to_string(X.k);
            }
            std::string idv;
            raw_string_ostream os2(idv);
            TA.id->printAsOperand(os2, false);
            const auto *II = dyn_cast<Instruction>(TA.id);
            const auto *IA = dyn_cast<Argument>(TA.id);
            detail = TA.site + ": object " + describe(objs[o]) + " reaches the walked pointer " + os2.str() +
                     (II ? " (" + II->getFunction()->getName().str() + ")"
                         : IA ? " (arg of " + IA->getParent()->getName().str() + ")" : std::string()) +
                     " and an access " + acc + " of the field at +" + std::to_string(TA.field);
            if (asmFailSites.size() < 40) asmFailSites.push_back(detail);
          }
        }
        for (uint32_t pi : asmPairs[a])
          if (!taggedFlipped.count({taggedPairs[pi].S, taggedPairs[pi].F}))
            flipPair(pi, "alias assumption failed at " + (detail.empty() ? taggedAssumes[a].site : detail));
      };
      if (E.idSide) {
        if (asmFailedAt[E.idx]) continue;
        auto &mine = asmIdKeys[E.idx][o];
        if (std::find(mine.begin(), mine.end(), key) != mine.end()) continue;
        mine.push_back(key);
        auto it = asmAccKeys[taggedAssumes[E.idx].accSet].find(o);
        if (it != asmAccKeys[taggedAssumes[E.idx].accSet].end() && meets(it->second)) fail(E.idx);
      } else {
        auto &mine = asmAccKeys[E.idx][o];
        if (std::find(mine.begin(), mine.end(), key) != mine.end()) continue;
        mine.push_back(key);
        asmAccFirst[E.idx].try_emplace(o, E.acc);
        for (uint32_t a : setAssumes[E.idx]) {
          if (asmFailedAt[a]) continue;
          auto it = asmIdKeys[a].find(o);
          if (it != asmIdKeys[a].end() && meets(it->second)) fail(a);
        }
      }
    }
  };
  watchCheck = [&](uint32_t wi, uint32_t f) {
    const TaggedWatch &W = taggedWatches[wi];
    const Cell &C = cells[f];
    if (C.kind == CellKind::Func || C.kind == CellKind::Out) return;
    for (const Member &mb : std::vector<Member>(memb[f])) {
      uint32_t o = mb.first;
      int64_t lo = decOff(mb.second) + W.lo, hi = decOff(mb.second) + W.hi + W.w;
      const bool all = W.unb || C.kind == CellKind::Any ||
                       ((mb.second & kFoldedBit) && (W.lo || W.hi));
      // Through the header into trailing objects.
      for (int d = 0; d < 16; d++) {
        if (!objs[o].layout) {
          watchPending[o].push_back({wi, f});
          break;
        }
        flipCovered(o, lo, hi, all, W.at);
        if (!objs[o].tail || (!all && hi <= objs[o].size)) break;
        const int64_t sz = objs[o].size;
        o = tailOf(o);
        lo = std::max<int64_t>(lo - sz, 0);
        hi -= sz;
      }
    }
  };

  // ---- Propagation (difference propagation over a worklist) ----
  const auto tSolve = Clock::now();
  uint64_t walkSteps = 0;
  size_t hubLinks = 0, funcDerefs = 0, outDerefs = 0;
  auto linkHub = [&](uint32_t h, uint32_t f) {
    MintCause mc(mintCause, "hub link", VerboseLevel >= 2);
    const Cell &C = cells[findFact(f)];
    if (C.kind == CellKind::Func) { funcDerefs++; return; }
    if (C.kind == CellKind::Out) { outDerefs++; return; }
    hubLinks++;
    uint32_t ld = C.load, st = C.store;
    auto kit = cellHubKey.find(h);
    if (kit != cellHubKey.end() && !entryOfKey.empty())
      if (auto eh = entryOfKey.find(kit->second); eh != entryOfKey.end()) {
        // A method's entry-keyed read (plan 3.54), its other side: an
        // object that entered the formal other than by a test dispatch or
        // a channel is read unkeyed; one that came through a channel reads
        // the keys its terms admit (3.54 (b)); the link points are kept for
        // the terms or the other entries still to come.
        const uint32_t j = eh->second, fi = taggedEntryReads.at(taggedEntryReadList[j]);
        EntryF &ef = entryF[fi];
        const std::vector<Member> ms = memb[findFact(f)];
        bool now = ef.poisoned || C.kind != CellKind::Off;
        if (!now)
          for (auto [o, e] : ms) now |= ef.other.count(o) != 0;
        if (now) {
          addEdge(ld, h);
          return;
        }
        for (auto [o, e] : ms) {
          ef.held[o].push_back({h, f, j});
          if (auto tit = ef.terms.find(o); tit != ef.terms.end())
            for (uint32_t t : std::vector<uint32_t>(tit->second)) termLinkFn(fi, j, h, f, o, t);
        }
        return;
      }
    if (kit != cellHubKey.end() && C.kind == CellKind::Off) {
      // A keyed union access: its key's cell, for every member object
      // (an object not yet labeled waits).
      for (auto [o, e] : memb[findFact(f)]) {
        if (!objs[o].layout) {
          keyedWait[o].push_back({h, f});
          keyedWaits++;
          continue;
        }
        const uint32_t K = keyedOf(o, contentKey(objs[o], decOff(e)), kit->second);
        addEdge(K, h);
        if (storeHub[h] != UINT32_MAX) addEdge(storeHub[h], K);
      }
      return;
    }
    addEdge(ld, h);
    if (storeHub[h] != UINT32_MAX) addEdge(storeHub[h], st);
  };
  linkHubFn = linkHub;
  // Plan 3.54: object bookkeeping of the split formals.
  // Read j of formal fi, at hub h, for object o of fact f, under term t (a
  // formal whose method X the object's entry tested, 3.54 (b)): the keys of
  // the writers a test D == X admits, for each D of X's tests; every writer
  // when one of them is not keyed for the read.
  termLinkFn = [&](uint32_t fi, uint32_t j, uint32_t h, uint32_t f, uint32_t o, uint32_t t) {
    if (t == fi) return; // its own test: the read's own keys
    EntryF &ef = entryF[fi];
    const auto &ET = taggedEntryFormals[t];
    auto tk = taggedEntryTermKeys.find(taggedEntryReadList[j]);
    std::vector<uint32_t> kids;
    bool all = ET.Ds.empty() || tk == taggedEntryTermKeys.end();
    for (int64_t D : ET.Ds) {
      if (all) break;
      auto dit = tk->second.find(D);
      if (dit == tk->second.end()) { all = true; break; }
      auto xit = dit->second.find(ET.M);
      if (xit == dit->second.end()) { all = true; break; } // every writer
      for (const std::string &kn : xit->second) kids.push_back(NF.internCellName(kn));
    }
    ef.termLinks++;
    if (all || !objs[o].layout) {
      addEdge(cells[findFact(f)].load, h);
      return;
    }
    const std::vector<Member> ms = memb[findFact(f)];
    for (auto [o2, e] : ms) {
      if (o2 != o) continue;
      for (uint32_t kid : kids) addEdge(keyedOf(o, contentKey(objs[o], decOff(e)), kid), h);
    }
  };
  std::function<void(uint32_t, uint32_t)> entryOtherObj = [&](uint32_t fi, uint32_t o) {
    EntryF &ef = entryF[fi];
    if (!ef.other.insert(o).second) return;
    if (auto hit = ef.held.find(o); hit != ef.held.end()) {
      const auto hs = std::move(hit->second);
      ef.held.erase(hit);
      for (auto [h, f0, j] : hs) {
        addEdge(cells[findFact(f0)].load, h);
        ef.flushed++;
      }
    }
    if (auto sit = ef.subs.find(o); sit != ef.subs.end())
      for (uint32_t z : std::vector<uint32_t>(sit->second)) entryOtherObj(z, o);
  };
  std::function<void(uint32_t, uint32_t, uint32_t)> entryTermObj = [&](uint32_t fi, uint32_t o, uint32_t t) {
    EntryF &ef = entryF[fi];
    if (ef.other.count(o)) return; // read unkeyed already, and so are those it was passed to
    auto &ts = ef.terms[o];
    if (std::find(ts.begin(), ts.end(), t) != ts.end()) return;
    ts.push_back(t);
    if (auto hit = ef.held.find(o); hit != ef.held.end())
      for (auto [h, f0, j] : std::vector<std::array<uint32_t, 3>>(hit->second)) termLinkFn(fi, j, h, f0, o, t);
    if (auto sit = ef.subs.find(o); sit != ef.subs.end())
      for (uint32_t z : std::vector<uint32_t>(sit->second)) entryTermObj(z, o, t);
  };
  entryOtherFn = [&](uint32_t fi, uint32_t f) {
    entryF[fi].otherEntries++;
    for (auto [o, e] : std::vector<Member>(memb[findFact(f)])) entryOtherObj(fi, o);
  };
  entryTestFn = [&](uint32_t fi, uint32_t f) {
    for (auto [o, e] : std::vector<Member>(memb[findFact(f)])) entryTermObj(fi, o, fi);
  };
  // An object arriving through the channel X -> Y takes X's state for it
  // (and Y follows X's later changes): other at X (or X not split, or no
  // state there) is other at Y; else X's terms.
  chanArriveFn = [&](uint32_t fx, uint32_t fy, uint32_t f) {
    EntryF &X = entryF[fx];
    entryF[fy].chanEntries++;
    for (auto [o, e] : std::vector<Member>(memb[findFact(f)])) {
      auto &sb = X.subs[o];
      if (std::find(sb.begin(), sb.end(), fy) == sb.end()) sb.push_back(fy);
      auto tit = X.terms.find(o);
      if (X.poisoned || X.other.count(o) || tit == X.terms.end() || tit->second.empty()) {
        entryOtherObj(fy, o);
        continue;
      }
      for (uint32_t t : std::vector<uint32_t>(tit->second)) entryTermObj(fy, o, t);
    }
  };
  entryPoison = [&](uint32_t fi, const std::string &why) { // with the flush
    EntryF &ef = entryF[fi];
    if (ef.poisoned) return;
    ef.poisoned = true;
    ef.why = why;
    for (auto &[o, hs] : ef.held)
      for (auto [h, f0, j] : hs) {
        addEdge(cells[findFact(f0)].load, h);
        ef.flushed++;
      }
    ef.held.clear();
    for (auto &[o, zs] : std::vector<std::pair<uint32_t, std::vector<uint32_t>>>(ef.subs.begin(), ef.subs.end()))
      for (uint32_t z : zs) entryOtherObj(z, o);
  };
  // A cell merge: a cell at an other-entry node, or at a channel, now
  // stands for more objects.
  entryMergedFn = [&](uint32_t a, uint32_t b) {
    for (uint32_t fi = 0; fi < entryF.size(); fi++) {
      EntryF &ef = entryF[fi];
      if (ef.poisoned || ef.Ao == UINT32_MAX) continue;
      const uint32_t ao = find(ef.Ao);
      if (pts[ao].test(a) || pts[ao].test(b)) entryOtherFn(fi, a);
    }
    for (auto &[cn, xy] : chanOfNode) {
      const uint32_t c = find(cn);
      if (pts[c].test(a) || pts[c].test(b)) chanArriveFn(xy.first, xy.second, a);
    }
  };
  // The keyed accesses still waiting at the fixpoint, on objects never
  // labeled: linked unkeyed (the solve goes on from them).
  auto flushKeyedWait = [&]() {
    for (auto &[o, ws] : keyedWait)
      for (auto [h, f0] : ws) {
        const uint32_t f = findFact(f0);
        addEdge(cells[f].load, h);
        if (storeHub[h] != UINT32_MAX) addEdge(storeHub[h], cells[f].store);
        keyedFlushed++;
      }
    keyedWait.clear();
  };
  // The any-offset cells of every object a cell stands for, into dst.
  auto toAny = [&](uint32_t f, uint32_t dst) {
    anyCause = "field-any loop";
    anyCauseNode = dst;
    if (cells[f].kind == CellKind::Out) return; // outside stays outside
    std::vector<uint32_t> &W = anyDst[f];
    if (std::find(W.begin(), W.end(), dst) != W.end()) return;
    W.push_back(dst);
    for (size_t i = 0; i < memb[f].size(); i++)
      add(dst, anyOf(memb[f][i].first));
  };
  // A step of cell f along label li into dst: every member object steps
  // (recorded, so members that join f later are stepped too).
  auto applyStep = [&](uint32_t f, uint32_t li, uint32_t dst) {
    const Cell &C = cells[f];

    if (C.kind == CellKind::Func || C.kind == CellKind::Any) {
      add(dst, f);
      return;
    }
    if (C.kind == CellKind::Out) { // outside the object stays outside
      add(dst, f);
      return;
    }
    anyCause = "step";
    stepDst[f].push_back((uint64_t)find(dst) << 32 | li);
    curStepFact = f;
    for (size_t i = 0; i < memb[f].size(); i++) {
      const Member mb = memb[f][i];
      const std::vector<uint32_t> &R = stepOne(mb.first, mb.second, li);
      for (size_t j = 0; j < R.size(); j++) add(dst, R[j]);
    }
  };
  // A walk (a field edge on a cycle whose steps have gcd g): the walking
  // pointer reaches the object's offsets congruent modulo g, so g becomes
  // the object's period and the walk lands on the start's residue cell.
  // A walk (a field edge on a cycle) is an index stepping by the gcd of
  // the cycle's steps: it stays in its array like any variable index.
  std::vector<uint32_t> walkOut;
  walkOne = [&](uint32_t o, int64_t c, uint32_t li, int64_t g, uint32_t dst) {
    walkOut.clear();
    // An index walk (p++) stays where it is; a member-step walk moves by
    // its member offset first. An untyped offset walking from inside a
    // byte array (bufpt[-1] in a loop) is an index of the array: it stays
    // in it (plan 3.43); a byte address of the object also moves
    // struct-relative, an address of the array as such does not.
    const LazyLabel &L = lazyLabels[li];
    const bool arr = (c & kFoldedBit) != 0;
    if (!L.ty && !L.arith && !L.stride && L.off != 0) {
      const auto [lo2, at] = locate(o, decOff(c));
      const Obj &O = objs[lo2];
      int64_t lo = 0, hi = 0, esz = 0;
      const int64_t pos = O.layout && O.repeats ? ((at % O.size) + O.size) % O.size : at;
      if (O.layout && !O.tail && pos >= 0 && pos < O.size &&
          innermostArraySpan(O.layout, pos, DL, lo, hi, esz) && esz == 1 && hi - lo > 1) {
        strideCells(o, decOff(c), g, walkOut, arr, L.elem);
        if (arr) byteWalkStays++;
        else {
          byteWalkStructRel++;
          strideCells(o, decOff(c) + L.off, g, walkOut, false, L.elem);
        }
        for (uint32_t f2 : walkOut) add(dst, f2);
        return;
      }
    }
    strideCells(o, decOff(c) + (L.arith || L.stride ? 0 : L.off), g, walkOut, arr, L.elem);
    for (uint32_t f2 : walkOut) add(dst, f2);
  };
  auto applyWalk = [&](uint32_t f, const FieldEdge &e) {
    const Cell &C = cells[f];
    if (C.kind == CellKind::Func || C.kind == CellKind::Any) {
      add(e.dst, f);
      return;
    }
    if (C.kind == CellKind::Out) {
      add(e.dst, f);
      return;
    }
    walkSteps++;
    std::vector<FieldEdge> &W = walkDst[f];
    for (const FieldEdge &w : W)
      if (w.dst == e.dst && w.li == e.li && w.walk == e.walk) return;
    W.push_back(e);
    for (size_t i = 0; i < memb[f].size(); i++) {
      const Member mb = memb[f][i];
      walkOne(mb.first, mb.second, e.li, e.walk, e.dst);
    }
  };
  // Pointer nodes with equal sets (no function among them: answers stay
  // as computed) merge into one node.
  size_t ptrMerges = 0;
  auto mergeEqualSets = [&]() {
    std::vector<uint32_t> buf;
    auto canonSet = [&](uint32_t u, bool &hasFn) {
      buf.clear();
      hasFn = false;
      pts[u].forEach([&](uint32_t f) {
        f = findFact(f);
        hasFn |= cells[f].kind == CellKind::Func;
        buf.push_back(f);
      });
      std::sort(buf.begin(), buf.end());
      buf.erase(std::unique(buf.begin(), buf.end()), buf.end());
    };
    boost::unordered_flat_map<uint64_t, std::vector<uint32_t>> groups;
    for (uint32_t u = 0; u < G; u++) {
      if (find(u) != u || isHub[u] || pts[u].count() == 0) continue;
      bool hasFn;
      canonSet(u, hasFn);
      if (hasFn) continue;
      uint64_t h = buf.size();
      for (uint32_t f : buf) h = (h ^ f) * 0x9E3779B97F4A7C15ull;
      groups[h].push_back(u);
    }
    std::vector<uint32_t> first, touched;
    for (auto &[h, U] : groups) {
      if (U.size() < 2) continue;
      bool hasFn;
      canonSet(U[0], hasFn);
      first = buf;
      for (size_t i = 1; i < U.size(); i++) {
        canonSet(U[i], hasFn);
        if (buf != first) continue; // hash collision
        absorb(find(U[0]), U[i]);
        ptrMerges++;
        touched.push_back(find(U[0]));
      }
    }
    std::sort(touched.begin(), touched.end());
    touched.erase(std::unique(touched.begin(), touched.end()), touched.end());
    for (uint32_t r : touched) finalize(r);
  };
  // Sets still holding ids that unification retired: rewrite them to the
  // survivors (equivalent content, smaller sets). Pending deltas are
  // mapped when popped.
  size_t retiredDropped = 0;
  auto canonicalizeSets = [&]() {
    std::vector<uint32_t> buf;
    for (uint32_t u = 0; u < numNodes; u++) {
      if (find(u) != u || pts[u].count() == 0) continue;
      bool stale = false;
      pts[u].forEach([&](uint32_t f) { stale |= findFact(f) != f; });
      if (!stale) continue;
      buf.clear();
      pts[u].forEach([&](uint32_t f) { buf.push_back(findFact(f)); });
      const size_t before = pts[u].count();
      pts[u] = Facts();
      for (uint32_t f : buf) pts[u].set(f);
      retiredDropped += before - pts[u].count();
    }
  };
  // Backward path from `target` to the origin of an object whose
  // description contains `want`, through nodes holding one of its cells
  // (copy and hub edges, field steps).
  auto factDescP = [&](uint32_t f) -> std::string {
    const Cell &C = cells[f];
    std::string k = C.kind == CellKind::Off ? NF.cellNameString(C.name)
                    : C.kind == CellKind::Func ? "fn " + objs[C.obj].fn->getName().str()
                    : C.kind == CellKind::Any ? "*" : "out";
    return k + " @" + std::to_string(C.off) + " of " + describe(objs[C.obj]);
  };
  boost::unordered_flat_map<NodeIndex, std::pair<NodeIndex, uint32_t>> keyedPtrOf;
  std::function<std::string(uint32_t)> nodeDesc;
  nodeDescFn = [&](uint32_t m) { return nodeDesc(m); };
  nodeDesc = [&](uint32_t m) -> std::string {
    if (m >= G) {
      for (uint32_t f = 0; f < cells.size(); f++) {
        const Cell &C = cells[f];
        if (C.store != m && C.load != m) continue;
        std::string k = C.kind == CellKind::Any ? "*" :
                        C.kind == CellKind::Off ? NF.cellNameString(C.name) : "?";
        return "cell " + k + (C.kind == CellKind::Any
                                  ? (C.store == m ? " (write)" : " (read)")
                                  : "") +
               " of " + describe(objs[C.obj]);
      }
      // A content cell's view: U (unkeyed writes), P (every member), or
      // a key's cell K.
      for (uint32_t o = 0; o < objs.size(); o++) {
        for (auto &[c, up] : objs[o].content)
          if (up.first == m || up.second == m)
            return "content " + cellName(o, c) +
                   (up.first == up.second ? ""
                    : up.first == m      ? " (U)"
                                         : " (P)") +
                   " #" + std::to_string(m) + " of " + describe(objs[o]);
        for (auto &[kk, kn] : objs[o].keyed)
          if (kn == m)
            return "content " + cellName(o, (int64_t)(uint32_t)(kk >> 32)) +
                   " (K " + NF.cellNameString((uint32_t)kk) + ") #" +
                   std::to_string(m) + " of " + describe(objs[o]);
      }
      for (uint32_t h = 0; h < G; h++)
        if (storeHub[h] == m)
          return "<stores through hub #" + std::to_string(h) + " #" +
                 std::to_string(m) + ">";
      return "<store collector #" + std::to_string(m) + ">";
    }
    const Value *V = NF.getValueForNode(m);
    std::string k;
    if (const auto *I = dyn_cast_or_null<Instruction>(V)) {
      std::string is;
      raw_string_ostream os(is);
      I->print(os);
      k = (I->getFunction()->getName() + ": " ).str() + os.str().substr(0, 140);
    } else if (const auto *A = dyn_cast_or_null<Argument>(V)) {
      k = (A->getParent()->getName() + " arg" + Twine(A->getArgNo())).str();
    } else if (NF.isObjectNode(m) && NF.getDerefParent(m) == AndersNodeFactory::InvalidIndex) {
      // An object's own memory node (a global, stack slot or allocation).
      const Value *OV = NF.getValueForNode(m);
      k = "memory of ";
      if (const auto *I = dyn_cast_or_null<Instruction>(OV))
        k += I->getFunction()->getName().str() + "::" + I->getOpcodeName();
      else if (OV)
        k += OV->getName().str();
      else
        k += "#" + std::to_string(m);
    } else if (NF.isDereferenceNode(m) || NF.isObjectNode(m)) {
      // A keyed union access (--cfl-union-keys=tag) has a dereference
      // node of its own, without a parent in the factory: its pointer and
      // key come from keyedDerefOf.
      if (keyedPtrOf.empty())
        for (const auto &[pk, d] : keyedDerefOf) keyedPtrOf.emplace(d, pk);
      NodeIndex par = NF.getDerefParent(m);
      std::string key;
      if (par == AndersNodeFactory::InvalidIndex)
        if (auto it = keyedPtrOf.find(m); it != keyedPtrOf.end()) {
          par = it->second.first;
          key = " key " + NF.cellNameString(it->second.second);
        }
      assert(par != AndersNodeFactory::InvalidIndex && "a hub without a pointer");
      k = "hub of #" + std::to_string(par) + key;
      if (const auto *I = dyn_cast_or_null<Instruction>(NF.getValueForNode(par)))
        k += " (" + I->getFunction()->getName().str() + ")";
      else if (const auto *A = dyn_cast_or_null<Argument>(NF.getValueForNode(par)))
        k += " (" + A->getParent()->getName().str() + " arg" + std::to_string(A->getArgNo()) + ")";
    } else if (NF.isReturnNode(m)) {
      k = "return of " + cast<Function>(V)->getName().str();
    } else if (NF.isVarargNode(m)) {
      k = "vararg of " + cast<Function>(V)->getName().str();
    } else if (V) {
      k = V->getName().str();
    } else {
      k = "<node #" + std::to_string(m) + ">";
    }
    return k;
  };
  std::function<void(uint32_t, const std::string &, int)> tracePathD;
  auto tracePath = [&](uint32_t target, const std::string &want) {
    tracePathD(target, want, 0);
  };
  tracePathD = [&](uint32_t target, const std::string &want, int depth) {
    const std::string ind(depth * 2, ' ');
    std::vector<char> objWant(objs.size(), 0);
    for (uint32_t o = 0; o < objs.size(); o++)
      objWant[o] = describe(objs[o]).find(want) != std::string::npos;
    auto holds = [&](uint32_t m) {
      bool h = false;
      pts[m].forEach([&](uint32_t f) {
        for (auto [o, off] : memb[findFact(f)]) h |= objWant[o];
      });
      return h;
    };
    std::vector<std::vector<uint32_t>> rev(numNodes);
    for (uint32_t u = 0; u < numNodes; u++) {
      if (find(u) != u) continue;
      for (uint32_t v : succ[u]) rev[find(v)].push_back(u);
      for (const FieldEdge &e : fieldOut[u]) rev[find(e.dst)].push_back(u);
    }
    std::vector<uint32_t> parent(numNodes, UINT32_MAX);
    std::vector<uint32_t> q{target};
    parent[target] = target;
    for (size_t i = 0; i < q.size(); i++)
      for (uint32_t p : rev[q[i]])
        if (parent[p] == UINT32_MAX && holds(p)) {
          parent[p] = q[i];
          q.push_back(p);
        }
    // The seed: the node an object of the wanted kind was minted at.
    uint32_t origin = UINT32_MAX;
    for (uint32_t o = 0; o < objs.size() && origin == UINT32_MAX; o++) {
      if (!objWant[o]) continue;
      const uint32_t sn = find(getCanonicalNode(objs[o].origin));
      if (sn < numNodes && parent[sn] != UINT32_MAX) origin = sn;
    }
    if (origin == UINT32_MAX) {
      CG_LOG("Cells: " << ind << "no path from the object's seed (" << q.size()
             << " holders reached backward)\n");
      return;
    }
    CG_LOG("Cells: " << ind << "path of '" << want << "' into "
           << nodeDesc(target) << " (origin first):\n");
    std::vector<std::pair<uint32_t, uint32_t>> hubsOnPath; // hub, its cell node
    uint32_t prev = UINT32_MAX;
    for (uint32_t u = origin, k = 0; k < 200; k++) {
      CG_LOG("Cells: " << ind << "  " << nodeDesc(u) << "\n");
      if (u < G && (NF.isDereferenceNode(u) || NF.isObjectNode(u)) &&
          prev != UINT32_MAX && prev >= G)
        hubsOnPath.push_back({u, prev});
      if (u == target || parent[u] == UINT32_MAX) break;
      prev = u;
      u = parent[u];
    }
    // Why does each load's pointer hold the cell it read?
    if (depth >= 4) return;
    for (auto [h, cellNode] : hubsOnPath) {
      const NodeIndex par = NF.getDerefParent(h);
      if (par == AndersNodeFactory::InvalidIndex) continue;
      uint32_t obj = UINT32_MAX;
      for (uint32_t f = 0; f < cells.size() && obj == UINT32_MAX; f++)
        if (cells[f].load == cellNode || cells[f].store == cellNode)
          obj = cells[f].obj;
      if (obj == UINT32_MAX) continue;
      const std::string w = describe(objs[obj]);
      CG_LOG("Cells: " << ind << "  why does the pointer of that load hold "
             << w << "?\n");
      tracePathD(find(getCanonicalNode(par)), w.substr(0, w.find(" [")), depth + 1);
    }
  };
  // Confluence census: per function, the width of its pointer formals
  // and return (distinct names / objects held) and its direct call
  // sites. Width x sites ranks clone candidates.
  auto confluenceCensus = [&]() {
    struct Row { double score; size_t names, objects, sites, holders; std::string what; };
    std::vector<Row> rows;
    std::vector<char> seenObj(objs.size(), 0);
    auto width = [&](uint32_t u, size_t &nn, size_t &no) {
      boost::unordered_flat_set<uint32_t> names;
      std::vector<uint32_t> os;
      pts[find(u)].forEach([&](uint32_t f) {
        f = findFact(f);
        const Cell &C = cells[f];
        names.insert(C.kind == CellKind::Off ? C.name : (uint32_t)C.kind + (1u << 31));
        for (auto [o, off] : memb[f])
          if (!seenObj[o]) { seenObj[o] = 1; os.push_back(o); }
      });
      for (uint32_t o : os) seenObj[o] = 0;
      nn = names.size();
      no = os.size();
    };
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (F.isDeclaration()) continue;
        size_t sites = 0;
        for (const User *U : F.users())
          if (const auto *CB = dyn_cast<CallBase>(U))
            if (CB->getCalledOperand() == &F) sites++;
        size_t bestN = 0, bestO = 0;
        std::string what;
        for (Argument &A : F.args()) {
          if (!A.getType()->isPointerTy()) continue;
          const NodeIndex vn = NF.getValueNodeFor(&A);
          if (vn == AndersNodeFactory::InvalidIndex) continue;
          const uint32_t c = getCanonicalNode(vn);
          if (c >= G) continue;
          size_t nn, no;
          width(c, nn, no);
          if (nn > bestN) { bestN = nn; bestO = no; what = "arg" + std::to_string(A.getArgNo()); }
        }
        const NodeIndex rn = NF.getReturnNodeFor(&F);
        if (rn != AndersNodeFactory::InvalidIndex && getCanonicalNode(rn) < G) {
          size_t nn, no;
          width(getCanonicalNode(rn), nn, no);
          if (nn > bestN) { bestN = nn; bestO = no; what = "ret"; }
        }
        if (bestN < 2) continue;
        rows.push_back({(double)bestN * std::max<size_t>(sites, 1), bestN, bestO,
                        sites, 0, F.getName().str() + " " + what +
                                   (F.hasAddressTaken() ? " (address taken)" : "")});
      }
    std::sort(rows.begin(), rows.end(),
              [](const Row &a, const Row &b) { return a.score > b.score; });
    CG_LOG("Cells: confluence census at " << pops << " pops (" << rows.size()
           << " functions with a formal/return of 2+ names)\n");
    for (size_t i = 0; i < rows.size() && i < 40; i++)
      CG_LOG("Cells:   " << rows[i].what << ": " << rows[i].names
             << " names, " << rows[i].objects << " objects, " << rows[i].sites
             << " direct call sites\n");
    // What a named formal holds: its objects (by label) and names.
    unsigned instId = UINT32_MAX;
    if (StringRef(CFLCellCensusFormal).contains(":%")) {
      // FUNCTION:%N names an instruction by its printed operand.
      auto [fn2, inst2] = StringRef(CFLCellCensusFormal).split(':');
      for (auto &[M, _] : Ctx->Modules)
        if (Function *F2 = M->getFunction(fn2))
          for (Instruction &I : instructions(*F2)) {
            std::string op;
            raw_string_ostream os(op);
            I.printAsOperand(os, false);
            if (os.str() == inst2) instId = NF.getValueNodeFor(&I);
          }
      if (instId != UINT32_MAX && instId != AndersNodeFactory::InvalidIndex) {
        std::vector<NodeIndex> mem;
        collectCanonicalMembers(getCanonicalNode(instId), mem);
        CG_LOG("Cells: " << CFLCellCensusFormal << " = node " << instId
               << ", canonical " << getCanonicalNode(instId) << ", solver rep "
               << find(getCanonicalNode(instId)) << "; class members:\n");
        for (NodeIndex m : mem) CG_LOG("Cells:   member " << nodeDesc(m) << "\n");
        const uint32_t t = find(getCanonicalNode(instId));
        for (uint32_t u = 0; u < numNodes; u++) {
          if (find(u) != u) continue;
          for (const FieldEdge &e : fieldOut[u])
            if (find(e.dst) == t) {
              const LazyLabel &L = lazyLabels[e.li];
              CG_LOG("Cells:   field edge in from " << nodeDesc(u) << ": +" << L.off
                     << " stride " << L.stride << (L.arith ? " arith" : "")
                     << (e.walk ? " WALK" : "") << "\n");
            }
          for (uint32_t v : succ[u])
            if (find(v) == t)
              CG_LOG("Cells:   copy in from " << nodeDesc(u) << "\n");
        }
        std::string fl;
        pts[t].forEach([&](uint32_t f) { fl += " [" + factDescP(findFact(f)) + "]"; });
        CG_LOG("Cells:   holds:" << fl.substr(0, 3000) << "\n");
      }
    } else if (StringRef(CFLCellCensusFormal).starts_with("#")) {
      unsigned id = 0;
      StringRef(CFLCellCensusFormal).drop_front(1).getAsInteger(10, id);
      const uint32_t t = find(getCanonicalNode(id));
      CG_LOG("Cells: node #" << id << " = " << nodeDesc(t) << ", "
             << pts[t].count() << " facts\n");
      if (!CFLCellTraceObj.empty()) tracePath(t, CFLCellTraceObj);
    } else if (!CFLCellCensusFormal.empty()) {
      StringRef spec(CFLCellCensusFormal);
      auto [fname, argno] = spec.split(':');
      unsigned ai = 0;
      argno.getAsInteger(10, ai);
      for (auto &[M, _] : Ctx->Modules) {
        Function *F = M->getFunction(fname);
        if (!F || F->isDeclaration() || ai >= F->arg_size()) continue;
        const NodeIndex vn = NF.getValueNodeFor(F->getArg(ai));
        if (vn == AndersNodeFactory::InvalidIndex) continue;
        std::map<std::string, size_t> byLabel;
        std::map<std::string, size_t> nameCount;
        pts[find(getCanonicalNode(vn))].forEach([&](uint32_t f) {
          f = findFact(f);
          const Cell &C = cells[f];
          for (auto [o, off] : memb[f]) byLabel[describe(objs[o])]++;
          nameCount[C.kind == CellKind::Off ? NF.cellNameString(C.name)
                    : C.kind == CellKind::Func ? "fn"
                    : C.kind == CellKind::Any ? "*" : "out"]++;
        });
        CG_LOG("Cells: " << fname << " arg" << ai << " holds "
               << byLabel.size() << " objects:\n");
        if (!CFLCellTraceObj.empty())
          tracePath(find(getCanonicalNode(vn)), CFLCellTraceObj);
        for (auto &[d, c] : byLabel) CG_LOG("Cells:   obj " << d << "\n");
        std::string nl;
        for (auto &[n2, c] : nameCount) nl += " " + n2;
        CG_LOG("Cells:   names:" << nl.substr(0, 4000) << "\n");
      }
    }
  };
  // Two cells' names are compatible when one may be viewed as the other:
  // equal names, or a struct starting at both addresses (a base embedded
  // at offset 0 of a derived struct, a list_head in two containers).
  std::vector<std::string> chainA, chainB;
  // The declared pointee of the pointer slot at offset `off` of object o:
  // a struct member by its debug-info struct, a stack or global variable
  // by its own debug type.
  std::map<std::string, const DICompositeType *> diStructs;
  bool diStructsDone = false;
  auto diPointerLeafUncached = [&](uint32_t o, int64_t off) -> std::string {
    const Obj &O = objs[o];
    const DIType *T = nullptr;
    const Value *V = NF.getValueForNode(O.origin);
    if (const auto *AI = dyn_cast_or_null<AllocaInst>(V)) {
      for (auto *DDI : findDbgDeclares(const_cast<AllocaInst *>(AI)))
        if (DDI->getVariable()) { T = DDI->getVariable()->getType(); break; }
      // -O3: dbg.value(slot, DW_OP_deref), the variable living in the slot.
      if (!T) {
        SmallVector<DbgValueInst *, 2> dvs;
        findDbgValues(dvs, const_cast<AllocaInst *>(AI));
        for (DbgValueInst *DV : dvs)
          if (DV->getVariable() && DV->getExpression()->getNumElements() == 1 &&
              DV->getExpression()->getElement(0) == dwarf::DW_OP_deref) {
            T = DV->getVariable()->getType();
            break;
          }
      }
    } else if (const auto *GV = dyn_cast_or_null<GlobalVariable>(V)) {
      SmallVector<DIGlobalVariableExpression *, 1> GVEs;
      GV->getDebugInfo(GVEs);
      if (!GVEs.empty()) T = GVEs[0]->getVariable()->getType();
    }
    if (!T) {
      Type *L = O.layout;
      while (auto *AT = dyn_cast<ArrayType>(L)) L = AT->getElementType();
      auto *ST = dyn_cast<StructType>(L);
      if (!ST || !ST->hasName()) return "";
      if (!diStructsDone) {
        diStructsDone = true;
        for (auto &[M, _] : Ctx->Modules) {
          DebugInfoFinder DIF;
          DIF.processModule(*M);
          for (const DIType *DT : DIF.types())
            if (const auto *CT = dyn_cast<DICompositeType>(DT))
              if ((CT->getTag() == dwarf::DW_TAG_structure_type ||
                   CT->getTag() == dwarf::DW_TAG_union_type) &&
                  !CT->getName().empty() && !CT->isForwardDecl())
                diStructs.emplace(CT->getName().str(), CT);
        }
      }
      // By name, when the debug struct has the IR layout; linking names
      // structurally identical types once (TermOffset reads as
      // struct.ReusableSpace), so otherwise every debug struct of that
      // layout, when they agree.
      const StructLayout *SL = DL.getStructLayout(ST);
      auto sameLayout = [&](const DICompositeType *C) {
        if (C->getSizeInBits() / 8 != SL->getSizeInBytes()) return false;
        std::vector<uint64_t> di, ir;
        for (const DINode *N2 : C->getElements())
          if (const auto *M = dyn_cast<DIDerivedType>(N2))
            if (M->getTag() == dwarf::DW_TAG_member) di.push_back(M->getOffsetInBits() / 8);
        for (unsigned k = 0; k < ST->getNumElements(); k++) ir.push_back(SL->getElementOffset(k));
        return di == ir;
      };
      StringRef N = stripStructNameSuffix(ST->getName());
      N.consume_front("struct.");
      auto it = diStructs.find(N.str());
      if (it != diStructs.end() && sameLayout(it->second)) {
        T = it->second;
      } else {
        std::string key;
        for (auto &[nm, C] : diStructs)
          if (sameLayout(C)) {
            const std::string k = diPointeeKey(diMemberAt(C, (uint64_t)off));
            if (k.empty()) return "";
            if (key.empty()) key = k;
            else if (key != k) return "";
          }
        return key;
      }
    }
    return diPointeeKey(diMemberAt(T, (uint64_t)off));
  };
  // Memoized per (object, folded offset): the layout scan above is
  // costly, and the one-label check asks the same pairs again and again.
  std::map<std::pair<uint32_t, int64_t>, std::string> diLeafMemo;
  auto diPointerLeaf = [&](uint32_t o, int64_t off) -> std::string {
    const Obj &O = objs[o];
    if (!O.layout) return "";
    off = foldIn(O.layout, off, DL);
    auto it = diLeafMemo.find({o, off});
    if (it != diLeafMemo.end()) return it->second;
    std::string k = diPointerLeafUncached(o, off);
    diLeafMemo.emplace(std::make_pair(o, off), k);
    return k;
  };
  // 1: the same name; 2: compatible but distinct (an embedding: a jmp_buf *
  // may hold a png_struct, whose first member it is; or the same scalar
  // leaf type); 0: a conflict. Nothing merges (the check observes).
  auto namesCompatible = [&](uint32_t a, uint32_t f) -> int {
    if (cells[a].name == cells[f].name) return 1;
    const Obj &OA = objs[cells[a].obj], &OB = objs[cells[f].obj];
    if (!OA.layout || !OB.layout) return 0; // bytes meet only bytes
    structChain(OA.layout, foldIn(OA.layout, cells[a].off, DL), DL, chainA);
    structChain(OB.layout, foldIn(OB.layout, cells[f].off, DL), DL, chainB);
    // The outermost struct by its identity (debug info), not the name the
    // linker kept for a merged layout.
    auto byIdent = [](const Obj &O, std::vector<std::string> &ch) {
      if (!O.ident.empty() && !ch.empty()) ch[0] = O.ident + ch[0].substr(ch[0].rfind('+'));
    };
    byIdent(OA, chainA);
    byIdent(OB, chainB);
    for (const std::string &x : chainA)
      for (const std::string &y : chainB)
        if (x == y) return 2; // embedding (base and derived): one-way
    // A scalar member is an embedded scalar: `int *pi` may hold a local int
    // or &r->nTerm, `char **pp` a char * variable or &t->pList. Compatible,
    // but distinct objects: they coexist unmerged.
    Type *LA = leafAt(OA.layout, foldIn(OA.layout, cells[a].off, DL), DL);
    Type *LB = leafAt(OB.layout, foldIn(OB.layout, cells[f].off, DL), DL);
    if (LA && LB && LA == LB && !LA->isPointerTy()) {
      leafMerges++;
      return 2;
    }
    // Pointer leaves: by their declared pointee (debug info; opaque IR
    // pointers all read alike).
    if (LA && LB && LA->isPointerTy() && LB->isPointerTy()) {
      const std::string KA = diPointerLeaf(cells[a].obj, cells[a].off);
      const std::string KB = diPointerLeaf(cells[f].obj, cells[f].off);
      if (!KA.empty() && KA == KB) {
        leafMerges++;
        return 2;
      }
    }
    return 0;
  };
  auto factDesc = [&](uint32_t f) {
    const Cell &C = cells[f];
    std::string d = NF.cellNameString(C.name) + " @" + std::to_string(C.off) + " of {";
    for (size_t i = 0; i < memb[f].size() && i < 6; i++)
      d += (i ? "; " : "") + describe(objs[memb[f][i].first]);
    if (memb[f].size() > 6) d += "; ... " + std::to_string(memb[f].size()) + " members";
    return d + "}";
  };
  // Collect mode (--cfl-cell-one-label-max > 1): where the two labels'
  // paths into n meet. A meet at a formal is call-context confluence: the
  // function is a clone candidate; elsewhere (a load, a phi) it is not.
  auto meetPoints = [&](uint32_t n, uint32_t a, uint32_t f) {
    // Different objects: hold by object (a field step changes the cell,
    // not the object). Fields of one object: hold by cell identity.
    const uint32_t ra = findFact(a), rf = findFact(f);
    std::set<uint32_t> oa, ob;
    for (auto [o, e] : memb[ra]) oa.insert(o);
    for (auto [o, e] : memb[rf]) ob.insert(o);
    bool disjoint = true;
    for (uint32_t o : oa) disjoint &= !ob.count(o);
    auto holdsCell = [&](uint32_t u, uint32_t want) {
      const std::set<uint32_t> &os = want == ra ? oa : ob;
      bool h = false;
      pts[u].forEach([&](uint32_t x) {
        if (h) return;
        x = findFact(x);
        if (!disjoint) { h = x == want; return; }
        for (auto [o, e] : memb[x])
          if (os.count(o)) { h = true; break; }
      });
      return h;
    };
    std::vector<std::vector<uint32_t>> rev(numNodes);
    for (uint32_t u = 0; u < numNodes; u++) {
      if (find(u) != u) continue;
      for (uint32_t v : succ[u]) rev[find(v)].push_back(u);
      for (const FieldEdge &e : fieldOut[u]) rev[find(e.dst)].push_back(u);
    }
    std::vector<char> seen(numNodes, 0);
    std::vector<uint32_t> q{n};
    seen[n] = 1;
    std::vector<uint32_t> meets;
    for (size_t i = 0; i < q.size() && i < 200000; i++) {
      const uint32_t u = q[i];
      bool pA = false, pB = false;
      for (uint32_t p : rev[u]) {
        const bool ha = holdsCell(p, ra), hb = holdsCell(p, rf);
        if (ha && !hb) pA = true;
        if (hb && !ha) pB = true;
        if ((ha || hb) && !seen[p]) { seen[p] = 1; q.push_back(p); }
      }
      if (pA && pB) meets.push_back(u);
    }
    for (uint32_t u : meets) {
      const Value *V = u < G ? NF.getValueForNode(u) : nullptr;
      std::string d = nodeDesc(u);
      if (const auto *A = dyn_cast_or_null<Argument>(V)) {
        cloneCandidates[A->getParent()->getName().str()]++;
        CG_LOG("Cells:   meet at a formal: " << d << " -> clone "
               << A->getParent()->getName() << "\n");
      } else {
        std::string kind = u >= G ? "cell" : NF.isDereferenceNode(u) || NF.isObjectNode(u) ? "load"
                           : V && isa<PHINode>(V) ? "phi" : V && isa<SelectInst>(V) ? "select"
                           : NF.isReturnNode(u) ? "return" : "value";
        otherMeets[kind]++;
        CG_LOG("Cells:   meet at a " << kind << ": " << d << "\n");
      }
    }
    if (meets.empty()) CG_LOG("Cells:   no meet point found\n");
  };
  // Program defects the solver reports and does not model (C undefined
  // behavior, copies between unrelated structs). In stop mode the counts
  // are the ones seen so far.
  std::vector<std::string> copyMismatchAt;
  size_t copyMismatches = 0;
  // Relay rows (plan 3.53 rule 4): a byte copy between storage of
  // different labels, per (site, source label, destination label); a null
  // label is bytes (an unlabeled object or a char array). The count is
  // of copied regions.
  std::map<std::tuple<const Instruction *, Type *, Type *>, size_t> relayRows;
  // Pointer subtractions across objects (kept for the rule report).
  size_t rrPtrAlways = 0, rrPtrMay = 0;
  std::vector<std::string> rrPtrAt;
  auto reportDefects = [&]() {
    CG_LOG("Cells: " << copyMismatches
           << " copies between unrelated structs (copied byte by byte, "
              "reported)\n");
    for (const std::string &d : copyMismatchAt) CG_LOG("Cells:   " << d << "\n");
    size_t disjoint = 0, partial = 0, same = 0, empty = 0;
    std::vector<std::string> ex;
    for (auto &[pN, qN, at] : ptrDiffs) {
      std::set<uint32_t> po, qo;
      pts[find(canon(pN))].forEach([&](uint32_t f) {
        for (auto [o, e] : memb[findFact(f)]) po.insert(o);
      });
      pts[find(canon(qN))].forEach([&](uint32_t f) {
        for (auto [o, e] : memb[findFact(f)]) qo.insert(o);
      });
      if (po.empty() || qo.empty()) { empty++; continue; }
      bool any = false;
      for (uint32_t o : po) any |= qo.count(o) != 0;
      if (po == qo) { same++; continue; }
      (any ? partial : disjoint)++;
      if (ex.size() < 8)
        ex.push_back(std::string(any ? "may" : "always") +
                     " two objects: " + instLoc(at) + " (" +
                     std::to_string(po.size()) + " vs " +
                     std::to_string(qo.size()) + " objects)");
    }
    rrPtrAlways = disjoint;
    rrPtrMay = partial;
    rrPtrAt = ex;
    CG_LOG("Cells: pointer subtractions (C: one object only): "
           << ptrDiffs.size() << ", same objects " << same
           << ", undefined behavior: always " << disjoint << ", may "
           << partial << " (no facts: " << empty << ")\n");
    for (const std::string &d : ex) CG_LOG("Cells:   " << d << "\n");
  };
  auto finishCollect = [&]() {
    reportDefects();
    std::string c;
    for (auto &[fn, k] : cloneCandidates) c += (c.empty() ? "" : ",") + fn;
    std::string o;
    for (auto &[k, v] : otherMeets) o += " " + k + "=" + std::to_string(v);
    errs() << "Cells: " << conflicts << " name conflicts; meets elsewhere:" << o
           << "\nCLONE-CANDIDATES: " << c << "\n";
    exit(0);
  };
  reportTypedStep = [&](uint32_t n, uint32_t f, const StructType *S,
                        const char *why) {
    CG_LOG("Cells: NAME CONFLICT at pop " << pops << ": " << nodeDesc(n)
           << " holds a cell (" << memb[f].size() << " objects) " << why
           << ", now stepped as "
           << (S->hasName() ? S->getName().str() : std::string("<struct>"))
           << "\n");
    CG_LOG("Cells:   cell = " << factDesc(f) << "\n");
    std::set<std::string> seen;
    for (auto [o, eo] : memb[f]) {
      const std::string w = describe(objs[o]);
      if (!seen.insert(w).second || seen.size() > 3) continue;
      tracePathD(n, w.substr(0, w.find(" [")), 3);
    }
    reportDefects();
    errs() << "Cells: --cfl-cell-one-label stopped at the first name "
           << "conflict (measurement only, no answers)\n";
    exit(0);
  };
  auto reportConflict = [&](uint32_t n, uint32_t a, uint32_t f) {
    CG_LOG("Cells: NAME CONFLICT at pop " << pops << ": " << nodeDesc(n)
           << " points to\n");
    CG_LOG("Cells:   A = " << factDesc(a) << "\n");
    CG_LOG("Cells:   B = " << factDesc(f) << "\n");
    for (uint32_t x : {a, f}) {
      const std::string w = describe(objs[memb[x][0].first]);
      tracePathD(n, w.substr(0, w.find(" [")), 3); // depth 3: one level of why
    }
  };
  // The access that gave an unlabeled object its layout: the stepped
  // pointer and the step's result (a member step), or a byte copy.
  noteLayoutCause = [&](uint32_t o, StructType *S) {
    if (CFLCellTraceObj.empty() ||
        describe(objs[o]).find(CFLCellTraceObj) == std::string::npos)
      return;
    CG_LOG("Cells: LAYOUT " << describe(objs[o]) << " learned " << typeLabel(S) << " ("
           << mintCause << ") stepping "
           << (curStepNode == UINT32_MAX ? std::string("?") : nodeDesc(curStepNode).substr(0, 160))
           << " into "
           << (curStepDst == UINT32_MAX ? std::string("?") : nodeDesc(curStepDst).substr(0, 200))
           << (layoutCopyFrom.empty() ? std::string() : "; the copy at " + layoutCopyFrom) << "\n");
  };
  noteAnyCause = [&](uint32_t o) {
    if (CFLCellTraceObj.empty() ||
        describe(objs[o]).find(CFLCellTraceObj) == std::string::npos)
      return;
    CG_LOG("Cells: ANY CELL of " << describe(objs[o]) << " made by "
           << anyCause << " at "
           << (anyCauseNode == UINT32_MAX ? std::string("?") : nodeDesc(anyCauseNode))
           << "\n");
  };
  // Byte copies: each (source cell, destination cell) pair copies content
  // position by position, through the folding (arrays are one element):
  // the copy's length, or (unknown) the rest of the innermost array
  // element or of the object. An unknown object a variable-length copy
  // touches is bytes.
  auto regionLen = [&](uint32_t o, int64_t a) -> int64_t {
    if (objs[o].fn) return 0; // a function holds no cells
    const Obj &O = objs[o];
    if (!O.layout) {
      // An unlabeled object's bytes are its any-offset cell: one position.
      if (!O.period) return 1;
      return O.period - (((a % O.period) + O.period) % O.period);
    }
    int64_t pos = a;
    if (O.repeats) pos = ((pos % O.size) + O.size) % O.size;
    int64_t b = 0, e = 0;
    if (innermostArray(O.layout, pos, DL, b, e)) return e - (pos - b);
    return O.size - pos;
  };
  boost::unordered_flat_set<std::tuple<uint32_t, uint32_t, uint32_t>,
                            boost::hash<std::tuple<uint32_t, uint32_t, uint32_t>>>
      copyPairsDone;
  size_t copyPairs = 0, copyEdges = 0, effectiveTyped = 0, intNameToBytes = 0;
  // Byte-array relays (measurement, soup profiler): per byte-array object
  // B, the typed regions copied in (source object, B offset, length) and
  // copied out (destination object, B offset, length).
  struct RelayEnd { uint32_t obj; int64_t at, len, cells; const Instruction *I; };
  boost::unordered_flat_map<uint32_t, std::vector<RelayEnd>> relayIn, relayOut;
  std::set<std::tuple<uint32_t, uint32_t, int64_t, int64_t>> relaySeen;
  std::set<std::string> intNameToBytesAt;
  // contentKey for the byte walk, with foldIn memoized per (layout,
  // offset in one instance): a copy revisits the same few offsets of the
  // same layouts for every cell pair.
  struct FoldKeyHash {
    size_t operator()(const std::pair<Type *, int64_t> &k) const {
      return (size_t)(((uint64_t)(uintptr_t)k.first * 0x9E3779B97F4A7C15ull) ^
                      ((uint64_t)k.second * 0xBF58476D1CE4E5B9ull));
    }
  };
  boost::unordered_flat_map<std::pair<Type *, int64_t>, int64_t, FoldKeyHash> foldMemo;
  // An unlabeled object without an element size is one key: its any-offset
  // cell (bytes is not a label).
  constexpr int64_t kCopyAny = std::numeric_limits<int64_t>::min();
  auto copyKey = [&](const Obj &O, int64_t off) -> int64_t {
    if (!O.layout) return O.period ? contentKey(O, off) : kCopyAny;
    assert(!(O.tail && off >= O.size) && "trailing offsets route to the tail object");
    off = ((off % O.size) + O.size) % O.size;
    auto [it, ins] = foldMemo.try_emplace({O.layout, off}, 0);
    if (ins) it->second = foldIn(O.layout, off, DL);
    return it->second;
  };
  auto copyRegion = [&](uint32_t os, int64_t a, uint32_t od, int64_t b,
                        int64_t len, const Instruction *at) {
    MintCause mc(mintCause, "byte copy", VerboseLevel >= 2);
    // Effective type (C11 6.5p6): a copy into an object with no declared
    // type gives it the source's type. An unknown destination copied into
    // from its start learns the struct the source region starts with.
    if (!objs[od].layout && b == 0 && objs[os].layout) {
      const Obj &Os = objs[os];
      const int64_t fa = Os.repeats ? ((a % Os.size) + Os.size) % Os.size : a;
      if (StructType *S = structAt(Os.layout, fa, DL)) {
        layoutCopyFrom = (at ? instLoc(at) : std::string("?")) + " from " + describe(Os) + " +" + std::to_string(fa);
        layoutCopySrc = fa == 0 ? os : UINT32_MAX; // the source's identity, from its start
        requestLayout(od, S);
        layoutCopyFrom.clear();
        layoutCopySrc = UINT32_MAX;
        if (objs[od].layout) effectiveTyped++;
      }
    }
    // A copy between two structs is compatible when one starts where the
    // other is (equal, or embedded: base and derived). Otherwise the
    // program copies one struct over an unrelated one: report it (in
    // one-label stop mode, stop); the bytes are still copied.
    auto startsIn = [&](StructType *S, Type *T, int64_t off) {
      return S->hasName() &&
             structStartsAt(T, off, stripStructNameSuffix(S->getName()), DL, S);
    };
    // Rule 4 (plan 3.53): storage of one label copied into storage of the
    // same label (or into an unlabeled object from its start, which took
    // the source's layout above) is copied cell to cell: the walk below
    // maps every position through both layouts, so fields, union members
    // and array elements move to their own cells. A copy between
    // different labels is still walked position by position, through
    // bytes on a byte side, and is a relay row.
    {
      auto labelAt = [&](uint32_t o, int64_t off) -> Type * {
        const Obj &O = objs[o];
        if (!O.layout || O.label == "i8") return nullptr;
        const int64_t f = O.repeats ? ((off % O.size) + O.size) % O.size : off;
        if (StructType *S = structAt(O.layout, f, DL)) return S;
        return O.layout;
      };
      const auto [lso, lsa] = locate(os, a);
      const auto [ldo, ldb] = locate(od, b);
      Type *ls = labelAt(lso, lsa), *ld = labelAt(ldo, ldb);
      auto fold = [&](const Obj &O, int64_t off) {
        return O.repeats ? ((off % O.size) + O.size) % O.size : off;
      };
      const bool embedded =
          ls && ld && ((isa<StructType>(ls) && startsIn(cast<StructType>(ls), objs[ldo].layout, fold(objs[ldo], ldb))) ||
                       (isa<StructType>(ld) && startsIn(cast<StructType>(ld), objs[lso].layout, fold(objs[lso], lsa))));
      if (ls != ld && !embedded) relayRows[{at, ls, ld}]++;
    }
    if (objs[os].layout && objs[od].layout) {
      const Obj &Os = objs[os], &Od = objs[od];
      const int64_t fa = Os.repeats ? ((a % Os.size) + Os.size) % Os.size : a;
      const int64_t fb = Od.repeats ? ((b % Od.size) + Od.size) % Od.size : b;
      StructType *Ss = structAt(Os.layout, fa, DL), *Sd = structAt(Od.layout, fb, DL);
      if (Ss && Sd && Ss != Sd && !startsIn(Ss, Od.layout, fb) &&
          !startsIn(Sd, Os.layout, fa)) {
        if (!copyMismatches && curCopy != UINT32_MAX)
          firstMismatch = {curCopy, curCopySrcFact, os, od};
        copyMismatches++;
        const std::string d =
            instLoc(at) + ": " + describe(Os) + " +" + std::to_string(fa) +
            " (" + typeLabel(Ss) + ") into " + describe(Od) + " +" +
            std::to_string(fb) + " (" + typeLabel(Sd) + ")";
        if (copyMismatchAt.size() < 8) copyMismatchAt.push_back(d);
        if (CFLCellOneLabel && CFLCellOneLabelMax <= 1 && curCopyDst != UINT32_MAX)
          pend1({2, curCopyDst, 0, curCopySrcFact, nullptr, d, pops});
        if (CFLCellOneLabel) otherMeets["copy-mismatch"]++;
      }
    }
    const auto [ro, ra] = locate(os, a);
    const int64_t L = std::min<int64_t>(len >= 0 ? len : regionLen(ro, ra),
                                        (int64_t)kExpandCap);
    if (CFLCellSoupProfile && L > 0) {
      // Typed -> byte array (in) and byte array -> typed (out).
      auto cellsOf = [&](uint32_t o, int64_t from, int64_t n) {
        std::set<int64_t> ks;
        for (int64_t k = 0; k < n && k < 4096; k++) {
          const auto [o2, x] = locate(o, from + k);
          if (o2 == o) ks.insert(contentKey(objs[o2], x));
        }
        return (int64_t)ks.size();
      };
      const bool srcTyped = objs[os].layout && objs[os].label != "i8";
      const bool dstTyped = objs[od].layout && objs[od].label != "i8";
      if (srcTyped && !dstTyped && relaySeen.insert({od, os, b, a}).second)
        relayIn[od].push_back({os, b, L, cellsOf(os, a, L), at});
      else if (!srcTyped && dstTyped && relaySeen.insert({os, od, a, b}).second)
        relayOut[os].push_back({od, a, L, cellsOf(od, b, L), at});
    }
    boost::unordered_flat_set<SeenKey, SeenKeyHash> seenAt;
    // Positions whose (object, content key) pair on both sides repeats an
    // earlier one do nothing (seenAt). Over a run of positions each side's
    // key is periodic: bytes (period 1), a learned element (its period),
    // an array inside a labeled object (its element size, to the array's
    // end), an array of the layout (the layout's size); a scalar outside
    // any array is not. Once both sides are periodic and a whole common
    // period of the run has been walked, every later position of the run
    // repeats a pair, so the walk jumps to the run's end (which never
    // passes a trailing object's start or a non-array object's end). Same
    // pairs, same order, same edges.
    constexpr int64_t kNoEnd = std::numeric_limits<int64_t>::max();
    // A side's run at byte `off` of O, reached at position k: (period, end).
    auto runOf = [&](const Obj &O, int64_t off, int64_t k) -> std::pair<int64_t, int64_t> {
      const int64_t segEnd = O.tail ? k + (O.size - off) : kNoEnd;
      if (!O.layout) return {O.period ? O.period : 1, segEnd}; // any offset: one key
      const int64_t in = O.repeats ? ((off % O.size) + O.size) % O.size : off;
      const auto [e, aend] = foldPeriod(O.layout, in, DL);
      if (e > 0) return {e, std::min(segEnd, k + (aend - in))};
      if (O.repeats) return {O.size, segEnd};
      return {0, segEnd};
    };
    int64_t runStart = 0, runEnd = -1, runP = 0;
    uint32_t runSo = UINT32_MAX, runDo = UINT32_MAX;
    for (int64_t k = 0; k < L; k++) {
      // Past a header: the trailing object (located per position).
      const auto [so, sa] = locate(os, a + k);
      const auto [dob, db] = locate(od, b + k);
      const Obj &Os = objs[so], &Od = objs[dob];
      if (Os.layout && !Os.repeats && (sa < 0 || sa >= Os.size)) break;
      if (Od.layout && !Od.repeats && (db < 0 || db >= Od.size)) break;
      if (k >= runEnd || so != runSo || dob != runDo) {
        const auto [ps, es] = runOf(Os, sa, k);
        const auto [pd, ed] = runOf(Od, db, k);
        runStart = k;
        runEnd = std::min(es, ed);
        runP = ps > 0 && pd > 0 ? std::lcm(ps, pd) : 0;
        runSo = so;
        runDo = dob;
      }
      if (runP > 0 && k - runStart >= runP) {
        k = std::min(runEnd, L) - 1; // the rest of the run repeats
        continue;
      }
      const int64_t sk = copyKey(Os, sa), dk = copyKey(Od, db);
      if (!seenAt.insert(SeenKey{so, dob, sk, dk}).second) continue;
      // A byte copy writing a tagged field's tag other than as a co-move
      // (the same struct at the same offset) is a write the census did not
      // name: the pair flips to unkeyed (plan 3.51).
      if (!taggedPairs.empty() && Od.layout && tagNestsIn(Od.layout)) {
        auto coMove = [&](const std::string &e) {
          if (!Os.layout) return false;
          std::vector<std::string> chS;
          structChain(Os.layout, sk, DL, chS);
          return std::find(chS.begin(), chS.end(), e) != chS.end();
        };
        std::vector<std::string> chD;
        structChain(Od.layout, dk, DL, chD);
        for (const std::string &e : chD) {
          const size_t plus = e.rfind('+');
          auto it = tagPairsOf.find(e.substr(0, plus));
          if (it == tagPairsOf.end()) continue;
          const int64_t rel = std::stoll(e.substr(plus + 1));
          for (size_t pi : it->second) {
            const TaggedPair &tp = taggedPairs[pi];
            if (rel >= tp.D && rel < tp.D + tp.Dsize && !taggedFlipped.count({tp.S, tp.F}) && !coMove(e))
              flipPair(pi, "byte copy at " + (at ? instLoc(at) : std::string("?")));
          }
        }
      }
      // An integer name copied into bytes (the route by which an integer
      // could be read back as a pointer, plan 3.50 ruling): counted.
      if (!Od.layout && Os.layout && !Os.label.empty()) {
        auto it = intNameFlags.find({Os.label, sk});
        if (it != intNameFlags.end() && it->second == 0) {
          intNameToBytes++;
          if (intNameToBytesAt.size() < 8 && at)
            intNameToBytesAt.insert(instLoc(at) + " (" + Os.label + "+" + std::to_string(sk) + ")");
        }
      }
      auto sideOf = [&](uint32_t o, int64_t k, bool read) -> std::pair<uint32_t, uint32_t> {
        if (k != kCopyAny) return contentOf(o, k);
        markBytes(o);
        const Cell &A = cells[anyOf(o)];
        return read ? std::make_pair(A.load, A.load) : std::make_pair(A.store, A.store);
      };
      const auto [su, sp] = sideOf(so, sk, true);
      const auto [du, dp] = sideOf(dob, dk, false);
      if (CFLCellLeakCensus) // before the edge: its facts arrive inside addEdge
        leakCopyEdge.try_emplace((uint64_t)find(su != sp && du != dp ? su : sp) << 32 | find(du), curCopy);
      if (su != sp && du != dp) {
        // Keyed union slot to keyed union slot: unkeyed to unkeyed, each
        // key to the same key (a realloc of a node array keeps its keys).
        addEdge(su, du);
        objs[so].copyOut.push_back({sk, dob, dk});
        std::vector<std::pair<uint32_t, uint32_t>> ks; // key, node
        for (auto &[kk, kn] : objs[so].keyed)
          if ((int64_t)(uint32_t)(kk >> 32) == (int64_t)(uint32_t)sk)
            ks.push_back({(uint32_t)kk, kn});
        for (auto [k, kn] : ks) addEdge(kn, keyedOf(dob, dk, k));
      } else {
        addEdge(sp, du);
      }
      copyEdges++;
      copyStat[curCopy].edges++;
    }
  };
  auto copyPair = [&](uint32_t ci, uint32_t fs, uint32_t fd) {
    if (soupStop) return; // the profiler stopped: no more work
    // The time cap, also between the pairs of a long byte-copy expansion
    // (its edges may bring no new fact, so the arrival check never runs).
    static uint32_t copyTick = 0;
    if (CFLCellSoupProfile && CFLCellSoupTime && (++copyTick & 0x3ff) == 0 &&
        std::chrono::duration<double>(Clock::now() - t0).count() > CFLCellSoupTime) {
      soupStop = true;
      return;
    }
    fs = findFact(fs);
    fd = findFact(fd);
    if (!copyPairsDone.insert(std::make_tuple(ci, fs, fd)).second) return;
    const Cell &S = cells[fs], &D = cells[fd];
    if (S.kind == CellKind::Func || D.kind == CellKind::Func ||
        S.kind == CellKind::Out || D.kind == CellKind::Out)
      return;
    copyPairs++;
    if (copyStat.size() < copies.size()) copyStat.resize(copies.size());
    curCopy = ci;
    copyStat[ci].pairs++;
    for (auto [o, e] : memb[fs]) copyStat[ci].srcObjs.insert(o);
    for (auto [o, e] : memb[fd]) copyStat[ci].dstObjs.insert(o);
    if (S.kind == CellKind::Any || D.kind == CellKind::Any) {
      if (CFLCellLeakCensus)
        leakCopyEdge.try_emplace((uint64_t)find(S.load) << 32 | find(D.store), ci);
      addEdge(S.load, D.store); // any offset: everything to everything
      return;
    }
    const std::vector<Member> ms = memb[fs], md = memb[fd];
    curCopyDst = find(copies[ci].dst);
    curCopySrcFact = fs;
    if (trackWhy) curWhy = {ci, fs, fd, W_COPY};
    for (auto [os, ea] : ms)
      for (auto [od, eb] : md)
        copyRegion(os, decOff(ea), od, decOff(eb), copies[ci].len, copies[ci].at);
    curCopyDst = UINT32_MAX;
  };
  std::vector<uint32_t> copyOther;
  auto applyCopies = [&](uint32_t n, const std::vector<uint32_t> &dlt) {
    for (size_t i = 0; i < copiesAt[n].size(); i++) {
      const uint32_t ci = copiesAt[n][i];
      const uint32_t sN = find(copies[ci].src), dN = find(copies[ci].dst);
      if (n == sN) {
        copyOther.clear();
        pts[dN].forEach([&](uint32_t g) { copyOther.push_back(g); });
        for (uint32_t f : dlt)
          for (uint32_t g : copyOther) copyPair(ci, f, g);
      }
      if (n == dN) {
        copyOther.clear();
        pts[sN].forEach([&](uint32_t g) { copyOther.push_back(g); });
        for (uint32_t g : dlt)
          for (uint32_t f : copyOther) copyPair(ci, f, g);
      }
    }
  };
  // ---- The soup profiler (--cfl-cell-soup-profile, plan 3.34) ----
  // A fact landing on a node where its name is incompatible with the
  // node's first (labeled) name is FOREIGN there. It inherits the entry of
  // the fact it came from (the cause the solver is propagating: an edge's
  // source, a step's base, a dispatch's receiver) when that was foreign
  // already; otherwise this node is the join where the incompatible name
  // entered, and becomes the entry. Mass = foreign facts per entry.
  struct SoupEntry {
    uint32_t node;
    size_t born = 0, mass = 0;
    std::vector<std::pair<uint32_t, size_t>> srcs; // entering source node, count
    uint32_t src0 = UINT32_MAX, fact0 = UINT32_MAX; // the first entering fact
  };
  std::vector<SoupEntry> soupEntries;
  boost::unordered_flat_map<uint32_t, uint32_t> soupEntryAt;  // join node -> entry
  boost::unordered_flat_map<uint64_t, uint32_t> soupForeign;  // (node, fact) -> entry
  std::vector<uint32_t> soupAnchor;
  if (CFLCellSoupProfile)
    soupArrive = [&](uint32_t n, uint32_t f) {
      if (soupStop) return;
      // The time cap, also inside a long pop (a byte copy's expansion).
      static uint32_t tick = 0;
      if (CFLCellSoupTime && (++tick & 0xffff) == 0 &&
          std::chrono::duration<double>(Clock::now() - t0).count() > CFLCellSoupTime) {
        soupStop = true;
        return;
      }
      f = findFact(f);
      const Cell &C = cells[f];
      if (C.kind != CellKind::Off) return;
      bool unknown = true;
      for (auto [o, e] : memb[f]) unknown &= !objs[o].layout;
      if (unknown) return; // no name yet
      if (n >= soupAnchor.size()) soupAnchor.resize(numNodes + 1024, UINT32_MAX);
      if (soupAnchor[n] == UINT32_MAX) { soupAnchor[n] = f; return; }
      const uint32_t a = findFact(soupAnchor[n]);
      if (a == f) return;
      int compat;
      {
        const uint64_t key = (uint64_t)a << 32 | f;
        auto cit = compatMemo.find(key);
        if (cit != compatMemo.end()) compat = cit->second;
        else compatMemo.emplace(key, compat = namesCompatible(a, f));
      }
      if (compat != 0) return;
      uint32_t entry = UINT32_MAX;
      const Why w = curWhy;
      const bool hasSrc = w.node < numNodes && w.fact < cells.size() &&
                          (w.kind == W_EDGE || w.kind == W_STEP || w.kind == W_WALK ||
                           w.kind == W_ANY || w.kind == W_DISPATCH);
      if (hasSrc) {
        auto it = soupForeign.find((uint64_t)find(w.node) << 32 | findFact(w.fact));
        if (it != soupForeign.end()) entry = it->second;
      }
      if (entry == UINT32_MAX) {
        auto [it, ins] = soupEntryAt.try_emplace(n, (uint32_t)soupEntries.size());
        if (ins) soupEntries.push_back({n});
        entry = it->second;
        SoupEntry &E = soupEntries[entry];
        E.born++;
        const uint32_t src = hasSrc ? find(w.node) : UINT32_MAX;
        bool found = false;
        for (auto &[sn, c] : E.srcs)
          if (sn == src) { c++; found = true; break; }
        if (!found && E.srcs.size() < 16) E.srcs.push_back({src, 1});
        if (E.fact0 == UINT32_MAX) { E.src0 = src; E.fact0 = f; }
      }
      soupForeign.emplace((uint64_t)n << 32 | f, entry);
      soupEntries[entry].mass++;
      if (soupForeign.size() >= CFLCellSoupCap) soupStop = true;
    };

  // ---- The leak census (--cfl-cell-leak-census) ----
  // A byte-named cell (i8[]) carries no pointer in a well-typed program,
  // so a non-char object's fact in one entered byte storage somewhere. A
  // fact arriving anywhere inherits the leak of the fact it came from (the
  // cause the solver is propagating), so a leak follows a pointer out of
  // the byte cell and into the next one; a non-char fact entering a byte
  // cell without one makes the arriving edge a leak, classified there:
  //   1 a store or initializer into a byte or union field of a struct,
  //   2 a byte copy, 3 a store into byte storage through a struct view,
  //   4 a store into byte storage through a char or untyped address,
  //   5 a vararg or bodiless call boundary, 6 anything else.
  // Mass = non-char facts in byte cells at the stop, by leak.
  // A leak site: its class, where, the cell it enters, and (stores and
  // copies) the pointers that chose the target: the store's address, or a
  // copy's destination and source, with their objects and labels when the
  // site was first seen; a struct view that did not fit the target.
  struct LeakSite {
    int cls;
    std::string where, into, detail;
    size_t born = 0, exited = 0;
    uint64_t firstPop = 0;
    uint32_t ptrNode = UINT32_MAX, srcNode = UINT32_MAX;
    size_t ptrObjs = 0, ptrLabels = 0, srcObjs = 0, srcLabels = 0;
    const Value *viewPtr = nullptr;
    std::string view;
    int recounted = 0; // the class before a stop-point recount moved it to 7
  };
  // The exit side: an edge out of a byte cell into a node that is not one
  // (a load's hub, a byte copy into a typed cell, anything else), with the
  // non-char facts it carries out (by leak; untagged ones apart) and the
  // byte cells they leave.
  struct LeakExit {
    std::string kind, desc;
    size_t mass = 0, untagged = 0, edges = 0;
    std::map<std::pair<uint32_t, int64_t>, size_t> from;
  };
  std::vector<LeakExit> leakExits;
  boost::unordered_flat_map<uint64_t, uint32_t> leakExitIdx; // (byte node, node) -> exit
  std::map<std::string, uint32_t> leakExitKey;              // site -> exit
  // A non-char fact arriving in a cell of a not yet named object: its
  // entry, classified then, becomes a leak if the object is named bytes.
  boost::unordered_flat_map<uint64_t, uint32_t> leakProv;
  // A hub that feeds only store collectors moves its facts (*q = *p, a
  // pointer-sized move) instead of reading them: it and the collectors
  // pass a byte cell's facts on, and the exit is where the move lands.
  boost::unordered_flat_set<uint32_t> leakTransit;
  std::vector<LeakSite> leakSites;
  std::map<std::string, uint32_t> leakSiteIdx;
  boost::unordered_flat_map<uint64_t, uint32_t> leakTag; // (node, fact) -> leak
  boost::unordered_flat_set<uint32_t> leakMergedByte;    // merged with a byte cell
  // Byte storage: a cell named i8[], or any cell of an unlabeled object
  // used as bytes (a variable byte access or a byte copy side: what the
  // old model named bytes).
  auto leakByteCell = [&](uint32_t o, int64_t c) {
    if (!objs[o].layout && objs[o].byteAccessed) return true;
    if (c == kLeakAny)
      return objs[o].layout && objs[o].label == "i8";
    return cellName(o, c) == "i8[]";
  };
  auto leakIsByte = [&](uint32_t n) {
    auto it = leakCellOf.find(n);
    if (it != leakCellOf.end() && leakByteCell(it->second.first, it->second.second))
      return true;
    return leakMergedByte.count(n) != 0;
  };
  // 0: a char or not yet named object; 1: a struct, union or class; 2:
  // another non-char object (scalars, pointer arrays); 3: a function.
  auto leakFactKind = [&](uint32_t f) -> int {
    if (cells[f].kind == CellKind::Func) return 3;
    int k = 0;
    for (auto [o, e] : memb[f]) {
      const Obj &O = objs[o];
      if (O.fn) return 3;
      if (!O.layout || O.label == "i8") continue;
      const StringRef L(O.label);
      if (L.starts_with("struct.") || L.starts_with("union.") || L.starts_with("class."))
        return 1;
      k = 2;
    }
    return k;
  };
  // The struct a store's address views its target as (through GEPs and
  // casts), "" for a char or untyped address.
  auto leakStructView = [&](const Value *P) -> std::string {
    for (int k = 0; k < 8 && P; k++) {
      P = P->stripPointerCasts();
      const auto *GEP = dyn_cast<GEPOperator>(P);
      if (!GEP) break;
      const std::string l = typeLabel(GEP->getSourceElementType());
      if (StringRef(l).starts_with("struct.") || StringRef(l).starts_with("union.") ||
          StringRef(l).starts_with("class."))
        return l;
      P = GEP->getPointerOperand();
    }
    return "";
  };
  // Content c of struct object o: the enclosing structs, and the tagged
  // pair whose field holds c (keyed, or flipped and why).
  auto leakFieldOf = [&](uint32_t o, int64_t c) -> std::string {
    std::vector<std::string> ch;
    structChain(objs[o].layout, c, DL, ch);
    std::string d;
    for (const std::string &e : ch) d += (d.empty() ? "" : " > ") + e;
    Type *T = objs[o].layout;
    int64_t off = c;
    for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
      if (auto *ST = dyn_cast<StructType>(T)) {
        if (ST->isOpaque()) break;
        const StructLayout *SL = DL.getStructLayout(ST);
        if ((uint64_t)off >= SL->getSizeInBytes()) break;
        const unsigned i = SL->getElementContainingOffset(off);
        if (ST->hasName())
          if (auto it = tagPairsOf.find(stripStructNameSuffix(ST->getName()).str());
              it != tagPairsOf.end())
            for (size_t pi : it->second) {
              const TaggedPair &tp = taggedPairs[pi];
              if (tp.F < 0 || (uint64_t)tp.F >= SL->getSizeInBytes() ||
                  SL->getElementContainingOffset(tp.F) != i)
                continue;
              const std::string pr = tp.S + "+" + std::to_string(tp.F);
              d += "; tagged pair " + pr + " (tag +" + std::to_string(tp.D) + ")";
              if (!taggedFlipped.count({tp.S, tp.F})) { d += " keyed"; continue; }
              d += " FLIPPED";
              for (const std::string &why : taggedFlipAt)
                if (why.rfind(pr + " ", 0) == 0) { d += " (" + why + ")"; break; }
            }
        off -= (int64_t)SL->getElementOffset(i);
        T = ST->getElementType(i);
        continue;
      }
      Type *E = nullptr;
      if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
      if (!E || DL.getTypeAllocSize(E) == 0) break;
      off %= (int64_t)DL.getTypeAllocSize(E);
      T = E;
    }
    if (inUnionSlot(objs[o], c)) d += "; keyed union slot";
    return d;
  };
  auto leakIR = [](const Instruction *I) {
    std::string s;
    raw_string_ostream os(s);
    I->print(os);
    s = os.str();
    s.erase(0, s.find_first_not_of(' '));
    return s.substr(0, 140);
  };
  // Per store address: (objects labeled as its struct view, all objects)
  // its pointer held when first asked.
  boost::unordered_flat_map<const Value *, std::pair<size_t, size_t>> leakPtrViews;
  auto leakObjLabel = [&](uint32_t o) -> std::string {
    const Obj &O = objs[o];
    return O.fn ? std::string("fn") : O.layout ? O.label : std::string("unnamed");
  };
  // A pointer's objects and distinct labels ("bytes", "unnamed", "fn" for
  // the unlabeled kinds).
  auto leakPtrShape = [&](uint32_t n, size_t &objs, size_t &labels) {
    objs = labels = 0;
    if (n == UINT32_MAX || find(n) >= pts.size()) return;
    boost::unordered_flat_set<uint32_t> os;
    std::set<std::string> ls;
    pts[find(n)].forEach([&](uint32_t g) {
      for (auto [o, e] : memb[findFact(g)])
        if (os.insert(o).second)
          ls.insert(leakObjLabel(o));
    });
    objs = os.size();
    labels = ls.size();
  };
  bool leakNew = false; // the last leakSiteOf made its site
  auto leakSiteOf = [&](int cls, const std::string &where, const std::string &into,
                        const std::string &detail) -> uint32_t {
    const std::string key = std::to_string(cls) + "|" + where + "|" + into;
    auto [it, ins] = leakSiteIdx.try_emplace(key, (uint32_t)leakSites.size());
    leakNew = ins;
    if (ins) {
      leakSites.push_back({cls, where, into, detail});
      leakSites.back().firstPop = pops;
    }
    return it->second;
  };
  // The pointers of a new site, with their shapes now.
  auto leakNote = [&](uint32_t id, uint32_t ptr, uint32_t src, const Value *viewPtr,
                      const std::string &view) {
    if (!leakNew) return;
    LeakSite &L = leakSites[id];
    L.ptrNode = ptr;
    L.srcNode = src;
    leakPtrShape(ptr, L.ptrObjs, L.ptrLabels);
    leakPtrShape(src, L.srcObjs, L.srcLabels);
    L.viewPtr = viewPtr;
    L.view = view;
  };
  // A bodiless or variadic callee among V's users (the call that models
  // the write when no IR store does).
  auto leakBodiless = [](const Value *V) -> std::string {
    if (!V) return "";
    for (const User *U : V->users())
      if (const auto *CB = dyn_cast<CallBase>(U))
        if (const Function *CF = CB->getCalledFunction())
          if (CF->isDeclaration() || CF->isVarArg())
            return CF->getName().str() + " at " + instLoc(CB);
    return "";
  };
  // A value's solver node, or UINT32_MAX for one made after the solve
  // began (no constraint mentions it).
  auto leakNodeOf = [&](const Value *V) -> uint32_t {
    const NodeIndex v = V ? NF.getValueNodeFor(V) : AndersNodeFactory::InvalidIndex;
    if (v == AndersNodeFactory::InvalidIndex || v >= G) return UINT32_MAX;
    const uint32_t c = getCanonicalNode(v);
    return c < G ? find(c) : UINT32_MAX;
  };
  auto leakDesc = [&](uint32_t n) { return n == UINT32_MAX ? std::string("?") : nodeDesc(n).substr(0, 120); };
  // The pointer value a hub (a dereference node, or a keyed one) reads or
  // writes through.
  auto leakHubPtr = [&](uint32_t h, NodeIndex &par) -> const Value * {
    par = h < G ? NF.getDerefParent(h) : AndersNodeFactory::InvalidIndex;
    if (h < G && par == AndersNodeFactory::InvalidIndex) {
      if (keyedPtrOf.empty())
        for (const auto &[pk, d] : keyedDerefOf) keyedPtrOf.emplace(d, pk);
      if (auto it = keyedPtrOf.find(h); it != keyedPtrOf.end()) par = it->second.first;
    }
    return par == AndersNodeFactory::InvalidIndex ? nullptr : NF.getValueForNode(par);
  };
  // An exit's site (key) and its row.
  auto leakExitAt = [&](uint32_t a, uint32_t n, std::string &key) -> LeakExit {
    LeakExit E;
    if (auto cit = leakCopyEdge.find((uint64_t)a << 32 | n); cit != leakCopyEdge.end()) {
      const ByteCopy &BC = copies[cit->second];
      key = "copy|" + std::to_string(cit->second);
      E.kind = "byte copy into a typed cell";
      E.desc = (BC.at ? instLoc(BC.at) + " " + leakIR(BC.at) : std::string("byte copy"));
      if (auto it = leakCellOf.find(n); it != leakCellOf.end())
        E.desc += " | e.g. into " + (it->second.second == kLeakAny ? std::string("*")
                                     : cellName(it->second.first, it->second.second)) +
                  " of " + describe(objs[it->second.first]);
      return E;
    }
    key = "node|" + std::to_string(n);
    if (auto it = leakCellOf.find(n); it != leakCellOf.end()) {
      E.kind = "cell edge into a typed cell";
      E.desc = (it->second.second == kLeakAny ? std::string("*")
                : cellName(it->second.first, it->second.second)) +
               " of " + describe(objs[it->second.first]);
      return E;
    }
    if (auto dit = dispatchOf.find(n); dit != dispatchOf.end()) {
      // A receiver's level node: the dispatch reads the byte cell as the
      // holder's slot (a byte object taken for a holder struct).
      const LevelKey &LK = dit->second;
      const RecvSite &R = recvSites[LK.si];
      key = "dispatch|" + std::to_string(LK.si) + "|" + std::to_string(LK.level);
      E.kind = LK.guard == UINT32_MAX ? "method dispatch reads it as a holder's slot"
                                      : "holder guard reads it as a holder's slot";
      E.desc = (R.cs ? instLoc(R.cs) + " " + R.cs->getFunction()->getName().str() + " " + leakIR(R.cs)
                     : std::string("a pseudo site of a holder guard")) +
               ", level " + std::to_string(LK.level);
      return E;
    }
    if (n >= G || !(NF.isDereferenceNode(n) || NF.isObjectNode(n))) {
      E.kind = "other";
      E.desc = nodeDesc(n).substr(0, 160);
      return E;
    }
    // A hub: the loads it feeds (its successors). A hub that feeds nothing
    // (a pointer only stored through) reads nothing out: not an exit.
    if (succ[n].empty()) return E; // kind "": skipped
    bool allColl = true;
    for (uint32_t v : succ[n]) allColl &= leakCollHub.count(find(v)) != 0;
    const LoadInst *first = nullptr;
    size_t ptrLoads = 0, loads = 0;
    auto visit = [&](const Value *V) {
      const auto *LI = dyn_cast_or_null<LoadInst>(V);
      if (!LI) return;
      loads++;
      if (LI->getType()->isPointerTy()) ptrLoads++;
      if (!first || (LI->getType()->isPointerTy() && !first->getType()->isPointerTy())) first = LI;
    };
    if (auto it = leakHubLoads.find(n); it != leakHubLoads.end())
      for (NodeIndex v : it->second) visit(NF.getValueForNode(v));
    else // merged: the hubs whose representative n is
      for (auto &[m, vs] : leakHubLoads)
        if (find(m) == n)
          for (NodeIndex v : vs) visit(NF.getValueForNode(v));
    if (!loads)
      for (uint32_t v : succ[n]) visit(find(v) < G ? NF.getValueForNode(find(v)) : nullptr);
    if (!loads && allColl) {
      leakTransit.insert(n);
      return E; // a move: skipped here, counted where it lands
    }
    NodeIndex par;
    const Value *Vp = first ? first->getPointerOperand() : leakHubPtr(n, par);
    const std::string view = Vp ? leakStructView(Vp) : "";
    E.kind = !loads ? "hub feeding merged nodes (no load among its successors)"
             : view.empty() ? "load through a char or untyped address"
                            : "load through a struct view (" + view + ")";
    E.desc = std::to_string(ptrLoads) + " pointer loads of " + std::to_string(loads) + " fed; " +
             (first ? instLoc(first) + " " + first->getFunction()->getName().str() + " " + leakIR(first)
                    : nodeDesc(n).substr(0, 80) + " -> " + std::to_string(succ[n].size()) +
                          " successors, e.g. " + nodeDesc(find(succ[n][0])).substr(0, 120));
    return E;
  };
  auto leakExit = [&](uint32_t a, uint32_t n, uint32_t s) {
    auto [it, ins] = leakExitIdx.try_emplace((uint64_t)a << 32 | n, UINT32_MAX);
    const bool moved = leakTransit.count(a) != 0;
    if (ins) {
      if (moved && leakCollHub.count(n)) { // the move goes on
        leakTransit.insert(n);
        return;
      }
      std::string key;
      LeakExit E = leakExitAt(a, n, key);
      if (E.kind.empty()) return; // not a read (memoized as UINT32_MAX)
      if (moved) {
        key += "|move";
        E.kind = "pointer-sized move (*q = *p), then " + E.kind;
      }
      auto [kit, kins] = leakExitKey.try_emplace(key, (uint32_t)leakExits.size());
      if (kins) leakExits.push_back(std::move(E));
      it->second = kit->second;
      leakExits[it->second].edges++;
    }
    if (it->second == UINT32_MAX) return;
    if (moved && s == UINT32_MAX) return; // a move carries the cell's own facts only
    LeakExit &E = leakExits[it->second];
    E.mass++;
    if (s == UINT32_MAX) E.untagged++;
    else leakSites[s].exited++;
    if (auto cit = leakCellOf.find(a); cit != leakCellOf.end()) {
      if (E.from.size() < 64 || E.from.count(cit->second)) E.from[cit->second]++;
    } else {
      E.from[{UINT32_MAX, moved ? 1 : 0}]++;
    }
  };
  // The leak a non-char fact f makes entering byte node n along cause w.
  auto leakClassify = [&](uint32_t n, uint32_t f, const Why &w, bool hasSrc) -> uint32_t {
    uint32_t dObj = UINT32_MAX;
    int64_t dC = 0;
    std::string into;
    if (auto it = leakCellOf.find(n); it != leakCellOf.end()) {
      dObj = it->second.first;
      dC = it->second.second;
      into = (dC == kLeakAny ? std::string("*") : cellName(dObj, dC)) + " of " +
             describe(objs[dObj]);
    } else {
      into = "a cycle holding a byte cell: " + nodeDesc(n).substr(0, 120);
    }
    const bool dStruct = dObj != UINT32_MAX && objs[dObj].layout && objs[dObj].label != "i8";
    const bool dBytes = dObj != UINT32_MAX && !dStruct;
    // A store (IR, initializer or seed) by its destination: 1, 3 or 4.
    // A store whose address views its target as struct S writing a cell
    // that is not S's there: if the pointer also holds S objects, it is
    // imprecise and the byte cell is a wrong target (class 7); if it holds
    // none, the program reads this storage as S (class 3, or 1 for a
    // struct's byte field).
    std::string misView; // a struct view that does not fit the target
    auto byDest = [&](const Value *ptr, std::string &detail) {
      const std::string v = ptr ? leakStructView(ptr) : "";
      bool wrong = false;
      if (!v.empty() && dObj != UINT32_MAX) {
        std::vector<std::string> ch;
        if (dStruct && dC != kLeakAny) structChain(objs[dObj].layout, dC, DL, ch);
        bool fits = false;
        for (const std::string &e : ch) fits |= e.rfind(v + "+", 0) == 0;
        if (!fits) {
          misView = v;
          const auto tried = leakPtrViews.try_emplace(ptr);
          const auto it = tried.first;
          if (tried.second) {
            const uint32_t pn = leakNodeOf(ptr);
            if (pn != UINT32_MAX)
              pts[pn].forEach([&](uint32_t g) {
                it->second.second++;
                for (auto [o, e] : memb[findFact(g)])
                  if (objs[o].layout && objs[o].label == v) { it->second.first++; break; }
              });
          }
          detail += "; viewed as " + v + ", the pointer holds " + std::to_string(it->second.first) +
                    " " + v + " of " + std::to_string(it->second.second) + " objects";
          wrong = it->second.first > 0;
        } else {
          detail += "; viewed as " + v;
        }
      }
      if (wrong) return 7;
      if (dStruct) {
        if (dC != kLeakAny) detail += "; field " + leakFieldOf(dObj, dC);
        return 1;
      }
      if (!dBytes) return 6;
      return v.empty() ? 4 : 3;
    };
    if (!hasSrc || w.kind != W_EDGE) {
      static const char *kinds[] = {"seed or initializer", "edge", "field step", "pointer walk",
                                    "any-offset step", "hub", "byte copy", "dispatch"};
      std::string detail = kinds[w.kind];
      if (hasSrc) detail += " from " + nodeDesc(find(w.node)).substr(0, 140);
      const int cls = w.kind == W_OTHER ? byDest(nullptr, detail) : 6;
      return leakSiteOf(cls, kinds[w.kind], into, detail);
    }
    const uint32_t a = find(w.node);
    if (auto cit = leakCopyEdge.find((uint64_t)a << 32 | n); cit != leakCopyEdge.end()) {
      const ByteCopy &BC = copies[cit->second];
      std::string from = "?";
      if (auto it = leakCellOf.find(a); it != leakCellOf.end())
        from = (it->second.second == kLeakAny ? std::string("*")
                                               : cellName(it->second.first, it->second.second)) +
               " of " + describe(objs[it->second.first]);
      const uint32_t id = leakSiteOf(2, BC.at ? instLoc(BC.at) + " " + leakIR(BC.at) : "byte copy", into,
                                     "from " + from + (dStruct ? "; into a struct interior" : ""));
      leakNote(id, find(BC.dst), find(BC.src), nullptr, "");
      return id;
    }
    if (auto hit = leakCollHub.find(a); hit != leakCollHub.end()) {
      const uint32_t h = hit->second;
      NodeIndex par;
      const Value *Vp = leakHubPtr(h, par);
      auto holds = [&](const Value *V) {
        const uint32_t vn = leakNodeOf(V);
        return vn != UINT32_MAX && pts[vn].test(f);
      };
      const StoreInst *SI = nullptr;
      bool held = true;
      if (auto sit = leakCollStores.find(a); sit != leakCollStores.end()) {
        for (const StoreInst *S : sit->second)
          if (holds(S->getValueOperand())) { SI = S; break; }
        if (!SI && !sit->second.empty()) { SI = sit->second.front(); held = false; }
      }
      if (!SI && Vp)
        for (const User *U : Vp->users())
          if (const auto *S = dyn_cast<StoreInst>(U))
            if (S->getPointerOperand() == Vp && holds(S->getValueOperand())) { SI = S; break; }
      const Value *Vv = nullptr;
      for (uint32_t v : leakCollIn[a])
        if (find(v) < pts.size() && pts[find(v)].test(f)) { Vv = NF.getValueForNode(v); break; }
      if (!SI && Vv)
        for (const User *U : Vv->users())
          if (const auto *S = dyn_cast<StoreInst>(U))
            if (S->getValueOperand() == Vv) {
              const uint32_t pn = leakNodeOf(S->getPointerOperand());
              if (pn == UINT32_MAX) continue;
              const auto &hs = hubsOf[pn];
              if (std::find(hs.begin(), hs.end(), h) != hs.end()) { SI = S; break; }
            }
      if (SI) {
        std::string detail = leakIR(SI) + (held ? "" : " (one of the collector's stores; none holds the fact now)");
        const int cls = byDest(SI->getPointerOperand(), detail);
        const uint32_t id = leakSiteOf(cls, instLoc(SI) + " " + SI->getFunction()->getName().str(), into, detail);
        leakNote(id, leakNodeOf(SI->getPointerOperand()), leakNodeOf(SI->getValueOperand()),
                 SI->getPointerOperand(), misView);
        return id;
      }
      std::string call = leakBodiless(Vp);
      if (call.empty()) call = leakBodiless(Vv);
      // A memcpy or memmove modeled as a load and a store: a byte copy.
      if (StringRef(call).starts_with("llvm.memcpy") || StringRef(call).starts_with("llvm.memmove")) {
        const uint32_t id = leakSiteOf(2, call, into, "a copy modeled as a load-store pair (*q = *p); pointer " +
                                                          leakDesc(leakNodeOf(Vp)));
        leakNote(id, leakNodeOf(Vp), leakNodeOf(Vv), nullptr, "");
        return id;
      }
      const std::string detail = "no IR store; pointer " + leakDesc(leakNodeOf(Vp)) +
                                 "; value " + leakDesc(leakNodeOf(Vv));
      return leakSiteOf(call.empty() ? 6 : 5, call.empty() ? "store collector" : call, into, detail);
    }
    if (auto it = leakCellOf.find(a); it != leakCellOf.end()) {
      const auto [so, sc] = it->second;
      if (sc == kLeakAny)
        return leakSiteOf(6, "any-offset write of " + describe(objs[so]), into, "");
      return leakSiteOf(6, "cell edge from " + cellName(so, sc) + " of " + describe(objs[so]), into,
                        "a byte copy merged away, or a union or tag-flip edge");
    }
    if (a < G && NF.isVarargNode(a))
      return leakSiteOf(5, "vararg pool " + nodeDesc(a).substr(0, 100), into, "");
    return leakSiteOf(6, "edge from " + nodeDesc(a).substr(0, 140), into, "");
  };
  if (CFLCellLeakCensus) {
    leakArrive = [&](uint32_t n, uint32_t f) {
      if (soupStop) return;
      f = findFact(f);
      const Why w = curWhy;
      const bool hasSrc = w.node < numNodes && w.fact < cells.size() &&
                          (w.kind == W_EDGE || w.kind == W_STEP || w.kind == W_WALK ||
                           w.kind == W_ANY || w.kind == W_DISPATCH);
      // An edge out of a byte cell into a node that is not one: an exit.
      auto exits = [&]() {
        return hasSrc && w.kind == W_EDGE && !leakIsByte(n) &&
               (leakIsByte(find(w.node)) || leakTransit.count(find(w.node)));
      };
      if (hasSrc) {
        auto it = leakTag.find((uint64_t)find(w.node) << 32 | findFact(w.fact));
        if (it != leakTag.end()) {
          leakTag.emplace((uint64_t)n << 32 | f, it->second);
          if (leakFactKind(f) && exits()) leakExit(find(w.node), n, it->second);
          return;
        }
      }
      if (!leakFactKind(f)) return;
      if (!leakIsByte(n)) {
        if (exits()) leakExit(find(w.node), n, UINT32_MAX);
        if (auto it = leakCellOf.find(n); it != leakCellOf.end()) {
          const Obj &O = objs[it->second.first];
          if (!O.layout && !O.fn)
            leakProv.try_emplace((uint64_t)n << 32 | f, leakClassify(n, f, w, hasSrc));
        }
        return;
      }
      const uint32_t s = leakClassify(n, f, w, hasSrc);
      leakSites[s].born++;
      leakTag.emplace((uint64_t)n << 32 | f, s);
    };
    leakMerge = [&](uint32_t r, uint32_t m) {
      if (leakIsByte(m)) leakMergedByte.insert(r);
      pts[m].forEach([&](uint32_t f) {
        auto it = leakTag.find((uint64_t)m << 32 | f);
        if (it != leakTag.end()) leakTag.try_emplace((uint64_t)r << 32 | f, it->second);
        auto pit = leakProv.find((uint64_t)m << 32 | f);
        if (pit != leakProv.end()) leakProv.try_emplace((uint64_t)r << 32 | f, pit->second);
      });
    };
    // Cells of o renamed (bytes, a period, a layout): a provisional entry
    // in what is now a byte cell becomes its leak.
    leakRefold = [&](uint32_t o) {
      // The refold merged o's cells (and moved a header's past its end to
      // the trailing object): the representatives stand for o's cells now.
      for (auto &[c, up] : objs[o].content) {
        leakCellOf[find(up.first)] = std::make_pair(o, c);
        leakCellOf[find(up.second)] = std::make_pair(o, c);
      }
      for (auto &[c, up] : objs[o].content) {
        if (!leakByteCell(o, c)) continue;
        for (uint32_t x : {up.first, up.second}) {
          const uint32_t R = find(x);
          if (leakProv.empty() || R >= pts.size()) continue;
          pts[R].forEach([&](uint32_t f0) {
            const uint32_t f = findFact(f0);
            const uint64_t k = (uint64_t)R << 32 | f;
            if (leakTag.count(k)) return;
            auto pit = leakProv.find(k);
            if (pit == leakProv.end()) pit = leakProv.find((uint64_t)R << 32 | f0);
            if (pit == leakProv.end()) return;
            leakTag.emplace(k, pit->second);
            leakSites[pit->second].born++;
          });
        }
      }
    };
  }

  // ---- The icall cone (--cfl-cell-one-label) ----
  // Nodes whose facts can reach an indirect call's callee operand, on the
  // current graph: backward over copy edges, field steps (the base
  // pointer), hubs (the pointer whose facts pick the cells) and store
  // collectors (the store's pointer); a byte copy into a cone cell brings
  // in its two pointers. Recomputed as the graph grows.
  std::vector<uint32_t> icallOps;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F))
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (!CB->isInlineAsm() && !isa<Function>(CB->getCalledOperand()->stripPointerCasts())) {
            const NodeIndex vn = NF.getValueNodeFor(CB->getCalledOperand());
            if (vn != AndersNodeFactory::InvalidIndex) icallOps.push_back(canon(vn));
          }
  std::vector<char> inCone;
  size_t coneSize = 0;
  auto computeCone = [&]() {
    std::vector<std::vector<uint32_t>> rev(numNodes);
    for (uint32_t u = 0; u < numNodes; u++) {
      if (find(u) != u) continue;
      for (uint32_t v : succ[u]) rev[find(v)].push_back(u);
      for (const FieldEdge &e : fieldOut[u]) rev[find(e.dst)].push_back(u);
      for (uint32_t h : hubsOf[u]) {
        rev[find(h)].push_back(u);
        if (h < G && storeHub[h] != UINT32_MAX) rev[find(storeHub[h])].push_back(u);
      }
    }
    inCone.assign(numNodes, 0);
    std::vector<uint32_t> work;
    auto mark = [&](uint32_t x) {
      x = find(x);
      if (!inCone[x]) { inCone[x] = 1; work.push_back(x); }
    };
    for (uint32_t s : icallOps) mark(s);
    for (int round = 0; round < 4; round++) {
      while (!work.empty()) {
        const uint32_t x = work.back();
        work.pop_back();
        for (uint32_t u : rev[x]) mark(u);
      }
      // Byte copies into a cone cell: their pointers decide what is copied.
      for (const ByteCopy &C : copies) {
        const uint32_t d = find(C.dst);
        if (inCone[d] && inCone[find(C.src)]) continue;
        bool hit = false;
        pts[d].forEach([&](uint32_t f) {
          if (hit) return;
          for (auto [o, e] : memb[findFact(f)]) {
            for (auto &[c, up] : objs[o].content)
              if (inCone[find(up.first)] || inCone[find(up.second)]) { hit = true; break; }
            if (hit) break;
          }
        });
        if (hit) { mark(C.src); mark(C.dst); }
      }
      if (work.empty()) break;
    }
    coneSize = 0;
    for (uint32_t u = 0; u < numNodes; u++) coneSize += inCone[u];
  };
  // Objects that carry function pointers: their content holds a function,
  // or a pointer to such an object (fixpoint). A conflict can add a wrong
  // icall target only through such objects.
  std::vector<char> fptrObj;
  auto computeFptrObjs = [&]() {
    fptrObj.assign(objs.size(), 0);
    auto nodesOf = [&](uint32_t o, auto &&fn) {
      for (auto &[c, up] : objs[o].content) { fn(find(up.first)); fn(find(up.second)); }
      for (auto &[kk, kn] : objs[o].keyed) fn(find(kn));
    };
    for (int round = 0; round < 16; round++) {
      bool changed = false;
      for (uint32_t o = 0; o < objs.size(); o++) {
        if (fptrObj[o] || objs[o].fn) continue;
        bool hit = false;
        nodesOf(o, [&](uint32_t m) {
          if (hit || m >= pts.size()) return;
          pts[m].forEach([&](uint32_t x) {
            if (hit) return;
            const Cell &C = cells[findFact(x)];
            if (C.kind == CellKind::Func) { hit = true; return; }
            for (auto [o2, e] : memb[findFact(x)])
              if (o2 < fptrObj.size() && fptrObj[o2]) { hit = true; break; }
          });
        });
        if (hit) { fptrObj[o] = 1; changed = true; }
      }
      if (!changed) break;
    }
  };
  auto factCarriesFptrs = [&](uint32_t f) {
    for (auto [o, e] : memb[findFact(f)])
      if (o < fptrObj.size() && fptrObj[o]) return true;
    return false;
  };
  size_t coneReported = 0, coneHarmless = 0;
  auto flushPending = [&](bool final) {
    if (pendingConf.empty() && !final) return;
    computeCone();
    computeFptrObjs();
    std::vector<PendingConflict> keep;
    for (PendingConflict &P : pendingConf) {
      if (!inCone[find(P.n)]) { keep.push_back(P); continue; }
      // Fact level: only objects carrying function pointers can change a
      // target set (both sides for two names; the stepped or copied object
      // otherwise). Harmless ones wait: the fixpoint may still change.
      const bool matters =
          P.kind == 0 ? factCarriesFptrs(P.a) && factCarriesFptrs(P.f)
          : factCarriesFptrs(P.f); // the stepped / copied-from object
      if (!matters) {
        if (final) coneHarmless++;
        else keep.push_back(P);
        continue;
      }
      if (CFLCellOneLabelMax <= 1) {
        CG_LOG("Cells: (inside the icall cone: " << coneSize << " nodes from "
               << icallOps.size() << " icall operands; the conflict arose at pop "
               << P.pop << ")\n");
        if (P.kind == 1) reportTypedStep(P.n, findFact(P.f), P.S, P.why.c_str()); // exits
        if (P.kind == 0) reportConflict(P.n, findFact(P.a), findFact(P.f));
        else CG_LOG("Cells: NAME CONFLICT at pop " << P.pop
                    << ": a copy between unrelated structs: " << P.why << "\n");
        reportDefects();
        errs() << "Cells: --cfl-cell-one-label stopped at the first name "
               << "conflict inside the icall cone (measurement only, no answers)\n";
        exit(0);
      }
      if (P.kind != 0) continue; // collect mode counts those in otherMeets
      conflicts++;
      coneReported++;
      const uint32_t a = findFact(P.a), f = findFact(P.f);
      CG_LOG("Cells: NAME CONFLICT #" << conflicts << " at pop " << P.pop << ": "
             << nodeDesc(P.n) << ": A = " << factDesc(a).substr(0, 160)
             << " | B = " << factDesc(f).substr(0, 160) << "\n");
      meetPoints(P.n, a, f);
      if (conflicts >= CFLCellOneLabelMax) finishCollect();
    }
    pendingConf.swap(keep);
    if (final)
      CG_LOG("Cells: icall cone " << coneSize << " nodes from " << icallOps.size()
             << " icall operands; " << pendingConf.size() + pendingDup
             << " conflicts outside it (unreported), " << coneHarmless
             << " inside but without function-pointer objects on both sides, "
             << coneReported << " inside\n");
  };
  std::vector<uint32_t> delta;
  // Plan 3.54: facts a split formal holds before the solve (seeds) entered
  // it other than by a dispatch.
  for (uint32_t fi = 0; fi < entryF.size(); fi++)
    if (entryF[fi].A != UINT32_MAX) {
      std::vector<uint32_t> fs;
      pts[find(entryF[fi].A)].forEach([&](uint32_t f) { fs.push_back(findFact(f)); });
      for (uint32_t f : fs) entryOtherFn(fi, f);
    }
  for (auto &[cn, xy] : chanOfNode) { // plan 3.54 (b): a channel's facts before the solve
    std::vector<uint32_t> fs;
    pts[find(cn)].forEach([&](uint32_t f) { fs.push_back(findFact(f)); });
    for (uint32_t f : fs) chanArriveFn(xy.first, xy.second, f);
  }
  uint64_t lastCollapsePops = 0;
  size_t edgesAtCollapse = edgeSet.size();
  uint32_t stoppedAt = 0;
  while (true) {
    if (!refoldQueue.empty()) drainRefolds();
    if (worklist.empty()) {
      if (!keyedWait.empty()) {
        flushKeyedWait();
        if (!worklist.empty()) continue;
      }
      if (CFLCellOneLabel) flushPending(true);
      break;
    }
    const uint32_t n = worklist.back();
    worklist.pop_back();
    inWL[n] = 0;
    if (find(n) != n) continue; // merged: its facts moved to the rep
    if (CFLCellSoupProfile && CFLCellSoupTime && (pops & 0xfff) == 0 &&
        std::chrono::duration<double>(Clock::now() - tSolve).count() > CFLCellSoupTime) {
      errs() << "Cells: --cfl-cell-soup-time reached; ";
      soupStop = true;
    }
    if (soupStop) {
      errs() << "Cells: --cfl-cell-soup-profile stopping at " << soupForeign.size()
             << " foreign facts (measurement only, no answers)\n";
      if (!taggedPairs.empty())
        errs() << "Cells: at the stop: " << pops << " pops; tagged pairs " << taggedPairs.size() << ", "
               << taggedFlipped.size() << " flipped; alias assumptions " << asmFailed << " of " << asmUsed
               << " failed\n";
      for (const std::string &d : taggedFlipAt) errs() << "Cells:   unkeyed during solve: " << d << "\n";
      for (const std::string &d : asmFailSites) errs() << "Cells:   alias assumption failed at " << d << "\n";
      stoppedAt = pops;
      break;
    }
    if (whyAnyArrived) {
      errs() << "Cells: --cfl-cell-why any: the queried any-offset cell arrived; "
             << "stopping (measurement only, no answers)\n";
      stoppedAt = pops;
      break;
    }
    // Pops counted over all iterations (the stop lands in the iteration
    // that explodes, not in an earlier, cheap one).
    static uint64_t allPops = 0;
    if (CFLCellCensusAt && ++allPops >= CFLCellCensusAt) {
      if (!recordWhy) confluenceCensus();
      errs() << "Cells: --cfl-cell-census-at stopped the solve (measurement "
             << "only, no answers)\n";
      if (!recordWhy && CFLCellStopAnswers.empty()) exit(0);
      stoppedAt = pops; // the why reports and the stop answers describe the partial state
      break;
    }
    delta.clear();
    delta.swap(pend[n]);
    if (delta.empty()) continue;
    whyClock = pops;
    if (CFLCellOneLabel && (pops & 0x1fff) == 0 && !pendingConf.empty())
      flushPending(false);
    if (++pops % (1u << 20) == 0) {
      size_t mass = 0;
      for (uint32_t m = 0; m < numNodes; m++) mass += pts[m].count();
      CG_LOG("Cells: progress " << pops << " pops, " << worklist.size()
             << " queued, " << numNodes << " nodes, " << cells.size()
             << " cells, " << mass << " facts, " << edgeSet.size()
             << " edges, " << stepCalls << " steps, "
             << std::chrono::duration<double>(Clock::now() - tSolve).count()
             << " s\n");
      topObjects(4);
      interiorReport();
      if (!taggedPairs.empty())
        CG_LOG("Cells: alias assumptions so far: " << asmFailed << " of " << asmUsed << " failed, "
               << taggedFlipped.size() << " tagged pairs flipped\n");
      if (pops % (1u << 22) == 0) massByObject(12);
    }
    for (uint32_t &f : delta) f = findFact(f);
    if (!entryOfAo.empty()) // plan 3.54: objects entering a split formal otherwise
      if (auto eit = entryOfAo.find(n); eit != entryOfAo.end())
        for (uint32_t f : delta) entryOtherFn(eit->second, f);
    if (!chanOfNode.empty()) // plan 3.54 (b): objects passed on through a channel
      if (auto cit = chanOfNode.find(n); cit != chanOfNode.end())
        for (uint32_t f : delta) chanArriveFn(cit->second.first, cit->second.second, f);
    if (!chanFrom.empty()) // plan 3.54 (b): a channel source's new facts, on to its channels
      if (auto cit = chanFrom.find(n); cit != chanFrom.end())
        for (uint32_t cn : std::vector<uint32_t>(cit->second))
          for (uint32_t f : delta) add(cn, f);
    if (!watchAt.empty())
      if (auto wit = watchAt.find(n); wit != watchAt.end())
        for (uint32_t wi : std::vector<uint32_t>(wit->second))
          for (uint32_t f : delta)
            if (watchSeen.insert((uint64_t)wi << 32 | f).second) watchCheck(wi, f);
    if (!asmAt.empty())
      if (auto ait = asmAt.find(n); ait != asmAt.end())
        for (const AsmEntry &E : std::vector<AsmEntry>(ait->second))
          for (uint32_t f : delta) asmCheck(E, f);
    if (!passOf.empty()) {
      auto pit = passOf.find(n);
      if (pit != passOf.end()) { // a path store's value: admitted
        for (uint32_t f : delta) {
          guardAdmitted.insert((uint64_t)pit->second << 32 | f);
          admitting = true;
          add(guards[pit->second].node, f);
          admitting = false;
        }
        continue;
      }
    }
    if (!dispatchOf.empty() && dispatchOf.count(n)) {
      dispatch(n, delta);
      continue;
    }
    if (!recvAt.empty()) {
      auto rit = recvAt.find(n);
      if (rit != recvAt.end())
        for (uint32_t si : std::vector<uint32_t>(rit->second))
          for (uint32_t f : delta) {
            if (trackWhy) curWhy = {n, f, UINT32_MAX, W_DISPATCH};
            bindReceiver(si, f);
          }
    }
    // One label per pointer: an arriving cell of the anchor's name merges
    // into it; a cell of another name is the anomaly: stop and report.
    if (CFLCellOneLabel && !unionView[n]) { // a union's views hold every member
      for (uint32_t &f : delta) {
        if (cells[f].kind != CellKind::Off) continue;
        // An unknown object (not yet used as anything) passes by: no
        // label, no conflict, no merge. Re-examined here once typed.
        bool unknown = true;
        for (auto [o, e] : memb[f])
          unknown &= !objs[o].layout;
        if (unknown) {
          for (auto [o, e] : memb[f]) passedBy[o].push_back({n, f});
          continue;
        }
        if (oneCell[n] == UINT32_MAX) { oneCell[n] = f; continue; }
        const uint32_t a = findFact(oneCell[n]);
        if (a == f) continue;
        // Memoized per fact pair (facts do not change their names or
        // objects once merged; the test builds struct chains).
        int compat;
        {
          const uint64_t key = (uint64_t)a << 32 | f;
          auto cit = compatMemo.find(key);
          if (cit != compatMemo.end()) compat = cit->second;
          else compatMemo.emplace(key, compat = namesCompatible(a, f));
        }
        // The check observes the solution, it does not change it: cells of
        // one name (several objects) are one label already; merging their
        // facts unified the objects by name (every step and hub on the
        // merged fact reached all of them: 150x the facts on libpng).
        if (compat != 0) continue;
        if (!seenConflict.insert(std::make_tuple(n, cells[a].name, cells[f].name)).second)
          continue;
        // Judged when the icall cone is known (flushPending).
        pend1({0, n, a, f, nullptr, "", pops});
        // keep both labels at n and go on
      }
      if (find(n) != n) continue;
    }
    // Unification by name: a node holds one cell per name.
    if (CFLCellUnify) {
      for (uint32_t &f : delta) {
        if (cells[f].kind != CellKind::Off) continue;
        auto [it, ins] = byName[n].try_emplace(cells[f].name, f);
        if (!ins) f = it->second = mergeFacts(it->second, f);
      }
      if (find(n) != n) continue; // absorbed by a merge: the rep re-runs
    }
    {
      for (uint32_t h : hubsOf[n])
        for (uint32_t f : delta) {
          if (trackWhy) curWhy = {n, f, UINT32_MAX, W_HUB};
          linkHub(h, f);
        }
      curStepNode = n;
      anyCauseNode = n;
      for (size_t ei = 0; ei < fieldOut[n].size(); ei++) {
        const FieldEdge e = fieldOut[n][ei];
        for (uint32_t f : delta) {
          if (trackWhy) curWhy = {n, f, UINT32_MAX, e.walk ? W_WALK : W_STEP};
          curStepDst = e.dst;
          curStepLi = e.li;
          if (e.walk) applyWalk(f, e);
          else applyStep(f, e.li, e.dst);
        }
      }
      if (anyLoop[n])
        for (uint32_t f : delta) {
          const CellKind k = cells[f].kind;
          if (trackWhy) curWhy = {n, f, UINT32_MAX, W_ANY};
          if (k == CellKind::Off || k == CellKind::Out)
            toAny(f, n);
        }
    }
    if (!copiesAt[n].empty()) applyCopies(n, delta);
    for (uint32_t m : succ[n])
      for (uint32_t f : delta) {
        if (trackWhy) curWhy = {n, f, UINT32_MAX, W_EDGE};
        add(m, f);
      }
    curWhy = Why();
    if (VerboseLevel >= 2 && pops % (1u << 16) == 0)
      CG_LOG("Cells: at " << pops << " pops: " << finalizes << " finalizes re-ran "
             << refacts << " facts; " << factMerges << " fact merges, "
             << ptrMerges << " ptr merges, " << hubLinks << " hub links\n");
    if (CFLCellCollapse && pops - lastCollapsePops >= (1u << 18) &&
        edgeSet.size() > edgesAtCollapse + edgesAtCollapse / 8) {
      collapseCycles();
      rekeyReceivers();
      dropMergedGuards();
      if (CFLCellMergePtrs) mergeEqualSets();
      if (CFLCellUnify) canonicalizeSets();
      lastCollapsePops = pops;
      edgesAtCollapse = edgeSet.size();
    }
  }
  // Collect mode runs on through the iterations (a soup often forms only
  // after calls resolve); it ends at the cap or at the last iteration.
  dynEdges = edgeSet.size() - staticEdges;
  const double solveSecs =
      std::chrono::duration<double>(Clock::now() - tSolve).count();

  // ---- Answers ----
  size_t resolved = 0, totalTargets = 0, newPairs = 0, typeRej = 0;
  // In IR order, targets in IR order: the wiring order sets the next
  // iteration's edge order.
  const std::vector<const CallBase *> icallSnapshot = icallsSorted;
  std::vector<std::pair<const CallBase *, std::vector<std::string>>> stopAnswers;
  for (const CallBase *CS : icallSnapshot) {
    Value *fptr = CS->getCalledOperand()->stripPointerCastsAndAliases();
    const NodeIndex fn = NF.getValueNodeFor(fptr);
    if (fn == AndersNodeFactory::InvalidIndex) continue;
    if (getCanonicalNode(fn) >= G) continue;
    const uint32_t n = find(getCanonicalNode(fn));
    FuncSet targets;
    pts[n].forEach([&](uint32_t f) {
      const Cell &C = cells[f];
      if (C.kind != CellKind::Func) return;
      const Function *F = objs[C.obj].fn;
      if (const Function *called = CS->getCalledFunction())
        if (F == called || F->getGUID() == called->getGUID()) return;
      if (!isCompatible(CS, F)) { typeRej++; return; }
      targets.insert(F);
    });
    if (!targets.empty()) { resolved++; totalTargets += targets.size(); }
    if (stoppedAt && !CFLCellStopAnswers.empty()) {
      std::vector<std::string> names;
      for (const Function *F : targets) names.push_back(F->getName().str());
      std::sort(names.begin(), names.end());
      stopAnswers.push_back({CS, std::move(names)});
    }
    std::vector<const Function *> targetsSorted(targets.begin(), targets.end());
    std::sort(targetsSorted.begin(), targetsSorted.end(), [&](const Function *a, const Function *b) {
      const uint64_t ka = stableKey(a), kb = stableKey(b);
      return ka != kb ? ka < kb : a->getName() < b->getName();
    });
    for (const Function *F : targetsSorted)
      if (wireResolvedCallee(CS, F)) newPairs++;
  }

  // ---- Report ----
  size_t factMass = 0, offCells = 0, anyCells = 0;
  for (uint32_t n = 0; n < numNodes; n++) factMass += pts[n].count();

  CG_LOG("Cells: " << walkEdges << " field edges on cycles (pointer walks), "
         << walkSteps << " walk steps, " << indexOutsideArray
         << " variable indexes on a single object (array of one), " << indexStays
         << " constant indexes staying in their array, " << indexAsOffset
         << " constant indexes outside an array of their element (byte offsets), "
         << "byte offsets from inside a byte array: " << byteStepStays << " stay in it, "
         << byteStepContainer << " leave it for a struct start (container_of), " << byteStepUB
         << " leave it otherwise (undefined behavior: not followed), " << byteStepStructRel
         << " from a byte address (struct-relative); walks from inside a byte array: "
         << byteWalkStays << " stay in it, " << byteWalkStructRel << " also struct-relative, "
         << leafMerges << " same-leaf coexistences (unmerged); "
         << "learned " << layoutsLearned << " layouts, " << periodsLearned
         << " element sizes; extents: " << extentArrays << " arrays by size, " << extentOne
         << " one by size, " << extentHeader << " header + data by size, " << extentUnknown
         << " one then unknown (size unknown), " << arraysExtended << " made arrays by a T-stride access ("
         << extendRefused << " refused: typed trailing data; " << tailIndexAny
         << " other variable indexes also reach the data after the T); " << tailWritesFolded
         << " writes of another struct into the data after a T (rule (b): not admitted); " << readStepsSkipped
         << " member steps through unlabeled objects that do not write (no label), "
         << varByteAny << " variable byte steps into unlabeled objects (their any-offset cell), "
         << keyedWaits << " keyed accesses waited for a label (" << keyedFlushed
         << " linked unkeyed at the fixpoint: never labeled) ("
         << refoldMerges << " cells merged by re-folding)\n");
  if (CFLCellUnify) canonicalizeSets();
  CG_LOG("Cells: " << leftObject << " byte offsets leaving a single "
         << "object (outside: one past the end, never dereferenced)\n");
  CG_LOG("Cells: " << cellHubKey.size() << " keyed union accesses, "
         << splitCells << " union-slot cells (" << lateSplits << " split when their object was typed), " << keyedCells
         << " keyed cells\n");
  // --cfl-cell-why: the chain of first causes that brought a cell of
  // `want` into `target`, latest first; the pointers whose hub links or
  // steps the chain used are explained in turn (two levels).
  // factDesc names offset cells only.
  auto whyDesc = [&](uint32_t f) {
    f = findFact(f);
    return cells[f].kind == CellKind::Off ? factDesc(f) : factDescP(f);
  };
  std::function<void(uint32_t, const std::string &, int)> explainWhy2;
  auto explainWhy = [&](uint32_t target, const std::string &want) {
    explainWhy2(target, want, 0);
  };
  explainWhy2 = [&](uint32_t target, const std::string &want, int depth) {
    const std::string ind(2 + depth * 4, ' ');
    auto matches = [&](uint32_t f) {
      f = findFact(f);
      if (describe(objs[cells[f].obj]).find(want) != std::string::npos) return true;
      for (auto [o, e] : memb[f])
        if (describe(objs[o]).find(want) != std::string::npos) return true;
      return false;
    };
    uint32_t f0 = UINT32_MAX;
    pts[target].forEach([&](uint32_t f) {
      if (f0 == UINT32_MAX && matches(f)) f0 = f;
    });
    if (f0 == UINT32_MAX) {
      CG_LOG("Cells:" << ind << nodeDesc(target) << " holds no cell of '" << want << "'\n");
      return;
    }
    CG_LOG("Cells:" << ind << "why does " << nodeDesc(target) << " hold "
           << whyDesc(f0) << "? (latest cause first)\n");
    std::vector<std::pair<uint32_t, uint32_t>> pointers; // pointer, its fact
    boost::unordered_flat_set<uint64_t> seen;
    uint32_t n = target, f = f0;
    for (int k = 0; k < 400; k++) {
      const uint64_t key = (uint64_t)n << 32 | f;
      if (!seen.insert(key).second) { CG_LOG("Cells:" << ind << "  (cycle)\n"); break; }
      auto it = factWhy.find(key);
      if (it == factWhy.end()) {
        CG_LOG("Cells:" << ind << "  " << nodeDesc(n) << ": " << whyDesc(f)
               << " (seed, or arrived before a merge)\n");
        break;
      }
      const Why w = it->second;
      std::string how;
      switch (w.kind) {
      case W_EDGE: {
        auto eit = edgeWhy.find((uint64_t)w.node << 32 | n);
        const Why e = eit == edgeWhy.end() ? Why() : eit->second;
        if (e.kind == W_HUB) {
          how = "edge made by a load/store through " + nodeDesc(e.node) +
                " holding " + whyDesc(e.fact);
          pointers.push_back({find(e.node), e.fact});
        } else if (e.kind == W_COPY) {
          how = "byte copy " + instLoc(copies[e.node].at) + " (" +
                whyDesc(e.fact) + " into " + whyDesc(e.extra) + ")";
          pointers.push_back({find(copies[e.node].src), e.fact});
        } else if (e.kind == W_OTHER && eit != edgeWhy.end()) {
          how = "edge (made outside the propagation loop)";
        } else if (eit == edgeWhy.end()) {
          how = "static copy edge or byte-copy content edge (unrecorded)";
        } else {
          static const char *kn[] = {"other", "edge", "step", "walk", "any-offset", "hub", "copy", "dispatch"};
          how = std::string("edge made during a ") + kn[e.kind] + " at " +
                (e.node < numNodes ? nodeDesc(e.node) : std::string("?")) +
                " holding " + (e.fact < cells.size() ? whyDesc(e.fact) : std::string("?"));
          if (e.node < numNodes && e.fact < cells.size())
            pointers.push_back({find(e.node), e.fact});
        }
        break;
      }
      case W_STEP: how = "step"; break;
      case W_WALK: how = "walk"; break;
      case W_ANY: how = "any-offset (field-any loop)"; break;
      case W_DISPATCH:
        how = "method dispatch of " +
              (w.extra < cells.size() ? whyDesc(w.extra) : std::string("?")) +
              " to the receiver";
        break;
      default: how = "other (seed, refold, finalize, merge replay)"; break;
      }
      if (w.kind == W_STEP || w.kind == W_WALK || w.kind == W_ANY ||
          w.kind == W_DISPATCH) {
        how += " of " + whyDesc(w.fact);
        CG_LOG("Cells:" << ind << "  " << nodeDesc(n) << " <- " << how << "\n");
        if (w.node == UINT32_MAX) break;
        n = find(w.node);
        f = findFact(w.fact);
        continue;
      }
      CG_LOG("Cells:" << ind << "  " << nodeDesc(n) << " <- " << how << "\n");
      if (w.kind != W_EDGE || w.node == UINT32_MAX) break;
      n = find(w.node);
      f = findFact(w.fact);
    }
    if (depth >= 2) return;
    // The first pointers the chain loaded or copied through.
    for (size_t i = 0; i < pointers.size() && i < 2; i++) {
      const uint32_t fo = findFact(pointers[i].second);
      const std::string w = describe(objs[cells[fo].obj]);
      explainWhy2(pointers[i].first, w.substr(0, w.find(" [")), depth + 1);
    }
  };
  // Boundary census (measurement, plan 3.51 Part C input): through which
  // function boundary did each soup entry's foreign name come? From the
  // entry's first entering source, walk backward over the nodes holding
  // a cell of that fact's object (copy, hub and field edges) to the first
  // boundary of a function with two or more call sites (or its address
  // taken): a pointer formal, a load through a formal (an out-parameter
  // read or a field of the formal), the collector of stores through a
  // formal (an out-parameter write), or the return. The entry's mass is
  // attributed to it; entries with no such boundary on the path are
  // counted as unattributed.
  auto soupBoundaryCensus = [&](const std::vector<uint32_t> &order, size_t total) {
    // The formal a pointer derives from: the argument itself, or (-O0) a
    // load of the slot the argument was spilled to; through GEPs (field).
    auto formalOf = [](const Value *P, bool &field) -> const Argument * {
      field = false;
      for (int k = 0; k < 8 && P; k++) {
        P = P->stripPointerCasts();
        if (const auto *A = dyn_cast<Argument>(P)) return A;
        if (const auto *GP = dyn_cast<GEPOperator>(P)) { field = true; P = GP->getPointerOperand(); continue; }
        if (const auto *L = dyn_cast<LoadInst>(P))
          if (const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
            for (const User *U : AI->users())
              if (const auto *SI = dyn_cast<StoreInst>(U))
                if (SI->getPointerOperand()->stripPointerCasts() == AI)
                  if (const auto *A = dyn_cast<Argument>(SI->getValueOperand()->stripPointerCasts()))
                    return A;
          }
        return nullptr;
      }
      return nullptr;
    };
    auto sitesOf = [](const Function *F) {
      size_t n = 0;
      for (const User *U : F->users())
        if (const auto *CB = dyn_cast<CallBase>(U))
          if (CB->getCalledOperand() == F) n++;
      return n;
    };
    // The values a function returns, through -O0 slots (bounded).
    auto retShape = [&](const Function *F) -> std::string {
      std::set<std::string> shapes;
      std::vector<const Value *> work;
      std::set<const Value *> seen;
      for (const BasicBlock &BB : *F)
        if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
          if (RI->getReturnValue()) work.push_back(RI->getReturnValue());
      while (!work.empty() && seen.size() < 64) {
        const Value *V = work.back()->stripPointerCasts();
        work.pop_back();
        if (!seen.insert(V).second) continue;
        if (const auto *PN = dyn_cast<PHINode>(V)) {
          for (const Value *In : PN->incoming_values()) work.push_back(In);
        } else if (const auto *SL = dyn_cast<SelectInst>(V)) {
          work.push_back(SL->getTrueValue());
          work.push_back(SL->getFalseValue());
        } else if (const auto *L = dyn_cast<LoadInst>(V)) {
          const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
          if (AI) {
            for (const User *U : AI->users())
              if (const auto *SI = dyn_cast<StoreInst>(U))
                if (SI->getPointerOperand()->stripPointerCasts() == AI)
                  work.push_back(SI->getValueOperand());
          } else {
            bool field;
            shapes.insert(formalOf(L->getPointerOperand(), field) && !field
                              ? "return of a load through a formal"
                              : "return of a load (lookup)");
          }
        } else if (const auto *CB = dyn_cast<CallBase>(V)) {
          if (const Function *T = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts())) {
            shapes.insert("return of a call to " + T->getName().str());
          } else {
            const auto *CL = dyn_cast<LoadInst>(CB->getCalledOperand()->stripPointerCasts());
            bool field = false;
            shapes.insert(CL && formalOf(CL->getPointerOperand(), field) && field
                              ? "return through an indirect call on an argument's field"
                              : "return of an indirect call");
          }
        } else if (isa<Argument>(V)) {
          shapes.insert("returns its argument");
        } else if (!isa<Constant>(V)) {
          shapes.insert(std::string("return of ") + (isa<Instruction>(V)
                            ? cast<Instruction>(V)->getOpcodeName() : "a value"));
        }
      }
      std::string r;
      for (const std::string &x : shapes) r += (r.empty() ? "" : "; ") + x;
      return r.empty() ? "return" : r;
    };
    struct Bound { const Function *F; std::string which, shape; uint32_t rep; };
    std::vector<Bound> bounds;
    std::map<std::pair<const Function *, std::string>, uint32_t> boundIdx;
    // A solver rep can be a collapsed class holding several boundaries:
    // the mass is the class's, and the report lists them all.
    boost::unordered_flat_map<uint32_t, std::vector<uint32_t>> boundOf; // rep -> bounds
    auto addBound = [&](uint32_t node, const Function *F, const std::string &which,
                        const std::string &shape) {
      if (sitesOf(F) < 2 && !F->hasAddressTaken()) return;
      const uint32_t r = find(getCanonicalNode(node));
      if (r >= numNodes) return;
      auto [it, ins] = boundIdx.try_emplace({F, which}, (uint32_t)bounds.size());
      if (ins) bounds.push_back({F, which, shape, r});
      auto &v = boundOf[r];
      if (std::find(v.begin(), v.end(), it->second) == v.end()) v.push_back(it->second);
    };
    // Formals and loads through them first: they win over a return that
    // shares their class.
    for (uint32_t n = 0; n < G; n++) {
      const Value *V = NF.getValueForNode(n);
      if (const auto *A = dyn_cast_or_null<Argument>(V)) {
        if (A->getType()->isPointerTy() && NF.getValueNodeFor(A) == n)
          addBound(n, A->getParent(), "arg" + std::to_string(A->getArgNo()), "formal");
      } else if (const auto *L = dyn_cast_or_null<LoadInst>(V)) {
        bool field;
        if (const Argument *A = formalOf(L->getPointerOperand(), field))
          addBound(n, A->getParent(), "arg" + std::to_string(A->getArgNo()) +
                   (field ? " (field read)" : " (pointee read)"),
                   field ? "field of a formal" : "out-parameter (read)");
      } else if (NF.isDereferenceNode(n) && storeHub[n] != UINT32_MAX) {
        const NodeIndex par = NF.getDerefParent(n);
        const Value *PV = par == AndersNodeFactory::InvalidIndex ? nullptr : NF.getValueForNode(par);
        bool field;
        if (const Argument *A = PV ? formalOf(PV, field) : nullptr)
          addBound(storeHub[n], A->getParent(), "arg" + std::to_string(A->getArgNo()) +
                   (field ? " (field write)" : " (pointee write)"),
                   field ? "field of a formal (write)" : "out-parameter (write)");
      }
    }
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (F.isDeclaration() || !F.getReturnType()->isPointerTy()) continue;
        const NodeIndex rn = NF.getReturnNodeFor(&F);
        if (rn != AndersNodeFactory::InvalidIndex) addBound(rn, &F, "ret", retShape(&F));
      }
    std::vector<std::vector<uint32_t>> rev(numNodes);
    for (uint32_t u = 0; u < numNodes; u++) {
      if (find(u) != u) continue;
      for (uint32_t v : succ[u]) rev[find(v)].push_back(u);
      for (const FieldEdge &e : fieldOut[u]) rev[find(e.dst)].push_back(u);
    }
    // A boundary is confluent when it holds two or more names.
    boost::unordered_flat_map<uint32_t, size_t> namesMemo;
    auto namesAt = [&](uint32_t r) {
      auto [it, ins] = namesMemo.try_emplace(r, 0);
      if (ins) {
        boost::unordered_flat_set<uint32_t> names;
        pts[r].forEach([&](uint32_t f) {
          f = findFact(f);
          if (cells[f].kind == CellKind::Off) names.insert(cells[f].name);
        });
        it->second = names.size();
      }
      return it->second;
    };
    // Entries covering 95% of the mass (at most 400).
    size_t covered = 0, attributed = 0, walked = 0;
    boost::unordered_flat_map<uint32_t, std::pair<size_t, size_t>> groupMass; // rep -> mass, entries
    std::vector<uint32_t> mark(numNodes, UINT32_MAX);
    std::vector<char> objWant(objs.size(), 0);
    for (size_t i = 0; i < order.size() && i < 400 && covered * 20 < total * 19; i++) {
      const SoupEntry &E = soupEntries[order[i]];
      covered += E.mass;
      walked++;
      if (E.fact0 == UINT32_MAX) continue;
      std::vector<uint32_t> wantObjs;
      for (auto [o, e] : memb[findFact(E.fact0)]) { objWant[o] = 1; wantObjs.push_back(o); }
      auto holds = [&](uint32_t m) {
        bool h = false;
        pts[m].forEach([&](uint32_t f) {
          if (h) return;
          for (auto [o, off] : memb[findFact(f)]) h |= objWant[o];
        });
        return h;
      };
      const uint32_t start = find(E.src0 < numNodes ? E.src0 : E.node);
      uint32_t hit = UINT32_MAX;
      std::vector<uint32_t> q{start};
      mark[start] = (uint32_t)i;
      for (size_t k = 0; k < q.size() && k < 200000 && hit == UINT32_MAX; k++) {
        if (boundOf.count(q[k]) && namesAt(q[k]) >= 2) { hit = q[k]; break; }
        for (uint32_t p : rev[q[k]])
          if (mark[p] != (uint32_t)i && holds(p)) {
            mark[p] = (uint32_t)i;
            q.push_back(p);
          }
      }
      for (uint32_t o : wantObjs) objWant[o] = 0;
      if (hit == UINT32_MAX) continue;
      auto &g = groupMass[hit];
      g.first += E.mass;
      g.second++;
      attributed += E.mass;
    }
    // Class sizes (graph nodes per solver rep) for the reps hit.
    boost::unordered_flat_map<uint32_t, size_t> classSize;
    for (auto &[r, _] : groupMass) classSize[r] = 0;
    for (uint32_t n = 0; n < G; n++) {
      auto it = classSize.find(find(getCanonicalNode(n)));
      if (it != classSize.end()) it->second++;
    }
    std::vector<std::pair<size_t, uint32_t>> go;
    for (auto &[r, me] : groupMass) go.push_back({me.first, r});
    std::sort(go.rbegin(), go.rend());
    std::set<const Function *> fns;
    for (auto &[m, r] : go)
      for (uint32_t b : boundOf[r]) fns.insert(bounds[b].F);
    CG_LOG("Cells: BOUNDARY census: the top " << walked << " entries hold " << covered
           << " of " << total << " foreign facts; " << attributed
           << " came through a boundary of a function with 2+ call sites holding 2+ names ("
           << go.size() << " nodes, " << fns.size() << " functions), " << covered - attributed
           << " through none\n");
    std::set<const Function *> cum;
    size_t cm = 0;
    int pct = 50;
    for (auto &[m, r] : go) {
      cm += m;
      for (uint32_t b : boundOf[r]) cum.insert(bounds[b].F);
      while (pct <= 90 && cm * 100 >= (size_t)pct * attributed) {
        CG_LOG("Cells:   BOUNDARY " << pct << "% of the attributed mass: " << cum.size()
               << " functions\n");
        pct += 20;
      }
    }
    for (size_t i = 0; i < go.size() && i < 30; i++) {
      const auto [m, r] = go[i];
      std::vector<uint32_t> bs = boundOf[r];
      std::stable_sort(bs.begin(), bs.end(), [&](uint32_t x, uint32_t y) {
        return sitesOf(bounds[x].F) > sitesOf(bounds[y].F);
      });
      std::set<const Function *> fr;
      for (uint32_t b : bs) fr.insert(bounds[b].F);
      CG_LOG("Cells:   BOUNDARY node #" << r << ": mass " << m << " ("
             << (total ? 100.0 * m / total : 0.0) << "%), " << groupMass[r].second
             << " entries; " << namesAt(r) << " names; a class of " << classSize[r]
             << " nodes holding " << bs.size() << " boundaries of " << fr.size()
             << " functions" << (bs.size() > 200 ? " (first 200)" : "") << ":\n");
      for (size_t j = 0; j < bs.size() && j < 200; j++) {
        const Bound &B = bounds[bs[j]];
        CG_LOG("Cells:     " << B.F->getName() << " " << B.which << ": " << B.shape << "; "
               << sitesOf(B.F) << " call sites"
               << (B.F->hasAddressTaken() ? " (address taken)" : "") << "\n");
      }
    }
  };
  if (CFLCellSoupProfile) {
    // Node descriptions, memoized (nodeDesc scans the cells of a cell node).
    boost::unordered_flat_map<uint32_t, std::string> descMemo;
    auto descOf = [&](uint32_t n) -> const std::string & {
      auto [it, ins] = descMemo.try_emplace(n);
      if (ins) it->second = nodeDesc(n);
      return it->second;
    };
    // Construct class of a join node, from its description.
    auto classOf = [&](uint32_t n) -> std::string {
      if (n < inPwc.size() && inPwc[find(n)]) return "offset cycle (pwc)";
      const std::string d = descOf(n);
      if (d.rfind("return of ", 0) == 0) return "return of a function";
      if (d.rfind("cell ", 0) == 0) return "struct field / object cell";
      if (d.rfind("hub of", 0) == 0) return "load/store through a pointer (hub)";
      if (d.rfind("<stores through", 0) == 0) return "store collector";
      if (d.find(" arg") != std::string::npos && d.find(':') == std::string::npos)
        return "formal of a function";
      if (d.find("= phi") != std::string::npos || d.find("= select") != std::string::npos)
        return "join (phi/select)";
      if (d.find("= load") != std::string::npos) return "load";
      if (d.find("call ") != std::string::npos) return "call result";
      if (d.find("getelementptr") != std::string::npos) return "address step (GEP)";
      return "other";
    };
    size_t total = 0;
    for (const SoupEntry &E : soupEntries) total += E.mass;
    CG_LOG("Cells: SOUP PROFILE: " << total << " foreign facts, " << soupEntries.size()
           << " entries (joins where an incompatible name entered)"
           << (soupStop ? " [stopped at the cap]" : "") << "\n");
    std::map<std::string, std::pair<size_t, size_t>> byClass; // mass, entries
    for (const SoupEntry &E : soupEntries) {
      auto &c = byClass[classOf(E.node)];
      c.first += E.mass;
      c.second++;
    }
    std::vector<std::pair<size_t, std::string>> cls;
    for (auto &[k, v] : byClass) cls.push_back({v.first, k + " (" + std::to_string(v.second) + " entries)"});
    std::sort(cls.rbegin(), cls.rend());
    for (auto &[m, k] : cls)
      CG_LOG("Cells:   SOUP class " << k << ": " << m << " ("
             << (total ? 100.0 * m / total : 0.0) << "%)\n");
    // The construct by its owner: the function the join is in (hub, load,
    // phi, formal, return) or the allocation site of the cell's object.
    auto ownerOf = [&](uint32_t n) -> std::string {
      const std::string d = descOf(n);
      size_t p;
      if (d.rfind("cell ", 0) == 0 && (p = d.find(" of ")) != std::string::npos) {
        const std::string o = d.substr(p + 4);
        return "object " + o.substr(0, o.find(" ["));
      }
      if (d.rfind("hub of", 0) == 0 && (p = d.rfind('(')) != std::string::npos)
        return "function " + d.substr(p + 1, d.size() - p - 2);
      if (d.rfind("return of ", 0) == 0) return "function " + d.substr(10);
      if (d.rfind("memory of ", 0) == 0) return "object " + d.substr(10);
      if ((p = d.find(':')) != std::string::npos) return "function " + d.substr(0, p);
      if ((p = d.find(" arg")) != std::string::npos) return "function " + d.substr(0, p);
      return d.substr(0, 60);
    };
    std::map<std::string, size_t> byOwner;
    for (const SoupEntry &E : soupEntries) byOwner[ownerOf(E.node)] += E.mass;
    std::vector<std::pair<size_t, std::string>> own;
    for (auto &[k, m] : byOwner) own.push_back({m, k});
    std::sort(own.rbegin(), own.rend());
    for (size_t i = 0; i < own.size() && i < 20; i++)
      CG_LOG("Cells:   SOUP construct " << own[i].second << ": " << own[i].first << " ("
             << (total ? 100.0 * own[i].first / total : 0.0) << "%)\n");
    std::vector<uint32_t> order(soupEntries.size());
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](uint32_t x, uint32_t y) {
      return soupEntries[x].mass > soupEntries[y].mass;
    });
    for (size_t i = 0; i < order.size() && i < 40; i++) {
      const SoupEntry &E = soupEntries[order[i]];
      CG_LOG("Cells:   SOUP #" << i + 1 << " mass " << E.mass << " ("
             << (total ? 100.0 * E.mass / total : 0.0) << "%), born " << E.born << ", "
             << classOf(E.node) << ": " << nodeDesc(E.node) << "\n");
      std::vector<std::pair<uint32_t, size_t>> sr = E.srcs;
      std::sort(sr.begin(), sr.end(), [](auto &x, auto &y) { return x.second > y.second; });
      for (size_t j = 0; j < sr.size() && j < 3; j++)
        CG_LOG("Cells:       entered from " << (sr[j].first < numNodes ? nodeDesc(sr[j].first) : std::string("(no source)"))
               << " x" << sr[j].second << "\n");
    }
    // Width per formal and per struct field (distinct names held).
    std::vector<std::pair<size_t, uint32_t>> formals, fields;
    for (uint32_t n = 0; n < numNodes; n++) {
      if (find(n) != n || pts[n].count() < 2) continue;
      boost::unordered_flat_set<uint32_t> names;
      pts[n].forEach([&](uint32_t f) {
        f = findFact(f);
        if (cells[f].kind == CellKind::Off) names.insert(cells[f].name);
      });
      if (names.size() < 2) continue;
      const std::string d = nodeDesc(n);
      if (d.rfind("cell ", 0) == 0) fields.push_back({names.size(), n});
      else if (d.find(" arg") != std::string::npos && d.find(':') == std::string::npos)
        formals.push_back({names.size(), n});
    }
    std::sort(formals.rbegin(), formals.rend());
    std::sort(fields.rbegin(), fields.rend());
    for (size_t i = 0; i < formals.size() && i < 25; i++)
      CG_LOG("Cells:   WIDTH formal " << formals[i].first << " names: " << nodeDesc(formals[i].second) << "\n");
    for (size_t i = 0; i < fields.size() && i < 25; i++)
      CG_LOG("Cells:   WIDTH field " << fields[i].first << " names: " << nodeDesc(fields[i].second) << "\n");
    soupBoundaryCensus(order, total);
  }
  // Leak census report: the inert check of byte cells, then the leaks by
  // class and by site, with the non-char facts each explains.
  if (CFLCellLeakCensus) {
    // Every fact at the stop, and those downstream of a leak (by leak).
    size_t allFacts = 0, downAll = 0;
    std::vector<size_t> down(leakSites.size(), 0);
    for (uint32_t m = 0; m < numNodes; m++) {
      if (find(m) != m) continue;
      allFacts += pts[m].count();
      pts[m].forEach([&](uint32_t f0) {
        auto it = leakTag.find((uint64_t)m << 32 | findFact(f0));
        if (it == leakTag.end()) it = leakTag.find((uint64_t)m << 32 | f0);
        if (it == leakTag.end()) return;
        downAll++;
        down[it->second]++;
      });
    }
    size_t byteCells = 0, inert = 0, onlyChar = 0, withLeak = 0, byteFacts = 0, untagged = 0;
    size_t kindFacts[4] = {0, 0, 0, 0};
    std::vector<size_t> siteMass(leakSites.size(), 0);
    std::vector<boost::unordered_flat_map<uint32_t, size_t>> siteObjs(leakSites.size());
    std::map<std::pair<uint32_t, int64_t>, size_t> untaggedAt;
    boost::unordered_flat_set<uint32_t> seenRep;
    std::vector<uint32_t> reps;
    for (uint32_t o = 0; o < objs.size(); o++) {
      auto cellOf = [&](int64_t c) {
        reps.clear();
        if (c == kLeakAny) {
          reps.push_back(find(cells[objs[o].any].store));
          reps.push_back(find(cells[objs[o].any].load));
        } else {
          const auto &up = objs[o].content.at(c);
          reps.push_back(find(up.first));
          reps.push_back(find(up.second));
          for (auto &[kk, kn] : objs[o].keyed)
            if ((int64_t)(uint32_t)(kk >> 32) == (int64_t)(uint32_t)c) reps.push_back(find(kn));
        }
        std::sort(reps.begin(), reps.end());
        reps.erase(std::unique(reps.begin(), reps.end()), reps.end());
        byteCells++;
        size_t facts = 0;
        bool leak = false;
        for (uint32_t R : reps) {
          facts += R < pts.size() ? pts[R].count() : 0;
          const bool first = seenRep.insert(R).second;
          if (R >= pts.size()) continue;
          pts[R].forEach([&](uint32_t f0) {
            const uint32_t f = findFact(f0);
            const int k = leakFactKind(f);
            if (k) leak = true;
            if (!first) return;
            byteFacts++;
            if (!k) return;
            kindFacts[k]++;
            auto it = leakTag.find((uint64_t)R << 32 | f);
            if (it == leakTag.end()) it = leakTag.find((uint64_t)R << 32 | f0);
            if (it == leakTag.end()) {
              untagged++;
              untaggedAt[{o, c}]++;
              return;
            }
            siteMass[it->second]++;
            siteObjs[it->second][memb[f][0].first]++;
          });
        }
        (facts == 0 ? inert : leak ? withLeak : onlyChar)++;
      };
      for (auto &[c, up] : objs[o].content)
        if (leakByteCell(o, c)) cellOf(c);
      if (objs[o].any != UINT32_MAX && leakByteCell(o, kLeakAny)) cellOf(kLeakAny);
    }
    const size_t leakFacts = kindFacts[1] + kindFacts[2] + kindFacts[3];
    auto pct = [](size_t a, size_t b) {
      char buf[32];
      snprintf(buf, sizeof buf, "%.1f", b ? 100.0 * a / b : 0.0);
      return std::string(buf);
    };
    CG_LOG("Cells: LEAK census: " << byteCells << " byte-named cells (i8[]): " << inert
           << " hold no fact, " << onlyChar << " only char or unnamed objects' facts, "
           << withLeak << " a non-char object's fact; facts: " << allFacts << " in all nodes, "
           << byteFacts << " in byte cells, " << leakFacts << " of them non-char objects ("
           << pct(leakFacts, allFacts) << "% of all facts; struct " << kindFacts[1]
           << ", other non-char " << kindFacts[2] << ", function " << kindFacts[3] << "); "
           << leakSites.size() << " leak sites; " << downAll << " facts downstream of a leak ("
           << pct(downAll, allFacts) << "% of all facts)\n");
    static const char *clsName[] = {"", "store into a byte or union field of a struct",
                                    "byte copy", "byte storage written through a struct view",
                                    "byte storage written through a char or untyped address",
                                    "vararg or bodiless call boundary", "other",
                                    "store through an imprecise pointer (it also holds the objects it views)"};
    // The struct-view recount: a store whose view did not fit its target,
    // through a pointer that holds objects of that view at the stop, is a
    // store through an imprecise pointer (it held none when first seen).
    size_t from3 = 0, from1 = 0;
    for (LeakSite &L : leakSites) {
      if (L.view.empty() || !L.viewPtr || L.cls == 7) continue;
      const uint32_t pn = leakNodeOf(L.viewPtr);
      size_t k = 0;
      if (pn != UINT32_MAX)
        pts[pn].forEach([&](uint32_t g) {
          for (auto [o, e] : memb[findFact(g)])
            if (objs[o].layout && objs[o].label == L.view) { k++; break; }
        });
      if (!k) continue;
      (L.cls == 3 ? from3 : from1)++;
      L.recounted = L.cls;
      L.cls = 7;
      L.detail += "; at the stop the pointer holds " + std::to_string(k) + " " + L.view;
    }
    CG_LOG("Cells:   LEAK recount at the stop: " << from3 + from1 << " sites moved to class 7 ("
           << from3 << " from class 3, " << from1 << " from class 1)\n");
    size_t clsMass[8] = {}, clsSites[8] = {}, clsExited[8] = {}, exitedAll = 0, exitedUntagged = 0;
    for (size_t s = 0; s < leakSites.size(); s++) {
      clsMass[leakSites[s].cls] += siteMass[s];
      clsExited[leakSites[s].cls] += leakSites[s].exited;
      clsSites[leakSites[s].cls]++;
    }
    for (const LeakExit &E : leakExits) {
      exitedAll += E.mass;
      exitedUntagged += E.untagged;
    }
    CG_LOG("Cells:   LEAK exits: " << leakExits.size() << " edges out of byte cells carry "
           << exitedAll << " non-char (node, fact) pairs out (" << exitedUntagged
           << " of them untagged)\n");
    for (int c = 1; c <= 7; c++)
      CG_LOG("Cells:   LEAK class " << c << " (" << clsName[c] << "): exited " << clsExited[c]
             << " (" << pct(clsExited[c], exitedAll) << "%), resident " << clsMass[c] << " ("
             << pct(clsMass[c], leakFacts) << "%), " << clsSites[c] << " sites\n");
    CG_LOG("Cells:   LEAK untagged: " << untagged << " (" << pct(untagged, leakFacts)
           << "%): the fact or the cell was not yet named when it arrived, or a cycle merge "
           << "brought it\n");
    std::vector<uint32_t> order(leakSites.size());
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](uint32_t x, uint32_t y) {
      if (leakSites[x].exited != leakSites[y].exited) return leakSites[x].exited > leakSites[y].exited;
      return siteMass[x] != siteMass[y] ? siteMass[x] > siteMass[y] : x < y;
    });
    size_t covered = 0;
    for (size_t i = 0; i < order.size() && i < 60; i++) {
      const uint32_t s = order[i];
      if (!siteMass[s] && !leakSites[s].exited && i >= 10) break;
      covered += siteMass[s];
      std::vector<std::pair<size_t, uint32_t>> os;
      for (auto &[o, c] : siteObjs[s]) os.push_back({c, o});
      std::sort(os.begin(), os.end(), [](auto &x, auto &y) {
        return x.first != y.first ? x.first > y.first : x.second < y.second;
      });
      std::string objsTop;
      for (size_t j = 0; j < os.size() && j < 3; j++)
        objsTop += (j ? "; " : "") + describe(objs[os[j].second]) + " " + std::to_string(os[j].first);
      if (os.size() > 3) objsTop += "; +" + std::to_string(os.size() - 3) + " objects";
      const LeakSite &L = leakSites[s];
      CG_LOG("Cells:   LEAK #" << i + 1 << " class " << L.cls << " exited " << L.exited << " ("
             << pct(L.exited, exitedAll) << "%), resident " << siteMass[s] << " ("
             << pct(siteMass[s], leakFacts) << "%), born " << L.born << ", downstream " << down[s]
             << ": " << L.where << " | into " << L.into << " | " << L.detail
             << " | objects: " << objsTop << "\n");
    }
    // The earliest leaks by solve order: the pop of a site's first entry,
    // with its pointers' shapes then and at the stop. A pointer is precise
    // when its objects carry one label (a copy: both pointers).
    auto shapeOf = [&](const LeakSite &L) {
      if (L.ptrNode == UINT32_MAX) return std::string("no pointer");
      size_t o2, l2;
      leakPtrShape(L.ptrNode, o2, l2);
      std::string d = "pointer " + std::to_string(L.ptrObjs) + " objects/" + std::to_string(L.ptrLabels) +
                      " labels at entry, " + std::to_string(o2) + "/" + std::to_string(l2) + " at the stop";
      if (L.cls == 2 && L.srcNode != UINT32_MAX) {
        leakPtrShape(L.srcNode, o2, l2);
        d += "; source " + std::to_string(L.srcObjs) + "/" + std::to_string(L.srcLabels) + " at entry, " +
             std::to_string(o2) + "/" + std::to_string(l2) + " at the stop";
      }
      return d;
    };
    auto precise = [&](const LeakSite &L) {
      return L.ptrNode != UINT32_MAX && L.ptrLabels == 1 &&
             (L.cls != 2 || L.srcNode == UINT32_MAX || L.srcLabels <= 1);
    };
    std::vector<uint32_t> early(leakSites.size());
    std::iota(early.begin(), early.end(), 0);
    std::sort(early.begin(), early.end(), [&](uint32_t x, uint32_t y) {
      return leakSites[x].firstPop != leakSites[y].firstPop ? leakSites[x].firstPop < leakSites[y].firstPop
                                                            : x < y;
    });
    for (int pass = 0; pass < 2; pass++) {
      size_t shown = 0;
      for (uint32_t s : early) {
        const LeakSite &L = leakSites[s];
        if (!L.born) continue; // provisional, never became a leak
        if (pass == 0 && !precise(L)) continue;
        if (++shown > 10) break;
        CG_LOG("Cells:   LEAK EARLY " << (pass ? "any" : "precise") << " #" << shown << " pop " << L.firstPop
               << " class " << L.cls << (L.recounted ? " (was " + std::to_string(L.recounted) + ")" : std::string())
               << " exited " << L.exited << ", resident " << siteMass[s] << ", downstream " << down[s] << ": "
               << L.where << " | into " << L.into << " | " << L.detail << " | " << shapeOf(L) << "\n");
      }
    }
    CG_LOG("Cells:   LEAK the listed sites hold " << covered << " (" << pct(covered, leakFacts)
           << "%) of the non-char facts in byte cells\n");
    std::vector<std::pair<size_t, std::pair<uint32_t, int64_t>>> ut;
    for (auto &[k, c] : untaggedAt) ut.push_back({c, k});
    std::sort(ut.begin(), ut.end(), [](auto &x, auto &y) {
      return x.first != y.first ? x.first > y.first : x.second < y.second;
    });
    for (size_t i = 0; i < ut.size() && i < 10; i++) {
      const auto [o, c] = ut[i].second;
      CG_LOG("Cells:   LEAK untagged " << ut[i].first << " in "
             << (c == kLeakAny ? std::string("*") : cellName(o, c)) << " of "
             << describe(objs[o]) << "\n");
    }
    // The exit table: where pointers leave byte cells, by facts carried.
    std::vector<uint32_t> eo(leakExits.size());
    std::iota(eo.begin(), eo.end(), 0);
    std::sort(eo.begin(), eo.end(), [&](uint32_t x, uint32_t y) {
      return leakExits[x].mass != leakExits[y].mass ? leakExits[x].mass > leakExits[y].mass : x < y;
    });
    std::map<std::string, size_t> exitKinds;
    for (const LeakExit &E : leakExits)
      exitKinds[E.kind.substr(0, E.kind.find(" ("))] += E.mass;
    for (auto &[k, m] : exitKinds)
      CG_LOG("Cells:   LEAK exit kind " << k << ": " << m << " (" << pct(m, exitedAll) << "%)\n");
    size_t ecov = 0;
    for (size_t i = 0; i < eo.size() && i < 40; i++) {
      const LeakExit &E = leakExits[eo[i]];
      ecov += E.mass;
      std::vector<std::pair<size_t, std::pair<uint32_t, int64_t>>> fr;
      for (auto &[k, c] : E.from) fr.push_back({c, k});
      std::sort(fr.begin(), fr.end(), [](auto &x, auto &y) {
        return x.first != y.first ? x.first > y.first : x.second < y.second;
      });
      std::string from;
      for (size_t j = 0; j < fr.size() && j < 3; j++) {
        const auto [o, c] = fr[j].second;
        from += (j ? "; " : "") +
                (o == UINT32_MAX ? std::string(c ? "a move" : "a cycle holding a byte cell")
                 : (c == kLeakAny ? std::string("*") : cellName(o, c)) + " of " + describe(objs[o])) +
                " " + std::to_string(fr[j].first);
      }
      if (fr.size() > 3) from += "; +" + std::to_string(fr.size() - 3) + " cells";
      CG_LOG("Cells:   LEAK EXIT #" << i + 1 << " " << E.mass << " (" << pct(E.mass, exitedAll)
             << "%, untagged " << E.untagged << ", " << E.edges << " edges): " << E.kind << " | " << E.desc
             << " | from " << from << "\n");
    }
    CG_LOG("Cells:   LEAK the listed exits carry " << ecov << " (" << pct(ecov, exitedAll)
           << "%)\n");
  }
  {
    std::vector<uint32_t> order;
    for (uint32_t ci = 0; ci < copyStat.size(); ci++)
      if (copyStat[ci].pairs) order.push_back(ci);
    std::sort(order.begin(), order.end(), [&](uint32_t x, uint32_t y) {
      return copyStat[x].edges > copyStat[y].edges;
    });
    for (size_t i = 0; i < order.size() && i < 12; i++) {
      const uint32_t ci = order[i];
      const CopyStat &C = copyStat[ci];
      CG_LOG("Cells:   copy " << instLoc(copies[ci].at) << " len "
             << copies[ci].len << ": " << C.pairs << " cell pairs, "
             << C.edges << " content edges, " << C.srcObjs.size()
             << " source objects (" << pts[find(copies[ci].src)].count()
             << " facts at the source pointer), " << C.dstObjs.size()
             << " destination objects (" << pts[find(copies[ci].dst)].count()
             << " facts)\n");
      if (i > 0) continue;
      // The heaviest copy: its source pointer's facts by object.
      std::map<uint32_t, size_t> perObj;
      pts[find(copies[ci].src)].forEach([&](uint32_t f) {
        for (auto [o, e] : memb[f]) perObj[o]++;
      });
      for (auto [o, k] : perObj)
        CG_LOG("Cells:     source " << describe(objs[o]) << ": " << k << " facts\n");
      if (recordWhy) explainWhy(find(copies[ci].src), CFLCellWhy);
    }
    // --cfl-cell-why=any:OBJ: where OBJ's any-offset cell first arrived.
    if (recordWhy && StringRef(CFLCellWhy).starts_with("any:")) {
      const std::string want = CFLCellWhy.substr(4);
      uint64_t bestKey = 0;
      uint32_t bestT = UINT32_MAX;
      for (auto &[key, w] : factWhy) {
        const uint32_t f = (uint32_t)key;
        if (f >= cells.size() || cells[f].kind != CellKind::Any) continue;
        if (describe(objs[cells[f].obj]).find(want) == std::string::npos) continue;
        if (w.t < bestT) { bestT = w.t; bestKey = key; }
      }
      if (bestT == UINT32_MAX) {
        CG_LOG("Cells: no any-offset cell of '" << want << "' arrived\n");
      } else {
        const uint32_t n0 = (uint32_t)(bestKey >> 32), f0 = (uint32_t)bestKey;
        const Why w = factWhy[bestKey];
        CG_LOG("Cells: first any-offset cell " << whyDesc(f0) << " arrived at pop "
               << bestT << " at " << nodeDesc(n0) << " (cause kind " << (int)w.kind
               << ") from " << (w.node < numNodes ? nodeDesc(w.node) : std::string("?"))
               << " holding " << (w.fact < cells.size() ? whyDesc(w.fact) : std::string("?"))
               << "\n");
        if (w.node < numNodes && w.fact < cells.size()) {
          const std::string d = describe(objs[cells[findFact(w.fact)].obj]);
          explainWhy(find(w.node), d.substr(0, d.find(" [")));
        }
      }
    }
    if (recordWhy && firstRuleB.node != UINT32_MAX) {
      const std::string w = describe(objs[firstRuleB.obj]);
      CG_LOG("Cells: first rule (b) step: " << nodeDesc(firstRuleB.node) << " steps "
             << firstRuleB.ty->getName() << " on " << w << "\n");
      explainWhy(find(firstRuleB.node), w.substr(0, w.find(" [")));
    }
    // The first copy between unrelated structs: how its two pointers came
    // to hold the two objects.
    if (recordWhy && firstMismatch.ci != UINT32_MAX) {
      const ByteCopy &C = copies[firstMismatch.ci];
      CG_LOG("Cells: first copy between unrelated structs: " << instLoc(C.at)
             << ": " << describe(objs[firstMismatch.os]) << " into "
             << describe(objs[firstMismatch.od]) << "\n");
      const std::string ws = describe(objs[firstMismatch.os]),
                        wd = describe(objs[firstMismatch.od]);
      explainWhy(find(C.src), ws.substr(0, ws.find(" [")));
      explainWhy(find(C.dst), wd.substr(0, wd.find(" [")));
    }
    // --cfl-cell-why-at=NODE: why the nodes NODE describes hold the object.
    if (recordWhy && !CFLCellWhyAt.empty()) {
      std::set<uint32_t> asked;
      boost::unordered_flat_map<uint32_t, uint32_t> classSize;
      for (uint32_t m = 0; m < numNodes; m++) classSize[find(m)]++;
      for (uint32_t m = 0; m < numNodes; m++)
        if (nodeDesc(m).find(CFLCellWhyAt) != std::string::npos && asked.insert(find(m)).second) {
          CG_LOG("Cells: why-at " << nodeDesc(m) << ": class " << find(m) << " of "
                 << classSize[find(m)] << " nodes, represented by " << nodeDesc(find(m)) << "\n");
          for (StringRef alt : llvm::split(StringRef(CFLCellWhy.getValue()), '|'))
            if (!alt.empty()) explainWhy(find(m), alt.str());
        }
      if (asked.empty()) CG_LOG("Cells: no node matches '" << CFLCellWhyAt << "'\n");
    }
  }
  if (CFLCellReceivers)
    CG_LOG("Cells: method calls p->f(.., p, ..): " << recvSites.size()
           << " sites, " << recvLevels << " levels (" << recvUnstepped << " slot not a field step of p: every "
           << "receiver to every method; " << recvNoNode << " without facts), "
           << recvBound << " receiver cells dispatched; " << guards.size()
           << " holder reloads guarded in methods (" << guardsLive << " installed during the solve, "
           << guardsLiveDropped << " dropped by a later shape; " << guardHeldFacts
           << " holder arrivals checked, " << guardAdmitted.size() << " admitted, "
           << guardDropped << " guards dropped by a merge)\n");
  if (recordWhy)
    for (const RecvSite &R : recvSites)
      CG_LOG("Cells:   method call " << instLoc(R.cs) << " receiver arg" << R.k
             << (R.all ? " (every receiver)" : "") << "\n");
  CG_LOG("Cells: " << copies.size() << " byte copies, " << copyPairs
         << " cell pairs copied, " << copyEdges << " content edges, "
         << effectiveTyped << " unknown destinations typed by the source\n");
  reportDefects();
  CG_LOG("Cells: " << g_innerAllocSites
         << " allocator calls inside kept allocator bodies (no object: the "
            "outer FRESH stands for it); "
         << g_p2iNumberOnly
         << " ptrtoints used as numbers only (no field-any loop); " << g_dataOnlyGeps
         << " GEPs of data pointers (character traffic: no edges, no cells); " << g_intNameLoads
         << " loads of integer names (no facts; " << g_counterRetired << " counters); "
         << g_vaMachineryLoads << " va_list bookkeeping loads (no vararg edges); " << g_carves
         << " carved regions (one past an array, used as another type; see CARVE lines); "
         << g_poolCarves << " pool carves (allocation sites; see PoolCarve lines); "
         << g_freeDropped << " deallocator stores into or of the freed block (FREE)\n");
  if (!taggedPairs.empty())
    CG_LOG("Cells: tagged fields (plan 3.51): " << taggedPairs.size() << " keyed pairs, "
           << taggedFlipped.size() << " flipped to unkeyed during the solve (a byte copy or a watched "
           << "store wrote the tag); " << taggedWatches.size() << " watched store roots ("
           << watchAt.size() << " nodes, " << watchNoNode << " with no node), "
           << watchPending.size() << " objects never typed with watched writes pending\n");
  if (!taggedPairs.empty()) {
    CG_LOG("Cells: alias assumptions (plan 3.51): " << asmUsed - asmFailed << " held, " << asmFailed
           << " failed (" << asmNoNode << " for want of a node)\n");
    for (const std::string &d : asmFailSites) CG_LOG("Cells:   alias assumption failed at " << d << "\n");
  }
  for (const std::string &d : taggedFlipAt) CG_LOG("Cells:   unkeyed during solve: " << d << "\n");
  if (!varargAllKeys.empty())
    CG_LOG("Cells: varargs keyed by format specifier (plan 3.47): " << varargKeyedSites
           << " call sites with a constant format, " << varargPoolSites
           << " with a non-constant format (unkeyed: every key), " << varargUnparsed
           << " whose specifiers do not match their arguments (unkeyed)\n");
  CG_LOG("Cells: " << factMerges << " cells unified by name ("
         << retiredDropped << " retired ids dropped from sets), "
         << ptrMerges << " pointer nodes merged by equal sets\n");
  for (auto [n, o, pos, k] : byteStepUBAt)
    CG_LOG("Cells:   byte array exit (UB): " << (n < numNodes ? nodeDesc(n) : std::string("?"))
           << " steps " << k << " from " << describe(objs[o]) << " +" << pos << "\n");
  CG_LOG("Cells: " << collapses << " cycle collapses merged "
         << collapsedNodes << " solver nodes (" << collapseSecs << " s)\n");
  // The largest cycles: members by function, and the memory cells in them
  // (a cycle through a cell is a store and a load of one name).
  for (size_t ci = 0; ci < bigCycles.size(); ci++) {
    const auto &M = bigCycles[ci];
    std::map<std::string, size_t> byFn;
    std::vector<std::string> cellsIn;
    for (uint32_t m : M) {
      const std::string d = nodeDesc(m);
      if (d.rfind("cell ", 0) == 0) {
        if (cellsIn.size() < 16) cellsIn.push_back(d);
        byFn["<cells>"]++;
        continue;
      }
      byFn[d.substr(0, d.find(':'))]++;
    }
    std::vector<std::pair<size_t, std::string>> top;
    for (auto &[k, c] : byFn) top.push_back({c, k});
    std::sort(top.rbegin(), top.rend());
    std::string fl;
    for (size_t i = 0; i < top.size() && i < 16; i++)
      fl += " " + top[i].second + "(" + std::to_string(top[i].first) + ")";
    CG_LOG("Cells:   cycle of " << M.size() << " nodes:" << fl << "\n");
    for (const std::string &c : cellsIn) CG_LOG("Cells:     " << c << "\n");
    // Its cells by object label, and the members carrying a field-any loop.
    std::map<std::string, size_t> byLabel;
    std::set<uint32_t> typed, buffer;
    for (uint32_t m : M) {
      const std::string d = nodeDesc(m);
      if (d.rfind("cell ", 0) != 0) continue;
      const size_t lb = d.rfind(" ["), rb = d.rfind(']');
      const std::string label = lb != std::string::npos && rb > lb ? d.substr(lb + 2, rb - lb - 2) : "?";
      byLabel[label]++;
      const bool buf = d.find("cell i8[]") == 0 || label == "unlabeled" || label == "i8";
      (buf ? buffer : typed).insert(m);
    }
    std::vector<std::pair<size_t, std::string>> lt;
    for (auto &[l, c] : byLabel) lt.push_back({c, l});
    std::sort(lt.rbegin(), lt.rend());
    std::string ll;
    for (size_t i = 0; i < lt.size() && i < 3; i++)
      ll += " [" + lt[i].second + "] " + std::to_string(lt[i].first);
    CG_LOG("Cells:     cells by object label: " << byLabel.size() << " labels; largest:" << ll
           << " (" << typed.size() << " typed cells, " << buffer.size() << " byte-buffer cells)\n");
    for (auto &[n, why] : wildcardWhy) {
      const uint32_t s2 = getCanonicalNode(n) < G ? canon(n) : UINT32_MAX;
      if (s2 != UINT32_MAX && std::find(M.begin(), M.end(), s2) != M.end())
        CG_LOG("Cells:     field-any loop at " << nodeDesc(s2) << " [" << why << "]\n");
    }
    // Entry census (the largest cycle only): every edge from outside into
    // the cycle, the construct of its source, the objects it carries in,
    // and per object the number of separate entries (one route or many).
    if (ci == 0 || M.size() == std::max_element(bigCycles.begin(), bigCycles.end(),
                       [](auto &a, auto &b) { return a.size() < b.size(); })->size()) {
      const uint32_t rep = find(M[0]);
      auto kindOf = [&](const std::string &d) -> std::string {
        if (d.rfind("hub of", 0) == 0) return "load through a pointer (hub)";
        if (d.rfind("<stores through", 0) == 0) return "store collector";
        if (d.rfind("cell ", 0) == 0 || d.rfind("content ", 0) == 0) return "memory cell (byte copy / relay)";
        if (d.rfind("return of", 0) == 0) return "function return";
        if (d.rfind("vararg of", 0) == 0) return "vararg pool";
        if (d.find(" arg") != std::string::npos && d.find(':') == std::string::npos) return "formal";
        if (d.find("= phi") != std::string::npos || d.find("= select") != std::string::npos) return "join";
        if (d.find("= load") != std::string::npos) return "load";
        if (d.find("call ") != std::string::npos) return "call result";
        if (d.find("getelementptr") != std::string::npos) return "address step";
        return "other";
      };
      std::map<std::string, std::pair<size_t, size_t>> byKind; // edges, objects carried
      std::map<std::string, size_t> byFn;
      boost::unordered_flat_map<uint32_t, uint32_t> entriesOf; // object -> entry edges
      std::vector<std::tuple<size_t, std::string>> topSrc;
      size_t edges = 0;
      for (uint32_t u = 0; u < numNodes; u++) {
        if (find(u) != u || u == rep) continue;
        bool enters = false;
        for (uint32_t v : succ[u]) if (find(v) == rep) { enters = true; break; }
        if (!enters) continue;
        edges++;
        std::set<uint32_t> os;
        pts[u].forEach([&](uint32_t f) {
          for (auto [o, e] : memb[findFact(f)]) os.insert(o);
        });
        for (uint32_t o : os) entriesOf[o]++;
        const std::string d = nodeDesc(u);
        auto &bk = byKind[kindOf(d)];
        bk.first++;
        bk.second += os.size();
        const size_t colon = d.find(':');
        if (colon != std::string::npos && d.rfind("cell ", 0) != 0) byFn[d.substr(0, colon)] += os.size();
        topSrc.push_back({os.size(), d});
      }
      size_t one = 0, few = 0, many = 0;
      for (auto &[o, n] : entriesOf) (n == 1 ? one : n < 10 ? few : many)++;
      // Which objects: the pool (entering by 10+ edges) by label, and each
      // single-route object with its one entry.
      std::map<std::string, size_t> poolLabels;
      for (auto &[o, n] : entriesOf)
        if (n >= 10) poolLabels[objs[o].layout ? objs[o].label : std::string("unlabeled/bytes")]++;
      std::string pl;
      for (auto &[l, c] : poolLabels) pl += " " + l + " x" + std::to_string(c);
      CG_LOG("Cells:     entry pool (objects entering by 10+ edges) by label:" << pl << "\n");
      std::map<uint32_t, std::string> singleFrom;
      for (uint32_t u = 0; u < numNodes && singleFrom.size() < 200; u++) {
        if (find(u) != u || u == rep) continue;
        bool enters = false;
        for (uint32_t v : succ[u]) if (find(v) == rep) { enters = true; break; }
        if (!enters) continue;
        pts[u].forEach([&](uint32_t f) {
          for (auto [o, e] : memb[findFact(f)])
            if (entriesOf[o] == 1 && !singleFrom.count(o)) singleFrom[o] = nodeDesc(u);
        });
      }
      std::map<std::string, std::vector<std::string>> byEntry;
      for (auto &[o, d] : singleFrom) byEntry[d.substr(0, 150)].push_back(describe(objs[o]));
      std::vector<std::pair<size_t, std::string>> be;
      for (auto &[d, v] : byEntry) be.push_back({v.size(), d});
      std::sort(be.rbegin(), be.rend());
      for (size_t i = 0; i < be.size() && i < 12; i++) {
        std::string ex;
        for (size_t j = 0; j < byEntry[be[i].second].size() && j < 3; j++) ex += " | " + byEntry[be[i].second][j].substr(0, 70);
        CG_LOG("Cells:       single-route " << be[i].first << " objects via " << be[i].second << ":" << ex << "\n");
      }
      CG_LOG("Cells:     entry census: " << edges << " edges enter the cycle; " << entriesOf.size()
             << " objects enter it: " << one << " by one edge, " << few << " by 2-9, " << many
             << " by 10 or more\n");
      std::vector<std::pair<size_t, std::string>> kt;
      for (auto &[k, ec] : byKind) kt.push_back({ec.second, k + " (" + std::to_string(ec.first) + " edges)"});
      std::sort(kt.rbegin(), kt.rend());
      for (auto &[c, k] : kt) CG_LOG("Cells:       by construct: " << k << ": " << c << " objects carried\n");
      std::vector<std::pair<size_t, std::string>> ft;
      for (auto &[f, c] : byFn) ft.push_back({c, f});
      std::sort(ft.rbegin(), ft.rend());
      std::string fl;
      for (size_t i = 0; i < ft.size() && i < 15; i++) fl += " " + ft[i].second + "(" + std::to_string(ft[i].first) + ")";
      CG_LOG("Cells:       by function (objects carried):" << fl << "\n");
      std::sort(topSrc.rbegin(), topSrc.rend());
      for (size_t i = 0; i < topSrc.size() && i < 15; i++)
        CG_LOG("Cells:       entry " << std::get<0>(topSrc[i]) << " objects from "
               << std::get<1>(topSrc[i]).substr(0, 180) << "\n");
    }
    // The byte copies relaying between objects of the cycle: content
    // edges from a copy are what joins two cells directly.
    {
      const uint32_t rep = find(M[0]);
      std::set<uint32_t> cyc;
      for (uint32_t o = 0; o < objs.size(); o++)
        for (auto &[c, up] : objs[o].content)
          if (find(up.first) == rep || find(up.second) == rep) { cyc.insert(o); break; }
      std::vector<std::tuple<size_t, size_t, size_t, uint32_t>> cs;
      for (uint32_t ci2 = 0; ci2 < copyStat.size() && ci2 < copies.size(); ci2++) {
        size_t s3 = 0, d3 = 0;
        for (uint32_t o : copyStat[ci2].srcObjs) s3 += cyc.count(o);
        for (uint32_t o : copyStat[ci2].dstObjs) d3 += cyc.count(o);
        if (s3 && d3) cs.push_back({s3 * d3, s3, d3, ci2});
      }
      std::sort(cs.rbegin(), cs.rend());
      CG_LOG("Cells:     " << cyc.size() << " objects in the cycle; " << cs.size()
             << " byte copies relay between them; the largest:\n");
      for (size_t i = 0; i < cs.size() && i < 8; i++) {
        const auto [sc, s3, d3, ci2] = cs[i];
        CG_LOG("Cells:       copy " << instLoc(copies[ci2].at) << " len " << copies[ci2].len
               << ": " << s3 << " source x " << d3 << " destination objects of the cycle\n");
      }
    }
    // The weld: a shortest path inside the cycle from a typed cell to a
    // byte-buffer cell, and one back.
    if (ci < bigCycleEdges.size() && !typed.empty() && !buffer.empty()) {
      std::map<uint32_t, std::vector<uint32_t>> adj;
      for (auto [a, b] : bigCycleEdges[ci]) adj[a].push_back(b);
      auto path = [&](const std::set<uint32_t> &from, const std::set<uint32_t> &to, const char *what) {
        std::map<uint32_t, uint32_t> prev;
        std::vector<uint32_t> q(from.begin(), from.end());
        for (uint32_t f : from) prev[f] = f;
        for (size_t qi = 0; qi < q.size(); qi++) {
          const uint32_t u = q[qi];
          if (to.count(u) && !from.count(u)) {
            std::vector<uint32_t> p{u};
            while (prev[p.back()] != p.back()) p.push_back(prev[p.back()]);
            std::reverse(p.begin(), p.end());
            CG_LOG("Cells:     weld " << what << " (" << p.size() << " nodes):\n");
            for (uint32_t x : p) CG_LOG("Cells:       " << nodeDesc(x) << "\n");
            return;
          }
          for (uint32_t v : adj[u])
            if (!prev.count(v)) { prev[v] = u; q.push_back(v); }
        }
        CG_LOG("Cells:     weld " << what << ": no path in the recorded edges\n");
      };
      path(typed, buffer, "typed -> byte buffer");
      path(buffer, typed, "byte buffer -> typed");
    }
  }
  for (const Cell &C : cells) {
    offCells += C.kind == CellKind::Off;
    anyCells += C.kind == CellKind::Any;
  }
  const double secs =
      std::chrono::duration<double>(Clock::now() - t0).count();
  CG_LOG("Cells: iteration " << iteration << ": " << objs.size()
         << " origins (" << funcSeeds << " function seeds, " << objSeeds
         << " objects (" << tailMinted << " trailing, " << trailingArrays << " of them arrays of unknown extent, " << tailMoved
         << " cells moved to them); heap " << heapLabeled << " labeled (" << heapPtrArrays
         << " arrays of pointer slots, " << tailObjects
         << " header + trailing data), " << heapUnlabeled
         << " unlabeled, " << heapConflict << " with conflicting labels, "
         << heapContainerRelabeled << " relabeled to the container their size names, "
         << heapContainerAmbiguous << " left unlabeled (several containers of that size)), "
         << cells.size() << " cells (" << offCells << " named offsets, "
         << anyCells << " any-offset, " << outMints << " outside)\n");
  CG_LOG("Cells: " << numNodes << " solver nodes, " << staticCopies
         << " copies, " << stores << " stores, " << lazyFEdges.size()
         << " field edges, " << dynEdges << " hub edges (" << hubLinks
         << " links), " << pops << " pops, " << factMass << " facts, "
         << secs << " s (labels " << labelSecs << " s, propagation "
         << solveSecs << " s)\n");
  CG_LOG("Cells: any-offset from: " << cappedMints << " capped mints, "
         << stridedUnlabeled << " strided steps on unlabeled objects, "
         << expandCapped << " capped expansions (" << stepCalls
         << " steps over " << stepOffsets << " offsets); dereferences of a "
         << "function " << funcDerefs << ", of an outside address "
         << outDerefs << "\n");
  interiorReport();
  {
    size_t n = 0;
    std::string line;
    for (auto &[k, c] : identPairs) {
      n += c;
      if (line.size() < 600) line += " " + k.second + " as " + k.first + " x" + std::to_string(c) + ";";
    }
    CG_LOG("Cells: debug-info identities the linked IR merged away: " << n << " objects ("
           << identPairs.size() << " identity / IR struct pairs):" << line << "\n");
  }
  CG_LOG("Cells: rule (b): struct written into storage used as bytes (not admitted as its "
         << "layout; the value flows to the raw cell): " << bytesWritesRefused
         << ", by writing site | struct:\n");
  {
    std::vector<std::pair<size_t, std::string>> top;
    for (auto &[k, c] : bytesWritesBy) top.push_back({c, k});
    std::sort(top.rbegin(), top.rend());
    for (size_t i = 0; i < top.size() && i < 15; i++)
      CG_LOG("Cells:   x" << top[i].first << " " << top[i].second << "\n");
  }
  // Writes of another struct into the data after a T, folded into its
  // array (one label per allocation): rule (b) rows too.
  ruleB += tailWritesFolded + bytesWritesRefused;
  for (auto &[k, c] : tailFoldPairs) ruleBPairs[k] += c;
  CG_LOG("Cells: rule (b) member steps whose struct is not at the "
         << "address's offset: " << ruleB << " (" << ruleBPairs.size()
         << " object label / struct pairs)\n");
  if (VerboseLevel >= 2) {
    topObjects(12);
    massByObject(10);
    std::vector<std::pair<size_t, std::pair<std::string, std::string>>> top;
    for (auto &[k, c] : ruleBPairs) top.push_back({c, k});
    std::sort(top.rbegin(), top.rend());
    for (size_t i = 0; i < top.size() && i < 20; i++)
      CG_LOG("Cells:   rule (b) x" << top[i].first << " object "
             << top[i].second.first << ", step of struct "
             << top[i].second.second << "\n");
  }
  CG_LOG("FlowsTo: resolved " << resolved << " icalls, " << totalTargets
         << " targets (" << newPairs << " new pairs wired, " << typeRej
         << " type-rejected), iteration " << iteration << "\n");
  // ---- The rule report (plan 3.11, cells writer): the rules the call
  // graph assumes and where the program breaks them, from the cell
  // solver's state. Rewritten each iteration; the last one stands. ----
  // Byte-array relays (measurement): typed -> B -> typed paths, the cell
  // pairs they join today (B is one cell: every source cell to every
  // destination cell) and with offset preservation (a copy into B keeps
  // the source offset as +k, a copy out maps +k back: only overlapping
  // positions join, one to one).
  if (CFLCellSoupProfile && !relayIn.empty()) {
    size_t paths = 0, broken = 0;
    double now = 0, kept = 0;
    std::vector<std::tuple<double, uint32_t, size_t, size_t>> big; // pairs now, B, ins, outs
    for (auto &[B, ins] : relayIn) {
      auto oit = relayOut.find(B);
      if (oit == relayOut.end()) continue;
      double bn = 0;
      for (const RelayEnd &i : ins)
        for (const RelayEnd &o : oit->second) {
          if (i.obj == o.obj) continue;
          paths++;
          const double pn = (double)i.cells * (double)o.cells;
          const int64_t lo = std::max(i.at, o.at), hi = std::min(i.at + i.len, o.at + o.len);
          const double pk = hi > lo ? (double)std::min<int64_t>(hi - lo, std::min(i.cells, o.cells)) : 0;
          broken += pk == 0;
          now += pn;
          kept += pk;
          bn += pn;
        }
      big.push_back({bn, B, ins.size(), oit->second.size()});
    }
    std::sort(big.rbegin(), big.rend());
    // Per relay B: (1) the source types it receives, (3) the destination
    // types it feeds, (2) whether each source/destination type pair is
    // compatible (equal, or one embedded at the other's start).
    auto labelOf = [&](uint32_t o) {
      return objs[o].layout ? objs[o].label : std::string("unlabeled");
    };
    auto compat = [&](uint32_t a, uint32_t c) {
      const Obj &A = objs[a], &C = objs[c];
      if (!A.layout || !C.layout) return false;
      if (A.label == C.label) return true;
      return (C.layout->isStructTy() && structStartsAt(A.layout, 0, C.label, DL)) ||
             (A.layout->isStructTy() && structStartsAt(C.layout, 0, A.label, DL));
    };
    size_t oneSrc = 0, oneDst = 0, allCompat = 0, pathsCompat = 0, pathsAll = 0;
    std::vector<std::string> relayLines;
    for (auto &[bn, B, ni, no] : big) {
      std::map<std::string, size_t> sl, dl;
      for (const RelayEnd &e : relayIn[B]) sl[labelOf(e.obj)]++;
      for (const RelayEnd &e : relayOut[B]) dl[labelOf(e.obj)]++;
      bool every = true;
      size_t pc = 0, pa = 0;
      for (const RelayEnd &i : relayIn[B])
        for (const RelayEnd &o : relayOut[B]) {
          if (i.obj == o.obj) continue;
          pa++;
          if (compat(i.obj, o.obj)) pc++;
          else every = false;
        }
      oneSrc += sl.size() == 1;
      oneDst += dl.size() == 1;
      allCompat += every;
      pathsCompat += pc;
      pathsAll += pa;
      if (relayLines.size() < 6) {
        auto top = [](const std::map<std::string, size_t> &m) {
          std::vector<std::pair<size_t, std::string>> v;
          for (auto &[k, c] : m) v.push_back({c, k});
          std::sort(v.rbegin(), v.rend());
          std::string r;
          for (size_t i = 0; i < v.size() && i < 4; i++) r += " " + v[i].second + " x" + std::to_string(v[i].first);
          return std::to_string(m.size()) + " types:" + r;
        };
        relayLines.push_back(describe(objs[B]) + ": in " + top(sl) + "; out " + top(dl) + "; compatible pairs " +
                             std::to_string(pc) + " of " + std::to_string(pa));
      }
    }
    CG_LOG("Cells: relay questions: of " << big.size() << " relays, " << oneSrc
           << " receive one type, " << oneDst << " feed one type, " << allCompat
           << " have every source/destination pair compatible; paths compatible " << pathsCompat
           << " of " << pathsAll << "\n");
    for (const std::string &l : relayLines) CG_LOG("Cells:   relay " << l << "\n");
    CG_LOG("Cells: byte-array relays: " << big.size() << " arrays relay typed->typed, " << paths
           << " object paths (" << broken << " with no overlapping offsets); cell pairs joined "
           << (size_t)now << " today, " << (size_t)kept << " with offset preservation\n");
    for (size_t i = 0; i < big.size() && i < 3; i++) {
      const auto [bn, B, ni, no] = big[i];
      CG_LOG("Cells:   relay " << describe(objs[B]) << ": " << ni << " typed regions in, " << no
             << " out, " << (size_t)bn << " cell pairs today\n");
      std::set<std::string> where;
      for (const RelayEnd &e : relayIn[B]) if (e.I && where.size() < 3) where.insert("in " + instLoc(e.I) + " from " + describe(objs[e.obj]));
      for (const RelayEnd &e : relayOut[B]) if (e.I && where.size() < 6) where.insert("out " + instLoc(e.I) + " to " + describe(objs[e.obj]));
      for (const std::string &w : where) CG_LOG("Cells:     " << w << "\n");
    }
  }
  // ---- Pool handle cells after the solve (plan 3.53 rule 3). The carve
  // checks before the solve see typed accesses only. A write into a
  // certified pool's handle cell from anywhere but the pool's own form
  // sites (bump, refill, handle-field stores, rewinds) is a rule row:
  // "pool handle written outside its forms". This checks the hypothesis
  // that an offset-0 handle is reached only through typed accesses
  // (`*(void **)o = p` through the struct's address). ----
  std::vector<std::pair<const Instruction *, std::string>> poolRows;
  if (!poolHandleFields.empty()) {
    std::set<std::string> poolStructs;
    for (const std::string &f : poolHandleFields) poolStructs.insert(f.substr(0, f.rfind('+')));
    auto structOf = [&](const Obj &O) {
      std::string l = stripStructNameSuffix(O.ident.empty() ? O.label : O.ident).str();
      return StringRef(l).starts_with("struct.") ? l.substr(7) : l;
    };
    // The handle fields a write through fact f reaches: its cell's field;
    // every handle field of the struct at or past the cell for a block
    // copy (memcpy, memmove; a memset writes no pointer), and all of them
    // for an any-offset cell.
    auto reach = [&](uint32_t f, bool block, std::set<std::string> &out) -> bool {
      const size_t before = out.size();
      const Cell &c = cells[f];
      if (c.kind != CellKind::Off && c.kind != CellKind::Any) return false;
      const Obj &O = objs[c.obj];
      if (!O.layout) return false;
      const std::string s = structOf(O);
      if (!poolStructs.count(s)) return false;
      for (const std::string &h : poolHandleFields) {
        if (h.compare(0, s.size() + 1, s + "+") != 0) continue;
        const int64_t ho = std::stoll(h.substr(s.size() + 1));
        if (c.kind == CellKind::Any || (block && ho >= c.off) || (!block && ho == c.off)) out.insert(h);
      }
      return out.size() > before;
    };
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (Instruction &I : instructions(F)) {
          const Value *Addr = nullptr;
          bool block = false;
          if (const auto *SI = dyn_cast<StoreInst>(&I)) {
            Addr = SI->getPointerOperand();
          } else if (const auto *MI = dyn_cast<MemTransferInst>(&I)) {
            Addr = MI->getDest(); // a memset writes no pointer
            block = true;
          }
          if (!Addr || poolBookkeeping.count(&I)) continue;
          const NodeIndex n = NF.getValueNodeFor(Addr);
          if (n == AndersNodeFactory::InvalidIndex || getCanonicalNode(n) >= G) continue;
          std::set<std::string> hit;
          const uint32_t pn = find(canon(n));
          uint32_t cause = UINT32_MAX; // the leak that carried a reaching fact here
          bool tagged = false;
          pts[pn].forEach([&](uint32_t f) {
            if (!reach(f, block, hit) || tagged) return;
            if (auto it = leakTag.find((uint64_t)pn << 32 | findFact(f)); it != leakTag.end()) {
              cause = it->second;
              tagged = true;
            }
          });
          if (hit.empty()) continue;
          // The row: the solver's facts admit a writer of the handle cell
          // outside the forms, and its first cause (the leak census's tag
          // of the reaching fact at the writer's pointer).
          std::string fs;
          for (const std::string &h : hit) fs += (fs.empty() ? "" : " ") + h;
          fs += "; first cause: ";
          if (!CFLCellLeakCensus) fs += "unknown (run with --cfl-cell-leak-census)";
          else if (!tagged) fs += "not carried by a byte-storage leak";
          else fs += "the imprecise pointer at " + leakSites[cause].where;
          poolRows.push_back({&I, fs});
        }
    CG_LOG("Cells: pool handle cells (" << poolHandleFields.size() << " fields of the certified pools): "
           << poolRows.size() << " writes outside the pools' forms (rule rows: the carve model assumes "
           << "they do not change the handle; sound when the program keeps its pool discipline)\n");
    for (size_t i = 0; i < poolRows.size() && i < 20; i++)
      CG_LOG("Cells:   the solver's facts admit a writer of the handle cell outside the pool's forms at "
             << instLoc(poolRows[i].first) << ": " << poolRows[i].second << "\n");
  }
  if (!CFLRuleReport.empty()) {
    std::error_code EC;
    raw_fd_ostream RO(CFLRuleReport, EC, sys::fs::OF_Text);
    if (EC) {
      errs() << "FATAL: cannot write " << CFLRuleReport << ": " << EC.message() << "\n";
      exit(1);
    }
    // (a) pointers made from integers that carry no address: an inttoptr
    // used as a pointer whose value holds no fact; its integer sources
    // say what the bytes were.
    struct AHit { const Instruction *I; std::string kind, srcs; };
    std::vector<AHit> ruleA;
    size_t aData = 0, aConst = 0, aLost = 0;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (Instruction &I : instructions(F)) {
          auto *IP = dyn_cast<IntToPtrInst>(&I);
          if (!IP) continue;
          bool usedAsPtr = false;
          for (const User *U : IP->users()) {
            if (const auto *LI = dyn_cast<LoadInst>(U)) usedAsPtr |= LI->getPointerOperand() == IP;
            else if (const auto *SI = dyn_cast<StoreInst>(U)) usedAsPtr |= SI->getPointerOperand() == IP;
            else if (const auto *CB = dyn_cast<CallBase>(U)) usedAsPtr |= CB->getCalledOperand() == IP;
            else if (const auto *G = dyn_cast<GetElementPtrInst>(U)) usedAsPtr |= G->getPointerOperand() == IP;
          }
          if (!usedAsPtr) continue;
          const NodeIndex n = NF.getValueNodeFor(IP);
          if (n != AndersNodeFactory::InvalidIndex && getCanonicalNode(n) < G &&
              pts[find(canon(n))].count())
            continue;
          SmallVector<const Value *, 16> work{IP->getOperand(0)};
          SmallPtrSet<const Value *, 16> seen;
          std::string srcs;
          bool lost = false, allConst = true;
          while (!work.empty() && seen.size() < 24) {
            const Value *V = work.pop_back_val();
            if (!seen.insert(V).second) continue;
            std::string leaf;
            if (isa<ConstantInt>(V)) leaf = "const";
            else if (isa<PtrToIntInst>(V) || (isa<ConstantExpr>(V) &&
                     cast<ConstantExpr>(V)->getOpcode() == Instruction::PtrToInt)) {
              leaf = "ptrtoint";
              lost = true;
            } else if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
              work.push_back(BO->getOperand(0));
              work.push_back(BO->getOperand(1));
              continue;
            } else if (const auto *CA = dyn_cast<CastInst>(V)) {
              work.push_back(CA->getOperand(0));
              continue;
            } else if (const auto *PN = dyn_cast<PHINode>(V)) {
              for (const Value *In : PN->incoming_values()) work.push_back(In);
              continue;
            } else if (const auto *SE = dyn_cast<SelectInst>(V)) {
              work.push_back(SE->getTrueValue());
              work.push_back(SE->getFalseValue());
              continue;
            } else if (const auto *LI = dyn_cast<LoadInst>(V)) leaf = "load " + instLoc(LI);
            else if (const auto *A = dyn_cast<Argument>(V))
              leaf = "arg " + A->getParent()->getName().str() + "#" + std::to_string(A->getArgNo());
            else if (const auto *CB = dyn_cast<CallBase>(V)) {
              const Function *CF = CB->getCalledFunction();
              leaf = "call " + (CF ? CF->getName().str() : std::string("<icall>"));
            } else if (const auto *I4 = dyn_cast<Instruction>(V)) leaf = I4->getOpcodeName();
            else leaf = "other";
            if (leaf != "const") allConst = false;
            if (srcs.size() < 300) srcs += (srcs.empty() ? "" : "; ") + leaf;
          }
          const char *kind = lost ? "unknown" : allConst ? "constant" : "data";
          (lost ? aLost : allConst ? aConst : aData)++;
          if (ruleA.size() < 5000) ruleA.push_back({&I, kind, srcs});
        }
    // ---- Outside dependence per indirect call (plan 3.48; DSA's
    // completeness flag). An object the outside can reach (a pointer
    // passed to a bodiless call without a summary, an undefined global,
    // an asm operand), and every object reachable from its cells, is
    // exposed; an indirect call whose callee is loaded from an exposed
    // object, or comes from an uncalled function's formal, a bodiless
    // call's result or an asm result, depends on those boundaries. ----
    std::vector<std::pair<std::string, std::string>> bnd; // (kind, id)
    std::map<std::pair<std::string, std::string>, uint32_t> bndIdx;
    auto bid = [&](const std::string &kind, const std::string &id) {
      auto [it, ins] = bndIdx.try_emplace({kind, id}, (uint32_t)bnd.size());
      if (ins) bnd.push_back({kind, id});
      return it->second;
    };
    // Exposure is per content cell: a pointer to (o, off) hands the outside
    // the subobject there (the struct starting at off, else the byte or
    // element array holding it, else the cell; an unlabeled object whole),
    // and what its cells point to.
    std::map<std::pair<uint32_t, int64_t>, std::set<uint32_t>> exposedBy;
    std::vector<std::pair<uint32_t, int64_t>> exWork;
    std::map<const Function *, uint32_t> fnsOutside; // functions whose address reaches the outside (a boundary)
    auto exposeAt = [&](uint32_t o, int64_t off, const std::set<uint32_t> &B, bool whole = false) {
      const Obj &O = objs[o];
      if (const auto *Fn = dyn_cast_or_null<Function>(NF.getValueForNode(O.origin)); Fn && !B.empty())
        fnsOutside.try_emplace(Fn, *B.begin());
      int64_t lo = INT64_MIN, hi = INT64_MAX;
      if (O.layout && !whole) {
        const int64_t pos = O.repeats ? ((off % O.size) + O.size) % O.size : off;
        int64_t alo = 0, ahi = 0, esz = 0;
        if (StructType *S = structAt(O.layout, pos, DL)) {
          lo = pos;
          hi = pos + (int64_t)DL.getTypeAllocSize(S);
        } else if (innermostArraySpan(O.layout, pos, DL, alo, ahi, esz)) {
          lo = alo;
          hi = ahi;
        } else {
          lo = pos;
          hi = pos + 1;
        }
      }
      for (auto &[c, up] : O.content) {
        if (c < lo || c >= hi) continue;
        std::set<uint32_t> &E = exposedBy[{o, c}];
        const size_t before = E.size();
        for (uint32_t b : B) if (E.size() < 5) E.insert(b); // capped: "several"
        if (E.size() != before) exWork.push_back({o, c});
      }
    };
    auto factsAt = [&](const Value *V, std::vector<std::pair<uint32_t, int64_t>> &out) {
      const NodeIndex n = NF.getValueNodeFor(V);
      if (n == AndersNodeFactory::InvalidIndex || getCanonicalNode(n) >= G) return;
      pts[find(canon(n))].forEach([&](uint32_t f) {
        for (auto [o, e] : memb[findFact(f)]) out.push_back({o, decOff(e)});
      });
    };
    auto summarized = [&](const Function *F) {
      auto it = Ctx->FuncSummaries.find(F);
      return it != Ctx->FuncSummaries.end() && !it->second->none;
    };
    std::set<const Function *> calledFns;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (Instruction &I : instructions(F))
          if (const auto *CB = dyn_cast<CallBase>(&I)) {
            if (const Function *CF = CB->getCalledFunction()) {
              calledFns.insert(CF);
              calledFns.insert(getFuncDef(const_cast<Function *>(CF)));
            }
            if (auto cit = Ctx->Callees.find(CB); cit != Ctx->Callees.end())
              for (const Function *T : cit->second) calledFns.insert(T);
          }
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (Instruction &I : instructions(F)) {
          const auto *CB = dyn_cast<CallBase>(&I);
          if (!CB || isa<IntrinsicInst>(CB)) continue;
          std::set<uint32_t> B;
          if (CB->isInlineAsm()) {
            B.insert(bid("asm", instLoc(CB)));
          } else if (const Function *CF = CB->getCalledFunction()) {
            const Function *D = getFuncDef(const_cast<Function *>(CF));
            if (!D->isDeclaration() || summarized(D) || summarized(CF)) continue;
            B.insert(bid("bodiless call", D->getName().str()));
          } else {
            continue; // indirect calls: below, once their callees' boundaries are known
          }
          for (const Value *A : CB->args()) {
            if (!A->getType()->isPointerTy()) continue;
            std::vector<std::pair<uint32_t, int64_t>> fs;
            factsAt(A, fs);
            for (auto [o, off] : fs) exposeAt(o, off, B);
          }
        }
    for (uint32_t o = 0; o < objs.size(); o++) {
      const auto *GV = dyn_cast_or_null<GlobalVariable>(NF.getValueForNode(objs[o].origin));
      if (!GV) continue;
      if (GV->isDeclaration())
        exposeAt(o, 0, {bid("undefined global", GV->getName().str())}, true);
      else if (!CFLWholeProgram && !GV->hasLocalLinkage())
        exposeAt(o, 0, {bid("exported global", GV->getName().str())}, true);
    }
    auto drainExposure = [&]() {
      while (!exWork.empty()) { // what an exposed cell points to
        const auto [o, c] = exWork.back();
        exWork.pop_back();
        const std::set<uint32_t> B = exposedBy[{o, c}];
        auto cit = objs[o].content.find(c);
        if (cit == objs[o].content.end()) continue;
        pts[find(cit->second.second)].forEach([&](uint32_t f) {
          for (auto [o2, e] : memb[findFact(f)]) exposeAt(o2, decOff(e), B);
        });
      }
    };
    drainExposure();
    // The boundaries an indirect call's callee depends on.
    std::function<void(const Value *, std::set<uint32_t> &, std::set<const Value *> &)> calleeDeps =
        [&](const Value *V, std::set<uint32_t> &out, std::set<const Value *> &seen) {
      V = V->stripPointerCasts();
      if (!seen.insert(V).second || seen.size() > 512) return;
      if (const auto *A = dyn_cast<Argument>(V)) {
        if (!calledFns.count(A->getParent()))
          out.insert(bid("uncalled formal", A->getParent()->getName().str() + "#" +
                                                std::to_string(A->getArgNo())));
        return;
      }
      if (const auto *L = dyn_cast<LoadInst>(V)) {
        // A local slot: what is stored into it.
        if (const auto *AI = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts()))
          for (const User *U : AI->users())
            if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand()->stripPointerCasts() == AI)
              calleeDeps(St->getValueOperand(), out, seen);
        std::vector<std::pair<uint32_t, int64_t>> fs;
        factsAt(L->getPointerOperand(), fs);
        for (auto [o, off] : fs) {
          auto it = exposedBy.find({o, contentKey(objs[o], off)});
          if (it != exposedBy.end()) out.insert(it->second.begin(), it->second.end());
        }
        return;
      }
      if (const auto *CB = dyn_cast<CallBase>(V)) {
        if (CB->isInlineAsm()) { out.insert(bid("asm", instLoc(CB))); return; }
        // A call's result: a bodiless call is a boundary; a body's (or each
        // resolved target's) returned values are followed.
        std::vector<const Function *> Ts;
        if (const Function *CF = CB->getCalledFunction()) Ts.push_back(getFuncDef(const_cast<Function *>(CF)));
        else if (auto cit = Ctx->Callees.find(CB); cit != Ctx->Callees.end())
          for (const Function *T : cit->second) Ts.push_back(T);
        for (const Function *D : Ts) {
          if (D->isDeclaration()) {
            if (!summarized(D)) out.insert(bid("bodiless call", D->getName().str()));
            continue;
          }
          for (const BasicBlock &RB : *D)
            if (const auto *Ret = dyn_cast<ReturnInst>(RB.getTerminator()); Ret && Ret->getReturnValue())
              calleeDeps(Ret->getReturnValue(), out, seen);
        }
        return;
      }
      if (const auto *PN = dyn_cast<PHINode>(V)) {
        for (const Value *In : PN->incoming_values()) calleeDeps(In, out, seen);
        return;
      }
      if (const auto *SI = dyn_cast<SelectInst>(V)) {
        calleeDeps(SI->getTrueValue(), out, seen);
        calleeDeps(SI->getFalseValue(), out, seen);
        return;
      }
      if (const auto *GEP = dyn_cast<GEPOperator>(V)) calleeDeps(GEP->getPointerOperand(), out, seen);
    };
    // Indirect calls whose callee may come from the outside (plan 3.51 Q1:
    // a dlsym'd entry point): their arguments reach the outside. Exposure
    // grows the set of loads that depend on it, so repeat to a fixpoint.
    std::set<const CallBase *> outTargeted;
    for (bool grew = true; grew;) {
      grew = false;
      for (const CallBase *CS : Ctx->IndirectCallInsts) {
        if (outTargeted.count(CS) || CS->isInlineAsm()) continue;
        std::set<uint32_t> deps;
        std::set<const Value *> seen;
        calleeDeps(CS->getCalledOperand(), deps, seen);
        if (deps.empty()) continue;
        outTargeted.insert(CS);
        grew = true;
        const std::set<uint32_t> B{bid("outside indirect call", instLoc(CS))};
        for (const Value *A : CS->args()) {
          if (!A->getType()->isPointerTy()) continue;
          std::vector<std::pair<uint32_t, int64_t>> fs;
          factsAt(A, fs);
          for (auto [o, off] : fs) exposeAt(o, off, B);
        }
      }
      drainExposure();
    }
    // The outside-domain premise (plan 3.51 a.2, Q1): a function the
    // pre-solve domain excluded never reaches the outside, and no indirect
    // call in the corpus reaches an entry whose parameters were read under it.
    std::vector<std::string> domainBroken;
    if (!taggedOutsideEntries.empty()) {
      for (auto &[Fn, b] : fnsOutside)
        if (!Fn->isDeclaration() && !taggedOutsidePre.count(Fn) && (CFLWholeProgram || Fn->hasLocalLinkage()))
          domainBroken.push_back("function " + Fn->getName().str() + ", outside the pre-solve domain, reaches the outside (" +
                                 bnd[b].first + " " + bnd[b].second + ")");
      for (auto &[CB, Ts] : Ctx->Callees)
        if (!CB->getCalledFunction() && !CB->isInlineAsm())
          for (const Function *T : Ts)
            if (taggedOutsideEntries.count(T))
              domainBroken.push_back("indirect call at " + instLoc(CB) + " reaches the outside entry " +
                                     T->getName().str());
    }
    std::vector<std::string> depRows;
    size_t nComplete = 0, nDepend = 0;
    std::map<std::string, size_t> byKind, byBodiless;
    for (const CallBase *CS : Ctx->IndirectCallInsts) {
      std::set<uint32_t> out;
      std::set<const Value *> seen;
      calleeDeps(CS->getCalledOperand(), out, seen);
      if (out.empty()) {
        nComplete++;
        depRows.push_back("R complete " + instLoc(CS));
        continue;
      }
      nDepend++;
      std::string l = "R depends " + instLoc(CS) + ":";
      std::set<std::string> kinds;
      size_t shown = 0;
      for (uint32_t b : out) {
        kinds.insert(bnd[b].first);
        if (bnd[b].first == "bodiless call") byBodiless[bnd[b].second]++;
        if (shown++ < 4) l += " [" + bnd[b].first + " " + bnd[b].second + "]";
      }
      if (out.size() > 4) l += " (several: " + std::to_string(out.size()) + ")";
      for (const std::string &k : kinds) byKind[k]++;
      depRows.push_back(l);
    }
    const std::string prog = Ctx->Modules.empty() ? std::string("?")
                                                  : Ctx->Modules.front().first->getName().str();
    std::vector<std::pair<size_t, std::pair<std::string, std::string>>> bTop;
    for (auto &[k, c] : ruleBPairs) bTop.push_back({c, k});
    std::sort(bTop.rbegin(), bTop.rend());
    RO << "# Rule report (plan 3.11; cells writer). Input: " << prog << "\n"
       << "# Rows under --cfl-cells (plan 3.48 note): (b) counts member steps of\n"
       << "# struct T on an address whose object has another label at that offset;\n"
       << "# (c) lists the premises the solver assumes (untyped writes and bodiless\n"
       << "# calls write no struct slot), struct copies between unrelated types, and\n"
       << "# relay rows: byte copies between differently labeled storage (3.53 rule 4).\n";
    RO << "SUMMARY a " << aData << " pointers from data, " << aConst
       << " from constant addresses, " << aLost << " from pointers lost before the cast\n";
    RO << "SUMMARY b " << ruleB << " member steps whose struct is not at the address's offset ("
       << ruleBPairs.size() << " object label / struct pairs)\n";
    // Rule 4: one row per (site, source label, destination label); types
    // that print as one label (renamed copies of a struct) are one row.
    std::map<std::string, size_t> relayLines;
    for (auto &[k, n] : relayRows) {
      auto [I, ls, ld] = k;
      auto lab = [](Type *T) { return T ? typeLabel(T) : std::string("bytes"); };
      relayLines[(I ? instLoc(I) : std::string("?")) + ": " + lab(ls) + " into " + lab(ld)] += n;
    }
    RO << "SUMMARY c " << modUntypedWrites << " untyped writes and " << modBodiless
       << " calls of bodiless functions assumed to write no struct slot; "
       << copyMismatches << " copies between unrelated structs; " << relayLines.size()
       << " relay rows (byte copies between differently labeled storage, rule 4)\n";
    RO << "SUMMARY UB " << byteStepUB << " byte steps leaving a byte array, "
       << leftObject << " offsets past a single object, " << indexOutsideArray
       << " variable indexes on a single object, pointer subtractions across objects: always "
       << rrPtrAlways << ", may " << rrPtrMay << "\n";
    {
      std::string k;
      for (auto &[n, c] : byKind) k += ", " + n + " " + std::to_string(c);
      RO << "SUMMARY outside " << nComplete << " indirect calls complete, " << nDepend
         << " depend on an outside boundary (--cfl-outside=" << CFLOutside.getValue()
         << ")" << k << "\n";
    }
    {
      size_t t = 0, un = 0, mx = 0, cl = 0;
      for (const PwcComp &P : pwcComps) {
        (P.typed && P.untyped ? mx : P.typed ? t : un)++;
        cl += P.cls;
      }
      // Indirect-call width downstream of a cycle with offset.
      std::vector<uint8_t> down(numNodes, 0);
      std::vector<uint32_t> work;
      for (uint32_t u = 0; u < numNodes && u < inPwc.size(); u++)
        if (inPwc[u]) { down[u] = 1; work.push_back(u); }
      while (!work.empty()) {
        const uint32_t u = work.back();
        work.pop_back();
        auto visit = [&](uint32_t v) { v = find(v); if (v < numNodes && !down[v]) { down[v] = 1; work.push_back(v); } };
        for (uint32_t v : succ[u]) visit(v);
        for (const FieldEdge &e : fieldOut[u]) visit(e.dst);
      }
      size_t wAll = 0, wDown = 0;
      for (const CallBase *CS : Ctx->IndirectCallInsts) {
        auto cit = Ctx->Callees.find(CS);
        const size_t w = cit == Ctx->Callees.end() ? 0 : cit->second.size();
        wAll += w;
        const NodeIndex n = NF.getValueNodeFor(CS->getCalledOperand());
        if (n != AndersNodeFactory::InvalidIndex && getCanonicalNode(n) < G && down[find(canon(n))])
          wDown += w;
      }
      RO << "SUMMARY pwc " << pwcComps.size() + g_counterRetired + g_counterKept
         << " cycles with offset (typed " << t + g_counterRetired + g_counterKept << ": walks " << t
         << ", counters " << g_counterRetired << " retired by the integer-name test and "
         << g_counterKept << " kept on the int-launder fallback; untyped " << un << ", mixed " << mx
         << "; through a C++ class step " << cl << "); indirect-call width downstream of the walks: "
         << wDown << " of " << wAll << " targets\n";
    }
    RO << "SUMMARY varargs " << varargMapped << " renderers mapped, " << varargKeyedReads
       << " va_arg reads keyed, " << varargUnkeyedReads << " unkeyed; call sites: "
       << varargKeyedSites << " constant format, " << varargPoolSites << " non-constant, "
       << varargUnparsed << " unparsed\n";
    if (!taggedPairs.empty())
      RO << "SUMMARY tagged fields " << taggedPairs.size() << " pairs keyed, " << taggedFlipped.size()
         << " flipped in the solve; alias assumptions " << asmUsed - asmFailed << " held, " << asmFailed
         << " failed; predicate tests: " << taggedCounts[7] << " closed, " << taggedCounts[8]
         << " open; parameter-pair tests: " << taggedCounts[9] << " keyed reads, " << taggedCounts[10]
         << " untested; outside-domain entries " << taggedOutsideEntries.size() << ", premise broken at "
         << (stoppedAt ? std::string("unknown (the solve stopped: no icall answers)") : std::to_string(domainBroken.size()))
         << "\n";
    for (const std::string &d : domainBroken) RO << "T outside domain broken: " << d << "\n";
    if (!taggedPairs.empty()) {
      // Which functions the outside can call (their address reaches it),
      // by the boundary that exposed them: this, not linkage, is "callers
      // not all visible".
      std::map<uint32_t, size_t> byB;
      size_t defined = 0, inPre = 0;
      for (auto &[Fn, b] : fnsOutside)
        if (!Fn->isDeclaration()) byB[b]++, defined++, inPre += taggedOutsidePre.count(Fn);
      // A stopped solve has no icall answers: which callers the outside
      // has is not known (calls through resolved targets are not followed).
      if (stoppedAt)
        RO << "SUMMARY outside callers: unknown (the solve stopped at pop " << stoppedAt
           << ": no icall answers; at least " << defined << " defined functions reach the outside; pre-solve domain "
           << taggedOutsidePre.size() << " functions)\n";
      else
        RO << "SUMMARY outside callers: " << defined << " defined functions reach the outside after the solve, "
           << inPre << " of them in the pre-solve domain (" << taggedOutsidePre.size() << " functions)\n";
      for (auto &[b, n] : byB) RO << "T outside callers: " << n << " via " << bnd[b].first << " " << bnd[b].second << "\n";
    }
    if (!taggedEntryRows.empty() || !entryF.empty()) {
      // Plan 3.54: per method formal, how its objects entered (stop
      // numbers when the solve stopped).
      size_t other = 0, onlyKeys = 0, poisoned = 0, carried = 0, chanSites = 0;
      for (const EntryF &ef : entryF) {
        poisoned += ef.poisoned;
        other += ef.other.size();
        for (auto &[o, hs] : ef.held) onlyKeys += !hs.empty();
        for (auto &[o, ts] : ef.terms) carried += !ef.other.count(o) && ts.size() > 1;
      }
      for (auto &[cs, chs] : taggedEntryChannels) chanSites += chs.size();
      RO << "SUMMARY method entry tests (3.54) " << entryF.size() << " method formals, "
         << taggedEntryReads.size() << " reads keyed by an entry test; " << taggedEntrySites.size()
         << " dispatch sites are tests; " << chanSites << " calls pass a formal's object on, "
         << chanNodeOf.size() << " channels used (3.54 (b)); " << poisoned
         << " formals not split (every object unkeyed); objects " << other << " entered otherwise (unkeyed), "
         << onlyKeys << " read through keys, " << carried << " of them with terms carried in"
         << (stoppedAt ? " (at the stop)" : "") << "\n";
      for (const std::string &r : taggedEntryRows) RO << "T entry " << r << "\n";
      for (uint32_t fi = 0; fi < entryF.size(); fi++) {
        const EntryF &ef = entryF[fi];
        RO << "T entry formal " << taggedEntryFormals[fi].M->getName() << " arg " << taggedEntryFormals[fi].k
           << ": " << ef.testEntries << " test-dispatch entries, " << ef.chanEntries << " channel entries, "
           << ef.otherEntries << " other entries, " << ef.other.size() << " objects read unkeyed, "
           << ef.termLinks << " term links"
           << (ef.poisoned ? " (not split: " + ef.why + ")" : std::string()) << "\n";
      }
    }
    if (!taggedInPlace.empty()) {
      RO << "SUMMARY tagged fields in-place retags " << taggedInPlace.size()
         << " (open tag writes no test guards and no content write accompanies: they retag every writer)\n";
      for (auto &[f, I, mp] : taggedInPlace)
        RO << "T in-place retag without content write, callers not all visible: " << instLoc(I) << " of " << f
           << " map " << mp << "\n";
    }
    if (!taggedUntested.empty()) {
      RO << "SUMMARY tagged fields untested reads " << taggedUntested.size()
         << " (reads of a field with candidate tags that no tag test guards: every writer)\n";
      for (auto &[f, I] : taggedUntested) RO << "U untested read " << instLoc(I) << " of " << f << "\n";
    }
    RO << "\n== assumptions the rows rest on\n"
       << "ASSUME outside code honors the type of what it is handed: it writes only within the "
          "subobject it received and what that subobject points to, never stepping past it "
          "(under --cfl-outside=pure this is part of \"writes nothing\"; under roots it is the "
          "whole claim of the outside rows)\n"
       << "ASSUME setjmp/longjmp: bodiless calls (the jmp_buf they receive is exposed); longjmp "
          "does not return (noreturn), and its non-local return to the setjmp carries no "
          "pointer value the flow-insensitive solve does not already hold\n"
       << "ASSUME untyped writes and calls of bodiless functions write no struct slot "
          "(receivers premise; counted in SUMMARY c)\n"
       << "ASSUME a va_arg read under the case of specifier c reads only arguments passed under "
          "c or under a non-constant format (plan 3.47)\n";
    if (!taggedPairs.empty())
      RO << "ASSUME tagged fields (plan 3.51): a tag write in a function whose callers are not all "
            "visible (address taken, or exported in a partial corpus) applies, under its guard, to "
            "every writer of the field; outside code handing such an object back honors its "
            "declared type and writes none of its fields (the struct is opaque to it), so the "
            "field's content writers are the program's own; a call returns only through its "
            "returns (longjmp not modeled)\n";
    if (!taggedOutsideEntries.empty())
      RO << "ASSUME tagged fields, outside domain (plan 3.51 a.2): a function-pointer parameter of an "
            "exported function entered from outside holds its call sites' arguments, NULL, -1, a "
            "function of the outside, an exported function, or a function whose address reaches "
            "the outside; checked: no internal function reaches the outside and no indirect call in "
            "the corpus reaches such an entry (T rows name each break)\n";
    RO << "\n== (a) pointers made from bytes that never were a pointer\n";
    for (const AHit &h : ruleA) RO << "A " << h.kind << " " << instLoc(h.I) << " from: " << h.srcs << "\n";
    RO << "\n== (b) member steps of a struct the object is not at that offset\n";
    for (auto &[c, k] : bTop) RO << "B x" << c << " object " << k.first << " stepped as " << k.second << "\n";
    RO << "\n== (c) premises and copies between unrelated structs\n";
    for (const std::string &d : copyMismatchAt) RO << "C copy " << d << "\n";
    for (auto &[r, n] : relayLines) RO << "C relay " << r << " (" << n << " regions)\n";
    RO << "C integer name copied into bytes: " << intNameToBytes << " positions\n";
    for (const std::string &d : intNameToBytesAt) RO << "C int-to-bytes " << d << "\n";
    RO << "\n== UB undefined behavior (counted, not followed)\n";
    for (auto [n, o, pos, k] : byteStepUBAt)
      RO << "UB byte-exit " << (n < numNodes ? nodeDesc(n) : std::string("?")) << " steps " << k
         << " from " << describe(objs[o]) << " +" << pos << "\n";
    for (const std::string &d : rrPtrAt) RO << "UB ptr-sub " << d << "\n";
    RO << "\n== cycles with offset, the ten largest (plan 3.49)\n";
    {
      std::vector<PwcComp> top = pwcComps;
      std::sort(top.begin(), top.end(), [](const PwcComp &a, const PwcComp &b) {
        return a.size != b.size ? a.size > b.size : a.rep < b.rep;
      });
      for (size_t i = 0; i < top.size() && i < 10; i++)
        RO << "P size " << top[i].size << " step " << top[i].g << " typed " << top[i].typed
           << " untyped " << top[i].untyped << (top[i].cls ? " C++ class" : "") << " at "
           << (top[i].rep < numNodes ? nodeDesc(top[i].rep) : std::string("?")) << "\n";
    }
    RO << "\n== outside dependence per indirect call (plan 3.48)\n";
    {
      std::vector<std::pair<size_t, std::string>> rank;
      for (auto &[f, c] : byBodiless) rank.push_back({c, f});
      std::sort(rank.rbegin(), rank.rend());
      for (auto &[c, f] : rank) RO << "O bodiless " << f << ": " << c << " indirect calls depend on it\n";
      std::sort(depRows.begin(), depRows.end()); // the call set is pointer-ordered
      for (const std::string &d : depRows) RO << d << "\n";
    }
    RO << "\n== varargs keyed by format specifier (plan 3.47)\n";
    for (const std::string &d : varargReport) RO << "V " << d << "\n";
    if (!poolHandleFields.empty()) {
      RO << "\n== pool handle cells written outside the pools' forms (plan 3.53 rule 3)\n";
      RO << "SUMMARY pool handles " << poolHandleFields.size() << " fields, " << poolRows.size()
         << " writes outside the forms\n";
      for (auto &[I, fs] : poolRows)
        RO << "P the solver's facts admit a writer of this handle cell outside the pool's forms (" << instLoc(I)
           << "); the carve model assumes that write does not change the handle; sound when the program keeps "
           << "its pool discipline: " << fs << "\n";
    }
    CG_LOG("Cells: rule report written to " << CFLRuleReport << "\n");
  }
  if (stoppedAt && !CFLCellStopAnswers.empty()) {
    // The partial state at the stop, one line per indirect call (its
    // function, location and ordinal there), sorted: the cells gate pins it.
    std::error_code EC;
    raw_fd_ostream SO(CFLCellStopAnswers, EC, sys::fs::OF_Text);
    if (EC) {
      errs() << "FATAL: cannot write " << CFLCellStopAnswers << ": " << EC.message() << "\n";
      exit(1);
    }
    SO << "STOP pops " << stoppedAt << " cells " << cells.size() << " facts " << factMass << "\n";
    std::vector<std::string> lines;
    for (auto &[CS, names] : stopAnswers) {
      unsigned pos = 0; // the call's position in its function
      for (const Instruction &I : instructions(*CS->getFunction())) {
        if (&I == CS) break;
        pos++;
      }
      std::string l = CS->getFunction()->getName().str() + " " + instLoc(CS) + " #" + std::to_string(pos) + ":";
      for (const std::string &n : names) l += " " + n;
      lines.push_back(l);
    }
    std::sort(lines.begin(), lines.end());
    for (const std::string &l : lines) SO << l << "\n";
  }
  if (stoppedAt) {
    errs() << "Cells: stopped at " << stoppedAt << " pops (--cfl-cell-census-at); "
           << "the reports above describe the partial state\n";
    exit(0);
  }

  if (CFLCellOneLabel && CFLCellOneLabelMax > 1 && newPairs == 0) finishCollect();
  if (newPairs == 0) return false;
  if (iteration + 1 >= (int)CFLFlowsToMaxIters) {
    if (!CFLIterCapOk) {
      errs() << "ERROR: cell solver hit the iteration cap ("
             << CFLFlowsToMaxIters.getValue() << ") with " << newPairs
             << " newly wired pairs unprocessed; raise "
             << "--cfl-flows-to-max-iters\n";
      exit(1);
    }
    WARNING("[UNSOUND-RISK] cell solver hit the iteration cap with "
            << newPairs << " newly wired pairs unprocessed\n");
    soundnessCapped = true;
    return false;
  }
  return true;
}
