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
#include "ValueMap.h"
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
  // A container element minted per owner (plan 3.55): the owner object
  // (UINT32_MAX: not a row object).
  uint32_t rowOwner = UINT32_MAX;
  // Laid out at mint as the largest constructor element: never a tail.
  bool rowLaidOut = false;
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
  // Labeled at mint as an array of the scalar every creating site declares
  // and uses (ruling A): a struct step into it is a rule (b) row.
  bool declScalar = false;
  // Declared at mint as an array of its element (a scalar, ruling A; a
  // pointer slot, 1b's T**): every element is named, no extent rule.
  bool declArray = false;
  // A segment the site indexes by a stride of its struct: an array of it
  // without an extent (the struct analogue of declArray).
  bool segArray = false;
  // Widened from T to a container S that has T at offset 0 (row 2): the
  // cells inside T keep T's names (widenLabel+c for c < widenSize).
  std::string widenLabel;
  int64_t widenSize = 0;
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
// members and array elements)? An anonymous struct's name names nothing
// (isAnonStruct): it is found only as the type Same itself, or one of its
// layout.
bool structStartsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL,
                    const StructType *Same = nullptr) {
  const bool anon = isAnonStructName(S);
  for (int depth = 0; depth < 64 && T && off >= 0; depth++) {
    if (auto *ST = dyn_cast<StructType>(T)) {
      if (anon ? ST == Same : ST->hasName() && stripStructNameSuffix(ST->getName()) == S)
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
      if (ST->hasName() && !isAnonStruct(ST))
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

// The last store into slot S at or before I, walking back in I's block.
const StoreInst *lastStoreFrom(const Instruction *I, const AllocaInst *S) {
  for (; I; I = I->getPrevNode())
    if (const auto *SI = dyn_cast<StoreInst>(I); SI && SI->getPointerOperand() == S) return SI;
  return nullptr;
}
// The last store into S in BB, and the last one before L in L's block.
const StoreInst *lastStoreIn(const BasicBlock *BB, const AllocaInst *S) { return lastStoreFrom(&BB->back(), S); }
const StoreInst *lastStoreBefore(const Instruction *L, const AllocaInst *S) {
  return lastStoreFrom(L->getPrevNode(), S);
}

// The store into S reaching BB's end: BB's last, else up a chain of single
// predecessors (not through `stop`, the block a load is in).
const StoreInst *storeAtEnd(const BasicBlock *BB, const AllocaInst *S, const BasicBlock *stop) {
  std::set<const BasicBlock *> walked{stop};
  for (; BB && walked.insert(BB).second; BB = BB->getSinglePredecessor())
    if (const StoreInst *SI = lastStoreIn(BB, S)) return SI;
  return nullptr;
}

// Is A a slot (only loaded, and stored into by value)? *several: stored
// more than once; *only: its store when once.
bool sizeSlot(const AllocaInst *A, bool &several, const StoreInst *&only) {
  several = false;
  only = nullptr;
  for (const User *U : A->users()) {
    if (isa<LoadInst>(U)) continue;
    const auto *SI = dyn_cast<StoreInst>(U);
    if (!SI || SI->getPointerOperand() != A || SI->getValueOperand() == A) return false;
    several |= only != nullptr;
    only = SI;
  }
  return only != nullptr;
}

// The one store reaching load L of slot S stored several times: the last
// store before L in its block, else in the nearest block up a chain of
// single predecessors, else the store every predecessor's chain reaches
// (all the same one), else, when every store is in the entry block, the
// last one there. Null when none of these decides it.
const StoreInst *reachingStore(const LoadInst *L, const AllocaInst *S) {
  const BasicBlock *B = L->getParent();
  if (const StoreInst *SI = lastStoreBefore(L, S)) return SI;
  if (const BasicBlock *P = B->getSinglePredecessor()) return storeAtEnd(P, S, B);
  const StoreInst *agreed = nullptr;
  bool all = !pred_empty(B);
  for (const BasicBlock *P : predecessors(B)) {
    const StoreInst *SI = storeAtEnd(P, S, B);
    all &= SI && (!agreed || SI == agreed);
    agreed = SI;
  }
  if (all && agreed) return agreed;
  const BasicBlock *E = &L->getFunction()->getEntryBlock();
  if (B == E) return nullptr;
  for (const User *U : S->users())
    if (const auto *SI = dyn_cast<StoreInst>(U); SI && SI->getParent() != E) return nullptr;
  return lastStoreIn(E, S);
}

// An allocation size's source: through casts, and at -O0 a local slot that
// never escapes (its only users are direct loads and stores into it: no
// call can write it through its address) forwards the stored value
// reaching the load (sqlite3: nByte = sizeof(Fts3SegReader) +
// (nElem+1)*sizeof(Fts3HashElem *); malloc(nByte); fts3InitVtab reuses
// nByte; newchunk rounds n at entry).
const Value *sizeThrough(const Value *V) {
  for (int d = 0; d < 8; d++) {
    if (const auto *CI = dyn_cast<CastInst>(V)) { V = CI->getOperand(0); continue; }
    if (const auto *L = dyn_cast<LoadInst>(V))
      if (const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
        bool several = false;
        const StoreInst *only = nullptr;
        if (sizeSlot(S, several, only)) {
          if (!several) { V = only->getValueOperand(); continue; }
          if (const StoreInst *SI = reachingStore(L, S)) { V = SI->getValueOperand(); continue; }
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
// (`n*sizeof(T) + sizeof(T)` is an array of n+1)? The size is add + the
// product of ops (a wrapper's term `n + 16` at its call `w(len)`: len
// read as above, 16 one more constant term).
bool headerPlusTail(const std::vector<const Value *> &ops, uint64_t sz, int64_t add = 0) {
  auto lookThrough = sizeThrough;
  auto multipleOf = [&](const Value *X) { return isMultipleOf(X, sz); };
  if (add) {
    uint64_t prod = 1;
    bool allConst = true, multiple = false;
    for (const Value *A : ops) {
      const auto *K = dyn_cast<ConstantInt>(lookThrough(A));
      if (K) prod *= K->getZExtValue();
      else allConst = false;
      multiple |= isMultipleOf(A, sz);
    }
    if (allConst) {
      const int64_t k = (int64_t)prod + add;
      return k > (int64_t)sz && k % (int64_t)sz != 0;
    }
    if (add < (int64_t)sz) return false; // no header among the constants
    if (ops.size() != 1) return !multiple; // add + a product
  }
  if (ops.size() != 1) return false; // a product (calloc) is an array or one, not T plus data
  for (const Value *A : ops) {
    const Value *V = lookThrough(A);
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
    if (terms.size() < 2 && !add) continue;
    bool header = add >= (int64_t)sz, other = false;
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
bool exactlyOne(const std::vector<const Value *> &ops, uint64_t sz, int64_t add = 0) {
  uint64_t prod = 1;
  bool any = false;
  for (const Value *V : ops) {
    V = sizeThrough(V);
    const auto *K = dyn_cast<ConstantInt>(V);
    if (!K) return false;
    prod *= K->getZExtValue();
    any = true;
  }
  return any && (int64_t)prod + add == (int64_t)sz;
}

// Does an allocation call's size say "an array of T": an integer argument
// that is a multiple of sizeof(T) (calloc(n, sizeof T), malloc(n * sizeof
// T), realloc(p, k * sizeof T))?
bool sizeIsMultiple(const std::vector<const Value *> &ops, uint64_t sz, int64_t add = 0) {
  if (add % (int64_t)sz) return false;
  for (const Value *V : ops)
    if (isMultipleOf(V, sz, true)) return true;
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

  // Kernel dispatch as named cells (plan 3.53, kernel census, Fable
  // 2026-10-13). A direct call to a bodiless __SCT__X trampoline is an
  // indirect call through the cell (@__SCK__X, static_call_key.func)
  // (GraphBuild: the key's load into the call's callee node; the
  // trampoline is never an origin); the key's initializer and
  // __static_call_update's store `key->func = func` are ordinary flow.
  // __traceiter_X is a defined function and a call to it a direct call;
  // its `it_func = funcs->func` dispatch resolves by flow from
  // tracepoint_probe_register's store into tp->funcs.
  {
    size_t traceIterCalls = 0;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M)
        for (Instruction &I : instructions(F))
          if (const auto *CB = dyn_cast<CallBase>(&I))
            if (const Function *CF = CB->getCalledFunction(); CF && CF->getName().starts_with("__traceiter_"))
              traceIterCalls++;
    if (g_staticCallWired || g_staticCallNoKey || traceIterCalls)
      CG_LOG("Cells: kernel dispatch: " << g_staticCallWired << " __SCT__ sites rewritten through their key, "
             << g_staticCallNoKey << " __SCT__ sites without a visible key (an extern call: outside), "
             << traceIterCalls << " __traceiter_ direct calls kept\n");
  }

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
  std::vector<std::vector<uint32_t>> rowsAt; // owner pointer -> its container row links
  std::vector<std::vector<uint32_t>> mintsAt; // owner pointer -> its element mint links
  std::vector<std::vector<uint32_t>> inheritAt; // a body's element value -> the containers it serves
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
    hubsOf.resize(cap); rowsAt.resize(cap); mintsAt.resize(cap); inheritAt.resize(cap);
    fieldOut.resize(cap); anyLoop.resize(cap, 0);
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
  // Container rows (plan 3.55): each row link at its owner pointer.
  for (uint32_t i = 0; i < rowLinks.size(); i++) {
    const uint32_t o = canon(rowLinks[i].owner);
    inGraph[o] = 1;
    rowsAt[o].push_back(i);
    if (rowLinks[i].in != AndersNodeFactory::InvalidIndex) inGraph[canon(rowLinks[i].in)] = 1;
    if (rowLinks[i].out != AndersNodeFactory::InvalidIndex) inGraph[canon(rowLinks[i].out)] = 1;
  }
  for (uint32_t i = 0; i < mintLinks.size(); i++) {
    const uint32_t o = canon(mintLinks[i].owner);
    inGraph[o] = inGraph[canon(mintLinks[i].out)] = 1;
    mintsAt[o].push_back(i);
  }
  for (uint32_t ci = 0; ci < containerElemSources.size(); ci++)
    for (const Value *E : containerElemSources[ci]) {
      const NodeIndex n = getRepNodeForValue(E);
      if (n == AndersNodeFactory::InvalidIndex) continue;
      inGraph[canon(n)] = 1;
      inheritAt[canon(n)].push_back(ci);
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
    rowsAt[r].insert(rowsAt[r].end(), rowsAt[m].begin(), rowsAt[m].end());
    rowsAt[m].clear();
    mintsAt[r].insert(mintsAt[r].end(), mintsAt[m].begin(), mintsAt[m].end());
    mintsAt[m].clear();
    inheritAt[r].insert(inheritAt[r].end(), inheritAt[m].begin(), inheritAt[m].end());
    inheritAt[m].clear();
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
  uint32_t curStepFact = UINT32_MAX, curStepNode = UINT32_MAX, curStepDst = UINT32_MAX;
  uint32_t curStepLi = UINT32_MAX; // the label of the step or walk being applied
  // --cfl-cell-slot-census: what minted each content cell (the mint cause,
  // the arrival being applied, and for a step or walk its result node).
  struct SlotMint {
    std::string cause;
    Why why;
    uint32_t stepDst = UINT32_MAX;
  };
  boost::unordered_flat_map<std::pair<uint32_t, int64_t>, SlotMint> slotMint;
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
    if (CFLCellSlotCensus)
      slotMint.try_emplace(std::make_pair(o, c),
                           SlotMint{mintCause, curWhy,
                                    curWhy.kind == W_STEP || curWhy.kind == W_WALK ? curStepDst : UINT32_MAX});
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
    if (O.widenSize && c >= 0 && c < O.widenSize) return O.widenLabel + "+" + std::to_string(c);
    return (O.ident.empty() ? O.label : O.ident) + "+" + std::to_string(c);
  };
  // The address fact (o, off): exact, or folded (off is element 0's).
  // The trailing object of header+tail object o, minted on first use.
  size_t tailMinted = 0, tailMoved = 0, segmentsLabeled = 0, segmentArrays = 0, segmentsBytes = 0,
         segmentsPtrArrays = 0, segmentsScalarArrays = 0;
  // Tails a variable index linked while unlabeled, and how many of them a
  // later first typed use labeled (rule 1's own solve order; counted).
  boost::unordered_flat_set<uint32_t> tailLinkedUnlabeled;
  size_t tailLinkedThenLabeled = 0;
  // A segment the site declares at the tail's start (plan 3.53 rule 1:
  // an allocation of known size is a sequence of segments), its label and
  // extent from the known size; set once the extent rule exists.
  std::function<void(Obj &)> segmentLabel;
  auto tailOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].tailObj != UINT32_MAX) return objs[o].tailObj;
    assert(!objs[o].rowLaidOut && "a row object laid out as its largest constructor element has no tail");
    Obj T;
    T.origin = objs[o].origin;
    T.parentObj = o;
    T.base = objs[o].base + objs[o].size;
    // The site's declared segment at the tail's start, known size or not
    // (row (3): a constant-offset cast declares [c, c + sizeof B) as a
    // receiver declares T at 0; the size only ever governed the extent).
    if (segmentLabel) segmentLabel(T);
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
  // Collect mode reports a conflict once: a repeat (the same node, kind
  // and facts, after merges) is counted, not reported again.
  std::set<std::array<uint32_t, 4>> collectSeen;
  size_t collectDup = 0;
  size_t oneLabelFiltered = 0;
  std::function<bool(uint32_t)> oneLabelMatch; // set once describe exists
  auto pend1 = [&](PendingConflict P) {
    // --cfl-cell-one-label-object: only a conflict whose held or arriving
    // cell belongs to a matching object.
    if (!CFLCellOneLabelObject.empty() && oneLabelMatch) {
      const bool match = oneLabelMatch(P.f) || (P.kind == 0 && oneLabelMatch(P.a));
      if (!match) {
        oneLabelFiltered++;
        return;
      }
    }
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
    MintCause mc(mintCause, "fact merge", VerboseLevel >= 2);
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
  std::function<void(uint32_t, StructType *)> noteLayoutCause; // --cfl-cell-trace-obj, --cfl-cell-why
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
  // The size of an allocating call (plan 3.53, ruling B): a term of the
  // callee, evaluated at the call. A primitive allocator's term is its
  // signature's size operand(s); a fresh wrapper's is its returned
  // allocation's, composed through the inner call (a body is read; a
  // summary row without a body has none unless it declares SIZE, and a
  // row's SIZE replaces its body's), and a pool carve's is its form's
  // size (row 1: CarveSize). Never the call's integer arguments by
  // position (`new_stmt(cstate, code)`: the opcode is no size). Unknown:
  // the size says nothing.
  // The grammar: add + c x (up to two formals), rounded up to align (a
  // power of two: `(n + 7) & -8`) when align is set. partial: a further
  // factor that is not known; the term then says only that the size is a
  // MULTIPLE of c x formals (`(old + add) * element_size`), add is 0 and
  // nothing gives a count, a header or a tail position from it. Sums of
  // two products, a rounding whose input is not exact, and two returns
  // that disagree keep only that fact: a multiple of the gcd of what each
  // is a multiple of (gcd 1: unknown). zeroK (Fable 2026-10-13, only this
  // shape): a slot whose two reaching stores are a formal and a constant
  // k, the constant's under a branch on that formal compared equal to 0
  // (`if (!n) n = 1`; at -O3 a select), is "the formal, k when zero". At a
  // call it reads k for a zero constant, the actual when the actual is
  // known nonzero (a nonzero constant, or a term already reading k > 0
  // when zero, scaled up or rounded), the formal itself carried up when
  // the actual is a bare formal of the caller, and otherwise only the gcd
  // fact. Rounding an already rounded term is that term.
  struct SizeTerm {
    bool known = false;
    uint64_t c = 1;
    std::vector<unsigned> formals;
    bool partial = false;
    int64_t add = 0;
    uint64_t align = 0;
    // The product c x formals reads zeroK where it is 0 (`if (!n) n = 1`;
    // row (2): also a product actual, bfd_alloc2's size * n); -1: none.
    // With partial: a multiple of c x formals, or zeroK bytes holding no
    // element (the zero case names no element).
    int64_t zeroK = -1;
    bool isConst() const { return known && formals.empty() && !partial && !align; }
    bool operator==(const SizeTerm &o) const {
      return known == o.known && c == o.c && formals == o.formals && partial == o.partial && add == o.add &&
             align == o.align && zeroK == o.zeroK;
    }
  };
  // Is every value of t nonzero (a formal read k > 0 when 0, scaled and
  // shifted up, or rounded)?
  auto nonzero = [](const SizeTerm &t) {
    if (!t.known || t.partial) return false;
    if (t.isConst()) return t.c != 0;
    return t.zeroK > 0 && !t.formals.empty() && t.c > 0 && t.add >= 0;
  };
  auto constT = [](uint64_t k) { SizeTerm t; t.known = true; t.c = k; return t; };
  // What every value of t is a multiple of.
  auto multOf = [](const SizeTerm &t) -> uint64_t {
    if (t.align) return t.align;
    if (t.isConst()) return t.c;
    return std::gcd(t.c, (uint64_t)(t.add < 0 ? -t.add : t.add));
  };
  auto multiple = [](uint64_t m) {
    SizeTerm t;
    if (m <= 1) return t;
    t.known = true;
    t.c = m;
    t.partial = true;
    return t;
  };
  // A constant's add folds into c (a size below 0 is no size).
  auto norm = [](SizeTerm t) {
    if (t.formals.empty()) t.zeroK = -1;
    if (t.known && t.formals.empty() && !t.partial && !t.align) {
      const int64_t v = (int64_t)t.c + t.add;
      if (v < 0) return SizeTerm{};
      t.c = (uint64_t)v;
      t.add = 0;
    }
    return t;
  };
  auto plusT = [&](SizeTerm a, const SizeTerm &b) -> SizeTerm {
    if (!a.known || !b.known) return {};
    if (!a.isConst() && b.isConst() && !a.partial && !a.align) { a.add += (int64_t)b.c; return norm(a); }
    if (a.isConst() && !b.isConst() && !b.partial && !b.align) { SizeTerm r = b; r.add += (int64_t)a.c; return norm(r); }
    if (a.isConst() && b.isConst()) return constT(a.c + b.c);
    return multiple(std::gcd(multOf(a), multOf(b)));
  };
  auto plusK = [&](const SizeTerm &a, int64_t k) -> SizeTerm {
    if (!a.known) return {};
    if (a.isConst()) return norm(SizeTerm{true, a.c, {}, false, k, 0});
    if (a.partial || a.align) return multiple(std::gcd(multOf(a), (uint64_t)(k < 0 ? -k : k)));
    SizeTerm r = a;
    r.add += k;
    return norm(r);
  };
  auto timesT = [&](SizeTerm a, SizeTerm b) -> SizeTerm {
    if (!a.known && !b.known) return {};
    if (!a.known) std::swap(a, b);
    if (!b.known) { // a further unknown factor
      if (a.add || a.align || a.zeroK >= 0 || a.formals.empty()) return multiple(multOf(a));
      a.partial = true;
      return a;
    }
    if (a.isConst()) std::swap(a, b);
    if (b.isConst() && b.c == 1) return a;
    if (b.isConst()) {
      if (a.align) return multiple(a.align * b.c);
      a.c *= b.c;
      a.add *= (int64_t)b.c;
      if (a.zeroK >= 0) a.zeroK *= (int64_t)b.c; // the zero case scales too
      return norm(a);
    }
    if (a.add || b.add || a.align || b.align || a.zeroK >= 0 || b.zeroK >= 0 ||
        a.formals.size() + b.formals.size() > 2)
      return multiple(multOf(a) * multOf(b));
    a.c *= b.c;
    a.partial |= b.partial;
    a.formals.insert(a.formals.end(), b.formals.begin(), b.formals.end());
    return a;
  };
  auto alignT = [&](SizeTerm x, uint64_t al) -> SizeTerm {
    if (x.isConst()) return constT((x.c + al - 1) & ~(al - 1));
    if (x.known && x.align && x.align % al == 0) return x; // already rounded to al
    // A multiple of al rounded to al is itself (row (2): round8(72 n) is
    // 72 n); its zero case rounds.
    if (x.known && !x.align && !x.add && x.c % al == 0 && (x.partial || !x.formals.empty())) {
      if (x.zeroK >= 0) x.zeroK = (int64_t)(((uint64_t)x.zeroK + al - 1) & ~(al - 1));
      return x;
    }
    if (!x.known || x.partial || x.align) return multiple(std::max(al, x.align));
    x.align = al;
    return x;
  };
  // Two returns' terms: equal, or the gcd fact.
  auto joinT = [&](const SizeTerm &a, const SizeTerm &b) -> SizeTerm {
    if (!a.known || !b.known) return {};
    if (a == b) return a;
    return multiple(std::gcd(multOf(a), multOf(b)));
  };
  auto sigOf = [](StringRef N, std::vector<unsigned> &idx) {
    idx.clear();
    if (N == "calloc") idx = {0, 1};
    else if (N == "realloc" || N == "aligned_alloc" || N == "memalign") idx = {1};
    else if (N == "reallocarray") idx = {1, 2};
    else if (N == "malloc" || N == "valloc" || N == "pvalloc") idx = {0};
    else {
      int size = -1, flag = -1;
      if (isAllocFn(N, &size, &flag) && size >= 0) idx = {(unsigned)size};
    }
    return !idx.empty();
  };
  // V's term in F's formals.
  std::function<SizeTerm(const Value *, const Function *, int)> termIn =
      [&](const Value *V, const Function *F, int d) -> SizeTerm {
    if (d > 12) return {};
    V = sizeThrough(V);
    if (const auto *K = dyn_cast<ConstantInt>(V)) return K->isNegative() ? SizeTerm{} : constT(K->getZExtValue());
    if (const auto *A = dyn_cast<Argument>(V); A && A->getParent() == F) return {true, 1, {A->getArgNo()}};
    // "x, k when zero": x's term with zeroK, or x's own when it is nonzero.
    auto whenZero = [&](const Value *X, const ConstantInt *K) -> SizeTerm {
      if (!K || K->isNegative()) return {};
      SizeTerm t = termIn(X, F, d + 1);
      if (nonzero(t)) return t;
      if (t.known && !t.partial && !t.align && t.zeroK < 0 && t.formals.size() == 1 && t.c == 1 && !t.add) {
        t.zeroK = K->getSExtValue();
        return t;
      }
      return {};
    };
    // Is C `x == 0` (eq) or `x != 0` (!eq)? Returns x.
    auto zeroTest = [](const Value *C, bool &eq) -> const Value * {
      const auto *Cmp = dyn_cast<ICmpInst>(C);
      const auto *Z = Cmp ? dyn_cast<ConstantInt>(Cmp->getOperand(1)) : nullptr;
      if (!Z || !Z->isZero()) return nullptr;
      if (Cmp->getPredicate() != ICmpInst::ICMP_EQ && Cmp->getPredicate() != ICmpInst::ICMP_NE) return nullptr;
      eq = Cmp->getPredicate() == ICmpInst::ICMP_EQ;
      return Cmp->getOperand(0);
    };
    if (const auto *II = dyn_cast<IntrinsicInst>(V); II && II->getIntrinsicID() == Intrinsic::umax)
      for (unsigned o = 0; o < 2; o++) // -O2: umax(x, 1) is x ? x : 1, the same function
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(II->getArgOperand(o))); K && K->isOne())
          return whenZero(II->getArgOperand(1 - o), K);
    if (const auto *Sel = dyn_cast<SelectInst>(V)) { // -O3: select (x == 0), k, x
      bool eq = false;
      const Value *X = zeroTest(Sel->getCondition(), eq);
      const Value *KV = eq ? Sel->getTrueValue() : Sel->getFalseValue();
      const Value *XV = eq ? Sel->getFalseValue() : Sel->getTrueValue();
      const auto *K = dyn_cast<ConstantInt>(sizeThrough(KV));
      if (X && sizeThrough(X) == sizeThrough(XV)) return whenZero(XV, K);
      // The test before a rounding of the same formal (-O3 bfd_alloc:
      // select (n == 0), 8, (n + 7) & -8): the rounded formal reading K
      // when zero, K a multiple of the rounding (round(K) is K).
      const SizeTerm tx = X ? termIn(X, F, d + 1) : SizeTerm{};
      SizeTerm ty = termIn(XV, F, d + 1);
      if (K && !K->isNegative() && tx.known && tx.formals.size() == 1 && tx.c == 1 && !tx.add && !tx.align &&
          !tx.partial && tx.zeroK < 0 && ty.known && ty.formals == tx.formals && ty.c == 1 && !ty.add &&
          ty.align && !ty.partial && ty.zeroK < 0 && K->getZExtValue() % ty.align == 0) {
        ty.zeroK = K->getSExtValue();
        return ty;
      }
      return {};
    }
    if (const auto *L = dyn_cast<LoadInst>(V)) { // -O0: the slot form of the same
      const auto *S = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts());
      bool several = false;
      const StoreInst *only = nullptr;
      const BasicBlock *B = L->getParent();
      if (!S || !sizeSlot(S, several, only) || lastStoreBefore(L, S) || pred_size(B) != 2) return {};
      const BasicBlock *P = nullptr, *Q = nullptr;
      for (const BasicBlock *X : predecessors(B))
        if (const BasicBlock *XP = X->getSinglePredecessor(); XP && XP != X && is_contained(predecessors(B), XP))
          P = X, Q = XP;
      if (!P) return {};
      const auto *BrP = dyn_cast<BranchInst>(P->getTerminator());
      const auto *Br = dyn_cast<BranchInst>(Q->getTerminator());
      const StoreInst *SK = lastStoreIn(P, S);
      const StoreInst *SQ = storeAtEnd(Q, S, B);
      if (!BrP || BrP->isConditional() || !Br || !Br->isConditional() || !SK || !SQ) return {};
      bool eq = false;
      const Value *X = zeroTest(Br->getCondition(), eq);
      if (!X || Br->getSuccessor(eq ? 0 : 1) != P || Br->getSuccessor(eq ? 1 : 0) != B) return {};
      if (sizeThrough(X) != sizeThrough(SQ->getValueOperand())) return {};
      return whenZero(SQ->getValueOperand(), dyn_cast<ConstantInt>(SK->getValueOperand()));
    }
    const auto *B = dyn_cast<BinaryOperator>(V);
    if (!B) return {};
    const auto *K1 = dyn_cast<ConstantInt>(sizeThrough(B->getOperand(1)));
    switch (B->getOpcode()) {
    case Instruction::Mul:
      return timesT(termIn(B->getOperand(0), F, d + 1), termIn(B->getOperand(1), F, d + 1));
    case Instruction::Shl:
      if (K1 && K1->getZExtValue() < 63)
        return timesT(termIn(B->getOperand(0), F, d + 1), constT(1ULL << K1->getZExtValue()));
      return {};
    case Instruction::Add:
      if (K1) return plusK(termIn(B->getOperand(0), F, d + 1), K1->getSExtValue());
      return plusT(termIn(B->getOperand(0), F, d + 1), termIn(B->getOperand(1), F, d + 1));
    case Instruction::Sub:
      if (K1) return plusK(termIn(B->getOperand(0), F, d + 1), -K1->getSExtValue());
      return {};
    case Instruction::And:
      // x & -al: a multiple of al whatever x is; (n + al - 1) & -al is n
      // rounded up.
      if (K1 && K1->isNegative() && (-K1->getValue()).isPowerOf2()) {
        const uint64_t al = (-K1->getValue()).getZExtValue();
        // (y + al - 1) & -al, also ((y + al) - 1) & -al: y rounded up, read
        // from the sum's own operand (y may itself be rounded).
        int64_t k = 0;
        const Value *Y = sizeThrough(B->getOperand(0));
        for (int i = 0; i < 2; i++) {
          const auto *S = dyn_cast<BinaryOperator>(Y);
          const auto *C = S ? dyn_cast<ConstantInt>(sizeThrough(S->getOperand(1))) : nullptr;
          if (!C || (S->getOpcode() != Instruction::Add && S->getOpcode() != Instruction::Sub)) break;
          k += S->getOpcode() == Instruction::Add ? C->getSExtValue() : -C->getSExtValue();
          Y = sizeThrough(S->getOperand(0));
        }
        if (k == (int64_t)al - 1)
          if (const SizeTerm y = termIn(Y, F, d + 1); y.known) return alignT(y, al);
        SizeTerm x = termIn(B->getOperand(0), F, d + 1);
        if (x.isConst()) return constT(x.c & ~(al - 1));
        if (x.known && !x.partial && !x.align && x.add == (int64_t)al - 1) {
          x.add = 0;
          return alignT(x, al);
        }
        return multiple(al);
      }
      return {};
    default:
      return {};
    }
  };
  std::unordered_map<const Function *, SizeTerm> termMemo;
  std::set<const Function *> termBusy;
  std::set<const Instruction *> carveUnknownSize;
  std::function<SizeTerm(const Function *)> termOfFn;
  // The term of call C expressed in F's formals (F null: C's own operands
  // are not classified, the callee's term is returned as is).
  auto callTerm = [&](const CallBase *C, const Function *F) -> SizeTerm {
    const Function *CF = C->getCalledFunction();
    if (!CF) return {};
    std::vector<unsigned> idx;
    SizeTerm inner;
    auto sit = Ctx->FuncSummaries.find(CF);
    const GlobalContext::FuncSummary *FS = sit != Ctx->FuncSummaries.end() ? sit->second : nullptr;
    // A row's SIZE is read before the allocator table (GAPS "Size label"):
    // an explicit row beats the table's prefix guess (kmalloc* takes arg0,
    // the cache, in kmalloc_trace(s, flags, size)).
    if (FS && FS->fresh && !FS->sizeArgs.empty()) inner = {true, 1, FS->sizeArgs};
    else if (sigOf(CF->getName(), idx)) inner = {true, 1, idx};
    else if (FS && FS->fresh && !CF->isDeclaration())
      inner = termOfFn(CF);
    if (!inner.known) return {};
    if (!F) return inner;
    SizeTerm out = constT(inner.c);
    for (unsigned k : inner.formals) {
      if (k >= C->arg_size()) return {};
      out = timesT(out, termIn(C->getArgOperand(k), F, 0));
    }
    if (inner.zeroK >= 0) { // "the product, zeroK when zero" at these actuals
      const int64_t zk = inner.zeroK;
      if (out.isConst() && out.c == 0) out = constT((uint64_t)zk);
      else if (out.known && !nonzero(out)) {
        if (!out.align && !out.add && out.zeroK < 0 && (!out.formals.empty() || out.partial))
          out.zeroK = zk; // carried up: a product of F's formals, or a multiple (row (2))
        else
          out = multiple(std::gcd(multOf(out), (uint64_t)zk)); // the join with zeroK
      }
    }
    if (inner.partial) out = timesT(out, SizeTerm{});
    if (inner.add) out = plusK(out, inner.add);
    if (inner.align) out = alignT(out, inner.align);
    if (out.partial && out.c == 1 && out.formals.empty()) return {}; // no known factor
    return out;
  };
  // A pool carve's term in its function's formals (CarveSize).
  auto carveTerm = [&](const Instruction *I) -> SizeTerm {
    auto it = poolCarveSizes.find(I);
    const Function *F = I->getFunction();
    SizeTerm t;
    if (it != poolCarveSizes.end() && it->second.n)
      t = timesT(termIn(it->second.n, F, 0), constT(it->second.scale));
    else if (it != poolCarveSizes.end() && it->second.chunk) {
      // malloc(HDR + n) carved at HDR is n (the sum's own operand, not the
      // sum's term less HDR: a rounded n stays exact).
      const CallBase *CC = it->second.chunk;
      std::vector<unsigned> idx;
      const Function *CF = CC->getCalledFunction();
      if (CF && sigOf(CF->getName(), idx) && idx.size() == 1 && idx[0] < CC->arg_size())
        if (const auto *B = dyn_cast<BinaryOperator>(sizeThrough(CC->getArgOperand(idx[0])));
            B && B->getOpcode() == Instruction::Add)
          for (unsigned o = 0; o < 2 && !t.known; o++)
            if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(B->getOperand(o)));
                K && K->getSExtValue() == it->second.off)
              t = termIn(B->getOperand(1 - o), F, 0);
      if (!t.known) t = plusK(callTerm(CC, F), -it->second.off);
    }
    if (!t.known) carveUnknownSize.insert(I);
    return t;
  };
  termOfFn = [&](const Function *F) -> SizeTerm {
    if (auto it = termMemo.find(F); it != termMemo.end()) return it->second;
    if (!termBusy.insert(F).second) return {};
    std::optional<SizeTerm> agreed;
    bool bad = false;
    std::vector<const Value *> work;
    std::vector<const CallBase *> selfCalls;
    std::set<const Value *> seen;
    for (const BasicBlock &BB : *F)
      if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
        if (RI->getReturnValue()) work.push_back(RI->getReturnValue());
    while (!work.empty() && !bad) {
      const Value *V = work.back()->stripPointerCasts();
      work.pop_back();
      if (!seen.insert(V).second || isa<ConstantPointerNull>(V)) continue;
      if (const auto *PN = dyn_cast<PHINode>(V)) { for (const Value *In : PN->incoming_values()) work.push_back(In); continue; }
      if (const auto *SI = dyn_cast<SelectInst>(V)) { work.push_back(SI->getTrueValue()); work.push_back(SI->getFalseValue()); continue; }
      if (const auto *L = dyn_cast<LoadInst>(V)) // -O0: a slot only loaded and stored: every value stored
        if (const auto *A = dyn_cast<AllocaInst>(L->getPointerOperand()->stripPointerCasts())) {
          std::vector<const Value *> stored;
          bool slot = true;
          for (const User *U : A->users()) {
            if (const auto *St = dyn_cast<StoreInst>(U); St && St->getPointerOperand() == A && St->getValueOperand() != A)
              stored.push_back(St->getValueOperand());
            else if (!(isa<LoadInst>(U) && cast<LoadInst>(U)->getPointerOperand() == A) && !isa<DbgInfoIntrinsic>(U))
              slot = false;
          }
          if (slot && !stored.empty()) { work.insert(work.end(), stored.begin(), stored.end()); continue; }
        }
      const auto *C = dyn_cast<CallBase>(V);
      if (C && C->getCalledFunction() == F) { selfCalls.push_back(C); continue; } // below
      const auto *I = dyn_cast<Instruction>(V);
      const SizeTerm t = C ? callTerm(C, F) : I && poolCarves.count(I) ? carveTerm(I) : SizeTerm{};
      if (!t.known) { bad = true; break; }
      agreed = agreed ? joinT(*agreed, t) : t;
      bad = !agreed->known;
    }
    // A self call returns F's own term at its arguments: assumed, checked
    // against the other returns until it holds (the gcd fact descends).
    for (int round = 0; !bad && agreed && !selfCalls.empty(); round++) {
      termMemo[F] = *agreed;
      SizeTerm next = *agreed;
      for (const CallBase *C : selfCalls) next = joinT(next, callTerm(C, F));
      if (next == *agreed) break;
      agreed = next;
      bad = !next.known || round == 4;
    }
    termBusy.erase(F);
    const SizeTerm out = (bad || !agreed) ? SizeTerm{} : *agreed;
    if (VerboseLevel >= 3) {
      std::string ts = "unknown";
      if (out.known) {
        ts = std::to_string(out.c);
        for (unsigned k : out.formals) ts += " x arg" + std::to_string(k);
        if (out.zeroK >= 0) ts += " (" + std::to_string(out.zeroK) + " when zero)";
        if (out.add) ts += (out.add > 0 ? " + " : " - ") + std::to_string(out.add > 0 ? out.add : -out.add);
        if (out.align) ts = "round" + std::to_string(out.align) + "(" + ts + ")";
        if (out.partial) ts = "a multiple of " + ts;
      }
      CG_DEBUG("Cells: size term of " << F->getName() << ": " << ts << "\n");
    }
    return termMemo[F] = out;
  };
  size_t promotedUnknownSize = 0;
  // Allocations sized by a product through a zero-guarded wrapper (row
  // (2): bfd_alloc2(abfd, n, 72) = a multiple of 72).
  std::set<const CallBase *> zeroProductSites;
  // The size of an allocation site V as operands and an addend (size =
  // add + the product of ops; an undef operand is a factor not known),
  // false when the size is unknown. A call's inner term is evaluated at
  // its own operands (their sums read by headerPlusTail); a rounding is
  // folded when its input is constant at the call, else it is a multiple.
  // A carve's term only when it is constant or a multiple.
  auto sizeOps = [&](const Value *V, std::vector<const Value *> &ops, int64_t &add) {
    ops.clear();
    add = 0;
    LLVMContext &Cx = V->getContext();
    // A term at the site: a constant, a multiple; a product of the site's
    // own formals (values unknown here) is a multiple of c (its zero case
    // names no element, row (2)).
    auto fromTerm = [&](const SizeTerm &t) {
      if (!t.known || t.align || (!t.formals.empty() && t.add)) return false;
      ops.push_back(ConstantInt::get(Type::getInt64Ty(Cx), t.c));
      if (t.partial || !t.formals.empty()) ops.push_back(UndefValue::get(Type::getInt64Ty(Cx)));
      return true;
    };
    if (const auto *I = dyn_cast<Instruction>(V); I && poolCarves.count(I)) return fromTerm(carveTerm(I));
    const auto *C = dyn_cast<CallBase>(V);
    if (!C) return false;
    const SizeTerm t = callTerm(C, nullptr);
    if (!t.known) return false;
    if (t.align || t.zeroK >= 0) {
      const SizeTerm e = callTerm(C, C->getFunction());
      if (fromTerm(e)) {
        if (t.zeroK >= 0 && !e.isConst()) zeroProductSites.insert(C); // row (2)
        return true;
      }
      return t.align && fromTerm(multiple(t.align));
    }
    for (unsigned k : t.formals) {
      if (k >= C->arg_size()) { ops.clear(); return false; }
      ops.push_back(C->getArgOperand(k));
    }
    if (t.c != 1 || ops.empty())
      ops.push_back(ConstantInt::get(Type::getInt64Ty(Cx), t.c));
    if (t.partial) ops.push_back(UndefValue::get(Type::getInt64Ty(Cx))); // an unknown factor
    add = t.add;
    return true;
  };
  // The size label (GAPS "Size label"): a heap object whose allocation
  // size is a constant k larger than its label S takes the struct of size
  // k that embeds S at offset 0 (the struct analyzer's embedding table,
  // transitive); one such struct names it, several leave S (counted with
  // the candidates), none leaves S. A multiple of S's size is an array of
  // S (plan 3.53, rule 1), not a container.
  std::map<std::string, size_t> sizeLabelAmbiguous; // "S at k: {candidates}" -> objects
  auto containerOfSize = [&](const CallBase *C, const StructType *S, int64_t sz,
                             size_t &n) -> StructType * {
    n = 0;
    uint64_t k = 0;
    std::vector<const Value *> ops;
    int64_t add = 0;
    if (sizeOps(C, ops, add)) {
      uint64_t prod = 1;
      bool allConst = true;
      for (const Value *V : ops)
        if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(V))) prod *= K->getZExtValue();
        else allConst = false;
      prod += add;
      if (allConst && prod > (uint64_t)sz && prod % sz) k = prod;
    }
    if (!k) return nullptr;
    const StructInfo *SI =
        Ctx->structAnalyzer.getStructInfo(S, const_cast<Module *>(C->getModule()));
    if (!SI) return nullptr;
    StructType *one = nullptr;
    std::set<std::string> cands;
    for (auto &[ct, offs] : SI->getContainers())
      if (offs.count(0) && ct->isSized() && DL.getTypeAllocSize(const_cast<StructType *>(ct)) == k) {
        n++;
        one = const_cast<StructType *>(ct);
        cands.insert(typeLabel(one));
      }
    if (n > 1) {
      std::string c;
      for (const std::string &x : cands) c += (c.empty() ? "" : ", ") + x;
      sizeLabelAmbiguous[typeLabel(const_cast<StructType *>(S)) + " at " + std::to_string(k) + " bytes: {" + c + "}"]++;
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
    std::vector<const Value *> ops;
    int64_t add = 0;
    const bool sized = V && sizeOps(V, ops, add);
    if (C && !sized)
      if (const Function *CF = C->getCalledFunction())
        if (auto sit = Ctx->FuncSummaries.find(CF); sit != Ctx->FuncSummaries.end() && sit->second && sit->second->fresh)
          promotedUnknownSize++; // a fresh wrapper (promoted or a row) whose size term is unknown
    if (sized && headerPlusTail(ops, at, add)) { O.tail = true; extentHeader++; tailObjects++; }
    else if (sized && exactlyOne(ops, at, add)) extentOne++;
    else if (sized && sizeIsMultiple(ops, at, add)) { O.repeats = true; extentArrays++; }
    else { O.tail = true; O.tailUnsized = true; extentUnknown++; }
  };
  segmentLabel = [&](Obj &T) {
    const Value *V = NF.getValueForNode(T.origin);
    auto sit = allocSegments.find(V);
    if (sit == allocSegments.end()) return;
    auto bit = sit->second.find(T.base);
    if (bit == sit->second.end()) return;
    // A segment declared by a receiver of another kind, as the result's
    // receiver declares the block (Fable 2026-10-13): bytes (char *), byte-
    // used from mint; an array of pointer slots (T **) or of a declared
    // scalar, every element named, no extent rule.
    const StringRef K = bit->second;
    if (K == "bytes") {
      T.byteAccessed = true;
      segmentsBytes++;
      return;
    }
    if (K.starts_with("ptr[]:") || K.starts_with("scal[]:")) {
      LLVMContext &Cx = V->getContext();
      if (K.starts_with("ptr[]:")) {
        T.layout = PointerType::get(Cx, 0);
        T.ident = K.drop_front(6).str() + "[]";
        segmentsPtrArrays++;
      } else {
        const StringRef e = K.drop_front(7);
        unsigned bits = 0;
        T.layout = e == "float" ? Type::getFloatTy(Cx)
                   : e == "double" ? Type::getDoubleTy(Cx)
                   : e == "half" ? Type::getHalfTy(Cx)
                   : e.drop_front(1).getAsInteger(10, bits) ? nullptr
                                                            : (Type *)IntegerType::get(Cx, bits);
        assert(T.layout && "a scalar label names a scalar type");
        T.ident = e.str() + "[]";
        T.declScalar = true;
        segmentsScalarArrays++;
      }
      T.size = (int64_t)DL.getTypeAllocSize(T.layout);
      T.label = typeLabel(T.layout);
      T.repeats = true;
      T.declArray = true;
      segmentsLabeled++;
      return;
    }
    StructType *B = StructType::getTypeByName(V->getContext(), bit->second);
    if (!B || B->isOpaque() || !B->isSized()) return;
    T.layout = B;
    T.size = (int64_t)DL.getTypeAllocSize(B);
    T.label = typeLabel(B);
    segmentsLabeled++;
    // The site indexes it by a stride of B (`&VdbeFrameMem(p)[n]`): an
    // array of B without an extent, every element named, no tail; data
    // after it at a variable offset folds into B's element cells.
    if (auto ait = allocSegmentArrays.find(V); ait != allocSegmentArrays.end() && ait->second.count(T.base)) {
      T.repeats = true;
      T.declArray = true;
      T.segArray = true;
      segmentArrays++;
      return;
    }
    setExtent(T, V); // one B, an array of B, or B and a further tail (recursively)
  };
  // Row 2 (plan 3.53, Fable 2026-10-13): a struct step naming S at the
  // start of an object labeled T, where S has T at offset 0 (the
  // embedding: C inheritance, `container_of` at 0) and the allocation's
  // known constant size fits S, widens the label to S. Only a T followed by
  // data whose trailing object is not yet used: inside T the folded
  // offsets are the same under S, so every existing cell keeps its meaning
  // and its name; an array of T (folded element addresses), a used tail,
  // an unknown or too small size refuse, counted by reason.
  size_t widened = 0;
  // Objects an anonymous struct would label (isAnonStruct): unlabeled.
  size_t anonObjects = 0;
  boost::unordered_flat_set<uint32_t> anonLayoutRefused; // objects
  std::map<std::string, size_t> widenRefused;
  auto tryWiden = [&](uint32_t o, const StructType *S) -> bool {
    Obj &O = objs[o];
    auto *T = dyn_cast_or_null<StructType>(O.layout);
    if (!T || !S || isAnonStruct(S) || O.fn || O.parentObj != UINT32_MAX || O.base != 0 || O.declScalar || S->isOpaque() ||
        !S->isSized() || !T->hasName() ||
        !structStartsAt(const_cast<StructType *>(S), 0, stripStructNameSuffix(T->getName()), DL, T))
      return false;
    const int64_t sS = (int64_t)DL.getTypeAllocSize(const_cast<StructType *>(S));
    const Value *V = NF.getValueForNode(O.origin);
    std::vector<const Value *> ops;
    int64_t add = 0;
    uint64_t prod = 1;
    bool constant = V && sizeOps(V, ops, add);
    for (const Value *X : ops)
      if (const auto *K = dyn_cast<ConstantInt>(sizeThrough(X))) prod *= K->getZExtValue();
      else constant = false;
    const char *why = !constant ? "size not a known constant"
                      : (int64_t)prod + add < sS ? "the container does not fit the size"
                      : O.repeats ? "an array of T (element addresses fold)"
                      : !O.tail ? "one T exactly"
                      : O.tailObj != UINT32_MAX ? "the data after T is already used"
                      : nullptr;
    if (why) {
      widenRefused[why]++;
      return false;
    }
    O.widenLabel = O.ident.empty() ? O.label : O.ident;
    O.widenSize = O.size;
    O.layout = const_cast<StructType *>(S);
    O.size = sS;
    O.label = typeLabel(O.layout);
    O.ident.clear();
    // The extent by the size against S (statistics are the mint's).
    const size_t s1 = extentArrays, s2 = extentOne, s3 = extentHeader, s4 = extentUnknown, s5 = tailObjects,
                 s6 = promotedUnknownSize;
    setExtent(O, V);
    extentArrays = s1, extentOne = s2, extentHeader = s3, extentUnknown = s4, tailObjects = s5,
    promotedUnknownSize = s6;
    widened++;
    return true;
  };
  // The extension of a header+tail object into an array of its T (defined
  // with the steps; a label request on an unsized tail makes it).
  std::function<void(uint32_t)> extendToArrayFn;
  std::function<std::string(uint32_t)> nodeDescFn; // set once nodeDesc exists
  std::function<std::string(const Obj &)> describeFn; // set once describe exists
  size_t bytesWritesRefused = 0;
  // Ruling A: struct steps into storage declared scalar (rule (b): folded
  // into the array's element cells, flow kept), and how many write.
  size_t scalarStructSteps = 0, scalarStructWrites = 0;
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
    // container (GAPS "Size label"); with several such containers, the
    // first-access label (counted with the candidates).
    if (O.base == 0)
      if (const auto *C = dyn_cast_or_null<CallBase>(NF.getValueForNode(O.origin))) {
        size_t n = 0;
        if (StructType *CT = containerOfSize(C, S, sz, n)) {
          S = CT;
          sz = (int64_t)DL.getTypeAllocSize(S);
          heapContainerRelabeled++;
        } else if (n > 1) {
          heapContainerAmbiguous++; // the first-access label stays
        }
      }
    // An anonymous struct names nothing (isAnonStruct): the object stays
    // unlabeled, its cells by byte offset.
    if (isAnonStruct(S)) {
      anonLayoutRefused.insert(o);
      return;
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
    if (tailLinkedUnlabeled.erase(o)) tailLinkedThenLabeled++;
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
  size_t heapLabeled = 0, heapUnlabeled = 0, heapConflict = 0, heapPtrArrays = 0, heapScalarArrays = 0,
         heapBytesMarked = 0;
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
        O.declArray = true;
        O.ident = StringRef(*lit->second.begin()).drop_front(6).str() + "[]";
        heapLabeled++;
        heapPtrArrays++;
      } else if (lit != labels.end() && lit->second.size() == 1 &&
                 StringRef(*lit->second.begin()).starts_with("scal[]:")) {
        // Ruling A: every creating site declares and uses one scalar (a
        // float table): an array of it, labeled at mint.
        const StringRef e = StringRef(*lit->second.begin()).drop_front(7);
        LLVMContext &Cx = C->getContext();
        unsigned bits = 0;
        O.layout = e == "float" ? Type::getFloatTy(Cx)
                   : e == "double" ? Type::getDoubleTy(Cx)
                   : e == "half" ? Type::getHalfTy(Cx)
                   : e.drop_front(1).getAsInteger(10, bits) ? nullptr
                                                            : (Type *)IntegerType::get(Cx, bits);
        assert(O.layout && "a scalar label names a scalar type");
        O.repeats = true;
        O.declScalar = true;
        O.declArray = true;
        O.ident = e.str() + "[]";
        heapLabeled++;
        heapScalarArrays++;
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
        // Ruling A: every creating site uses it only as bytes (sdup's
        // string): used as bytes from mint, so a struct write arriving
        // through an imprecise pointer is a rule (b) row, not its label.
        if (allocBytesOnly.count(C)) {
          O.byteAccessed = true;
          heapBytesMarked++;
        }
      }
    }
    if (O.layout && O.layout->isSized())
      O.size = (int64_t)DL.getTypeAllocSize(O.layout);
    if (O.size <= 0) O.layout = nullptr; // opaque or empty: unlabeled
    else O.label = typeLabel(O.layout);
    // A global or stack object of an anonymous struct (or an array of one):
    // unlabeled, its cells by byte offset (isAnonStruct), its size kept.
    if (O.layout) {
      Type *E = O.layout;
      while (auto *AT = dyn_cast<ArrayType>(E)) E = AT->getElementType();
      if (isAnonStruct(dyn_cast<StructType>(E))) {
        O.layout = nullptr;
        O.label.clear();
        anonObjects++;
      }
    }
    if (O.layout && (isa_and_nonnull<AllocaInst>(V) || isa_and_nonnull<GlobalVariable>(V)))
      noteIdent(O, diMergedIdent(V, false));
    // A constant size larger than the label where some struct of exactly
    // that size starts with the label: the label is the first member of a
    // container (C inheritance: the allocating code writes only `pub`),
    // not a header before trailing data (GAPS "Size label"). One such
    // container: its type; several (cjpeg -O3: huff and phuff encoders are
    // both 200 bytes): the label stays, counted with the candidates.
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
            heapContainerAmbiguous++; // the label stays
          }
        }
    // A declared array (of a scalar, ruling A; of pointer slots, 1b) is an
    // array of its element whatever the size says: no header, no trailing
    // object.
    if (O.layout && O.repeats && !O.declArray && isa_and_nonnull<CallBase>(V)) setExtent(O, V);
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
  size_t repNotSite = 0, multiSiteClasses = 0;
  std::map<std::string, size_t> repKinds; // what represents a class that is not its site
  for (uint32_t n = 0; n < G; n++) {
    if (!inGraph[n] || getCanonicalNode(n) != n) continue;
    members.clear();
    collectCanonicalMembers(n, members);
    if (members.empty()) members.push_back(n);
    for (NodeIndex m : members) {
      const bool special = m == NF.getUniversalPtrNode() ||
                           m == NF.getUniversalObjNode();
      if (!special && !isOrigin(m)) continue;
      // An allocation's object is named by its own site, whatever node
      // represents its dedup class: one object per site.
      auto sit = AllocSiteNodes.find(m);
      if (!special && sit != AllocSiteNodes.end()) {
        assert(!sit->second.empty() && "an allocation class without a site");
        if (sit->second.size() > 1) multiSiteClasses++;
        for (NodeIndex own : sit->second) {
          if (own != m) {
            repNotSite++;
            const Value *RV = NF.getValueForNode(m);
            repKinds[!RV                                ? "no value"
                     : isa<Argument>(RV)                ? "formal"
                     : isa<CastInst>(RV)                ? "cast"
                     : isa<GetElementPtrInst>(RV)       ? "GEP"
                     : isa<PHINode>(RV) || isa<SelectInst>(RV) ? "phi/select"
                     : isa<LoadInst>(RV)                ? "load"
                     : isa<CallBase>(RV)                ? "call"
                                                        : "other"]++;
          }
          CG_DEBUG("Cells: allocation site #" << own << " under representative #" << m << " (class #" << n
                   << ", " << members.size() << " members): " << [&] {
                     std::string t;
                     raw_string_ostream os(t);
                     for (NodeIndex x : {own, m})
                       if (const Value *XV = NF.getValueForNode(x)) {
                         if (const auto *I = dyn_cast<Instruction>(XV)) os << I->getFunction()->getName() << ":";
                         XV->print(os);
                         os << " | ";
                       }
                     return os.str().substr(0, 400);
                   }() << "\n");
          add(n, cellAt(newObj(own, NF.getValueForNode(own)), 0));
          objSeeds++;
        }
        continue;
      }
      assert((special || !AllocSites.count(m)) && "an allocation site without its own node");
      const uint32_t o = newObj(m, NF.getValueForNode(m));
      add(n, cellAt(o, 0));
      objSeeds++;
    }
  }
  CG_LOG("Cells: allocation sites: " << repNotSite << " seeded by their own node under a class representative "
         << "that is not the site (" << [&] {
              std::string k;
              for (auto &[w, c] : repKinds) k += (k.empty() ? "" : ", ") + w + " " + std::to_string(c);
              return k.empty() ? std::string("none") : k;
            }() << "), " << multiSiteClasses << " classes with more than one site\n");
  mintCause = "other";

  // A variable index (stride s) from byte x of object o stays in the
  // innermost array holding x, arrays being one element: the same cell
  // when s is a multiple of the element, else the element's positions
  // congruent to x modulo gcd(s, element). An unlabeled object is an array
  // of s-byte elements (stride 1: bytes). An index from an address in no
  // array is undefined behavior: counted, the address stays.
  size_t indexInBoundedArray = 0; // a variable index into a declared array field within T: within its bound
  size_t segArrayOtherStride = 0; // another stride over a segment array: data after it, folded
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
    // Not from inside a declared array field that ends strictly within T:
    // an index there stays in that field (past its bound is a forged
    // pointer, rule (a): counted, assumed within the bound). The link
    // stays for the implicit array of T (no array holds the address), an
    // array that ends at T's end (trailing or flexible: the index runs
    // on), and a byte index.
    const bool tailIndex = objs[o].tail && !objs[o].repeats;
    Obj &O = objs[o];
    const int64_t pos = ((x % O.size) + O.size) % O.size;
    int64_t b = 0, e = 0;
    const bool inArray = innermostArray(O.layout, pos, DL, b, e);
    if (tailIndex) {
      int64_t lo = 0, hi = 0, esz = 0;
      const bool runsOn = s == 1 || !inArray ||
                          !innermostArraySpan(O.layout, pos, DL, lo, hi, esz) || hi >= O.size;
      if (runsOn) {
        // The unlabeled remainder: past the labeled segments (an index from
        // T landing in a segment of another label is assumed within bound).
        uint32_t t = tailOf(o);
        while (objs[t].layout && objs[t].fwd == UINT32_MAX && objs[t].tail && !objs[t].repeats) {
          indexInBoundedArray++;
          t = tailOf(t);
        }
        if (objs[t].layout && objs[t].fwd == UINT32_MAX) indexInBoundedArray++; // the last segment: no remainder
        else {
          tailIndexAny++;
          if (!objs[t].layout) tailLinkedUnlabeled.insert(t);
          out.push_back(anyOf(t));
        }
      } else
        indexInBoundedArray++;
    }
    if (!inArray && O.segArray && s % O.size != 0) {
      // Another stride over a segment array of T (`(VdbeCursor **)&aMem[n]`:
      // the data after the array at a variable offset): it may land on any
      // element offset its stride reaches, folded into T's element cells
      // (rule (b), flow kept; counted).
      segArrayOtherStride++;
      const int64_t g = std::gcd(s, O.size);
      for (int64_t j = pos % g; j < O.size; j += g) out.push_back(cellAtArr(o, j));
      return;
    }
    if (!inArray) {
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
    assert(li < lazyLabels.size() && o < objs.size() && "stepOne: a label or object out of range");
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
          if (CFLCellOneLabelMax <= 1 || !CFLCellOneLabelObject.empty()) // also collect mode, filtered
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
      if (L.ty && L.stride == 0 && C.off == 0 &&
          !structStartsAt(O.layout, C.off, stripStructNameSuffix(L.ty->getName()), DL, L.ty))
        tryWiden(C.obj, L.ty); // row 2: a container of the label at offset 0
      if (L.ty && L.stride == 0 &&
          !structStartsAt(O.layout, C.off, stripStructNameSuffix(L.ty->getName()), DL, L.ty)) {
        if (!ruleB && curStepFact != UINT32_MAX)
          firstRuleB = {curStepNode, C.obj, L.ty};
        ruleB++;
        if (O.declScalar) {
          scalarStructSteps++;
          scalarStructWrites += L.writes;
        }
        ruleBPairs[{O.label, stripStructNameSuffix(L.ty->getName()).str()}]++;
        // One label per pointer: a pointer used as L.ty holding an object
        // of another struct is the conflict itself.
        if (CFLCellOneLabel && curStepFact != UINT32_MAX) {
          if (CFLCellOneLabelMax <= 1 || !CFLCellOneLabelObject.empty()) // also collect mode, filtered
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
    } else if (const auto *A = dyn_cast_or_null<Argument>(V)) {
      // An object originating at a formal: an environment (outside) object.
      where = "arg#" + std::to_string(A->getArgNo()) + " of " + A->getParent()->getName().str() + " (outside)";
    } else if (V && V->hasName()) {
      where = V->getName().str();
    } else if (V) {
      // Never an empty name: an unnamed global prints its slot and type,
      // a constant expression itself.
      std::string t;
      raw_string_ostream os(t);
      const auto *GV = dyn_cast<GlobalValue>(V);
      V->printAsOperand(os, false, GV ? GV->getParent() : nullptr);
      if (const auto *G = dyn_cast<GlobalVariable>(V)) {
        os << " unnamed global: ";
        G->getValueType()->print(os);
      }
      where = os.str().substr(0, 160);
    }
    where += " #" + std::to_string(O.origin);
    if (O.rowOwner != UINT32_MAX) where = "element of the owner obj#" + std::to_string(O.rowOwner) + " at " + where;
    return where + (O.parentObj != UINT32_MAX ? " tail@" + std::to_string(O.base) : "") +
           " [" + (O.layout ? (O.ident.empty() ? O.label : O.ident + " as " + O.label) : std::string("unlabeled")) +
           (O.repeats ? " array" : "") + "]";
  };
  describeFn = describe;
  // A fact matches --cfl-cell-one-label-object when an object it holds
  // does (its description contains the pattern).
  oneLabelMatch = [&](uint32_t f) {
    for (auto [o, e] : std::vector<Member>(memb[findFact(f)])) {
      (void)e;
      if (describe(objs[o]).find(CFLCellOneLabelObject) != std::string::npos) return true;
    }
    return false;
  };
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
    assert(si < recvSites.size() && level < recvSites[si].lis.size() && g < cells.size() &&
           "linkLevel: a site, level or cell out of range");
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
    assert(K.si < recvSites.size() && "dispatch: a site out of range");
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
  boost::unordered_flat_map<uint64_t, Why> heldWhy; // (guard, fact) -> the cause it arrived by
  // A held fact admitted (or released): with the cause it arrived by
  // (first-arrival records only).
  auto admitHeld = [&](uint32_t gi, uint32_t f) {
    const Why saved = curWhy;
    if (trackWhy)
      if (auto it = heldWhy.find((uint64_t)gi << 32 | f); it != heldWhy.end()) curWhy = it->second;
    admitting = true;
    add(guards[gi].node, f);
    admitting = false;
    curWhy = saved;
  };
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
  ValueMap<const Function *, ModSet> modOf;
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
    if (!ST || !ST->hasName() || isAnonStruct(ST)) return false; // anonymous: names nothing
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
        if (ST->hasName() && !isAnonStruct(ST)) key.first = stripStructNameSuffix(ST->getName()).str();
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
        modOf.update(&F, [&](ModSet &MS) {
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
        });
      }
    // Every key first, so the fixpoint only reads and updates in place
    // (ValueMap: no reference survives an insert).
    for (auto &[F, cs] : calls) {
      modOf.update(F, [](ModSet &) {});
      for (const Function *C : cs) modOf.update(C, [](ModSet &) {});
    }
    for (bool grew = true; grew;) {
      grew = false;
      for (auto &[F, cs] : calls)
        modOf.update(F, [&](ModSet &MS) {
          for (const Function *C : cs) {
            if (C == F) continue; // its own set: already in MS
            modOf.with(C, [&](const ModSet &CM) {
              if (CM.all && !MS.all) { MS.all = true; grew = true; }
              for (const auto &k : CM.slots)
                if (MS.slots.insert(k).second) grew = true;
            });
          }
        });
    }
  };
  auto mayWrite = [&](const Function *F, const std::pair<std::string, int64_t> &slot) {
    bool any = false;
    modOf.with(F, [&](const ModSet &MS) {
      if (MS.all) { any = true; return; }
      for (const auto &w : MS.slots)
        if (slotMatches(w, slot)) { any = true; return; }
    });
    return any;
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
          for (uint32_t f : Gd.held) admitHeld((uint32_t)(&Gd - guards.data()), f);
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
            // At offset 0 there is no step: level 1 is the pointer itself
            // (an empty chain), never the UINT32_MAX "no label yet" sentinel.
            RecvSite PS{nullptr, 0, n, n, {{}, li == UINT32_MAX ? std::vector<uint32_t>{} : std::vector<uint32_t>{li}}};
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
    assert(gi < guards.size() && f < cells.size() && "guardHold: a guard or fact out of range");
    Guard &Gd = guards[gi];
    if (trackWhy) heldWhy.try_emplace((uint64_t)gi << 32 | f, curWhy); // its cause, for the admission
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
      for (uint32_t f : Gd.held) admitHeld(gi, f);
    }
  };
  guardAdmit = [&](uint32_t gi, uint32_t f, uint32_t F) {
    Guard &Gd = guards[gi];
    if (objs[cells[F].obj].fn != Gd.F) return;
    if (!guardAdmitted.insert((uint64_t)gi << 32 | f).second) return;
    admitHeld(gi, f);
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
  // A container row at an owner fact (plan 3.55): the owner's element cell
  // (owner object, offset, container), its own node, outside every content
  // cell, so no other access reads or writes it; an insert's element flows
  // in, a lookup's result reads it.
  boost::unordered_flat_map<std::tuple<uint32_t, int64_t, uint32_t>, uint32_t,
                            boost::hash<std::tuple<uint32_t, int64_t, uint32_t>>>
      rowCell;
  size_t rowFacts = 0, rowSkipped = 0;
  // Copies, not references: minting cells and nodes grows cells and memb.
  auto linkRow = [&](uint32_t li, uint32_t f) {
    const CellKind kind = cells[findFact(f)].kind;
    if (kind != CellKind::Off && kind != CellKind::Any) { rowSkipped++; return; }
    const RowLink &L = rowLinks[li];
    const std::vector<Member> ms = memb[findFact(f)];
    for (auto [o, e] : ms) {
      const int64_t off = kind == CellKind::Any ? INT64_MIN : decOff(e);
      auto [it, ins] = rowCell.try_emplace(std::make_tuple(o, off, L.name), 0);
      if (ins) it->second = newNode();
      rowFacts++;
      if (L.in != AndersNodeFactory::InvalidIndex) addEdge(canon(L.in), it->second);
      if (L.out != AndersNodeFactory::InvalidIndex) addEdge(it->second, canon(L.out));
    }
  };
  // The element mint: (owner object, site) -> the row object; per
  // container, the row objects minted, and the (body element, row object)
  // pairs whose inherited fields are linked.
  std::map<std::pair<uint32_t, const Value *>, uint32_t> mintedObj;
  std::vector<std::vector<uint32_t>> mintedOf(containerElemSources.size());
  boost::unordered_flat_set<uint64_t> inherited;
  size_t inheritLinks = 0, rowsLaidOut = 0, rowsByOwnerCtor = 0, rowsByLargestOfSeveral = 0, rowsByGlobalLargest = 0;
  // Row object R inherits body element C's body-written fields (C -> R).
  auto inheritFields = [&](uint32_t C, uint32_t R, uint32_t ci) {
    if (C == R || objs[C].rowOwner != UINT32_MAX || objs[C].fn || !inherited.insert((uint64_t)C << 32 | R).second)
      return;
    for (int64_t w : containerInherit[ci]) {
      // A row object laid out by its owner's constructor has no bytes past
      // that element: offsets the body writes on larger elements of other
      // owners are not its fields.
      if (objs[R].rowLaidOut && w >= objs[R].size) continue;
      // A body write at no constant offset rejects a minting container
      // (Containers.cc): never here.
      assert(w >= 0 && "an inherited field at no constant offset");
      // Through forwards and trailing objects on both sides.
      const auto [co, cw] = locate(C, w);
      const auto [ro, rw] = locate(R, w);
      const auto a = contentOf(co, contentKey(objs[co], cw)), b = contentOf(ro, contentKey(objs[ro], rw));
      addEdge(a.second, b.first);
      inheritLinks++;
    }
  };
  std::function<void(uint32_t, uint32_t)> linkMint = [&](uint32_t li, uint32_t f) {
    const CellKind kind = cells[findFact(f)].kind;
    if (kind != CellKind::Off && kind != CellKind::Any) { rowSkipped++; return; }
    const MintLink &L = mintLinks[li];
    const std::vector<Member> ms = memb[findFact(f)];
    for (auto [o, e] : ms) {
      auto [it, ins] = mintedObj.try_emplace(std::make_pair(o, L.site), 0);
      if (ins) {
        const NodeIndex sn = NF.getValueNodeFor(L.site);
        it->second = newObj(sn == AndersNodeFactory::InvalidIndex ? L.out : sn, nullptr);
        objs[it->second].rowOwner = o;
        // Its layout (Fable 2026-10-14): its OWNER's constructor's element
        // (the constants fed into o's code field at the feeding sites whose
        // owner value holds o); several: the largest of them; none known
        // yet: the container's largest. A write past it asserts (a wrong
        // pairing), it never falls back to a tail.
        StructType *RT = nullptr;
        if (L.cont < containerOwnerCtors.size()) {
          std::set<const Function *> ctors;
          for (const auto &[V, fs] : containerOwnerCtors[L.cont]) {
            const NodeIndex vn = getRepNodeForValue(V);
            if (vn == AndersNodeFactory::InvalidIndex) continue;
            bool holds = false;
            pts[find(canon(vn))].forEach([&](uint32_t g) {
              for (auto [mo, me] : memb[findFact(g)])
                holds |= mo == o && me == e; // the same owner: object and offset (an object may embed several)
            });
            if (holds) ctors.insert(fs.begin(), fs.end());
          }
          for (const Function *Fc : ctors)
            if (auto tit = containerCtorType[L.cont].find(Fc); tit != containerCtorType[L.cont].end() && tit->second)
              if (!RT || DL.getTypeAllocSize(tit->second) > DL.getTypeAllocSize(RT)) RT = tit->second;
          if (RT) (ctors.size() == 1 ? rowsByOwnerCtor : rowsByLargestOfSeveral)++;
          std::string cs;
          for (const Function *Fc : ctors) cs += (cs.empty() ? "" : " ") + Fc->getName().str();
          CG_LOG("Cells: row object at " << nodeDescFn(canon(L.out)).substr(0, 100) << " of owner "
                 << describeFn(objs[o]).substr(0, 100) << ": constructors {" << cs << "}"
                 << (RT ? " -> " + typeLabel(RT) : std::string(" -> none known")) << "\n");
        }
        if (!RT && L.cont < containerElemType.size() && containerElemType[L.cont]) {
          RT = containerElemType[L.cont];
          rowsByGlobalLargest++;
        }
        if (RT) {
          Obj &R = objs[it->second];
          R.layout = RT;
          R.size = (int64_t)DL.getTypeAllocSize(R.layout);
          R.label = typeLabel(R.layout);
          R.repeats = false;
          R.rowLaidOut = true;
          rowsLaidOut++;
        }
        mintedOf[L.cont].push_back(it->second);
        // Its inherited fields from every body element already known.
        const uint32_t R = it->second;
        for (const Value *E : containerElemSources[L.cont])
          if (const NodeIndex n = getRepNodeForValue(E); n != AndersNodeFactory::InvalidIndex) {
            std::vector<uint32_t> gs;
            pts[find(canon(n))].forEach([&](uint32_t g) { gs.push_back(g); });
            for (uint32_t g : gs) inheritFields(cells[g].obj, R, L.cont);
          }
      }
      const uint32_t fr = cellAt(it->second, 0);
      add(find(canon(L.out)), fr);
      if (L.name != UINT32_MAX) {
        const int64_t off = kind == CellKind::Any ? INT64_MIN : decOff(e);
        auto [rc, rins] = rowCell.try_emplace(std::make_tuple(o, off, L.name), 0);
        if (rins) rc->second = newNode();
        add(find(rc->second), fr);
      }
      // Storage visibility and the body's own writes: the row object is
      // one of the body's elements.
      for (const Value *E : containerElemSources[L.cont])
        if (const NodeIndex n = getRepNodeForValue(E); n != AndersNodeFactory::InvalidIndex) add(find(canon(n)), fr);
    }
  };
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
  // A constant integer is not a carrier (Fable 2026-10-13): the shared
  // constant-int node ends the solve (or a census stop) without a fact; a
  // ptrtoint constant is a value node of its object (NodeFactory).
  auto checkConstInt = [&]() {
    const uint32_t k4 = find(NF.getConstantIntNode());
    if (pts[k4].count()) {
      size_t shown = 0;
      pts[k4].forEach([&](uint32_t f) {
        if (shown++ < 4) CG_LOG("Cells: the constant-int node holds " << factDescP(f) << "\n");
      });
      assert(false && "the constant-int node holds a fact: a nameless hub every integer constant reads");
    }
    size_t atStore = 0, atPhi = 0, atCall = 0, atOther = 0;
    for (const Constant *K : NF.ptrToIntConstants)
      for (const User *U : K->users()) {
        if (const auto *SI = dyn_cast<StoreInst>(U); SI && SI->getValueOperand() == K) atStore++;
        else if (isa<PHINode>(U) || isa<SelectInst>(U)) atPhi++;
        else if (isa<CallBase>(U) || isa<ReturnInst>(U)) atCall++;
        else if (isa<Instruction>(U)) atOther++;
      }
    CG_LOG("Cells: " << NF.ptrToIntConstants.size()
           << " integer constants derived from one pointer given their pointer's node (uses: " << atStore
           << " stored, " << atPhi << " joined, " << atCall << " passed or returned, " << atOther << " other); "
           << NF.absoluteAddresses.size() << " inttoptr constants of a pure integer (a fixed address: null); "
           << "the constant-int node holds no fact\n");
  };
  boost::unordered_flat_map<NodeIndex, std::pair<NodeIndex, uint32_t>> keyedPtrOf;
  // A hub's pointer the way the solver knows it: a dereference edge whose
  // target's representative is the hub (the factory parent is the original
  // node's; a representative may have none). Built on first use.
  boost::unordered_flat_map<NodeIndex, NodeIndex> hubPtrOf;
  auto hubPointer = [&](NodeIndex h) -> NodeIndex {
    if (hubPtrOf.empty())
      for (const GraphEdge &E : Graph.edges())
        if (E.kind == EdgeKind::Deref) hubPtrOf.emplace(canon(E.to), canon(E.from));
    auto it = hubPtrOf.find(h);
    return it == hubPtrOf.end() ? AndersNodeFactory::InvalidIndex : it->second;
  };
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
    } else if (m <= NF.getConstantIntNode()) {
      // The factory's special nodes, by name.
      static const char *special[] = {"the universal pointer", "the universal object", "the null pointer",
                                      "the null object", "the constant-int node"};
      k = special[m];
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
      if (par == AndersNodeFactory::InvalidIndex && (par = hubPointer(m)) != AndersNodeFactory::InvalidIndex)
        key = " (a representative: its pointer by the dereference edge)";
      if (par == AndersNodeFactory::InvalidIndex) {
        // An unexpected node: name it before the assertion.
        bool keyed = false;
        for (const auto &[pk, d] : keyedDerefOf) keyed |= d == m;
        const Value *MV = NF.getValueForNode(m);
        std::string mv;
        if (MV) { raw_string_ostream os(mv); MV->print(os); }
        errs() << "Cells: a hub without a pointer: node #" << m << " (dereference " << NF.isDereferenceNode(m)
               << ", object " << NF.isObjectNode(m) << ", value " << NF.isValueNode(m) << ", keyed " << keyed
               << ", named shadow " << isShadowCell(m) << ", rep #" << find(m) << ", value " << mv.substr(0, 160)
               << ")\n";
        // Its creator shows in its edges: the first ones in and out.
        static const char *kindName[] = {"copy", "deref", "field", "fieldany"};
        size_t shown = 0;
        for (const GraphEdge &E : Graph.edges()) {
          if (E.to != m && E.from != m) continue;
          const NodeIndex o = E.to == m ? E.from : E.to;
          std::string ov;
          if (const Value *OV = NF.getValueForNode(o)) {
            raw_string_ostream os(ov);
            if (const auto *I = dyn_cast<Instruction>(OV)) os << I->getFunction()->getName() << ": ";
            OV->print(os);
          }
          errs() << "Cells:   " << (E.to == m ? "in " : "out ") << kindName[(int)E.kind] << " "
                 << (E.to == m ? "from" : "to") << " #" << o << " (dereference " << NF.isDereferenceNode(o)
                 << ", object " << NF.isObjectNode(o) << ", value " << NF.isValueNode(o) << ", parent #"
                 << (int64_t)(NF.isDereferenceNode(o) ? (int64_t)NF.getDerefParent(o) : -1) << ") "
                 << ov.substr(0, 160) << "\n";
          if (++shown >= 8) break;
        }
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
  // --cfl-cell-why-at=NODE: why the nodes NODE describes hold the object;
  // run at every report (a one-label stop, a census-at or soup-cap stop,
  // the fixpoint), from reportDefects.
  auto whyAtReport = [&]() {
    if (recordWhy && !CFLCellWhyAt.empty()) {
      std::set<uint32_t> asked;
      boost::unordered_flat_map<uint32_t, uint32_t> classSize;
      for (uint32_t m = 0; m < numNodes; m++) classSize[find(m)]++;
      // Only nodes whose class holds a fact can hold the object (and only
      // those are described: an orphan dereference node has no pointer).
      for (uint32_t m = 0; m < numNodes; m++)
        if (pts[find(m)].count() && nodeDesc(m).find(CFLCellWhyAt) != std::string::npos &&
            asked.insert(find(m)).second) {
          CG_LOG("Cells: why-at " << nodeDesc(m) << ": class " << find(m) << " of "
                 << classSize[find(m)] << " nodes, represented by " << nodeDesc(find(m)) << "\n");
          for (StringRef alt : llvm::split(StringRef(CFLCellWhy.getValue()), '|'))
            if (!alt.empty()) explainWhy(find(m), alt.str());
        }
      if (asked.empty()) CG_LOG("Cells: no node matches '" << CFLCellWhyAt << "'\n");
    }
  };
  // Orphan dereference nodes (Fable 2026-10-15): a dereference node with
  // no parent pointer, no keyed pointer and no dereference edge should not
  // exist (nodeDesc asserts on one); counted and listed, with the value
  // the factory recorded for it.
  auto orphanDerefCensus = [&]() {
    boost::unordered_flat_set<uint32_t> keyedDerefs;
    for (const auto &[pk, d] : keyedDerefOf) keyedDerefs.insert(d);
    std::vector<uint32_t> orphans;
    for (uint32_t m = 0; m < G; m++) // graph nodes (cell nodes are the solver's own)
      if (NF.isDereferenceNode(m) && NF.getDerefParent(m) == AndersNodeFactory::InvalidIndex &&
          !keyedDerefs.count(m) && hubPointer(m) == AndersNodeFactory::InvalidIndex)
        orphans.push_back(m);
    CG_LOG("Cells: orphan dereference nodes: " << orphans.size() << "\n");
    for (size_t i = 0; i < orphans.size() && i < 10; i++) {
      std::string v = "none";
      if (const Value *MV = NF.getValueForNode(orphans[i])) {
        v.clear();
        raw_string_ostream os(v);
        if (const auto *I = dyn_cast<Instruction>(MV)) os << I->getFunction()->getName() << ": ";
        MV->print(os);
      }
      CG_LOG("Cells:   orphan dereference node #" << orphans[i] << ", value " << v.substr(0, 200) << "\n");
    }
  };
  auto reportDefects = [&]() {
    whyAtReport();
    orphanDerefCensus();
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
    errs() << "Cells: " << collectDup << " repeats of a reported conflict skipped (same node, kind and facts)\n";
    errs() << "Cells: " << conflicts << " name conflicts; meets elsewhere:" << o
           << "\nCLONE-CANDIDATES: " << c << "\n";
    errs() << "Cells: stopped at " << pops << " pops (one-label stop, " << conflicts << " conflicts)\n";
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
    errs() << "Cells: stopped at " << pops << " pops (one-label stop, 1 conflict)\n";
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
  // Also for the --cfl-cell-why objects (each '|' alternative), with the
  // pop: where a wrong-target pointer labeled the object first.
  noteLayoutCause = [&](uint32_t o, StructType *S) {
    const std::string d = describe(objs[o]);
    bool want = !CFLCellTraceObj.empty() && d.find(CFLCellTraceObj) != std::string::npos;
    for (StringRef alt : llvm::split(StringRef(CFLCellWhy.getValue()), '|'))
      if (!want && !alt.empty() && d.find(alt.str()) != std::string::npos) want = true;
    if (!want) return;
    CG_LOG("Cells: LAYOUT " << d << " learned " << typeLabel(S) << " at pop " << pops << " ("
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
        if (CFLCellOneLabel && (CFLCellOneLabelMax <= 1 || !CFLCellOneLabelObject.empty()) &&
            curCopyDst != UINT32_MAX) // also collect mode, filtered
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

  // ---- The weld census (--cfl-cell-weld-census, Part C input) ----
  // A weld: the first fact of a second label at a value node (an IR value,
  // a formal, a return) that held one label; unlabeled storage is a label
  // of its own. Its join is the cause that delivered that fact. A fact of
  // the second label arriving from a node where it was already foreign
  // descends from that weld (its mass); memory and hub nodes only pass the
  // descent on. Welds are numbered in arrival order: the first ones are the
  // causes, the later ones mostly their consequences.
  struct Weld { uint32_t node, pop, anchor, fact, src, srcFact; uint8_t kind; size_t mass = 0; std::string ctx; };
  std::vector<Weld> welds;
  boost::unordered_flat_map<uint32_t, uint32_t> weldAnchor, weldAt;
  boost::unordered_flat_map<uint64_t, uint32_t> weldForeign; // (node, fact) -> weld
  auto isValueNode = [&](uint32_t n) {
    if (n >= G || NF.isDereferenceNode(n) || NF.isObjectNode(n)) return false;
    const Value *V = NF.getValueForNode(n);
    return V && (isa<Instruction>(V) || isa<Argument>(V) || NF.isReturnNode(n) || NF.isVarargNode(n));
  };
  if (CFLCellSoupProfile && CFLCellWeldCensus) {
    auto soupPrev = soupArrive;
    soupArrive = [&, soupPrev](uint32_t n, uint32_t f) {
      if (soupPrev) soupPrev(n, f);
      if (soupStop) return;
      f = findFact(f);
      if (cells[f].kind != CellKind::Off && cells[f].kind != CellKind::Any) return;
      auto [ait, ins] = weldAnchor.try_emplace(n, f);
      if (ins) return;
      const uint32_t a = findFact(ait->second);
      if (a == f) return;
      // Byte storage (no label, or a char/byte array) is one label.
      auto bytes = [&](uint32_t c) { // the cell's leaf: a char member of a struct is bytes too
        Type *L = objs[cells[c].obj].layout;
        if (!L) return true;
        Type *T = leafAt(L, foldIn(L, cells[c].off, DL), DL);
        while (T && T->isArrayTy()) T = T->getArrayElementType();
        return T && T->isIntegerTy(8);
      };
      const bool la = !bytes(a), lf = !bytes(f);
      if (!la && !lf) return; // bytes meet bytes: one label
      if (la && lf) {
        const uint64_t key = (uint64_t)a << 32 | f;
        auto cit = compatMemo.find(key);
        const int c = cit != compatMemo.end() ? cit->second : namesCompatible(a, f);
        if (cit == compatMemo.end()) compatMemo.emplace(key, c);
        if (c != 0) return;
      }
      const Why w = curWhy;
      const bool hasSrc = w.node < numNodes && w.fact < cells.size() &&
                          (w.kind == W_EDGE || w.kind == W_STEP || w.kind == W_WALK ||
                           w.kind == W_ANY || w.kind == W_DISPATCH);
      uint32_t wi = UINT32_MAX;
      if (hasSrc)
        if (auto it = weldForeign.find((uint64_t)find(w.node) << 32 | findFact(w.fact)); it != weldForeign.end())
          wi = it->second;
      if (wi == UINT32_MAX) {
        if (!isValueNode(n)) return;
        auto [wit, wins] = weldAt.try_emplace(n, (uint32_t)welds.size());
        if (wins)
          welds.push_back({n, (uint32_t)whyClock, a, f, hasSrc ? find(w.node) : UINT32_MAX,
                           hasSrc ? findFact(w.fact) : UINT32_MAX, (uint8_t)w.kind, 0,
                           hasSrc ? std::string() : mintCause}); // the replay's cause (merge, refold, ...)
        wi = wit->second;
      }
      if (weldForeign.emplace((uint64_t)n << 32 | f, wi).second) welds[wi].mass++;
    };
  }

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
    uint32_t anyObj = UINT32_MAX; // class 6 "any-offset write of X": X
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
  ValueMap<uint64_t, uint32_t> leakProv;
  // A hub that feeds only store collectors moves its facts (*q = *p, a
  // pointer-sized move) instead of reading them: it and the collectors
  // pass a byte cell's facts on, and the exit is where the move lands.
  boost::unordered_flat_set<uint32_t> leakTransit;
  std::vector<LeakSite> leakSites;
  std::map<std::string, uint32_t> leakSiteIdx;
  ValueMap<uint64_t, uint32_t> leakTag; // (node, fact) -> leak
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
      else par = hubPointer(h);
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
  // The IR store by which fact f entered through store collector a (of hub
  // h): one of the collector's stores whose value holds f (else its first,
  // held = false), else a store through the hub's pointer, else one of the
  // stored value's stores into the hub. Vp, Vv: the hub's pointer and the
  // stored value that holds f.
  auto leakStoreAt = [&](uint32_t a, uint32_t h, uint32_t f, const Value *&Vp, const Value *&Vv,
                         bool &held) -> const StoreInst * {
    NodeIndex par;
    Vp = leakHubPtr(h, par);
    auto holds = [&](const Value *V) {
      const uint32_t vn = leakNodeOf(V);
      return vn != UINT32_MAX && pts[vn].test(f);
    };
    const StoreInst *SI = nullptr;
    held = true;
    if (auto sit = leakCollStores.find(a); sit != leakCollStores.end()) {
      for (const StoreInst *S : sit->second)
        if (holds(S->getValueOperand())) { SI = S; break; }
      if (!SI && !sit->second.empty()) { SI = sit->second.front(); held = false; }
    }
    if (!SI && Vp)
      for (const User *U : Vp->users())
        if (const auto *S = dyn_cast<StoreInst>(U))
          if (S->getPointerOperand() == Vp && holds(S->getValueOperand())) { SI = S; break; }
    Vv = nullptr;
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
    return SI;
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
      const Value *Vp = nullptr, *Vv = nullptr;
      bool held = true;
      const StoreInst *SI = leakStoreAt(a, hit->second, f, Vp, Vv, held);
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
      if (sc == kLeakAny) {
        const uint32_t id = leakSiteOf(6, "any-offset write of " + describe(objs[so]), into, "");
        leakSites[id].anyObj = so;
        return id;
      }
      return leakSiteOf(6, "cell edge from " + cellName(so, sc) + " of " + describe(objs[so]), into,
                        "a byte copy merged away, or a union or tag-flip edge");
    }
    if (a < G && NF.isVarargNode(a))
      return leakSiteOf(5, "vararg pool " + nodeDesc(a).substr(0, 100), into, "");
    return leakSiteOf(6, "edge from " + nodeDesc(a).substr(0, 140), into, "");
  };
  // The feeder of each non-char fact entering a typed object's any-offset
  // cell (its write side): an IR store (its address), or a tagged cause
  // (kind in bits 40..47, a node or copy in the low 32 bits). A class-6
  // "any-offset write of X" leak relays what X's feeders wrote (plan, slot
  // census ruling 1): its rank goes to them.
  boost::unordered_flat_map<uint64_t, uint64_t> leakAnyFeed; // (object << 32 | fact) -> feeder
  auto leakFeedKey = [](uint64_t kind, uint64_t sub, uint32_t x) {
    return 1ull << 63 | kind << 40 | sub << 32 | x;
  };
  if (CFLCellLeakCensus) {
    leakArrive = [&](uint32_t n, uint32_t f) {
      if (soupStop) return;
      f = findFact(f);
      const Why w = curWhy;
      const bool hasSrc = w.node < numNodes && w.fact < cells.size() &&
                          (w.kind == W_EDGE || w.kind == W_STEP || w.kind == W_WALK ||
                           w.kind == W_ANY || w.kind == W_DISPATCH);
      if (auto ait = leakCellOf.find(n); ait != leakCellOf.end() && ait->second.second == kLeakAny) {
        const uint32_t o = ait->second.first;
        if (objs[o].layout && !objs[o].fn && objs[o].any != UINT32_MAX && find(cells[objs[o].any].store) == n &&
            !leakByteCell(o, kLeakAny) && leakFactKind(f)) {
          const uint64_t k = (uint64_t)o << 32 | f;
          if (!leakAnyFeed.count(k)) {
            uint64_t key;
            if (hasSrc && w.kind == W_EDGE) {
              const uint32_t a = find(w.node);
              if (auto hit = leakCollHub.find(a); hit != leakCollHub.end()) {
                const Value *Vp = nullptr, *Vv = nullptr;
                bool held = true;
                const StoreInst *SI = leakStoreAt(a, hit->second, f, Vp, Vv, held);
                key = SI ? (uint64_t)(uintptr_t)SI : leakFeedKey(1, 0, a);
              } else if (auto cit = leakCopyEdge.find((uint64_t)a << 32 | n); cit != leakCopyEdge.end()) {
                key = leakFeedKey(2, 0, cit->second);
              } else {
                key = leakFeedKey(leakCellOf.count(a) ? 3 : 4, 0, a);
              }
            } else {
              key = leakFeedKey(5, w.kind, hasSrc ? find(w.node) : UINT32_MAX);
            }
            leakAnyFeed.emplace(k, key);
          }
        }
      }
      // An edge out of a byte cell into a node that is not one: an exit.
      auto exits = [&]() {
        return hasSrc && w.kind == W_EDGE && !leakIsByte(n) &&
               (leakIsByte(find(w.node)) || leakTransit.count(find(w.node)));
      };
      if (hasSrc) {
        if (const auto tag = leakTag.get((uint64_t)find(w.node) << 32 | findFact(w.fact))) {
          leakTag.insert((uint64_t)n << 32 | f, *tag);
          if (leakFactKind(f) && exits()) leakExit(find(w.node), n, *tag);
          return;
        }
      }
      if (!leakFactKind(f)) return;
      if (!leakIsByte(n)) {
        if (exits()) leakExit(find(w.node), n, UINT32_MAX);
        if (auto it = leakCellOf.find(n); it != leakCellOf.end()) {
          const Obj &O = objs[it->second.first];
          if (!O.layout && !O.fn)
            leakProv.insert((uint64_t)n << 32 | f, leakClassify(n, f, w, hasSrc));
        }
        return;
      }
      const uint32_t s = leakClassify(n, f, w, hasSrc);
      leakSites[s].born++;
      leakTag.insert((uint64_t)n << 32 | f, s);
    };
    leakMerge = [&](uint32_t r, uint32_t m) {
      if (leakIsByte(m)) leakMergedByte.insert(r);
      pts[m].forEach([&](uint32_t f) {
        if (const auto tag = leakTag.get((uint64_t)m << 32 | f)) leakTag.insert((uint64_t)r << 32 | f, *tag);
        if (const auto prov = leakProv.get((uint64_t)m << 32 | f)) leakProv.insert((uint64_t)r << 32 | f, *prov);
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
            auto prov = leakProv.get(k);
            if (!prov) prov = leakProv.get((uint64_t)R << 32 | f0);
            if (!prov) return;
            leakTag.insert(k, *prov);
            leakSites[*prov].born++;
          });
        }
      }
    };
  }

  // ---- The slot census (--cfl-cell-slot-census) ----
  // A content cell's slot: what its object's layout has at the cell's
  // offset. A pointer, a pointer-width integer (where the int-store rule
  // admits a pointer-carrying integer), unlabeled bytes, the any-offset
  // cell and a union's bytes can hold a pointer; a char or other integer
  // member, a float or other scalar, the interior of a scalar and an
  // offset past the layout cannot. Report only: at the stop, the facts in
  // cells by slot, and the cells without a pointer-width slot by facts,
  // with the sites whose arrivals fed them (a store's site, its pointer's
  // shape, and the stored facts' origin kinds).
  // A va_list object's cells hold the engine's vararg pool (va_start
  // writes the creator's arguments there, LoweredVAArg reads them): an
  // engine pool cell, reported on its own line, out of the no-slot mass.
  enum SlotKind : uint8_t {
    SL_PTR, SL_INTPTR, SL_BYTES, SL_ANY, SL_UNION, // can hold a pointer
    SL_VAPOOL,                                     // the engine's pool
    SL_CHAR, SL_INT, SL_OTHER, SL_INTERIOR, SL_BEYOND, SL_N
  };
  static const char *const slotNames[SL_N] = {
      "pointer member", "pointer-width integer", "unlabeled bytes", "any-offset cell", "union bytes",
      "engine pool cell (a va_list's arguments)",
      "char member or char object", "other integer member", "float or other scalar member",
      "interior of a scalar member", "past the layout or opaque"};
  // Fact origin kinds: what allocated the stored pointer's object.
  static const char *const originNames[8] = {"function", "global", "stack", "heap", "row",
                                             "trailing", "outside", "other"};
  // A slot witness (a pointer-width access through an address that is
  // untyped or views the object as a struct enclosing the cell), by kind:
  // through a va_arg value (the vararg pool's address, ruling 3), other
  // untyped, or a fitting view.
  static const char *const witnessNames[3] = {"untyped witness", "untyped witness (vararg pool)",
                                              "witness through a fitting view"};
  // A lowered va_arg's value: a load through the reg_save_area or
  // overflow_arg_area pointer loaded from a __va_list_tag.
  auto vaArgValue = [](const Value *V) {
    const auto *LI = dyn_cast<LoadInst>(V);
    if (!LI) return false;
    std::vector<const Value *> work{LI->getPointerOperand()};
    std::set<const Value *> seen;
    while (!work.empty() && seen.size() < 32) {
      const Value *P = work.back();
      work.pop_back();
      if (!seen.insert(P).second) continue;
      if (const auto *PN = dyn_cast<PHINode>(P)) {
        for (const Value *In : PN->incoming_values()) work.push_back(In);
      } else if (const auto *GEP = dyn_cast<GEPOperator>(P)) {
        work.push_back(GEP->getPointerOperand());
      } else if (const auto *BC = dyn_cast<BitCastOperator>(P)) {
        work.push_back(BC->getOperand(0));
      } else if (const auto *L = dyn_cast<LoadInst>(P)) {
        if (const auto *AG = dyn_cast<GEPOperator>(L->getPointerOperand()))
          if (const auto *ST = dyn_cast<StructType>(AG->getSourceElementType()))
            if (ST->hasName() && ST->getName().starts_with("struct.__va_list_tag")) return true;
      }
    }
    return false;
  };
  const unsigned ptrBits = DL.getPointerSizeInBits();
  auto slotOf = [&](uint32_t o, int64_t c) -> uint8_t {
    const Obj &O = objs[o];
    if (!O.layout) return SL_BYTES;
    if (StringRef(O.label).starts_with("struct.__va_list_tag")) return SL_VAPOOL;
    Type *T = O.layout;
    int64_t off = c;
    for (int depth = 0; depth < 64; depth++) {
      if (off < 0) return SL_BEYOND;
      if (auto *ST = dyn_cast<StructType>(T)) {
        if (ST->isOpaque()) return SL_BEYOND;
        if (ST->hasName() && ST->getName().starts_with("union.")) return SL_UNION;
        const StructLayout *SL = DL.getStructLayout(ST);
        if ((uint64_t)off >= SL->getSizeInBytes()) return SL_BEYOND;
        const unsigned i = SL->getElementContainingOffset(off);
        off -= (int64_t)SL->getElementOffset(i);
        T = ST->getElementType(i);
        continue;
      }
      Type *E = nullptr;
      if (auto *AT = dyn_cast<ArrayType>(T)) E = AT->getElementType();
      else if (auto *VT = dyn_cast<FixedVectorType>(T)) E = VT->getElementType();
      if (E) {
        const int64_t e = (int64_t)DL.getTypeAllocSize(E);
        if (e == 0) return SL_BEYOND;
        off %= e;
        T = E;
        continue;
      }
      if (off != 0) return off < (int64_t)DL.getTypeAllocSize(T) ? SL_INTERIOR : SL_BEYOND;
      if (T->isPointerTy()) return SL_PTR;
      if (T->isIntegerTy(ptrBits)) return SL_INTPTR;
      if (T->isIntegerTy(8)) return SL_CHAR;
      if (T->isIntegerTy()) return SL_INT;
      return SL_OTHER;
    }
    return SL_BEYOND;
  };
  auto originKind = [&](uint32_t f) -> int {
    if (cells[f].kind == CellKind::Func) return 0;
    for (auto [o, e] : memb[f]) {
      const Obj &O = objs[o];
      if (O.fn) return 0;
      if (O.rowOwner != UINT32_MAX) return 4;
      if (O.parentObj != UINT32_MAX) return 5;
      const Value *V = NF.getValueForNode(O.origin);
      if (isa_and_nonnull<GlobalVariable>(V)) return 1;
      if (isa_and_nonnull<AllocaInst>(V)) return 2;
      if (isa_and_nonnull<CallBase>(V)) return 3;
      if (isa_and_nonnull<Argument>(V)) return 6;
      return 7;
    }
    return 7;
  };
  // A feeding site: an IR store (its address), or a tagged cause: the
  // kind in bits 40..47 and a node (or copy) in the low 32 bits.
  enum SlotCause : uint64_t { SC_COLL = 1, SC_COPY, SC_CELL, SC_EDGE, SC_WHY };
  auto slotCauseKey = [](uint64_t kind, uint64_t sub, uint32_t x) {
    return 1ull << 63 | kind << 40 | sub << 32 | x;
  };
  struct SlotFeed {
    uint64_t arrivals = 0;
    uint64_t byOrigin[8] = {};
  };
  boost::unordered_flat_map<std::pair<uint32_t, int64_t>, uint32_t> slotFeedIdx;
  std::vector<boost::unordered_flat_map<uint64_t, SlotFeed>> slotFeeds;
  uint64_t slotArrivals = 0;
  boost::unordered_flat_map<uint64_t, uint32_t> slotStoreColl; // a store site -> the collector it was found by
  if (!CFLCellVarargActuals.empty() && !CFLCellSoupProfile) {
    errs() << "Cells: --cfl-cell-vararg-actuals reports at the soup profiler's stop point; "
           << "it needs --cfl-cell-soup-profile\n";
    exit(1);
  }
  if (CFLCellSlotCensus && !CFLCellLeakCensus) {
    errs() << "Cells: --cfl-cell-slot-census reads the leak census's cell and store maps; "
           << "it needs --cfl-cell-leak-census\n";
    exit(1);
  }
  if (CFLCellSlotCensus) {
    auto leakPrev = leakArrive;
    leakArrive = [&, leakPrev](uint32_t n, uint32_t f) {
      leakPrev(n, f);
      if (soupStop) return;
      const auto it = leakCellOf.find(n);
      if (it == leakCellOf.end()) return;
      const auto [o, c] = it->second;
      if (c == kLeakAny || objs[o].fn || slotOf(o, c) < SL_CHAR) return;
      f = findFact(f);
      const Why w = curWhy;
      const bool hasSrc = w.node < numNodes && w.fact < cells.size() &&
                          (w.kind == W_EDGE || w.kind == W_STEP || w.kind == W_WALK ||
                           w.kind == W_ANY || w.kind == W_DISPATCH);
      uint64_t key;
      if (hasSrc && w.kind == W_EDGE) {
        const uint32_t a = find(w.node);
        if (auto hit = leakCollHub.find(a); hit != leakCollHub.end()) {
          const Value *Vp = nullptr, *Vv = nullptr;
          bool held = true;
          const StoreInst *SI = leakStoreAt(a, hit->second, f, Vp, Vv, held);
          key = SI ? (uint64_t)(uintptr_t)SI : slotCauseKey(SC_COLL, 0, a);
          if (SI) slotStoreColl.try_emplace(key, a);
        } else if (auto cit = leakCopyEdge.find((uint64_t)a << 32 | n); cit != leakCopyEdge.end()) {
          key = slotCauseKey(SC_COPY, 0, cit->second);
        } else {
          key = slotCauseKey(leakCellOf.count(a) ? SC_CELL : SC_EDGE, 0, a);
        }
      } else {
        key = slotCauseKey(SC_WHY, w.kind, hasSrc ? find(w.node) : UINT32_MAX);
      }
      const auto [iit, ins] = slotFeedIdx.try_emplace(it->second, (uint32_t)slotFeeds.size());
      const uint32_t idx = iit->second;
      if (ins) slotFeeds.emplace_back();
      SlotFeed &F = slotFeeds[idx][key];
      F.arrivals++;
      F.byOrigin[originKind(f)]++;
      slotArrivals++;
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
    // --cfl-cell-one-label-object asks where the object first meets another
    // label: its conflicts are reported inside the cone or not, with
    // function-pointer objects or not (both marked); the cone and the
    // function-pointer tests decide only in the unfiltered mode.
    const bool filtered = !CFLCellOneLabelObject.empty();
    for (PendingConflict &P : pendingConf) {
      const bool inC = inCone[find(P.n)] != 0;
      // Fact level: only objects carrying function pointers can change a
      // target set (both sides for two names; the stepped or copied object
      // otherwise). Harmless ones wait: the fixpoint may still change.
      const bool matters =
          P.kind == 0 ? factCarriesFptrs(P.a) && factCarriesFptrs(P.f)
          : factCarriesFptrs(P.f); // the stepped / copied-from object
      if (!filtered) {
        if (!inC) { keep.push_back(P); continue; }
        if (!matters) {
          if (final) coneHarmless++;
          else keep.push_back(P);
          continue;
        }
      }
      const std::string marks = std::string(" [fn-ptr: ") + (matters ? "yes" : "no") +
                                ", in cone: " + (inC ? "yes" : "no") + "]";
      if (CFLCellOneLabelMax <= 1) {
        CG_LOG("Cells: (" << (inC ? "inside" : "outside") << " the icall cone: " << coneSize << " nodes from "
               << icallOps.size() << " icall operands; the conflict arose at pop "
               << P.pop << ")" << marks << "\n");
        if (P.kind == 1) reportTypedStep(P.n, findFact(P.f), P.S, P.why.c_str()); // exits
        if (P.kind == 0) reportConflict(P.n, findFact(P.a), findFact(P.f));
        else CG_LOG("Cells: NAME CONFLICT at pop " << P.pop
                    << ": a copy between unrelated structs: " << P.why << "\n");
        reportDefects();
        errs() << "Cells: --cfl-cell-one-label stopped at the first name "
               << "conflict" << (filtered ? "" : " inside the icall cone") << " (measurement only, no answers)\n";
        errs() << "Cells: stopped at " << pops << " pops (one-label stop, 1 conflict)\n";
        exit(0);
      }
      if (P.kind != 0 && !filtered) continue; // collect mode counts those in otherMeets
      if (!collectSeen.insert({find(P.n), (uint32_t)P.kind, P.kind == 0 ? findFact(P.a) : 0u, findFact(P.f)})
               .second) {
        collectDup++;
        continue;
      }
      if (P.kind != 0) {
        // A step of another struct or a copy between unrelated structs:
        // the cell, and how its objects arrived.
        conflicts++;
        coneReported++;
        const uint32_t f = findFact(P.f);
        CG_LOG("Cells: NAME CONFLICT #" << conflicts << " at pop " << P.pop << marks << ": " << nodeDesc(P.n)
               << ": " << (P.kind == 1 ? "a step as " + (P.S && P.S->hasName() ? P.S->getName().str() : std::string("<struct>")) +
                                             " of a cell " + P.why
                                       : "a copy between unrelated structs: " + P.why)
               << " | cell = " << factDesc(f).substr(0, 160) << "\n");
        std::set<std::string> seen;
        for (auto [o, eo] : memb[f]) {
          const std::string w = describe(objs[o]);
          if (!seen.insert(w).second || seen.size() > 3) continue;
          tracePathD(P.n, w.substr(0, w.find(" [")), 3);
        }
        if (conflicts >= CFLCellOneLabelMax) finishCollect();
        continue;
      }
      conflicts++;
      coneReported++;
      const uint32_t a = findFact(P.a), f = findFact(P.f);
      CG_LOG("Cells: NAME CONFLICT #" << conflicts << " at pop " << P.pop << marks << ": "
             << nodeDesc(P.n) << ": A = " << factDesc(a).substr(0, 160)
             << " | B = " << factDesc(f).substr(0, 160) << "\n");
      meetPoints(P.n, a, f);
      // Both arrival paths, as the stop mode prints them (depth 3).
      for (uint32_t x : {a, f}) {
        const std::string w = describe(objs[memb[x][0].first]);
        tracePathD(P.n, w.substr(0, w.find(" [")), 3);
      }
      if (conflicts >= CFLCellOneLabelMax) finishCollect();
    }
    pendingConf.swap(keep);
    if (final)
      CG_LOG("Cells: icall cone " << coneSize << " nodes from " << icallOps.size()
             << " icall operands; " << pendingConf.size() + pendingDup
             << " conflicts outside it (unreported), " << coneHarmless
             << " inside but without function-pointer objects on both sides, "
             << coneReported << " inside"
             << (CFLCellOneLabelObject.empty() ? std::string()
                                               : "; " + std::to_string(oneLabelFiltered) +
                                                     " conflicts filtered out (no object matching \"" +
                                                     CFLCellOneLabelObject.getValue() + "\")")
             << "\n");
  };
  // At a stop other than the mode's own (a soup cap, census-at): the cone
  // line the final flush would print, and the conflicts still held (outside
  // the cone, or inside without function-pointer objects on both sides).
  auto coneStopSummary = [&]() {
    computeCone();
    computeFptrObjs();
    size_t outside = 0, harmless = 0;
    std::vector<std::string> held;
    for (const PendingConflict &P : pendingConf) {
      const bool inC = inCone[find(P.n)] != 0;
      const bool matters = P.kind == 0 ? factCarriesFptrs(P.a) && factCarriesFptrs(P.f) : factCarriesFptrs(P.f);
      (inC ? harmless : outside)++;
      if (held.size() < 10)
        held.push_back("pop " + std::to_string(P.pop) + " [fn-ptr: " + (matters ? "yes" : "no") +
                       ", in cone: " + (inC ? "yes" : "no") + "] " + nodeDesc(P.n).substr(0, 120) + ": " +
                       (P.kind == 0 ? "A = " + factDesc(findFact(P.a)).substr(0, 120) + " | B = "
                        : P.kind == 1 ? std::string("a step of another struct: ")
                                      : std::string("a copy between unrelated structs: ")) +
                       factDesc(findFact(P.f)).substr(0, 120));
    }
    CG_LOG("Cells: icall cone at the stop: " << coneSize << " nodes from " << icallOps.size()
           << " icall operands; " << conflicts << " conflicts reported; held: " << outside
           << " outside the cone, " << harmless << " inside but without function-pointer objects on both sides; "
           << pendingDup << " further conflicts at nodes already holding one"
           << (CFLCellOneLabelObject.empty() ? std::string()
                                             : "; " + std::to_string(oneLabelFiltered) +
                                                   " conflicts filtered out (no object matching \"" +
                                                   CFLCellOneLabelObject.getValue() + "\")")
           << "\n");
    for (const std::string &h : held) CG_LOG("Cells:   held " << h << "\n");
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
  std::string stopKind; // the stop's name in the final line
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
      stopKind = soupForeign.size() >= CFLCellSoupCap ? "soup-cap stop" : "soup-time stop";
      break;
    }
    if (whyAnyArrived) {
      errs() << "Cells: --cfl-cell-why any: the queried any-offset cell arrived; "
             << "stopping (measurement only, no answers)\n";
      stoppedAt = pops;
      stopKind = "why-any stop";
      break;
    }
    // Pops counted over all iterations (the stop lands in the iteration
    // that explodes, not in an earlier, cheap one).
    static uint64_t allPops = 0;
    if (CFLCellCensusAt && ++allPops >= CFLCellCensusAt) {
      if (!recordWhy) confluenceCensus();
      checkConstInt();
      errs() << "Cells: --cfl-cell-census-at stopped the solve (measurement "
             << "only, no answers)\n";
      // The reports (soup profile, weld census, mass) describe the partial
      // state whether or not stop answers are asked for.
      stoppedAt = pops;
      stopKind = "census-at stop";
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
          for (uint32_t f : delta) {
            if (trackWhy) curWhy = {n, f, UINT32_MAX, W_EDGE};
            add(cn, f);
          }
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
          if (trackWhy) curWhy = {n, f, UINT32_MAX, W_EDGE};
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
      for (size_t ri = 0; ri < rowsAt[n].size(); ri++)
        for (uint32_t f : delta) linkRow(rowsAt[n][ri], f);
      for (size_t mi = 0; mi < mintsAt[n].size(); mi++)
        for (uint32_t f : delta) linkMint(mintsAt[n][mi], f);
      for (size_t ii = 0; ii < inheritAt[n].size(); ii++) {
        const uint32_t ci = inheritAt[n][ii];
        for (uint32_t f : delta)
          for (size_t k = 0; k < mintedOf[ci].size(); k++) inheritFields(cells[f].obj, mintedOf[ci][k], ci);
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
  checkConstInt();
  checkContainerPremises(stoppedAt != 0);
  // The owners' width at the row and mint sites (report only, Fable
  // 2026-10-14): the widest owner pointers, with the kinds of objects they
  // hold (struct label, byte storage, a trailing object, unlabeled).
  if (!rowLinks.empty() || !mintLinks.empty()) {
    std::vector<std::pair<size_t, std::string>> sites;
    std::set<uint32_t> allOwners;
    auto siteOf = [&](NodeIndex owner, const std::string &what) {
      std::map<std::string, size_t> kinds;
      std::set<uint32_t> mine;
      size_t nCells = 0;
      pts[find(canon(owner))].forEach([&](uint32_t f) {
        for (auto [o, e] : memb[findFact(f)]) {
          (void)e;
          nCells++;
          if (!mine.insert(o).second) continue;
          allOwners.insert(o);
          const Obj &O = objs[o];
          kinds[O.fn ? "function" : O.byteAccessed ? "bytes" : O.parentObj != UINT32_MAX ? "tail"
                : !O.layout ? "unlabeled" : O.label]++;
        }
      });
      const size_t w = mine.size();
      std::vector<std::pair<size_t, std::string>> ks;
      for (auto &[k, n] : kinds) ks.push_back({n, k});
      std::sort(ks.rbegin(), ks.rend());
      std::string d = what + ": " + std::to_string(w) + " owner objects in " + std::to_string(nCells) + " cells (";
      for (size_t i = 0; i < ks.size() && i < 4; i++) d += (i ? ", " : "") + ks[i].second + " " + std::to_string(ks[i].first);
      if (ks.size() > 4) d += ", ...";
      sites.push_back({w, d + ")"});
    };
    for (const RowLink &L : rowLinks) {
      const Value *V = NF.getValueForNode(L.owner);
      siteOf(L.owner, "row at " + (V ? nodeDescFn(canon(L.owner)).substr(0, 120) : std::string("?")));
    }
    for (const MintLink &L : mintLinks) siteOf(L.owner, "mint at " + nodeDescFn(canon(L.owner)).substr(0, 120));
    std::sort(sites.rbegin(), sites.rend());
    CG_LOG("Cells: owner width at " << sites.size() << " row/mint sites: " << allOwners.size()
           << " distinct owner objects; the widest:\n");
    for (size_t i = 0; i < sites.size() && i < 10; i++) CG_LOG("Cells:   " << sites[i].second << "\n");
  }
  if (!mintLinks.empty())
    CG_LOG("Cells: element mint: " << mintLinks.size() << " mint links (" << inlineInserts
           << " inline inserts), " << mintedObj.size() << " row objects minted (" << rowsByOwnerCtor
           << " by the owner's constructor, " << rowsByLargestOfSeveral << " by the largest of several, "
           << rowsByGlobalLargest << " by the container's largest element: owner's constructor unknown), "
           << inheritLinks << " inherited field links\n");
  if (!rowLinks.empty())
    CG_LOG("Cells: container rows: " << rowLinks.size() << " row links at call sites, " << rowCell.size()
           << " owner element cells, " << rowFacts << " owner facts linked (" << rowSkipped
           << " owner facts not an object offset)\n");

  CG_LOG("Cells: " << walkEdges << " field edges on cycles (pointer walks), "
         << walkSteps << " walk steps, " << indexOutsideArray
         << " variable indexes on a single object (array of one), " << segArrayOtherStride
         << " other strides over a segment array of a struct (data after it at a variable offset, folded), "
         << indexStays
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
         << " one then unknown (size unknown; " << promotedUnknownSize
         << " of them fresh wrappers with an unknown size term; " << carveUnknownSize.size()
         << " pool carves with an unknown size term; " << zeroProductSites.size()
         << " sized by a product through a zero-guarded wrapper), " << arraysExtended << " made arrays by a T-stride access ("
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
    if (CFLCellWeldCensus) {
      // The first welds in arrival order (a first arrival seen before the
      // stop cannot become earlier; later ones rank below these).
      static const char *kn[] = {"other", "edge", "step", "walk", "any-offset", "hub", "copy", "dispatch"};
      const char *tag = soupStop ? " (stop)" : " (fixpoint)";
      CG_LOG("Cells: WELD CENSUS: " << welds.size() << " welds; the first 20 by arrival (pop):\n");
      std::string filter;
      for (size_t i = 0; i < welds.size() && i < 20; i++) {
        const Weld &W = welds[i];
        CG_LOG("Cells:   WELD #" << i + 1 << " pop " << W.pop << " at " << nodeDesc(W.node) << " | held "
               << whyDesc(W.anchor) << " | got " << whyDesc(W.fact) << " | via " << kn[W.kind < 8 ? W.kind : 0]
               << (W.ctx.empty() ? std::string() : " (" + W.ctx + ")") << " from " << (W.src != UINT32_MAX ? nodeDesc(W.src) : std::string("-")) << " | mass " << W.mass
               << tag << ", " << format("%.2f", total ? 100.0 * W.mass / total : 0.0) << "% of the foreign facts"
               << tag << "\n");
        const std::string d = describe(objs[cells[W.fact].obj]);
        const std::string want = d.substr(0, d.find(" ["));
        if (filter.find(want) == std::string::npos) filter += (filter.empty() ? "" : "|") + want;
        if (recordWhy) explainWhy2(W.src != UINT32_MAX ? W.src : W.node, want, 2);
      }
      CG_LOG("Cells: WELD CENSUS --cfl-cell-why filter for these: " << filter << "\n");
      // Where the mass is: the heaviest welds, with their arrival rank.
      std::vector<uint32_t> byMass(welds.size());
      for (uint32_t i = 0; i < byMass.size(); i++) byMass[i] = i;
      std::stable_sort(byMass.begin(), byMass.end(), [&](uint32_t x, uint32_t y) { return welds[x].mass > welds[y].mass; });
      size_t first20 = 0;
      for (size_t i = 0; i < welds.size() && i < 20; i++) first20 += welds[i].mass;
      CG_LOG("Cells: WELD CENSUS mass: the first 20 carry " << first20 << tag << "; the heaviest:\n");
      for (size_t i = 0; i < byMass.size() && i < 10; i++) {
        const Weld &W = welds[byMass[i]];
        CG_LOG("Cells:   HEAVY weld #" << byMass[i] + 1 << " pop " << W.pop << " mass " << W.mass << tag << " at "
               << nodeDesc(W.node) << " | held " << whyDesc(W.anchor) << " | got " << whyDesc(W.fact) << " | via "
               << kn[W.kind < 8 ? W.kind : 0] << (W.ctx.empty() ? std::string() : " (" + W.ctx + ")") << " from "
               << (W.src != UINT32_MAX ? nodeDesc(W.src) : std::string("-")) << "\n");
      }
      // By subsystem (report only): the source directory of the weld
      // site's module; for the kernel, the directory under linux-*/ (one
      // level more under drivers/, net/, fs/, arch/, sound/).
      auto subsystemOf = [&](uint32_t n) -> std::string {
        const Function *F = nullptr;
        for (int d = 0; d < 4 && n < G && !F; d++) {
          const Value *V = NF.getValueForNode(n);
          if (const auto *I = dyn_cast_or_null<Instruction>(V)) F = I->getFunction();
          else if (const auto *A = dyn_cast_or_null<Argument>(V)) F = A->getParent();
          else if (const auto *FV = dyn_cast_or_null<Function>(V)) F = FV;
          else if (NF.getDerefParent(n) != AndersNodeFactory::InvalidIndex) n = NF.getDerefParent(n);
          else break;
        }
        if (!F) return "(no function)";
        SmallVector<StringRef, 16> cs;
        StringRef(F->getParent()->getModuleIdentifier()).split(cs, '/', -1, false);
        for (size_t i = 0; i + 1 < cs.size(); i++)
          if (cs[i].starts_with("linux")) {
            std::string sub = cs[i + 1].str();
            static const std::set<std::string> deep = {"drivers", "net", "fs", "arch", "sound"};
            if (deep.count(sub) && i + 3 < cs.size()) sub += "/" + cs[i + 2].str();
            return sub;
          }
        return cs.size() > 1 ? cs[cs.size() - 2].str() : std::string("(module)");
      };
      std::map<std::string, std::array<size_t, 6>> bySub; // all n/mass, first 20 n/mass, heavy 10 n/mass
      for (size_t i = 0; i < welds.size(); i++) {
        auto &t = bySub[subsystemOf(welds[i].node)];
        t[0]++;
        t[1] += welds[i].mass;
        if (i < 20) t[2]++, t[3] += welds[i].mass;
      }
      for (size_t i = 0; i < byMass.size() && i < 10; i++) {
        auto &t = bySub[subsystemOf(welds[byMass[i]].node)];
        t[4]++;
        t[5] += welds[byMass[i]].mass;
      }
      std::vector<std::pair<size_t, std::string>> subs;
      for (auto &[k, t] : bySub) subs.push_back({t[1], k});
      std::sort(subs.rbegin(), subs.rend());
      CG_LOG("Cells: WELD CENSUS by subsystem of the weld site (" << bySub.size() << " subsystems; welds, mass" << tag
             << "; first 20; heaviest 10):\n");
      for (auto &[m, k] : subs) {
        const auto &t = bySub[k];
        CG_LOG("Cells:   SUBSYSTEM " << k << ": " << t[0] << " welds, mass " << t[1] << "; first 20: " << t[2]
               << ", mass " << t[3] << "; heaviest 10: " << t[4] << ", mass " << t[5] << "\n");
      }
    }
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
    // Every fact at the stop, and those downstream of a leak (by leak). A
    // fact in a cell whose layout has no pointer-width slot there and is
    // not char (the interior of a scalar, another integer, a float, past
    // the layout) is no landing (slot census ruling 1): counted apart, out
    // of its leak's downstream. Facts a class-6 any-offset write tagged
    // are credited to the feeders of that object's any-offset cell.
    size_t allFacts = 0, downAll = 0, noLandAll = 0;
    std::vector<size_t> down(leakSites.size(), 0), noLand(leakSites.size(), 0);
    size_t noLandCls[SL_N] = {};
    std::map<uint32_t, std::map<uint64_t, std::pair<size_t, size_t>>> siteFeeders; // site -> feeder -> (landed, no landing)
    for (uint32_t m = 0; m < numNodes; m++) {
      if (find(m) != m) continue;
      allFacts += pts[m].count();
      uint8_t nl = SL_N;
      if (auto it = leakCellOf.find(m); it != leakCellOf.end() && it->second.second != kLeakAny &&
                                        !objs[it->second.first].fn) {
        const uint8_t k = slotOf(it->second.first, it->second.second);
        if (k == SL_INT || k == SL_OTHER || k == SL_INTERIOR || k == SL_BEYOND) nl = k;
      }
      pts[m].forEach([&](uint32_t f0) {
        auto tag = leakTag.get((uint64_t)m << 32 | findFact(f0));
        if (!tag) tag = leakTag.get((uint64_t)m << 32 | f0);
        if (!tag) return;
        downAll++;
        if (nl != SL_N) {
          noLandAll++;
          noLandCls[nl]++;
          noLand[*tag]++;
        } else {
          down[*tag]++;
        }
        if (const uint32_t ao = leakSites[*tag].anyObj; ao != UINT32_MAX) {
          const auto fit = leakAnyFeed.find((uint64_t)ao << 32 | findFact(f0));
          auto &e = siteFeeders[*tag][fit == leakAnyFeed.end() ? 0 : fit->second];
          (nl != SL_N ? e.second : e.first)++;
        }
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
            auto tag = leakTag.get((uint64_t)R << 32 | f);
            if (!tag) tag = leakTag.get((uint64_t)R << 32 | f0);
            if (!tag) {
              untagged++;
              untaggedAt[{o, c}]++;
              return;
            }
            siteMass[*tag]++;
            siteObjs[*tag][memb[f][0].first]++;
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
    CG_LOG("Cells:   LEAK no landing: " << noLandAll << " of the " << downAll
           << " downstream facts sit in cells with no pointer-width slot that are not char (interior of a scalar "
           << noLandCls[SL_INTERIOR] << ", other integer " << noLandCls[SL_INT] << ", float or other scalar "
           << noLandCls[SL_OTHER] << ", past the layout " << noLandCls[SL_BEYOND]
           << "); counted apart, out of each leak's downstream\n");
    // A feeder of an object's any-offset cell, by its key.
    auto feederDesc = [&](uint64_t key) -> std::string {
      if (key == 0) return "no recorded feeder (merge or pre-hook)";
      if (!(key >> 63)) {
        const auto *SI = reinterpret_cast<const StoreInst *>((uintptr_t)key);
        const std::string v = leakStructView(SI->getPointerOperand());
        return "store " + instLoc(SI) + " " + leakIR(SI) + " | address " +
               (v.empty() ? std::string("char or untyped") : "viewed as " + v);
      }
      const uint64_t kind = key >> 40 & 0xff, sub = key >> 32 & 0xff;
      const uint32_t x = (uint32_t)key;
      switch (kind) {
      case 1: {
        NodeIndex par;
        const auto hit = leakCollHub.find(x);
        const Value *Vp = hit == leakCollHub.end() ? nullptr : leakHubPtr(hit->second, par);
        return "store collector without an IR store; pointer " + leakDesc(leakNodeOf(Vp));
      }
      case 2:
        return "byte copy " + (copies[x].at ? instLoc(copies[x].at) + " " + leakIR(copies[x].at) : std::string("(no site)"));
      case 3: {
        const auto it = leakCellOf.find(x);
        return "cell edge from " +
               (it->second.second == kLeakAny ? std::string("*") : cellName(it->second.first, it->second.second)) +
               " of " + describe(objs[it->second.first]);
      }
      case 4:
        return "edge from " + leakDesc(x);
      default: {
        static const char *kinds[] = {"seed or initializer", "edge", "field step", "pointer walk",
                                      "any-offset step", "hub", "byte copy", "dispatch"};
        return std::string(kinds[sub]) + (x == UINT32_MAX ? std::string() : " from " + leakDesc(x));
      }
      }
    };
    // A class-6 any-offset write whose tagged facts are all no landing
    // hands its rank to its feeders (ANY-FEEDER below); it is listed there.
    auto handedOver = [&](uint32_t s) {
      return leakSites[s].anyObj != UINT32_MAX && down[s] == 0 && noLand[s] > 0;
    };
    std::vector<uint32_t> order;
    for (uint32_t s = 0; s < leakSites.size(); s++)
      if (!handedOver(s)) order.push_back(s);
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
             << (noLand[s] ? ", no landing " + std::to_string(noLand[s]) : std::string())
             << ": " << L.where << " | into " << L.into << " | " << L.detail
             << " | objects: " << objsTop << "\n");
      if (auto sit = siteFeeders.find(s); sit != siteFeeders.end()) {
        std::vector<std::pair<size_t, uint64_t>> fs;
        for (const auto &[k, lz] : sit->second) fs.emplace_back(lz.first + lz.second, k);
        std::sort(fs.begin(), fs.end(), [](const auto &x, const auto &y) {
          return x.first != y.first ? x.first > y.first : x.second < y.second;
        });
        for (size_t j = 0; j < fs.size() && j < 3; j++) {
          const auto &lz = sit->second.at(fs[j].second);
          CG_LOG("Cells:     fed by " << feederDesc(fs[j].second) << ": landed " << lz.first << ", no landing "
                 << lz.second << "\n");
        }
      }
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
    {
      // The feeders that took a handed-over site's rank: by the facts they
      // fanned out through it, each with the sites it took over.
      std::map<uint64_t, size_t> feederMass;
      std::map<uint64_t, std::vector<uint32_t>> feederSites;
      for (uint32_t s = 0; s < leakSites.size(); s++) {
        if (!handedOver(s)) continue;
        for (const auto &[k, lz] : siteFeeders[s]) {
          feederMass[k] += lz.first + lz.second;
          feederSites[k].push_back(s);
        }
      }
      std::vector<std::pair<size_t, uint64_t>> fo;
      for (const auto &[k, m] : feederMass) fo.emplace_back(m, k);
      std::sort(fo.begin(), fo.end(), [](const auto &x, const auto &y) {
        return x.first != y.first ? x.first > y.first : x.second < y.second;
      });
      CG_LOG("Cells:   LEAK any-offset writes handed to their feeders: " << feederSites.size() << " feeders\n");
      for (size_t i = 0; i < fo.size() && i < 20; i++) {
        CG_LOG("Cells:   LEAK ANY-FEEDER #" << i + 1 << " fans out " << fo[i].first << ": "
               << feederDesc(fo[i].second) << "\n");
        for (uint32_t s : feederSites[fo[i].second])
          CG_LOG("Cells:     " << leakSites[s].where << ": " << noLand[s] << " facts, all no landing\n");
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
  // Slot census report: facts in content cells by slot, then the cells
  // without a pointer-width slot by facts, with the sites that fed them.
  if (CFLCellSlotCensus) {
    auto pct = [](uint64_t a, uint64_t b) {
      char buf[16];
      snprintf(buf, sizeof buf, "%.1f", b ? 100.0 * (double)a / (double)b : 0.0);
      return std::string(buf);
    };
    uint64_t mass[SL_N] = {}, ncells[SL_N] = {}, all = 0, shared = 0;
    std::vector<std::tuple<uint64_t, uint32_t, int64_t, uint8_t>> noSlot; // facts, o, c, slot
    boost::unordered_flat_set<uint32_t> seen;
    for (uint32_t o = 0; o < objs.size(); o++) {
      const Obj &O = objs[o];
      if (O.fn) continue;
      if (O.any != UINT32_MAX) { // the facts written at any offset
        const uint32_t R = find(cells[O.any].store);
        if (seen.insert(R).second) {
          mass[SL_ANY] += pts[R].count();
          ncells[SL_ANY]++;
        } else {
          shared++;
        }
      }
      for (const auto &[c, up] : O.content) {
        const uint32_t R = find(up.second); // the read side: every write the cell holds
        if (!seen.insert(R).second) { shared++; continue; }
        const uint64_t m = pts[R].count();
        const uint8_t k = slotOf(o, c);
        mass[k] += m;
        ncells[k]++;
        if (k >= SL_CHAR && m) noSlot.emplace_back(m, o, c, k);
      }
    }
    uint64_t none = 0, noneCells = 0;
    for (int k = 0; k < SL_N; k++) all += mass[k];
    for (int k = SL_CHAR; k < SL_N; k++) none += mass[k], noneCells += ncells[k];
    CG_LOG("Cells: SLOT census at " << pops << " pops: " << all << " facts in content cells ("
           << shared << " cells share a node with one counted)\n");
    CG_LOG("Cells:   SLOT classes by the layout's leaf at the cell's offset: a slot is a pointer member, "
           "a pointer-width integer (an i" << ptrBits << " leaf, admitted or not), unlabeled bytes, the "
           "any-offset cell, or a union's bytes; a va_list's cells are the engine's vararg pool (apart); "
           "no slot is a char member or char object, another integer "
           "member, a float or other scalar member, the interior of a scalar member, or past the layout\n");
    for (int k = 0; k < SL_N; k++)
      CG_LOG("Cells:   SLOT " << (k == SL_VAPOOL ? "engine" : k < SL_CHAR ? "has a slot" : "NO slot") << ": " << slotNames[k] << ": "
             << mass[k] << " facts (" << pct(mass[k], all) << "%) in " << ncells[k] << " cells\n");
    CG_LOG("Cells:   SLOT no pointer-width slot: " << none << " facts (" << pct(none, all) << "%) in "
           << noneCells << " cells; " << slotArrivals << " arrivals into them recorded by site\n");
    std::sort(noSlot.begin(), noSlot.end(), [](const auto &x, const auto &y) {
      return std::get<0>(x) != std::get<0>(y) ? std::get<0>(x) > std::get<0>(y) : x < y;
    });
    // By object: equal cells of one object (the bytes of a scalar each
    // fed by its any-offset cell) would fill the cell list.
    {
      std::map<uint32_t, std::pair<uint64_t, uint64_t>> byObj; // facts, cells
      for (const auto &[m, o, c, k] : noSlot) {
        byObj[o].first += m;
        byObj[o].second++;
      }
      std::vector<std::pair<uint64_t, uint32_t>> ord;
      for (const auto &[o, mc] : byObj) ord.emplace_back(mc.first, o);
      std::sort(ord.begin(), ord.end(), [](const auto &x, const auto &y) {
        return x.first != y.first ? x.first > y.first : x.second < y.second;
      });
      for (size_t i = 0; i < ord.size() && i < 10; i++)
        CG_LOG("Cells:   SLOT object #" << i + 1 << " " << ord[i].first << " facts (" << pct(ord[i].first, none)
               << "% of no-slot) in " << byObj[ord[i].second].second << " cells: "
               << describe(objs[ord[i].second]) << "\n");
      // The top objects' no-slot cells: what minted each (the mint cause,
      // the step's result), and the loads and stores through pointers that
      // hold its address (width, site, the address's struct view). A
      // pointer-width access is a slot the layout does not declare.
      std::vector<std::pair<const Value *, uint32_t>> derefPtrs; // pointer value, its node
      if (!ord.empty())
        for (const GraphEdge &E : Graph.edges())
          if (E.kind == EdgeKind::Deref)
            if (const Value *V = NF.getValueForNode(E.from)) derefPtrs.emplace_back(V, canon(E.from));
      const uint64_t ptrBytes = ptrBits / 8;
      for (size_t i = 0; i < ord.size() && i < 3; i++) {
        const uint32_t o = ord[i].second;
        const Obj &O = objs[o];
        size_t undeclared = 0, listed = 0, otherLayout = 0;
        size_t witnessCells[3] = {0, 0, 0}; // cells by witness kind
        // Cells with the same mint and accesses print as one line.
        std::map<std::string, size_t> groupIdx, objWitness;
        std::vector<std::tuple<std::string, std::vector<int64_t>, uint64_t>> groups;
        for (const auto &[m, oo, c, k] : noSlot) {
          if (oo != o) continue;
          listed++;
          std::vector<std::string> chainAt;
          structChain(O.layout, c, DL, chainAt);
          std::string mint = "minted before the census (no record)";
          if (auto mit = slotMint.find(std::make_pair(o, c)); mit != slotMint.end()) {
            const SlotMint &M = mit->second;
            static const char *kinds[] = {"seed or other", "edge", "field step", "pointer walk",
                                          "any-offset step", "hub link", "byte copy", "dispatch"};
            mint = "minted by [" + M.cause + "] during a " + kinds[M.why.kind];
            if (M.stepDst != UINT32_MAX) {
              const Value *SV = M.stepDst < G ? NF.getValueForNode(M.stepDst) : nullptr;
              if (const auto *SI = dyn_cast_or_null<Instruction>(SV)) {
                mint += " at " + instLoc(SI) + " " + leakIR(SI);
                // A step through a struct that does not enclose c here: one
                // pointer holding objects of several layouts (ruling 6).
                if (const auto *GEP = dyn_cast<GEPOperator>(SI)) {
                  const std::string l = typeLabel(GEP->getSourceElementType());
                  bool fits = !StringRef(l).starts_with("struct.");
                  for (const std::string &e : chainAt) fits |= e.rfind(l + "+", 0) == 0;
                  if (!fits) {
                    mint += " | STEP THROUGH ANOTHER LAYOUT (" + l + ")";
                    otherLayout++;
                  }
                }
              } else {
                mint += " to " + leakDesc(M.stepDst);
              }
            } else if (M.why.kind == W_COPY && M.why.node < copies.size()) { // node: the copy's index
              const ByteCopy &BC = copies[M.why.node];
              mint += " " + (BC.at ? instLoc(BC.at) + " " + leakIR(BC.at) : std::string("(no site)")) +
                      ", len " + std::to_string(BC.len);
            } else if (M.why.node < numNodes) {
              mint += " from " + leakDesc(find(M.why.node));
            }
          }
          // The address facts of the cell (offsets that fold to c).
          std::vector<uint32_t> F;
          for (const auto &[key, f] : O.offCells) {
            const int64_t off = cells[f].off;
            if (O.tail && off >= O.size) continue;
            if (contentKey(O, off) == c) F.push_back(findFact(f));
          }
          std::map<uint64_t, size_t> widths;
          std::vector<std::string> ex;
          std::set<const Instruction *> seenI;
          // A pointer-width access is a slot the layout does not declare
          // when its address is untyped or views the object as one of the
          // structs enclosing c; through another struct's view it is a
          // pointer holding the wrong object (counted apart).
          bool ptrWide = false;
          size_t ptrWideMisView = 0;
          std::set<std::string> witnesses; // the pointer-width accesses that make it a slot
          std::set<int> witnessKinds;
          for (const auto &[V, pn] : derefPtrs) {
            const uint32_t r = find(pn);
            if (r >= pts.size()) continue;
            bool holds = false;
            for (uint32_t f : F) holds |= pts[r].test(f);
            if (!holds) continue;
            for (const User *U : V->users()) {
              const auto *I = dyn_cast<Instruction>(U);
              if (!I || !seenI.insert(I).second) continue;
              Type *T = nullptr;
              const char *what = nullptr;
              if (const auto *LI = dyn_cast<LoadInst>(I); LI && LI->getPointerOperand() == V) T = LI->getType(), what = "load";
              else if (const auto *SI = dyn_cast<StoreInst>(I); SI && SI->getPointerOperand() == V)
                T = SI->getValueOperand()->getType(), what = "store";
              if (!T) continue;
              const uint64_t w = DL.getTypeStoreSize(T);
              widths[w]++;
              const std::string v = leakStructView(V);
              if (w >= ptrBytes) {
                bool fits = v.empty();
                for (const std::string &e : chainAt) fits |= e.rfind(v + "+", 0) == 0;
                if (fits) {
                  ptrWide = true;
                  const int wk = !v.empty() ? 2 : vaArgValue(V) ? 1 : 0;
                  witnessKinds.insert(wk);
                  witnesses.insert(std::string(what) + " " + std::to_string(w) + "B " + instLoc(I) + " " + leakIR(I) +
                                   " (" + witnessNames[wk] + (v.empty() ? "" : ": viewed as " + v) + ")");
                } else {
                  ptrWideMisView++;
                }
              }
              if (ex.size() < 4 || (w >= ptrBytes && ex.size() < 6)) {
                ex.push_back(std::string(what) + " " + std::to_string(w) + "B " + instLoc(I) + " " + leakIR(I) +
                             (v.empty() ? " (untyped address)" : " (named: viewed as " + v + ")"));
              }
            }
          }
          std::string ws;
          for (const auto &[w, n] : widths) ws += (ws.empty() ? "" : ", ") + std::to_string(w) + "B x" + std::to_string(n);
          if (ptrWide) undeclared++;
          std::string wks;
          for (int wk : witnessKinds) {
            wks += (wks.empty() ? "" : ", ") + std::string(witnessNames[wk]);
            witnessCells[wk]++;
          }
          std::string body = std::string(slotNames[k]) + (ptrWide ? ", UNDECLARED SLOT: " + wks : "") +
                             (ptrWideMisView ? ", " + std::to_string(ptrWideMisView) +
                                                   " pointer-width accesses viewing another struct (a wrong target)"
                                             : std::string()) +
                             "): " + mint + "\nCells:       accesses through its address facts: " +
                             (ws.empty() ? std::string("none") : ws) + "\n";
          for (const std::string &e : ex) body += "Cells:         " + e + "\n";
          for (const std::string &e : witnesses) body += "Cells:         SLOT WITNESS " + e + "\n";
          for (const std::string &e : witnesses) objWitness[e]++;
          auto [git, gins] = groupIdx.try_emplace(body, groups.size());
          if (gins) groups.push_back({body, {}, 0});
          std::get<1>(groups[git->second]).push_back(c);
          std::get<2>(groups[git->second]) += m;
        }
        for (const auto &[body, offs, gm] : groups) {
          std::string os;
          for (size_t j = 0; j < offs.size(); j++) os += (j ? " +" : "+") + std::to_string(offs[j]);
          CG_LOG("Cells:     SLOT cells " << os << " of " << O.label << " (" << offs.size() << " cells, " << gm
                 << " facts, " << body);
        }
        CG_LOG("Cells:   SLOT object #" << i + 1 << ": " << listed << " no-slot cells with facts, " << undeclared
               << " with a pointer-width access (undeclared slot: " << witnessCells[0] << " " << witnessNames[0] << ", "
               << witnessCells[1] << " " << witnessNames[1] << ", " << witnessCells[2] << " " << witnessNames[2]
               << "), " << otherLayout << " minted by a step through another layout\n");
        for (const auto &[e, n] : objWitness)
          CG_LOG("Cells:   SLOT object #" << i + 1 << " witness in " << n << " cells: " << e << "\n");
      }
    }
    auto siteDesc = [&](uint64_t key, uint32_t target) -> std::string {
      if (!(key >> 63)) {
        const auto *SI = reinterpret_cast<const StoreInst *>((uintptr_t)key);
        const uint32_t pn = leakNodeOf(SI->getPointerOperand());
        size_t po = 0, pl = 0;
        leakPtrShape(pn, po, pl);
        // Does the store's address hold the target object? A collector
        // standing for several stores (a shared hub) names the first whose
        // value holds the fact, which need not be the one that wrote it.
        bool holdsTarget = false;
        if (pn != UINT32_MAX)
          pts[pn].forEach([&](uint32_t g) {
            for (auto [mo, e] : memb[findFact(g)]) holdsTarget |= mo == target;
          });
        std::string hub;
        if (auto cit = slotStoreColl.find(key); cit != slotStoreColl.end())
          if (auto hit = leakCollHub.find(cit->second); hit != leakCollHub.end()) {
            NodeIndex par;
            const Value *Vp = leakHubPtr(hit->second, par);
            hub = "; collector's hub pointer " + (Vp ? leakDesc(leakNodeOf(Vp)) : std::string("?")) + ", " +
                  std::to_string(leakCollStores.count(cit->second) ? leakCollStores.find(cit->second)->second.size() : 0) +
                  " IR stores";
          }
        const std::string v = leakStructView(SI->getPointerOperand());
        return "store " + instLoc(SI) + " " + leakIR(SI) +
               " | address " + (v.empty() ? std::string("char or untyped") : "viewed as " + v) + ", holds " +
               std::to_string(po) + " objects of " + std::to_string(pl) + " labels" +
               (holdsTarget ? ", the target among them" : ", NOT the target (attribution by a shared collector)") + hub;
      }
      const uint64_t kind = key >> 40 & 0xff, sub = key >> 32 & 0xff;
      const uint32_t x = (uint32_t)key;
      switch (kind) {
      case SC_COLL: {
        NodeIndex par;
        const uint32_t h = leakCollHub.count(x) ? leakCollHub.find(x)->second : UINT32_MAX;
        const Value *Vp = h == UINT32_MAX ? nullptr : leakHubPtr(h, par);
        const std::string call = leakBodiless(Vp);
        return "store collector without an IR store" + (call.empty() ? std::string() : " (" + call + ")") +
               "; pointer " + leakDesc(leakNodeOf(Vp));
      }
      case SC_COPY: {
        const ByteCopy &BC = copies[x];
        return "byte copy " + (BC.at ? instLoc(BC.at) + " " + leakIR(BC.at) : std::string("(no site)"));
      }
      case SC_CELL: {
        const auto it = leakCellOf.find(x);
        return "cell edge from " +
               (it->second.second == kLeakAny ? std::string("*") : cellName(it->second.first, it->second.second)) +
               " of " + describe(objs[it->second.first]);
      }
      case SC_EDGE:
        return "edge from " + leakDesc(x);
      default: {
        static const char *kinds[] = {"seed or initializer", "edge", "field step", "pointer walk",
                                      "any-offset step", "hub", "byte copy", "dispatch"};
        return std::string(kinds[sub]) + (x == UINT32_MAX ? std::string() : " from " + leakDesc(x));
      }
      }
    };
    for (size_t i = 0; i < noSlot.size() && i < 10; i++) {
      const auto [m, o, c, k] = noSlot[i];
      Type *L = leafAt(objs[o].layout, c, DL);
      std::string leaf = "-";
      if (L) {
        leaf.clear();
        raw_string_ostream os(leaf);
        L->print(os);
        os.flush();
      }
      CG_LOG("Cells:   SLOT #" << i + 1 << " " << m << " facts (" << pct(m, none) << "% of no-slot): "
             << cellName(o, c) << " of " << describe(objs[o]) << " | " << slotNames[k] << ", leaf " << leaf
             << " | " << leakFieldOf(o, c) << "\n");
      const auto fit = slotFeedIdx.find(std::make_pair(o, c));
      if (fit == slotFeedIdx.end()) {
        CG_LOG("Cells:     no arrival recorded (its facts came by a merge or before the census hook)\n");
        continue;
      }
      std::vector<std::pair<uint64_t, uint64_t>> sites; // arrivals, key
      uint64_t arrived = 0;
      for (const auto &[key, F] : slotFeeds[fit->second]) {
        sites.emplace_back(F.arrivals, key);
        arrived += F.arrivals;
      }
      std::sort(sites.begin(), sites.end(), [](const auto &x, const auto &y) {
        return x.first != y.first ? x.first > y.first : x.second < y.second;
      });
      CG_LOG("Cells:     " << arrived << " arrivals from " << sites.size() << " sites\n");
      for (size_t j = 0; j < sites.size() && j < 5; j++) {
        const SlotFeed &F = slotFeeds[fit->second].find(sites[j].second)->second;
        std::string by;
        for (int q = 0; q < 8; q++)
          if (F.byOrigin[q]) by += (by.empty() ? "" : ", ") + std::string(originNames[q]) + " " + std::to_string(F.byOrigin[q]);
        CG_LOG("Cells:     fed " << F.arrivals << " (" << by << ") by " << siteDesc(sites[j].second, o) << "\n");
      }
    }
  }
  // --cfl-cell-vararg-actuals: per direct call of the named variadic
  // functions, the facts each pointer actual in the variadic part holds
  // (members named: a fact unified by name lists every object), then the
  // pool's facts that no actual holds (they came another way).
  if (!CFLCellVarargActuals.empty()) {
    std::set<std::string> want;
    for (StringRef w : llvm::split(StringRef(CFLCellVarargActuals.getValue()), '|'))
      if (!w.empty()) want.insert(w.str());
    auto fdesc = [&](uint32_t f) -> std::string {
      const Cell &C = cells[f];
      if (C.kind == CellKind::Func) return describe(objs[C.obj]);
      if (C.kind == CellKind::Out) return "an outside fact of " + describe(objs[C.obj]);
      std::string d = (C.kind == CellKind::Any ? std::string("*") : NF.cellNameString(C.name)) + " @" +
                      std::to_string(C.off) + " of {";
      for (size_t i = 0; i < memb[f].size() && i < 6; i++)
        d += (i ? "; " : "") + describe(objs[memb[f][i].first]);
      if (memb[f].size() > 6) d += "; ... " + std::to_string(memb[f].size()) + " members";
      return d + "}";
    };
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        if (!F.isVarArg() || !want.count(F.getName().str())) continue;
        boost::unordered_flat_set<uint32_t> byActual;
        size_t calls = 0;
        for (const User *U : F.users()) {
          const auto *CB = dyn_cast<CallBase>(U);
          if (!CB || CB->getCalledFunction() != &F) continue;
          calls++;
          for (unsigned i = F.getFunctionType()->getNumParams(); i < CB->arg_size(); i++) {
            const Value *A = CB->getArgOperand(i);
            if (!A->getType()->isPointerTy()) continue;
            const uint32_t an = leakNodeOf(A);
            if (an == UINT32_MAX || an >= pts.size()) {
              CG_LOG("Cells: VARARG " << F.getName() << " " << instLoc(CB) << " actual " << i << ": no node\n");
              continue;
            }
            std::string fs;
            size_t nf = 0;
            pts[an].forEach([&](uint32_t g) {
              const uint32_t f = findFact(g);
              byActual.insert(f);
              if (nf++ < 6) fs += "\nCells:     " + fdesc(f);
            });
            CG_LOG("Cells: VARARG " << F.getName() << " " << instLoc(CB) << " actual " << i << " "
                   << leakDesc(an) << ": " << nf << " facts" << fs << "\n");
          }
        }
        const NodeIndex pool = NF.getVarargNodeFor(&F);
        const uint32_t pn = pool == AndersNodeFactory::InvalidIndex || pool >= G ? UINT32_MAX : find(getCanonicalNode(pool));
        size_t inPool = 0, notByActual = 0;
        std::string rest;
        if (pn != UINT32_MAX && pn < pts.size())
          pts[pn].forEach([&](uint32_t g) {
            inPool++;
            const uint32_t f = findFact(g);
            if (byActual.count(f)) return;
            if (notByActual++ < 12) rest += "\nCells:     " + fdesc(f);
          });
        CG_LOG("Cells: VARARG " << F.getName() << ": " << calls << " direct calls; pool " << inPool << " facts, "
               << notByActual << " held by no actual" << rest << "\n");
      }
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
         << " objects (" << tailMinted << " trailing, " << segmentsLabeled << " of them segments the site declares ("
         << segmentArrays << " arrays of their struct without an extent, " << segmentsPtrArrays
         << " arrays of pointer slots, " << segmentsScalarArrays << " arrays of a declared scalar; "
         << segmentsBytes << " more byte-used from mint by a char receiver), "
         << trailingArrays << " of them arrays of unknown extent, " << tailMoved
         << " cells moved to them); heap " << heapLabeled << " labeled (" << heapPtrArrays
         << " arrays of pointer slots, " << heapScalarArrays << " arrays of a declared scalar, " << tailObjects
         << " header + trailing data), " << heapUnlabeled
         << " unlabeled (" << heapBytesMarked << " used as bytes from mint), " << heapConflict
         << " with conflicting labels, "
         << heapContainerRelabeled << " relabeled to the container their size names, "
         << heapContainerAmbiguous << " ambiguous size labels (several containers of that size; the label stays)), "
         << cells.size() << " cells (" << offCells << " named offsets, "
         << anyCells << " any-offset, " << outMints << " outside)\n");
  for (const auto &[k, n] : sizeLabelAmbiguous)
    CG_LOG("Cells:   ambiguous size label: " << k << " (" << n << " objects)\n");
  CG_LOG("Cells: anonymous structs label nothing: " << anonObjects
         << " globals and stack objects unlabeled, " << anonLayoutRefused.size()
         << " objects a typed write would have labeled\n");
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
  {
    std::string why;
    for (auto &[w, n] : widenRefused) why += "; " + std::to_string(n) + " " + w;
    CG_LOG("Cells: labels widened to a container at offset 0 (row 2): " << widened << "; refused"
           << (why.empty() ? std::string(": none") : why) << "\n");
  }
  CG_LOG("Cells: rule (b): struct written into storage declared scalar (ruling A; folded into "
         << "the array's element cells, flow kept): " << scalarStructWrites << " writes, "
         << scalarStructSteps << " struct steps in all\n");
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
            if (const auto tag = leakTag.get((uint64_t)pn << 32 | findFact(f))) {
              cause = *tag;
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
      std::set<std::string> kinds, shown;
      for (uint32_t b : out) {
        kinds.insert(bnd[b].first);
        if (bnd[b].first == "bodiless call") byBodiless[bnd[b].second]++;
        shown.insert(" [" + bnd[b].first + " " + bnd[b].second + "]");
      }
      // The first four by text, not by boundary id (ids follow discovery order).
      size_t n = 0;
      for (const std::string &s : shown)
        if (n++ < 4) l += s;
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
    RO << "SUMMARY sites " << censusSites << " allocation sites: " << censusStructFieldOnly
       << " whose only receiver is a struct-pointer field (no declaration: a base-class slot), "
       << censusSharedDeclared << " declared through a shared slot (uses not followed), " << censusUndeclared
       << " with no declaration (" << censusUnclassified << " result slots also hold another value; "
       << censusReachedReloads << " of those sites have reloads only their own store reaches: followed for segments)\n";
    if (!containerClosureReport.empty()) {
      RO << "# Container closure (plan 3.55 obligation 1, --cfl-container-closure, report only): per field\n"
         << "# fed fresh blocks, closed or open with the failing uses.\n";
      for (const std::string &l : containerClosureReport) RO << "CLOSURE " << l << "\n";
    }
    if (!containerReport.empty()) {
      RO << "# Containers (plan 3.55): rows by provenance, the body, obligations O1-O6 PASS/FAIL, verdict.\n";
      for (const std::string &l : containerReport) RO << "CONTAINER " << l << "\n";
    }
    if (!linkWordReport.empty()) {
      RO << "# Link words (plan 3.55 R1, report only): integer fields read as pointers, by store and load\n"
         << "# shape; ASSUMPTION lines are reads that rely on tag 0; encoded pointer fields by shape only.\n";
      for (const std::string &l : linkWordReport) RO << "LINKWORD " << l << "\n";
    }
    RO << "SUMMARY segments declared by a receiver: " << censusSegments[0] << " a struct (" << censusSegments[1]
       << " indexed by a stride of it: arrays without an extent), " << censusSegments[2] << " arrays of pointer slots, "
       << censusSegments[3] << " arrays of a declared scalar, " << censusSegments[4] << " bytes (a char receiver); "
       << censusSegFieldSites << " sites through a struct field receiving the address\n";
    RO << "SUMMARY a " << aData << " pointers from data, " << aConst
       << " from constant addresses, " << aLost << " from pointers lost before the cast\n";
    RO << "SUMMARY b " << ruleB << " member steps whose struct is not at the address's offset ("
       << ruleBPairs.size() << " object label / struct pairs); struct written into storage declared scalar: "
       << scalarStructWrites << " writes (" << scalarStructSteps << " struct steps); struct array followed by other "
       << "data at a variable offset (another stride over a segment array, folded into its element cells): "
       << segArrayOtherStride << " steps\n";
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
       << " variable indexes on a single object, " << indexInBoundedArray
       << " variable indexes into a declared array field assumed within its bound, "
       << tailLinkedThenLabeled << " variable indexes linked a tail labeled later, "
          "pointer subtractions across objects: always "
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
    if (CFLCellOneLabel) coneStopSummary();
    errs() << "Cells: stopped at " << stoppedAt << " pops (" << stopKind << "); "
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
