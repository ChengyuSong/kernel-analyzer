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
  // An unlabeled object is unknown (its cells named ?#o, compatible only
  // with itself) until its first typed use: a struct step gives a layout,
  // byte arithmetic (a variable i8 index, a byte walk) makes it bytes.
  bool bytes = false;
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

// Does an allocation call's size argument say "a T followed by trailing
// data": a constant larger than T and not a multiple of it, or a sum (any
// depth: -O3 chains `sizeof(T) + 8*n + 40*m + k`) with a constant term of
// at least sizeof(T) and some other term that is not a multiple of it
// (`n*sizeof(T) + sizeof(T)` is an array of n+1)?
bool headerPlusTail(const CallBase *C, uint64_t sz) {
  // Casts only: a size term is never forwarded through memory (a slot
  // stored once may still be written through its address by a call).
  auto lookThrough = [](const Value *V) {
    while (const auto *CI = dyn_cast<CastInst>(V)) V = CI->getOperand(0);
    return V;
  };
  auto multipleOf = [&](const Value *X) {
    X = lookThrough(X);
    if (const auto *B = dyn_cast<BinaryOperator>(X)) {
      if (B->getOpcode() == Instruction::Mul)
        for (const Value *Op : B->operands())
          if (const auto *K = dyn_cast<ConstantInt>(lookThrough(Op)))
            return K->getZExtValue() % sz == 0;
      if (B->getOpcode() == Instruction::Shl)
        if (const auto *K = dyn_cast<ConstantInt>(lookThrough(B->getOperand(1))))
          return K->getZExtValue() < 63 && (1ULL << K->getZExtValue()) % sz == 0;
    }
    if (const auto *K = dyn_cast<ConstantInt>(X)) return K->getZExtValue() % sz == 0;
    return false;
  };
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
      if (K && K->getZExtValue() >= sz) header = true;
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
      if (recordWhy) {
        Why w = curWhy;
        w.t = whyClock;
        factWhy.try_emplace((uint64_t)n << 32 | f, w);
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
    if (!recordWhy) {
      pts[a].forEach([&](uint32_t f) { add(b, f); });
      return;
    }
    edgeWhy.try_emplace((uint64_t)a << 32 | b, curWhy);
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
  for (const GraphEdge &E : Graph.edges()) {
    switch (E.kind) {
    case EdgeKind::Copy: {
      const uint32_t a = canon(E.from), b = canon(E.to);
      inGraph[a] = inGraph[b] = 1;
      if (isHub[b]) { // a store: into the cells the hub's pointers hold
        if (storeHub[b] == UINT32_MAX) storeHub[b] = newNode();
        addEdge(a, storeHub[b]);
        stores++;
      } else {
        addEdge(a, b);
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

  // Merging solver nodes: the representative inherits every constraint
  // and re-propagates every fact (members brought facts the others'
  // successors and constraints have not seen).
  auto absorb = [&](uint32_t r, uint32_t m) {
    repOf[m] = r;
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
      std::vector<uint32_t> comp(numNodes, UINT32_MAX);
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
        }
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
  // The any-offset cell writes every content cell and reads them all.
  auto linkAny = [&](uint32_t a, uint32_t storeNode, uint32_t loadNode) {
    addEdge(cells[a].store, storeNode);
    addEdge(loadNode, cells[a].load);
  };
  // Why an any-offset cell was made (verbose, --cfl-cell-trace-obj).
  std::string anyCause = "?";
  uint32_t anyCauseNode = UINT32_MAX;
  std::function<void(uint32_t)> noteAnyCause;
  auto anyOf = [&](uint32_t o) -> uint32_t {
    if (objs[o].any != UINT32_MAX) return objs[o].any;
    if (noteAnyCause) noteAnyCause(o);
    const uint32_t w = newNode(), r = newNode();
    const uint32_t f = newCell({o, CellKind::Any, 0, UINT32_MAX, w, r,
                                NF.getCellNode(objs[o].origin, internName("*"))});
    objs[o].any = f;
    addEdge(w, r);
    for (auto &[c, u, pn] : objs[o].loadNodes) linkAny(f, u, pn);
    return f;
  };
  // Interior cells (a labeled object's offset inside a scalar member),
  // by the step that minted them (verbose census).
  std::map<std::string, size_t> interiorBy;
  std::string mintCause = "seed";
  size_t interiorCells = 0, beyondLabel = 0, leftObject = 0;
  // The content cell of folded offset c of object o, made on first use.
  // The content cell an offset of object o lands in: folded through its
  // layout (arrays are one element), or, unlabeled, one cell for bytes,
  // the offset modulo the learned element size, else the raw offset.
  auto contentKey = [&](const Obj &O, int64_t off) -> int64_t {
    if (!O.layout)
      return O.bytes ? 0 : O.period ? ((off % O.period) + O.period) % O.period : off;
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
  size_t splitCells = 0, keyedCells = 0;
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
    if (objs[o].any != UINT32_MAX) linkAny(objs[o].any, u, pn);
    if (objs[o].layout && !leafStart(objs[o].layout, c, DL)) {
      interiorCells++;
      interiorBy[mintCause]++;
    }
    return std::make_pair(u, pn);
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
    objs[o].keyed.emplace(kk, n);
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
      return O.bytes ? std::string("i8[]") : "?#" + std::to_string(o);
    if (O.label == "i8" || inByteArray(O.layout, c, DL))
      return "i8[]";
    return O.label + "+" + std::to_string(c);
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
  uint32_t curStepFact = UINT32_MAX, curStepNode = UINT32_MAX;
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
    return a;
  };
  // The exact address of byte `off` of object o (a heap array is one
  // element: offsets reduce modulo its size).
  auto cellAt = [&](uint32_t o, int64_t off) -> uint32_t {
    std::tie(o, off) = locate(o, off);
    Obj &O = objs[o];
    if (!O.layout) {
      // An unlabeled array of learned element size: the address reduces
      // modulo the element (bytes: to 0), as a heap object modulo its
      // struct.
      if (O.bytes) return mintOff(o, 0, false);
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
  // Some element at byte `off`: the folded address.
  auto cellAtFolded = [&](uint32_t o, int64_t off) -> uint32_t {
    return cellAt(o, off);
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
  size_t bytesLearned = 0;
  auto requestPeriod = [&](uint32_t o, int64_t s) {
    Obj &O = objs[o];
    if (O.layout || O.bytes || O.fn || s <= 0) return;
    const int64_t p = O.period ? std::gcd(O.period, s) : s;
    if (p == O.period) return;
    if (!O.period) periodsLearned++;
    O.period = p;
    refoldQueue.push_back(o);
  };
  // Byte arithmetic at offset `at` of an unknown object: bytes from `at`
  // on. At 0 the object is bytes; past 0 it is an unknown header followed
  // by a trailing bytes object (`zDb = (char *)&t[1]` in the storage after
  // a struct), so a struct learned later at 0 can still fill the header.
  std::function<void(uint32_t)> noteBytesCause; // --cfl-cell-trace-obj
  std::function<void(uint32_t, int64_t)> requestBytes;
  requestBytes = [&](uint32_t o, int64_t at) {
    std::tie(o, at) = locate(o, at);
    Obj &O = objs[o];
    if (O.layout || O.bytes || O.fn) return;
    if (at > 0) {
      if (O.tail) { // bytes from below the current boundary: move it down
        const uint32_t rest = O.tailObj; // bytes from the old boundary
        Obj M;
        M.origin = O.origin;
        M.parentObj = o;
        M.base = O.base + at;
        M.bytes = true;
        M.tail = rest != UINT32_MAX;
        M.size = O.size - at;
        M.tailObj = rest;
        objs.push_back(std::move(M));
        const uint32_t m = objs.size() - 1;
        if (rest != UINT32_MAX) objs[rest].parentObj = m;
        objs[o].tailObj = m;
        objs[o].size = at;
      } else {
        O.tail = true;
        O.size = at;
        const uint32_t t = tailOf(o);
        objs[t].bytes = true;
      }
      bytesLearned++;
      refoldQueue.push_back(o); // cells past `at` move to the trailing bytes
      return;
    }
    O.bytes = true;
    bytesLearned++;
    if (noteBytesCause) noteBytesCause(o);
    refoldQueue.push_back(o); // renames its cells i8[]
  };
  auto requestLayout = [&](uint32_t o, StructType *S) {
    Obj &O = objs[o];
    if (O.layout || O.bytes || !S || S->isOpaque() || !S->isSized()) return;
    const int64_t sz = (int64_t)DL.getTypeAllocSize(S);
    if (sz <= 0) return;
    if (O.tail) {
      // An unknown header before trailing bytes at O.size: the struct fills
      // it (sz == size) or leaves an unknown gap before them (sz < size).
      // A struct reaching into the bytes is the conflict (one-label).
      if (sz > O.size) return;
      if (sz < O.size) {
        Obj Gp;
        Gp.origin = O.origin;
        Gp.parentObj = o;
        Gp.base = O.base + sz;
        Gp.tail = true;
        Gp.size = O.size - sz;
        Gp.tailObj = O.tailObj;
        objs.push_back(std::move(Gp));
        const uint32_t g = objs.size() - 1;
        if (objs[g].tailObj != UINT32_MAX) objs[objs[g].tailObj].parentObj = g;
        objs[o].tailObj = g;
      }
      Obj &H = objs[o];
      H.layout = S;
      H.repeats = false; // a header is one object
      H.size = sz;
      H.label = typeLabel(S);
      H.learnedLayout = true;
      layoutsLearned++;
      refoldQueue.push_back(o);
      return;
    }
    O.layout = S;
    O.repeats = O.parentObj == UINT32_MAX; // a trailing struct is one object
    O.size = sz;
    O.label = typeLabel(S);
    O.learnedLayout = true;
    if (const auto *C = dyn_cast_or_null<CallBase>(NF.getValueForNode(O.origin))) {
      if (headerPlusTail(C, (uint64_t)(O.base + sz))) { O.tail = true; tailObjects++; }
      else if (O.base == 0 && exactlyOne(C, (uint64_t)sz)) O.repeats = false;
    }
    layoutsLearned++;
    refoldQueue.push_back(o);
  };
  auto canonOff = contentKey;
  auto refold = [&](uint32_t o) {
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
      std::vector<std::pair<int64_t, uint32_t>> past;
      for (auto &[key, f] : objs[o].offCells)
        if ((key >> 1) >= sz) past.push_back({key >> 1, findFact(f)});
      for (auto &[off, f] : past) {
        objs[o].offCells.erase(off * 2);
        objs[o].offCells.erase(off * 2 + 1);
        const auto [t, off2] = locate(o, off);
        for (Member &mb : memb[f])
          if (mb.first == o && decOff(mb.second) == off) mb = {t, encOff(off2, false)};
        if (cells[f].obj == o) {
          cells[f].obj = t;
          cells[f].off = off2;
          cells[f].name = internName(cellName(t, contentKey(objs[t], off2)));
        }
        auto it = objs[t].offCells.find(off2 * 2);
        if (it == objs[t].offCells.end()) objs[t].offCells[off2 * 2] = f;
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
    std::map<int64_t, std::vector<uint32_t>> byOff;
    for (auto &[key, f] : objs[o].offCells) {
      int64_t off = key >> 1;
      const Obj &O = objs[o];
      assert(!(O.tail && off >= O.size) && "moved to the trailing object above");
      if (O.repeats) off = ((off % O.size) + O.size) % O.size;
      else if (!O.layout && O.bytes) off = 0;
      else if (!O.layout && O.period) off = ((off % O.period) + O.period) % O.period;
      byOff[off].push_back(findFact(f));
    }
    objs[o].offCells.clear();
    for (auto &[off, G2] : byOff) {
      std::vector<uint32_t> fs = G2;
      std::sort(fs.begin(), fs.end());
      fs.erase(std::unique(fs.begin(), fs.end()), fs.end());
      const int64_t c = canonOff(objs[o], off);
      const uint32_t nm = internName(cellName(o, c));
      for (uint32_t f : fs) {
        for (Member &mb : memb[f])
          if (mb.first == o) mb.second = encOff(off, false);
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
      objs[o].offCells[off * 2] = surv;
    }
  };
  auto drainRefolds = [&]() {
    while (!refoldQueue.empty()) {
      const uint32_t o = refoldQueue.back();
      refoldQueue.pop_back();
      refold(o);
      // Typed now: its facts at the nodes it passed while unknown get the
      // one-label check (re-presented as pending; propagation is a no-op).
      auto pit = passedBy.find(o);
      if (pit == passedBy.end() || (!objs[o].layout && !objs[o].bytes)) continue;
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
  size_t heapLabeled = 0, heapUnlabeled = 0, heapConflict = 0;
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
      if (lit != labels.end() && lit->second.size() == 1) {
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
    if (O.layout && O.repeats)
      if (const auto *C = dyn_cast_or_null<CallBase>(V)) {
        if (headerPlusTail(C, (uint64_t)O.size)) { O.tail = true; tailObjects++; }
        else if (exactlyOne(C, (uint64_t)O.size)) O.repeats = false;
      }
    objs.push_back(std::move(O));
    return objs.size() - 1;
  };

  // ---- Seeds: functions and objects ----
  size_t funcSeeds = 0, objSeeds = 0;
  std::unordered_map<const Function *, uint32_t> funcFact;
  for (const Function *F : Ctx->AddressTakenFuncs) {
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

  // A variable index (stride s) from byte x of object o stays in the
  // innermost array holding x, arrays being one element: the same cell
  // when s is a multiple of the element, else the element's positions
  // congruent to x modulo gcd(s, element). An unlabeled object is an array
  // of s-byte elements (stride 1: bytes). An index from an address in no
  // array is undefined behavior: counted, the address stays.
  size_t indexOutsideArray = 0, indexAsOffset = 0, leafMerges = 0;
  auto strideCells = [&](uint32_t o, int64_t x, int64_t s,
                         std::vector<uint32_t> &out) {
    std::tie(o, x) = locate(o, x); // past a header: the trailing object
    Obj &O = objs[o];
    if (!O.layout) {
      if (s == 1) requestBytes(o, x);
      else requestPeriod(o, s);
      out.push_back(cellAt(o, x));
      return;
    }
    const int64_t pos = ((x % O.size) + O.size) % O.size;
    int64_t b = 0, e = 0;
    if (!innermostArray(O.layout, pos, DL, b, e)) {
      // No array holds the address: what it points to is a single object
      // (the object itself, or one embedded in it), an array of one: the
      // index stays.
      indexOutsideArray++;
      out.push_back(cellAt(o, pos));
      return;
    }
    if (s % e == 0) { out.push_back(cellAtFolded(o, pos)); return; }
    const int64_t g = std::gcd(s, e), r0 = (((pos - b) % g) + g) % g;
    for (int64_t j = r0; j < e; j += g) out.push_back(cellAtFolded(o, b + j));
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
    if (VerboseLevel >= 2)
      mintCause = (L.stride ? "stride " + std::to_string(L.stride)
                            : (L.arith ? "arith +" : "member +") +
                                  std::to_string(L.off)) +
                  (objs[C.obj].repeats ? " (heap)" : "");
    switch (C.kind) {
    case CellKind::Func:
    case CellKind::Any:
    case CellKind::Out:
      llvm_unreachable("stepOne steps offset cells only");
    case CellKind::Off: {
      const Obj &O = objs[C.obj];
      if (!O.layout && L.ty && !L.stride && !L.arith && C.off == 0) {
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
          strideCells(C.obj, C.off + L.off, (int64_t)L.stride, res);
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
        const bool inArray =
            (O.repeats && O.size == (int64_t)L.extent) ||
            inArrayOfSize(O.layout, ((C.off % O.size) + O.size) % O.size,
                          (int64_t)L.extent, DL);
        const bool index = L.arith && L.extent > 1 && L.off % L.extent == 0 &&
                           !O.tail && // &p[1] of a header block: its trailing data
                           inArray;
        if (L.arith && L.extent > 1 && L.off % L.extent == 0 && !O.tail && !inArray &&
            L.off != 0)
          indexAsOffset++;
        for (int64_t a : actual)
          res.push_back(index ? cellAt(C.obj, a) : cellAt(C.obj, a + L.off));
        break;
      }
      // Strided: a variable index stays in its array.
      for (int64_t a : actual)
        strideCells(C.obj, a + L.off, (int64_t)L.stride, res);
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
           " [" + (O.layout ? O.label : std::string("unlabeled")) +
           (O.repeats ? " array" : "") + "]";
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
  // itself), INT64_MIN when not constant.
  auto slotOffset = [&](const Value *Slot) -> int64_t {
    const auto *G = dyn_cast<GEPOperator>(Slot->stripPointerCasts());
    if (!G) return 0;
    APInt A(64, 0);
    return G->accumulateConstantOffset(DL, A) ? A.getSExtValue() : INT64_MIN;
  };
  struct RecvSite {
    const CallBase *cs;
    unsigned k;
    uint32_t base, callee;
    std::vector<uint32_t> lis; // per level: the field step (UINT32_MAX: none)
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
    for (const CallBase *CS : Ctx->IndirectCallInsts) {
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
        const NodeIndex vn = NF.getValueNodeFor(V), sn = NF.getValueNodeFor(Slot);
        uint32_t li = UINT32_MAX;
        bool stepped = vn != AndersNodeFactory::InvalidIndex &&
                       (sn == AndersNodeFactory::InvalidIndex ||
                        find(canon(sn)) == find(canon(vn)));
        if (!stepped && vn != AndersNodeFactory::InvalidIndex)
          for (const FieldEdge &e : fieldOut[find(canon(vn))])
            if (!e.walk && find(e.dst) == find(canon(sn))) {
              li = e.li;
              stepped = true;
              break;
            }
        R.all |= !stepped;
        R.lis.push_back(li);
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
    std::vector<uint32_t> slots;
    if (R.lis[level] == UINT32_MAX || C.kind == CellKind::Any) slots.push_back(g);
    else
      for (size_t i = 0; i < memb[g].size(); i++) {
        const Member mb = memb[g][i];
        const std::vector<uint32_t> &S = stepOne(mb.first, mb.second, R.lis[level]);
        slots.insert(slots.end(), S.begin(), S.end());
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
      if (R.all) continue; // plain edges: merges keep them
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
      const uint32_t formal = find(canon(fv));
      if (recordWhy) curWhy = {R.base, K.f, F, W_DISPATCH};
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
  size_t guardHeldFacts = 0, guardDropped = 0;
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
  if (CFLCellReceivers && !recvSites.empty()) {
    // Callers of each function (the previous iterations' call graph).
    boost::unordered_flat_map<const Function *, std::vector<const CallBase *>> callers;
    for (auto &[CS, FS] : Ctx->Callees)
      for (const Function *F : FS) callers[F].push_back(CS);
    boost::unordered_flat_map<const CallBase *, uint32_t> siteOf;
    for (uint32_t si = 0; si < recvSites.size(); si++) siteOf[recvSites[si].cs] = si;
    boost::unordered_flat_set<const Function *> done;
    guardIdx.assign(numNodes, UINT32_MAX);
    for (uint32_t si = 0; si < recvSites.size(); si++) {
      const RecvSite &R = recvSites[si];
      if (R.all || R.lis.size() < 2) continue;
      auto cit = Ctx->Callees.find(R.cs);
      if (cit == Ctx->Callees.end()) continue;
      for (const Function *F : cit->second) {
        if (!done.insert(F).second || F->isDeclaration() || R.k >= F->arg_size()) continue;
        bool uniform = true; // every call of F: a dispatch site of this shape
        for (const CallBase *C : callers[F]) {
          auto sit = siteOf.find(C);
          uniform &= sit != siteOf.end() && !recvSites[sit->second].all &&
                     recvSites[sit->second].sig == R.sig;
        }
        if (!uniform) continue;
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
          if (guardIdx[n] != UINT32_MAX) continue;
          guardIdx[n] = guards.size();
          guards.push_back({F, si, n, {}});
        }
      }
    }
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

  // ---- Propagation (difference propagation over a worklist) ----
  const auto tSolve = Clock::now();
  uint64_t walkSteps = 0;
  size_t hubLinks = 0, funcDerefs = 0, outDerefs = 0;
  auto linkHub = [&](uint32_t h, uint32_t f) {
    const Cell &C = cells[findFact(f)];
    if (C.kind == CellKind::Func) { funcDerefs++; return; }
    if (C.kind == CellKind::Out) { outDerefs++; return; }
    hubLinks++;
    uint32_t ld = C.load, st = C.store;
    auto kit = cellHubKey.find(h);
    if (kit != cellHubKey.end() && C.kind == CellKind::Off) {
      // A keyed union access: its key's cell, for every member object.
      for (auto [o, e] : memb[findFact(f)]) {
        const uint32_t K = keyedOf(o, contentKey(objs[o], decOff(e)), kit->second);
        addEdge(K, h);
        if (storeHub[h] != UINT32_MAX) addEdge(storeHub[h], K);
      }
      return;
    }
    addEdge(ld, h);
    if (storeHub[h] != UINT32_MAX) addEdge(storeHub[h], st);
  };
  // The any-offset cells of every object a cell stands for, into dst.
  auto toAny = [&](uint32_t f, uint32_t dst) {
    anyCause = "field-any loop";
    anyCauseNode = dst;
    if (cells[f].kind == CellKind::Out) return; // outside stays outside
    for (auto [o, e] : memb[f])
      if (!objs[o].layout) requestBytes(o, 0); // a variable i8 index into it
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
    // its member offset first.
    const LazyLabel &L = lazyLabels[li];
    strideCells(o, decOff(c) + (L.arith || L.stride ? 0 : L.off), g, walkOut);
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
  auto nodeDesc = [&](uint32_t m) -> std::string {
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
    } else if (NF.isDereferenceNode(m) || NF.isObjectNode(m)) {
      k = "hub of #" + std::to_string(NF.getDerefParent(m));
      const NodeIndex par = NF.getDerefParent(m);
      if (par != AndersNodeFactory::InvalidIndex)
        if (const auto *I = dyn_cast_or_null<Instruction>(NF.getValueForNode(par)))
          k += " (" + I->getFunction()->getName().str() + ")";
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
  noteBytesCause = [&](uint32_t o) {
    if (CFLCellTraceObj.empty() ||
        describe(objs[o]).find(CFLCellTraceObj) == std::string::npos)
      return;
    CG_LOG("Cells: BYTES " << describe(objs[o]) << " from offset 0, at "
           << (anyCauseNode == UINT32_MAX ? std::string("?") : nodeDesc(anyCauseNode))
           << " (" << mintCause << ")\n");
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
    Obj &O = objs[o];
    if (!O.layout) {
      if (!O.bytes && !O.period) requestBytes(o, a);
      if (O.bytes) return 1;
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
  size_t copyPairs = 0, copyEdges = 0, effectiveTyped = 0;
  auto copyRegion = [&](uint32_t os, int64_t a, uint32_t od, int64_t b,
                        int64_t len, const Instruction *at) {
    // Effective type (C11 6.5p6): a copy into an object with no declared
    // type gives it the source's type. An unknown destination copied into
    // from its start learns the struct the source region starts with.
    if (!objs[od].layout && !objs[od].bytes && b == 0 && objs[os].layout) {
      const Obj &Os = objs[os];
      const int64_t fa = Os.repeats ? ((a % Os.size) + Os.size) % Os.size : a;
      if (StructType *S = structAt(Os.layout, fa, DL)) {
        requestLayout(od, S);
        if (objs[od].layout) effectiveTyped++;
      }
    }
    // A copy between two structs is compatible when one starts where the
    // other is (equal, or embedded: base and derived). Otherwise the
    // program copies one struct over an unrelated one: report it (in
    // one-label stop mode, stop); the bytes are still copied.
    if (objs[os].layout && objs[od].layout) {
      const Obj &Os = objs[os], &Od = objs[od];
      const int64_t fa = Os.repeats ? ((a % Os.size) + Os.size) % Os.size : a;
      const int64_t fb = Od.repeats ? ((b % Od.size) + Od.size) % Od.size : b;
      StructType *Ss = structAt(Os.layout, fa, DL), *Sd = structAt(Od.layout, fb, DL);
      auto startsIn = [&](StructType *S, Type *T, int64_t off) {
        return S->hasName() &&
               structStartsAt(T, off, stripStructNameSuffix(S->getName()), DL, S);
      };
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
    std::set<std::tuple<uint32_t, int64_t, uint32_t, int64_t>> seenAt;
    for (int64_t k = 0; k < L; k++) {
      // Past a header: the trailing object (located per position).
      const auto [so, sa] = locate(os, a + k);
      const auto [dob, db] = locate(od, b + k);
      const Obj &Os = objs[so], &Od = objs[dob];
      if (Os.layout && !Os.repeats && (sa < 0 || sa >= Os.size)) break;
      if (Od.layout && !Od.repeats && (db < 0 || db >= Od.size)) break;
      const int64_t sk = contentKey(Os, sa), dk = contentKey(Od, db);
      if (!seenAt.insert({so, sk, dob, dk}).second) continue;
      if (!Os.layout && !Os.bytes && Os.content.size() >= CFLCellCap &&
          !Os.content.count(sk))
        continue; // capped: its any-offset cell already reads everything
      const auto [su, sp] = contentOf(so, sk);
      const auto [du, dp] = contentOf(dob, dk);
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
      addEdge(S.load, D.store); // any offset: everything to everything
      return;
    }
    const std::vector<Member> ms = memb[fs], md = memb[fd];
    curCopyDst = find(copies[ci].dst);
    curCopySrcFact = fs;
    if (recordWhy) curWhy = {ci, fs, fd, W_COPY};
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
  uint64_t lastCollapsePops = 0;
  size_t edgesAtCollapse = edgeSet.size();
  while (true) {
    if (!refoldQueue.empty()) drainRefolds();
    if (worklist.empty()) {
      if (CFLCellOneLabel) flushPending(true);
      break;
    }
    const uint32_t n = worklist.back();
    worklist.pop_back();
    inWL[n] = 0;
    if (find(n) != n) continue; // merged: its facts moved to the rep
    if (CFLCellCensusAt && pops >= CFLCellCensusAt) {
      confluenceCensus();
      errs() << "Cells: --cfl-cell-census-at stopped the solve (measurement "
             << "only, no answers)\n";
      exit(0);
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
      if (pops % (1u << 22) == 0) massByObject(12);
    }
    for (uint32_t &f : delta) f = findFact(f);
    if (!dispatchOf.empty() && dispatchOf.count(n)) {
      dispatch(n, delta);
      continue;
    }
    if (!recvAt.empty()) {
      auto rit = recvAt.find(n);
      if (rit != recvAt.end())
        for (uint32_t si : std::vector<uint32_t>(rit->second))
          for (uint32_t f : delta) {
            if (recordWhy) curWhy = {n, f, UINT32_MAX, W_DISPATCH};
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
          unknown &= !objs[o].layout && !objs[o].bytes;
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
          if (recordWhy) curWhy = {n, f, UINT32_MAX, W_HUB};
          linkHub(h, f);
        }
      curStepNode = n;
      anyCauseNode = n;
      for (size_t ei = 0; ei < fieldOut[n].size(); ei++) {
        const FieldEdge e = fieldOut[n][ei];
        for (uint32_t f : delta) {
          if (recordWhy) curWhy = {n, f, UINT32_MAX, e.walk ? W_WALK : W_STEP};
          if (e.walk) applyWalk(f, e);
          else applyStep(f, e.li, e.dst);
        }
      }
      if (anyLoop[n])
        for (uint32_t f : delta) {
          const CellKind k = cells[f].kind;
          if (recordWhy) curWhy = {n, f, UINT32_MAX, W_ANY};
          if (k == CellKind::Off || k == CellKind::Out)
            toAny(f, n);
        }
    }
    if (!copiesAt[n].empty()) applyCopies(n, delta);
    for (uint32_t m : succ[n])
      for (uint32_t f : delta) {
        if (recordWhy) curWhy = {n, f, UINT32_MAX, W_EDGE};
        add(m, f);
      }
    curWhy = Why();
    if (VerboseLevel >= 2 && pops % (1u << 16) == 0)
      CG_LOG("Cells: at " << pops << " pops: " << finalizes << " finalizes re-ran "
             << refacts << " facts; " << factMerges << " fact merges, "
             << ptrMerges << " ptr merges, " << hubLinks << " hub links\n");
    if (pops - lastCollapsePops >= (1u << 18) &&
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
  if (CFLCellOneLabel && CFLCellOneLabelMax > 1) finishCollect();
  dynEdges = edgeSet.size() - staticCopies - stores;
  const double solveSecs =
      std::chrono::duration<double>(Clock::now() - tSolve).count();

  // ---- Answers ----
  size_t resolved = 0, totalTargets = 0, newPairs = 0, typeRej = 0;
  const std::vector<const CallBase *> icallSnapshot(
      Ctx->IndirectCallInsts.begin(), Ctx->IndirectCallInsts.end());
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
    for (const Function *F : targets)
      if (wireResolvedCallee(CS, F)) newPairs++;
  }

  // ---- Report ----
  size_t factMass = 0, offCells = 0, anyCells = 0;
  for (uint32_t n = 0; n < numNodes; n++) factMass += pts[n].count();

  CG_LOG("Cells: " << walkEdges << " field edges on cycles (pointer walks), "
         << walkSteps << " walk steps, " << indexOutsideArray
         << " variable indexes on a single object (array of one), " << indexAsOffset
         << " constant indexes outside an array of their element (byte offsets), "
         << leafMerges << " same-leaf coexistences (unmerged); "
         << "learned " << layoutsLearned << " layouts, " << periodsLearned
         << " element sizes, " << bytesLearned << " byte arrays ("
         << refoldMerges << " cells merged by re-folding)\n");
  if (CFLCellUnify) canonicalizeSets();
  CG_LOG("Cells: " << leftObject << " byte offsets leaving a single "
         << "object (outside: one past the end, never dereferenced)\n");
  CG_LOG("Cells: " << cellHubKey.size() << " keyed union accesses, "
         << splitCells << " union-slot cells, " << keyedCells
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
          how = "static copy edge";
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
           << " holder reloads guarded in methods (" << guardHeldFacts
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
         << " ptrtoints used as numbers only (no field-any loop); " << g_carves
         << " carved regions (one past an array, used as another type; see CARVE lines); "
         << g_freeDropped << " deallocator stores into or of the freed block (FREE)\n");
  CG_LOG("Cells: " << factMerges << " cells unified by name ("
         << retiredDropped << " retired ids dropped from sets), "
         << ptrMerges << " pointer nodes merged by equal sets\n");
  CG_LOG("Cells: " << collapses << " cycle collapses merged "
         << collapsedNodes << " solver nodes (" << collapseSecs << " s)\n");
  for (const Cell &C : cells) {
    offCells += C.kind == CellKind::Off;
    anyCells += C.kind == CellKind::Any;
  }
  const double secs =
      std::chrono::duration<double>(Clock::now() - t0).count();
  CG_LOG("Cells: iteration " << iteration << ": " << objs.size()
         << " origins (" << funcSeeds << " function seeds, " << objSeeds
         << " objects (" << tailMinted << " trailing, " << tailMoved
         << " cells moved to them); heap " << heapLabeled << " labeled (" << tailObjects
         << " header + trailing data), " << heapUnlabeled
         << " unlabeled, " << heapConflict << " with conflicting labels), "
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
