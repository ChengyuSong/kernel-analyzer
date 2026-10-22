#ifndef KA_ALLOC_EXTENTS_H
#define KA_ALLOC_EXTENTS_H

// Allocation sizes (plan 3.53, ruling B; the A2' carve forms) and the IR
// helpers the extent rules read them with (rule 1, A1, gap 2, the size
// label): shared by the cell solver's mint (CellSolver.cc) and what must
// know an allocation's extent before the solve. AllocExtents.cc.

#include "CallGraph.h"
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace ka {
// Does a struct named like S start at offset `off` of T (through nested
// members and array elements)? An anonymous struct's name names nothing
// (isAnonStruct): it is found only as the type Same itself, or one of its
// layout.
bool structStartsAt(llvm::Type *T, int64_t off, llvm::StringRef S, const llvm::DataLayout &DL,
                    const llvm::StructType *Same = nullptr);

// The element type of the trailing array T ends in, or null: its last
// member, recursively, an array of 0 or 1 elements ending at T's end (the
// flexible-array idiom `x[0]` / `x[1]`; an array declared longer is a
// field of its own, and what follows it is a segment, labeled by its use).
llvm::Type *trailingArrayElem(llvm::Type *T, const llvm::DataLayout &DL, uint64_t *n = nullptr);

// The last store into slot S at or before I, walking back in I's block.
const llvm::StoreInst *lastStoreFrom(const llvm::Instruction *I, const llvm::AllocaInst *S);

// The last store into S in BB, and the last one before L in L's block.
const llvm::StoreInst *lastStoreIn(const llvm::BasicBlock *BB, const llvm::AllocaInst *S);

const llvm::StoreInst *lastStoreBefore(const llvm::Instruction *L, const llvm::AllocaInst *S);

// The store into S reaching BB's end: BB's last, else up a chain of single
// predecessors (not through `stop`, the block a load is in).
const llvm::StoreInst *storeAtEnd(const llvm::BasicBlock *BB, const llvm::AllocaInst *S, const llvm::BasicBlock *stop);

// Is A a slot (only loaded, and stored into by value)? *several: stored
// more than once; *only: its store when once.
bool sizeSlot(const llvm::AllocaInst *A, bool &several, const llvm::StoreInst *&only);

// The one store reaching load L of slot S stored several times: the last
// store before L in its block, else in the nearest block up a chain of
// single predecessors, else the store every predecessor's chain reaches
// (all the same one), else, when every store is in the entry block, the
// last one there. Null when none of these decides it.
const llvm::StoreInst *reachingStore(const llvm::LoadInst *L, const llvm::AllocaInst *S);

// An allocation size's source: through casts, and at -O0 a local slot that
// never escapes (its only users are direct loads and stores into it: no
// call can write it through its address) forwards the stored value
// reaching the load (sqlite3: nByte = sizeof(Fts3SegReader) +
// (nElem+1)*sizeof(Fts3HashElem *); malloc(nByte); fts3InitVtab reuses
// nByte; newchunk rounds n at entry).
const llvm::Value *sizeThrough(const llvm::Value *V);

// Is size expression X a multiple of sz: a constant multiple (nonzero: a
// size, not a flag), or a product (or shift) with one?
bool isMultipleOf(const llvm::Value *X, uint64_t sz, bool nonzero = false);

// Does an allocation call's size argument say "a T followed by trailing
// data": a constant larger than T and not a multiple of it, or a sum (any
// depth: -O3 chains `sizeof(T) + 8*n + 40*m + k`) with a constant term of
// at least sizeof(T) and some other term that is not a multiple of it
// (`n*sizeof(T) + sizeof(T)` is an array of n+1)? The size is add + the
// product of ops (a wrapper's term `n + 16` at its call `w(len)`: len
// read as above, 16 one more constant term).
bool headerPlusTail(const std::vector<const llvm::Value *> &ops, uint64_t sz, int64_t add = 0);

// Does an allocation call allocate exactly sz bytes (its integer
// arguments all constants, multiplying to sz: malloc(64), calloc(1, 64))?
// Then it is one T, not an array of T.
bool exactlyOne(const std::vector<const llvm::Value *> &ops, uint64_t sz, int64_t add = 0);

// Does an allocation call's size say "an array of T": an integer argument
// that is a multiple of sizeof(T) (calloc(n, sizeof T), malloc(n * sizeof
// T), realloc(p, k * sizeof T))?
bool sizeIsMultiple(const std::vector<const llvm::Value *> &ops, uint64_t sz, int64_t add = 0);

std::string typeLabel(llvm::Type *T);

} // namespace ka

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
struct CallGraphPass::SizeTerms {
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
  SizeTerms(CallGraphPass &Pass, const llvm::DataLayout &Layout);
  CallGraphPass &P;
  const llvm::DataLayout &DL;
  std::function<bool(const SizeTerm &)> nonzero;
  std::function<SizeTerm(uint64_t)> constT, multiple;
  std::function<uint64_t(const SizeTerm &)> multOf;
  std::function<SizeTerm(SizeTerm)> norm;
  std::function<SizeTerm(SizeTerm, const SizeTerm &)> plusT;
  std::function<SizeTerm(const SizeTerm &, int64_t)> plusK;
  std::function<SizeTerm(SizeTerm, SizeTerm)> timesT;
  std::function<SizeTerm(SizeTerm, uint64_t)> alignT;
  std::function<SizeTerm(const SizeTerm &, const SizeTerm &)> joinT;
  std::function<bool(llvm::StringRef, std::vector<unsigned> &)> sigOf;
  // V's term in F's formals.
  std::function<SizeTerm(const llvm::Value *, const llvm::Function *, int)> termIn;
  std::function<SizeTerm(const llvm::CallBase *, const llvm::Function *)> callTerm;
  std::function<SizeTerm(const llvm::Instruction *)> carveTerm;
  std::function<SizeTerm(const llvm::Function *)> termOfFn;
  std::function<bool(const llvm::Value *, std::vector<const llvm::Value *> &, int64_t &)> sizeOps;
  std::function<llvm::StructType *(const llvm::CallBase *, const llvm::StructType *, int64_t, size_t &)> containerOfSize;
  std::set<const llvm::Instruction *> sizeZextMask; // A2' (4): masks 2^k - al read as -al
  std::unordered_map<const llvm::Function *, SizeTerm> termMemo;
  std::set<const llvm::Function *> termBusy;
  // A2' counters: carves sized by "n, K when n == 0", by header-then-store,
  // carve phis read by their carve term, zext masks read as -al.
  std::set<const llvm::Instruction *> sizeWhenZero, sizeHeaderStore, sizeCarvePhi;
  std::set<const llvm::Instruction *> carveUnknownSize;
  // Allocations sized by a product through a zero-guarded wrapper (row
  // (2): bfd_alloc2(abfd, n, 72) = a multiple of 72).
  std::set<const llvm::CallBase *> zeroProductSites;
  // While a heapMint runs: the per-site counts it makes (zeroProductSites
  // inserts, sizeLabelAmbiguous keys), so a mint read from the table counts
  // them as the mint did.
  std::vector<const llvm::CallBase *> *zeroNote = nullptr;
  std::vector<std::string> *ambiguousNote = nullptr;
  std::map<std::string, size_t> sizeLabelAmbiguous; // "S at k: {candidates}" -> objects

  // A5b (Fable 2026-10-21): the size of a kmem_cache_alloc,
  // kmem_cache_zalloc or kmem_cache_alloc_node call is its cache's object
  // size when the cache is a load of a global whose one write (null
  // initializer, every other use a load) stores a kmem_cache_create or
  // kmem_cache_create_usercopy call with a constant size; the global
  // internal or the run whole-program (then its every module's copy is
  // read). 'n': not such a call; 's': *S; 'r': refused, *why.
  char cacheSize(const llvm::CallBase *C, uint64_t &S, std::string &why);

  // The extent a label covers (plan 3.53, rule 1): a T at the start, and
  // what the allocation's size says of the rest, for a label whose end is
  // byte `at` of the allocation V. A constant or a multiple of T's size is
  // an array of T; one T exactly is one; T plus trailing data, or a size
  // that says nothing (a wrapper's argument, a length read from input), is
  // a header followed by an unknown trailing object; a multiple of a struct
  // ending in a flexible array member is its header and tail (gap 2).
  struct Extent {
    bool tail = false, repeats = false, tailUnsized = false;
    char kind = 0; // 'h' header + tail, '1' one, 'a' array, 'f' FAM header + tail, 'u' unknown
    bool promotedUnknown = false; // a fresh wrapper whose size term is unknown
  };
  Extent extentOf(llvm::Type *layout, uint64_t at, const llvm::Value *V);

  // What a heap allocation call is minted as, from its site labels L (null:
  // none; the label reduction to the outermost of labels at offset 0 is
  // applied to *L): its layout, label, identity and extent, and what the
  // mint counts for it.
  struct HeapMint {
    llvm::Type *layout = nullptr;
    int64_t size = 0;
    std::string label, ident;
    bool repeats = false, declArray = false, declScalar = false, byteAccessed = false;
    bool tail = false, tailUnsized = false;
    // 'p' an array of pointer slots, 's' of a declared scalar, 'l' one
    // struct, 'x' a struct name the IR does not have, 'c' a conflict, 'n'
    // no label.
    char labelKind = 'n';
    bool bytesMarked = false, anon = false, containerRelabeled = false, containerAmbiguous = false;
    // A4: 'm' a merged-away identity applied (merged: it named the
    // object), 'd' its size is not the label's, 'n' no debug type at any
    // site.
    char a4 = 0;
    bool merged = false;
    bool identNoted = false; // ident was set by a debug identity (counted per IR label / identity pair)
    bool extentSet = false;
    Extent extent;
    // A5a: 'r' the container the site's receiver declares, 'c' a conflict
    // (readings: the row's text, "k x L (sz) vs C (S), ...").
    char readings = 0;
    std::string readingsRow;
    // A5b: a slab object is one object of its cache's size. 'l' the label
    // is that size; 'r' named by the one struct of that size embedding the
    // label at 0; 'c' several such structs, 'n' none (both unlabeled, a
    // conflict); 'u' no mint label; 'k' a declared array, kept; 'x' the
    // cache's size refused. cacheRow: the row's text (the cache, its size,
    // the candidates; or why refused).
    char cache = 0;
    std::string cacheRow;
    // Per-site counts the mint made (see zeroNote, ambiguousNote).
    std::vector<const llvm::CallBase *> zeroProduct;
    std::vector<std::string> ambiguous;
    bool sameObject(const HeapMint &o) const {
      return layout == o.layout && size == o.size && label == o.label && ident == o.ident && repeats == o.repeats &&
             declArray == o.declArray && declScalar == o.declScalar && byteAccessed == o.byteAccessed &&
             tail == o.tail && tailUnsized == o.tailUnsized;
    }
  };
  HeapMint heapMint(const llvm::CallBase *C, std::set<std::string> *L);
};

struct CallGraphPass::MintTable {
  std::unordered_map<const llvm::CallBase *, SizeTerms::HeapMint> at;
  std::vector<const llvm::CallBase *> order; // the entries in IR order
  // The table's evaluator: its memo-level counts are the heap part of the
  // log's size-term counts (the solve's evaluator counts the carves).
  std::unique_ptr<SizeTerms> terms;
};

#endif
