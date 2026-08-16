#ifndef KA_BITPLANE_H
#define KA_BITPLANE_H

// Self-contained dense bit plane for the flows-to FactSet (2026-08-15).
// Replaces llvm::BitVector inside FactSet: LLVM's word storage is
// private (BitWord typedef and getData() churn across releases), and
// the fused delta-OR kernels need honest mutable word access. This
// mirrors exactly the llvm::BitVector API surface FactSet consumes —
// size/resize/test/set/reset (bit, all, andn)/|=/&=/<<=/count/none/
// find_first/find_next — plus words()/numWords() for the kernels.
// Invariant: bits at positions >= size() in the last word are ZERO
// (maintained by resize/shift; word writers must preserve it — the
// fused kernels do, because their sources honor the same invariant).

#include <cassert>
#include <cstdint>
#include <cstring>
#include <vector>

namespace ka {

class BitPlane {
  std::vector<uint64_t> W;
  uint32_t NBits = 0;

  void clearTail() {
    if (NBits & 63u)
      W[NBits >> 6] &= (1ull << (NBits & 63u)) - 1;
  }

public:
  BitPlane() = default;
  explicit BitPlane(uint32_t bits) : W((bits + 63u) >> 6, 0), NBits(bits) {}

  uint32_t size() const { return NBits; }
  size_t numWords() const { return W.size(); }
  const uint64_t *words() const { return W.data(); }
  uint64_t *words() { return W.data(); }
  size_t capBytes() const { return W.capacity() * sizeof(uint64_t); }

  void resize(uint32_t bits) {
    W.resize((bits + 63u) >> 6, 0);
    const uint32_t old = NBits;
    NBits = bits;
    if (bits < old)
      clearTail(); // shrink: drop bits past the new size
  }

  bool none() const {
    for (uint64_t w : W)
      if (w)
        return false;
    return true;
  }
  size_t count() const {
    size_t c = 0;
    for (uint64_t w : W)
      c += (size_t)__builtin_popcountll(w);
    return c;
  }
  bool test(uint32_t i) const {
    assert(i < NBits);
    return (W[i >> 6] >> (i & 63u)) & 1u;
  }
  void set(uint32_t i) {
    assert(i < NBits);
    W[i >> 6] |= 1ull << (i & 63u);
  }
  void reset(uint32_t i) {
    assert(i < NBits);
    W[i >> 6] &= ~(1ull << (i & 63u));
  }
  void reset() { std::memset(W.data(), 0, W.size() * sizeof(uint64_t)); }
  // this &= ~o (width-safe: only overlapping words are affected)
  BitPlane &reset(const BitPlane &o) {
    const size_t n = W.size() < o.W.size() ? W.size() : o.W.size();
    for (size_t i = 0; i < n; i++)
      W[i] &= ~o.W[i];
    return *this;
  }
  // self-widening OR (llvm::BitVector semantics)
  BitPlane &operator|=(const BitPlane &o) {
    if (NBits < o.NBits)
      resize(o.NBits);
    for (size_t i = 0; i < o.W.size(); i++)
      W[i] |= o.W[i];
    return *this;
  }
  // intersect; our words beyond o's width become zero (llvm semantics)
  BitPlane &operator&=(const BitPlane &o) {
    const size_t n = W.size() < o.W.size() ? W.size() : o.W.size();
    for (size_t i = 0; i < n; i++)
      W[i] &= o.W[i];
    for (size_t i = n; i < W.size(); i++)
      W[i] = 0;
    return *this;
  }
  // shift toward higher bit positions; size FIXED, high bits drop
  // (llvm::BitVector semantics — callers widen first)
  BitPlane &operator<<=(uint32_t nbits) {
    if (nbits == 0 || W.empty())
      return *this;
    assert(nbits <= NBits);
    const uint32_t ws = nbits >> 6, bs = nbits & 63u;
    const size_t n = W.size();
    if (bs == 0) {
      for (size_t i = n; i-- > ws;)
        W[i] = W[i - ws];
    } else {
      for (size_t i = n; i-- > ws;) {
        uint64_t w = W[i - ws] << bs;
        if (i > ws)
          w |= W[i - ws - 1] >> (64u - bs);
        W[i] = w;
      }
    }
    for (uint32_t i = 0; i < ws && i < n; i++)
      W[i] = 0;
    clearTail();
    return *this;
  }
  int find_first() const { return find_next(-1); }
  int find_next(int prev) const {
    size_t wi = (size_t)(prev + 1) >> 6;
    if (wi >= W.size())
      return -1;
    uint64_t w = W[wi] & ~((prev + 1) & 63
                               ? (1ull << ((prev + 1) & 63)) - 1
                               : 0ull);
    while (true) {
      if (w)
        return (int)((wi << 6) + (size_t)__builtin_ctzll(w));
      if (++wi >= W.size())
        return -1;
      w = W[wi];
    }
  }
  bool operator==(const BitPlane &o) const {
    return NBits == o.NBits && W == o.W;
  }
};

} // namespace ka

#endif
