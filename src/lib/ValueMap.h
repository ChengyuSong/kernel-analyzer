//===-- ValueMap.h - a flat map that hands out no references ----*- C++ -*-===//
//
// A flat map (boost::unordered_flat_map underneath) whose lookups return
// copies and whose in-place access runs a callback: no iterator or
// reference into it can be held across an insert into it, which in a flat
// map rehashes and frees the storage (the kernel census use-after-free,
// plan 3.53). Inserts inside a callback on the same map are refused
// (assertion): the callback's reference would dangle.
//
//===----------------------------------------------------------------------===//
#ifndef KA_VALUEMAP_H
#define KA_VALUEMAP_H

#include <boost/unordered/unordered_flat_map.hpp>
#include <cassert>
#include <optional>
#include <utility>

template <class K, class V, class H = boost::hash<K>> class ValueMap {
  boost::unordered_flat_map<K, V, H> M;
  mutable unsigned Busy = 0; // callbacks running on this map
  struct InCallback {
    unsigned &B;
    explicit InCallback(unsigned &B) : B(B) { ++B; }
    ~InCallback() { --B; }
  };

public:
  // The value at K, copied out; nothing if absent.
  std::optional<V> get(const K &Key) const {
    auto It = M.find(Key);
    if (It == M.end()) return std::nullopt;
    return It->second;
  }
  size_t count(const K &Key) const { return M.count(Key); }
  bool empty() const { return M.empty(); }
  size_t size() const { return M.size(); }
  // Insert V at K when absent (V computed before the call); true if new.
  bool insert(const K &Key, V Val) {
    assert(!Busy && "ValueMap: insert inside a callback on the same map");
    return M.try_emplace(Key, std::move(Val)).second;
  }
  // Read V at K in place, if present (Fn must not insert into this map).
  template <class F> bool with(const K &Key, F &&Fn) const {
    auto It = M.find(Key);
    if (It == M.end()) return false;
    InCallback G(Busy);
    Fn(static_cast<const V &>(It->second));
    return true;
  }
  // Modify V at K in place, default-constructed when absent (Fn must not
  // insert into this map).
  template <class F> void update(const K &Key, F &&Fn) {
    assert(!Busy && "ValueMap: insert inside a callback on the same map");
    V &Ref = M[Key];
    InCallback G(Busy);
    Fn(Ref);
  }
  // Every entry (Fn must not insert into this map).
  template <class F> void forEach(F &&Fn) const {
    InCallback G(Busy);
    for (const auto &[Key, Val] : M) Fn(Key, Val);
  }
};

#endif
