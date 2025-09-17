#ifndef ANDERSEN_PTSSET_H
#define ANDERSEN_PTSSET_H

#include <boost/unordered/unordered_flat_set.hpp>
#include <algorithm>

class AndersPtsSet {
private:
  boost::unordered_flat_set<std::size_t> _set;

public:

  AndersPtsSet() = default;
  AndersPtsSet(const AndersPtsSet &S) : _set(S._set) {}
  ~AndersPtsSet() = default;

  const bool has(std::size_t idx) const {
    return _set.contains(idx);
  }

  bool insert(std::size_t idx) {
    return _set.insert(idx).second;
  }

  bool insert(const AndersPtsSet &S) {
    if (S.isEmpty()) return false;

    std::size_t oldSize = _set.size();
    _set.insert(S._set.begin(), S._set.end());
    return _set.size() > oldSize;
  }

  void reset(std::size_t idx) {
    _set.erase(idx);
  }

  void clear() {
    _set.clear();
  }

  std::size_t getSize() const {
    return _set.size();
  }

  bool isEmpty() const {
    return _set.empty();
  }

  // Iterator support
  auto begin() { return _set.begin(); }
  auto end() { return _set.end(); }
  auto begin() const { return _set.begin(); }
  auto end() const { return _set.end(); }
};

#endif //ANDERSEN_PTSSET_H
