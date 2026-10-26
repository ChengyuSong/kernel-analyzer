//===-- DeferredText.h - a text built only where it is printed ---*- C++ -*-===//
//
// Printing an llvm::Value without a slot tracker numbers the whole module
// (every metadata node) on each call: on httpd, IR text built for reasons
// that no log line at --verbose=1 prints was ~94% of the run (ST). A
// DeferredText holds a head, built at once (literals, locations: no IR
// printing), and a tail that builds the rest when str() is called, with
// the same printing call as before, so a printed text is unchanged. The
// tail captures literals and IR pointers by value, never references into
// containers; the IR is not changed between the store and the print.
//
//===----------------------------------------------------------------------===//
#ifndef KA_DEFERREDTEXT_H
#define KA_DEFERREDTEXT_H

#include <llvm/IR/Value.h>
#include <llvm/Support/raw_ostream.h>
#include <functional>
#include <string>
#include <utility>

class DeferredText {
  std::string Head;
  std::function<std::string()> Tail;

public:
  DeferredText() = default;
  DeferredText(std::string H) : Head(std::move(H)) {}
  DeferredText(const char *H) : Head(H) {}
  DeferredText(std::string H, std::function<std::string()> T) : Head(std::move(H)), Tail(std::move(T)) {}
  // The part built at once (its first word names the kind of reason).
  const std::string &head() const { return Head; }
  // The whole text: builds the tail now.
  std::string str() const { return Tail ? Head + Tail() : Head; }
  // A literal prefix: still deferred.
  friend DeferredText operator+(const std::string &P, const DeferredText &D) { return {P + D.Head, D.Tail}; }
};

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const DeferredText &D) { return OS << D.str(); }

// What `os << V` prints, as a string.
inline std::string irPrint(const llvm::Value &V) {
  std::string t;
  llvm::raw_string_ostream os(t);
  os << V;
  return os.str();
}

#endif
