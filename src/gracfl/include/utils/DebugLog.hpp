#pragma once
// Debug/progress logging gate for the vendored GraCFL engine.
// Silent by default: per-iteration progress lines and banners cost
// real I/O (std::endl flushes) inside timed solves. Set
// GRACFL_VERBOSE=1 in the environment to restore the output.
// Error reporting (std::cerr) is NOT routed through this gate.
#include <cstdlib>
#include <iostream>

namespace gracfl {
inline std::ostream &dbg() {
  struct NullBuf : std::streambuf {
    int overflow(int c) override { return c; }
  };
  static NullBuf nullBuf;
  static std::ostream nullStream(&nullBuf);
  static const bool on = [] {
    const char *e = std::getenv("GRACFL_VERBOSE");
    return e && *e && *e != '0';
  }();
  return on ? std::cout : nullStream;
}
} // namespace gracfl
