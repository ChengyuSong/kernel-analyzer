#!/usr/bin/env bash
# The AddressSanitizer gate: run before any commit touching
# src/lib/CellSolver.cc, FlowsToSolver.cc or the census/profiler code.
# Builds (or reuses) the sanitizer build directory asan/ (NOT release/:
# -fsanitize=address -fno-omit-frame-pointer, Release flags otherwise,
# jemalloc replaced by libdl so ASan sees every allocation), then runs
# test/cells-cases.sh, the small cells pins (libpng, cjpeg-O0, djpeg-O0)
# and test/asan-census.sh (tcpdump with the census instruments) against
# it. Fails on any sanitizer report or nonzero exit.
set -u
cd "$(dirname "$0")/.."
ROOT=$(pwd)
LLVM=${LLVM_BUILD:-/usr/lib/llvm-18}
R=${SOK_BC:-$HOME/fast/ka-scratch/sok-mlta/bitcodes/llvm15}
if [ ! -f asan/CMakeCache.txt ]; then
  mkdir -p asan
  (cd asan && PATH=$LLVM/bin:$PATH LLVM_ROOT_DIR=$LLVM/bin LLVM_LIBRARY_DIRS=$LLVM/lib \
     LLVM_INCLUDE_DIRS=$LLVM/include CC=clang CXX=clang++ cmake ../src -DCMAKE_BUILD_TYPE=Release \
     -DCMAKE_CXX_FLAGS="-fsanitize=address -fno-omit-frame-pointer -gline-tables-only" \
     -DCMAKE_EXE_LINKER_FLAGS=-fsanitize=address -DJEMALLOC_LIB=/usr/lib/x86_64-linux-gnu/libdl.so.2 \
     > cmake.log 2>&1) || { echo "FAIL[asan-gate]: cmake (asan/cmake.log)"; exit 1; }
fi
(cd asan && make -j"$(nproc)" KAMain > build.log 2>&1) || { echo "FAIL[asan-gate]: build (asan/build.log)"; exit 1; }
BIN=$ROOT/asan/lib/KAMain
export ASAN_OPTIONS=detect_leaks=0:halt_on_error=1
fail=0
KAMAIN=$BIN bash test/cells-cases.sh > asan/cases.log 2>&1 || { echo "FAIL[asan-gate]: cells-cases (asan/cases.log)"; fail=1; }
grep -q "ERROR: AddressSanitizer" asan/cases.log && { echo "FAIL[asan-gate]: sanitizer report in cells-cases"; fail=1; }
A="--func-summaries=$ROOT/func_summaries.txt --verbose=1 --cfl-cells --cfl-union-keys=tag --cfl-alloc-origins --cfl-whole-program"
for p in "libpng|$ROOT/test/libpng/libpng_read_fuzzer.0.0.preopt.bc" \
         "cjpeg-O0|$R/soundness_ossfuzz/O0_12.15.2025/libjpeg-turbo/cjpeg-static.bc" \
         "djpeg-O0|$R/soundness_ossfuzz/O0_12.15.2025/libjpeg-turbo/djpeg-static.bc"; do
  n=${p%%|*}; f=${p#*|}
  timeout 1800 "$BIN" $A "$f" > "asan/$n.log" 2>&1
  rc=$?
  if [ $rc -ne 0 ] || grep -q "ERROR: AddressSanitizer" "asan/$n.log"; then
    echo "FAIL[asan-gate]: $n rc $rc (asan/$n.log)"; fail=1
  fi
done
KAMAIN=$BIN bash test/asan-census.sh || fail=1
[ $fail = 0 ] && echo "PASS[asan-gate]"
exit $fail
