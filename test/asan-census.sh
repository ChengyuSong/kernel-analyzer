#!/usr/bin/env bash
# The census instruments under AddressSanitizer (the third kernel finding,
# plan 3.53: leakArrive read a leakTag iterator after an emplace rehashed
# the map). Runs tcpdump O0 in the census configuration with an ASan build
# of KAMain and fails on any ASan report or nonzero exit.
#   Build: mkdir asan && cd asan && CC=clang CXX=clang++ cmake ../src \
#     -DCMAKE_BUILD_TYPE=Release -DJEMALLOC_LIB=/usr/lib/x86_64-linux-gnu/libdl.so.2 \
#     -DCMAKE_CXX_FLAGS="-fsanitize=address -fno-omit-frame-pointer -gline-tables-only" \
#     -DCMAKE_EXE_LINKER_FLAGS=-fsanitize=address && make -j KAMain
#   (jemalloc replaced by libdl so ASan sees every allocation.)
# KAMAIN= the ASan binary (default ../asan/lib/KAMain), SOK_BC= the bitcode root.
set -u
cd "$(dirname "$0")"
BIN=${KAMAIN:-../asan/lib/KAMain}
R=${SOK_BC:-$HOME/fast/ka-scratch/sok-mlta/bitcodes/llvm15}
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
ASAN_OPTIONS=detect_leaks=0:halt_on_error=1 timeout 1800 "$BIN" --func-summaries=../func_summaries.txt \
  --verbose=1 --cfl-cells --cfl-union-keys=tag --cfl-alloc-origins --cfl-whole-program \
  --cfl-cell-soup-profile --cfl-cell-soup-cap=20000000 --cfl-cell-leak-census --cfl-cell-weld-census \
  --cfl-cell-collapse=false "$R/soundness_unifuzz/build_O0/tcpdump-4.8.1/tcpdump.bc" > "$OUT/log" 2>&1
rc=$?
if [ $rc -ne 0 ] || grep -q "ERROR: AddressSanitizer" "$OUT/log"; then
  echo "FAIL[asan-census]: rc $rc"; grep -m1 -A3 "ERROR: AddressSanitizer" "$OUT/log"; exit 1
fi
echo "PASS[asan-census]"
