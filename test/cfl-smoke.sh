#!/usr/bin/env bash
# CFL precision smoke test: pins the validated libpng tallies across the
# graph-construction lever configurations. Run from anywhere; exits nonzero
# on any precision regression. Override binary with KAMAIN=path.
set -u
cd "$(dirname "$0")/libpng"
BIN=${KAMAIN:-../../release/lib/KAMain}
BC=libpng_read_fuzzer.0.0.preopt.bc
EXPECT="Callee by type: total 27, match by CFL 9"
fail=0
run() {
  local name="$1"; shift
  local out
  out=$("$BIN" --verbose=2 "$@" "$BC" 2>&1)
  if grep -q "$EXPECT" <<<"$out" && ! grep -q "UNSOUND" <<<"$out"; then
    echo "PASS[$name]"
  else
    echo "FAIL[$name]:"
    grep -E "Callee by type|UNSOUND" <<<"$out" | head -3
    fail=1
  fi
}
run mono-base       --cfl-compositional=false
run comp-base
run mono-all-levers --cfl-compositional=false --cfl-field-buckets=16 --cfl-presolve-merge --cfl-fptr-slice
run comp-all-levers --cfl-field-buckets=16 --cfl-presolve-merge --cfl-fptr-slice
exit $fail
