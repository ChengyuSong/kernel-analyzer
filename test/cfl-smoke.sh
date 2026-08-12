#!/usr/bin/env bash
# CFL precision smoke test: pins the validated libpng tallies across the
# graph-construction lever configurations. Run from anywhere; exits nonzero
# on any precision regression. Override binary with KAMAIN=path.
set -u
cd "$(dirname "$0")/libpng"
BIN=${KAMAIN:-../../release/lib/KAMain}
BC=libpng_read_fuzzer.0.0.preopt.bc
fail=0
run() {
  local name="$1"; local expect="$2"; shift 2
  local out
  out=$("$BIN" --verbose=2 "$@" "$BC" 2>&1)
  if grep -q "$expect" <<<"$out" && ! grep -q "UNSOUND" <<<"$out"; then
    echo "PASS[$name]"
  else
    echo "FAIL[$name]:"
    grep -E "Callee by type|UNSOUND" <<<"$out" | head -3
    fail=1
  fi
}
# Pin moved 9 -> 19 in ALL configs when the FIELD FILTER was retired
# from the answer path (2026-08-11): the filter was unsound (rejected
# dynamically-true, graph-derived pairs — GT process_one_work family);
# the 10 pairs it trimmed at libpng were pool/wildcard admissions it
# had no proof about. 19 = the honest sound answer at current graph
# precision; tightening must come from the graph/channels, not
# syntactic masks.
EXPECT="Callee by type: total 27, match by CFL 19"
run mono-base       "$EXPECT" --cfl-compositional=false
run comp-base       "$EXPECT"
run mono-all-levers "$EXPECT" --cfl-compositional=false --cfl-field-buckets=16 --cfl-presolve-merge --cfl-fptr-slice
run comp-all-levers "$EXPECT" --cfl-field-buckets=16 --cfl-presolve-merge --cfl-fptr-slice
exit $fail
