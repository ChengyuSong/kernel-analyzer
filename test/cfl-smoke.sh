#!/usr/bin/env bash
# CFL precision smoke test: pins the validated libpng tallies for KAMain
# (flows-to, its default "full" configuration and the variants the eval
# runs) and for the CFL-reachability baseline KABaseline (monolithic and
# compositional saturation). Also writes every consumer-facing output of
# KAMain once, so a dropped option fails here. Run from anywhere; exits
# nonzero on any regression. Override binaries with KAMAIN=, KABASELINE=.
set -u
cd "$(dirname "$0")/libpng"
BIN=${KAMAIN:-../../release/lib/KAMain}
BASE=${KABASELINE:-../../release/baseline/KABaseline}
BC=libpng_read_fuzzer.0.0.preopt.bc
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
fail=0
run() {
  local name="$1"; local expect="$2"; local bin="$3"; shift 3
  local out
  out=$("$bin" --verbose=2 "$@" "$BC" 2>&1)
  if grep -q "$expect" <<<"$out" && ! grep -q "UNSOUND" <<<"$out"; then
    echo "PASS[$name]"
  else
    echo "FAIL[$name]:"
    grep -E "Callee by type|UNSOUND|rror" <<<"$out" | head -3
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
NOCHANNELS=(--func-summaries=../../func_summaries.txt
            --cfl-propose-chain-summaries=false --cfl-regfield-apply=false
            --cfl-regfield-obj=false --cfl-propose-solved-summaries=false
            --cfl-adopt-proposed-summaries=false)

# KAMain (flows-to). The default row also writes the consumer outputs.
run full     "$EXPECT" "$BIN" --cfl-dump-icalls-json="$OUT/icalls.json" \
    --callgraph-json="$OUT/callgraph.json" --ir-sidecar-dir="$OUT/sidecar"
run base     "$EXPECT" "$BIN" "${NOCHANNELS[@]}"
run fs       "$EXPECT" "$BIN" --cfl-nexus-fields=all+ids --cfl-bidi-prune \
    --cfl-presolve-once
run pexact   "$EXPECT" "$BIN" --cfl-presolve-exact --cfl-presolve-cone=false
for f in icalls.json callgraph.json sidecar/$BC.facts.json; do
  if python3 -c "import json,sys; json.load(open(sys.argv[1]))" \
       "$OUT/$f" 2>/dev/null; then
    echo "PASS[output $f]"
  else
    echo "FAIL[output $f]: missing or not JSON"; fail=1
  fi
done

# The cell solver (--cfl-cells): its rule report is pinned (row meanings,
# plans 3.47-3.49); a changed row is a reviewed re-pin.
CELLS=(--func-summaries=../../func_summaries.txt --cfl-cells --cfl-union-keys=tag
       --cfl-alloc-origins --cfl-whole-program)
if "$BIN" --verbose=0 "${CELLS[@]}" --cfl-rule-report="$OUT/rules.txt" "$BC" >/dev/null 2>&1 &&
   diff -q ../baselines/libpng-cells-rule-report.txt "$OUT/rules.txt" >/dev/null; then
  echo "PASS[cells rule report]"
else
  echo "FAIL[cells rule report]:"
  diff ../baselines/libpng-cells-rule-report.txt "$OUT/rules.txt" 2>&1 | head -5
  fail=1
fi

# The tagged-field last-writer cases (plan 3.51): each marked read keeps
# the writers the program can show it.
if KAMAIN=$(realpath "$BIN") bash ../tagged-gaps.sh > "$OUT/tagged.txt" 2>&1; then
  echo "PASS[tagged-field last-writer cases]"
else
  echo "FAIL[tagged-field last-writer cases]:"; grep FAIL "$OUT/tagged.txt" | head -3
  fail=1
fi

# KABaseline (GraCFL saturation on the same graph).
run sat-mono-base       "$EXPECT" "$BASE" --cfl-compositional=false
run sat-comp-base       "$EXPECT" "$BASE"
run sat-mono-all-levers "$EXPECT" "$BASE" --cfl-compositional=false \
    --cfl-field-buckets=16 --cfl-presolve-merge --cfl-fptr-slice
run sat-comp-all-levers "$EXPECT" "$BASE" --cfl-field-buckets=16 \
    --cfl-presolve-merge --cfl-fptr-slice
exit $fail
