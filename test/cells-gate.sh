#!/usr/bin/env bash
# The cells gate: the --cfl-cells solver (the configuration the leak census,
# the soup profiler and the plan's measurements run) on fixed inputs, its
# outputs pinned in test/cells-pins.txt. The consumer gate's configurations
# do not run this solver, so a cells change is certified here, in every gate.
#   full runs (libpng, libjpeg x4, httpd, tcpdump): answer pairs and the
#     icalls JSON's sha256;
#   nm-new O0/O3, stopped at a fixed pop: pops, cells and facts at the stop
#     (with the facts in key cells of keyed union slots, which repeat their
#     slot's unkeyed facts by construction) and the sha256 of the partial answers (--cfl-cell-stop-answers);
#   tiffsplit O0 (at 150K pops) and O3 (at 1M) likewise: it has not finished since 07be17c,
#     nor with plan 3.54 (method-installed state, embedded method fields,
#     terms along the receiver); the residue is in the 3.54 commit.
# Usage: test/cells-gate.sh [OUTDIR] [--update]; OUTDIR must not exist
# (every run writes fresh files: no output of an earlier run is ever
# compared). A run that does not exit 0 (a timeout is 124) is a failure,
# never a comparison. KAMAIN= overrides the binary, SOK_BC= the bitcode
# root. Exits nonzero on any difference from the pins; --update rewrites
# them (a change is attributed in its commit).
set -u
cd "$(dirname "$0")"
BIN=$(realpath "${KAMAIN:-../release/lib/KAMain}")
R=${SOK_BC:-$HOME/fast/ka-scratch/sok-mlta/bitcodes/llvm15}
OUT=${1:-}
UPDATE=0
[ "${2:-}" = "--update" ] && UPDATE=1
if [ -z "$OUT" ]; then
  OUT=$(mktemp -d)
elif [ -e "$OUT" ]; then
  echo "cells gate: $OUT exists; give a fresh directory" >&2
  exit 2
else
  mkdir -p "$OUT"
fi
FS=$(realpath ../func_summaries.txt)
# Every case runs in its own directory with a fixed command line (./k,
# fs.txt, in.bc, relative outputs): gate hygiene, so no path reaches argv.
# Determinism check: every stop case runs a second time from a directory
# of another length, with another binary name and output name (other
# argument lengths, another heap layout); the two stop states must be
# byte-identical, or the gate fails (NONDETERMINISTIC).
A="--func-summaries=fs.txt --verbose=1 --cfl-cells --cfl-union-keys=tag --cfl-alloc-origins --cfl-whole-program --mem-limit=16"
# name | input | stop pops (0: to completion)
CASES="libpng|$(realpath libpng/libpng_read_fuzzer.0.0.preopt.bc)|0
cjpeg-O0|$R/soundness_ossfuzz/O0_12.15.2025/libjpeg-turbo/cjpeg-static.bc|0
djpeg-O0|$R/soundness_ossfuzz/O0_12.15.2025/libjpeg-turbo/djpeg-static.bc|0
cjpeg-O3|$R/soundness_ossfuzz/O3_12.15.2025/libjpeg-turbo/cjpeg-static.bc|0
djpeg-O3|$R/soundness_ossfuzz/O3_12.15.2025/libjpeg-turbo/djpeg-static.bc|0
httpd|$R/soundness_ossfuzz/O0_12.15.2025/httpd/bin/httpd.bc|0
tcpdump|$R/soundness_unifuzz/build_O0/tcpdump-4.8.1/tcpdump.bc|0
nm-O0|$R/soundness_unifuzz/build_O0/binutils_5279478/nm-new.bc|200000
nm-O3|$R/soundness_unifuzz/build_O3/binutils_5279478/nm-new.bc|200000
tiffsplit-O0|$R/soundness_unifuzz/build_O0/libtiff-Release-v3-9-7/tiffsplit.bc|150000
tiffsplit-O3|$R/soundness_unifuzz/build_O3/libtiff-Release-v3-9-7/tiffsplit.bc|1000000"
while IFS='|' read -r n in stop; do
  d="$OUT/run-$n"
  mkdir -p "$d"
  ln -s "$BIN" "$d/k"
  ln -s "$FS" "$d/fs.txt"
  ln -s "$in" "$d/in.bc"
  if [ "$stop" = 0 ]; then
    ( s=$SECONDS; cd "$d" && timeout 3600 ./k $A --cfl-dump-icalls-json=a.json in.bc > "$OUT/$n.log" 2>&1
      echo $? > "$OUT/$n.rc"; echo $((SECONDS - s)) > "$OUT/$n.secs"
      [ -f "$d/a.json" ] && mv "$d/a.json" "$OUT/$n.json" ) &
  else
    ( s=$SECONDS; cd "$d" && timeout 3600 ./k $A --cfl-cell-census-at="$stop" --cfl-cell-stop-answers=a.stop in.bc \
        > "$OUT/$n.log" 2>&1
      echo $? > "$OUT/$n.rc"; echo $((SECONDS - s)) > "$OUT/$n.secs"
      [ -f "$d/a.stop" ] && mv "$d/a.stop" "$OUT/$n.stop" ) &
    d2="$OUT/determinism-check-from-a-directory-of-another-length/run-$n"
    mkdir -p "$d2"
    ln -s "$BIN" "$d2/kamain-under-another-name"
    ln -s "$FS" "$d2/summaries-under-another-name.txt"
    ln -s "$in" "$d2/bitcode-under-another-name.bc"
    ( cd "$d2" && timeout 3600 ./kamain-under-another-name ${A/fs.txt/summaries-under-another-name.txt} \
        --cfl-cell-census-at="$stop" --cfl-cell-stop-answers=stop-answers-under-another-name.txt \
        bitcode-under-another-name.bc > "$OUT/$n.det.log" 2>&1
      echo $? > "$OUT/$n.det.rc"; [ -f "$d2/stop-answers-under-another-name.txt" ] &&
        mv "$d2/stop-answers-under-another-name.txt" "$OUT/$n.det.stop" ) &
  fi
done <<< "$CASES"
wait
got="$OUT/pins.txt"
: > "$got"
fail=0
while IFS='|' read -r n in stop; do
  rc=$(cat "$OUT/$n.rc" 2>/dev/null || echo missing)
  out="$OUT/$n.json"
  [ "$stop" = 0 ] || out="$OUT/$n.stop"
  if [ "$rc" != 0 ] || [ ! -s "$out" ]; then
    echo "$n rc=$rc" >> "$got"
    fail=1
  elif [ "$stop" = 0 ]; then
    pairs=$(python3 -c "import json,sys; print(sum(len(v) for v in json.load(open(sys.argv[1])).values()))" "$OUT/$n.json")
    echo "$n pairs $pairs sha256 $(sha256sum < "$OUT/$n.json" | cut -c1-16)" >> "$got"
  else
    echo "$n $(head -1 "$OUT/$n.stop" | cut -d' ' -f2-) sha256 $(sha256sum < "$OUT/$n.stop" | cut -c1-16)" >> "$got"
    if [ "$(cat "$OUT/$n.det.rc" 2>/dev/null)" != 0 ] || ! cmp -s "$OUT/$n.stop" "$OUT/$n.det.stop"; then
      echo "NONDETERMINISTIC $n: the stop state differs with another directory, binary name and output name" >&2
      fail=1
    fi
  fi
done <<< "$CASES"
if [ $UPDATE = 1 ]; then
  if [ $fail = 1 ]; then echo "cells gate: a run failed; pins not updated" >&2; cat "$got"; exit 1; fi
  cp "$got" cells-pins.txt
  echo "cells gate: pins updated ($(wc -l < cells-pins.txt) cases)"
  cat cells-pins.txt
  exit 0
fi
while read -r line; do
  n=${line%% *}
  pin=$(grep "^$n " cells-pins.txt)
  if [ "$line" = "$pin" ]; then echo "SAME $line"
  else echo "DIFF $n: pinned [$pin] got [$line]"; fail=1; fi
done < "$got"
# Per-program status (Fable 2026-10-17): whether the run reached its
# fixpoint, and where a stop case stood (a stop case never does: it is
# stopped at a fixed pop count, before).
while IFS='|' read -r n in stop; do
  rc=$(cat "$OUT/$n.rc" 2>/dev/null || echo missing)
  secs=$(cat "$OUT/$n.secs" 2>/dev/null || echo "?")
  if [ "$rc" != 0 ]; then echo "STATUS $n: rc=$rc after $secs s (124: did not finish in 3600 s)"
  elif [ "$stop" = 0 ]; then
    echo "STATUS $n: fixpoint, $(grep "^$n " "$got" | cut -d' ' -f2-3), $secs s"
  else
    read -r _ _ p _ _ _ f _ < "$OUT/$n.stop"
    echo "STATUS $n: stop at $p pops of its iteration (--cfl-cell-census-at=$stop over all), $f facts, not at fixpoint, $secs s"
  fi
done <<< "$CASES"
echo "cells gate: outputs in $OUT"
exit $fail
