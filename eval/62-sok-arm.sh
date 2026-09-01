#!/bin/bash
# Run ORCFL over the SoK-MLTA bitcode datasets and emit per-program
# JSON in their harness's parsed_log format, so our rows sit in the
# same table as MLTA/DeepType/TFA/HPCFI/KallGraph/LLVM-CFI via
# THEIR compare_approaches.py (recall + AICT, their formulas).
#
# Inputs (their Drive layout; each .bc analyzed standalone, as
# their harness does):
#   KA_SOK_BC   one or more bitcode directories, colon-separated
#               (e.g. .../soundness_ossfuzz/build_O0:.../build_O3)
# Output:
#   $KA_RESULTS/sok/<config>/<dirtag>/parsed_log/<prog>.json
# Then add to their compare config, e.g.:
#   "RESULT_DIRS": { "ORCFL": ".../sok/full/<dirtag>/parsed_log/", ... }
# and run their scripts/compare_approaches.py.
#
# Configs: full (canonical channels + adoption) and base. Per-run
# timeout matches their harness budget (3600 s). Runs are quiet
# (--verbose=0); per-program time -v recorded. Single-threaded.

set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

: "${KA_SOK_BC:?set KA_SOK_BC to bitcode dir(s), colon-separated}"
OUT="${KA_SOK_OUT:-$KA_RESULTS/sok}"
SUM="$KA_REPO/func_summaries.txt"
TIMEOUT="${KA_SOK_TIMEOUT:-3600}"
export LC_ALL=C
export MALLOC_ARENA_MAX=2
PIN=()
[[ -n "${KA_CPUSET:-}" ]] && PIN=(taskset -c "$KA_CPUSET")

CHANNELS=(--cfl-propose-chain-summaries --cfl-regfield-apply
          --cfl-regfield-obj --cfl-propose-solved-summaries
          --cfl-adopt-proposed-summaries)

cfg_flags() {
  case "$1" in
    full) echo "${CHANNELS[@]}" ;;
    base) echo "" ;;
    *) return 1 ;;
  esac
}

IFS=':' read -ra DIRS <<< "$KA_SOK_BC"
for cfg in full base; do
  flags=$(cfg_flags "$cfg")
  for d in "${DIRS[@]}"; do
    tag=$(basename "$(dirname "$d")")_$(basename "$d")
    pdir="$OUT/$cfg/$tag/parsed_log"
    mkdir -p "$pdir"
    while IFS= read -r bc; do
      prog=$(basename "$bc" .bc)
      json="$pdir/$prog.json"
      log="$OUT/$cfg/$tag/$prog.log"
      if [[ -s "$json" && "${KA_FORCE:-0}" != 1 ]]; then
        echo "== $cfg/$tag/$prog: done, skipping"; continue
      fi
      echo "== $cfg/$tag/$prog"
      # shellcheck disable=SC2086
      timeout "$TIMEOUT" /usr/bin/time -v -o "$log.time" \
        "${PIN[@]}" "$KA_BIN" --verbose=0 --cfl-compositional=false \
        --cfl-flows-to --cfl-dump-icalls-json="$json" \
        --func-summaries="$SUM" $flags "$bc" > "$log" 2>&1
      rc=$?
      if [[ $rc -eq 124 ]]; then
        echo "!! $prog: TIMEOUT (${TIMEOUT}s) — no JSON emitted" >&2
        rm -f "$json"
      elif [[ $rc -ne 0 ]]; then
        echo "!! $prog: exited $rc — see $log" >&2
        rm -f "$json"
      fi
    done < <(find "$d" -name '*.bc' | sort)
  done
done

echo "== SoK arm complete. parsed_log dirs under $OUT/{full,base}/"
echo "== Next: add ORCFL entries to their compare config RESULT_DIRS"
echo "== and run scripts/compare_approaches.py in their repo."
