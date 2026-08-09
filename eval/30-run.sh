#!/bin/bash
# Run the eval matrix: per corpus, (a) flows-to FI (the paper's
# system config) and (b) the saturation baseline (GraCFL engine on
# the identical IR graph), both under /usr/bin/time -v with a
# wall-clock timeout. Every run writes <results>/<corpus>-<mode>.log;
# OOM/timeouts are recorded outcomes, not failures of this script.
#
# Usage: 30-run.sh [corpus ...]   (default: httpd pg [+KA_USER_NAME])
set -euo pipefail
source "$(dirname "$0")/env.sh"
ka_require "$KA_BIN" /usr/bin/time timeout
mkdir -p "$KA_RESULTS"

run_one() { # run_one <name> <bclist> <mode: ft|sat>
  local name=$1 bclist=$2 mode=$3
  local log="$KA_RESULTS/$name-$mode.log"
  local flags timeo
  case $mode in
    ft)  flags="--cfl-flows-to --cfl-dump-icalls $KA_EXTRA_FLAGS"
         timeo=$KA_FT_TIMEOUT ;;
    sat) flags=""
         timeo=$KA_SAT_TIMEOUT ;;
  esac
  echo "== $name/$mode -> $log"
  set +e
  timeout "$timeo" /usr/bin/time -v \
    "$KA_BIN" --verbose=2 --cfl-compositional=false $flags $(ka_memflag) \
      --bc-list="$bclist" > "$log" 2>&1
  local rc=$?
  set -e
  echo "exitcode: $rc" >> "$log"
  # Answer pin (deterministic; sha256 comparable across machines).
  if [ "$mode" = ft ]; then
    grep "ICALL" "$log" | sed 's/^CallGraph: //' | sort \
      > "$KA_RESULTS/$name-ft-icalls.sort" || true
    sha256sum "$KA_RESULTS/$name-ft-icalls.sort" \
      > "$KA_RESULTS/$name-ft-icalls.sort.sha256" || true
  fi
  echo "   done (rc=$rc)"
}

corpora=("$@")
if [ ${#corpora[@]} -eq 0 ]; then
  corpora=(httpd pg)
  [ -n "$KA_USER_BCLIST" ] && corpora+=("$KA_USER_NAME")
fi

for c in "${corpora[@]}"; do
  case $c in
    httpd) bl="$KA_WORK/httpd.bclist" ;;
    pg)    bl="$KA_WORK/pg.bclist" ;;
    "$KA_USER_NAME") bl="$KA_USER_BCLIST" ;;
    *) echo "unknown corpus $c" >&2; exit 1 ;;
  esac
  [ -s "$bl" ] || { echo "missing bclist $bl (run 20-build-corpora.sh)" >&2; exit 1; }
  for m in $KA_MODES; do
    run_one "$c" "$bl" "$m"
  done
done
echo "OK: logs + pins in $KA_RESULTS"
