#!/bin/bash
# Ablation matrix over the flows-to config. Two families with
# DIFFERENT success criteria:
#
#  EXACT family (perf machinery — answers must be byte-identical to
#  the default ft pin; a sha mismatch is a soundness bug, reported
#  loudly, never silently accepted):
#    noshare    --cfl-intern-planes=false        (#46 COW plane sharing)
#    nofastjoin --cfl-join-fastpath=false        (#48 cluster-mark skips)
#    lazymint   --cfl-lazy-mint                  (demand-driven mint)
#
#  PRECISION family (identity channels / relevance discipline —
#  answers change; channels only REMOVE pairs, so the default pin
#  must be a SUBSET of the ablated run (one-sided check = the -N/+0
#  certification), and the delta is the feature's contribution):
#    notpkeys    --cfl-tracepoint-keys=false
#    noopstables --cfl-static-ops-tables=false
#    nocone      --cfl-presolve-cone=false
#    nosummaries KA_EXTRA_FLAGS minus --func-summaries=... (only runs
#                when summaries were passed; NOT one-sided — summaries
#                both remove conflation and recover copies)
#
# Requires the default ft pin from 30-run.sh (<corpus>-ft-icalls.sort).
# Usage: 35-ablate.sh [corpus ...]   (default: httpd pg [+KA_USER_NAME])
# KA_ABLATE_LIST="noshare nocone ..." selects a subset.
set -euo pipefail
source "$(dirname "$0")/env.sh"
ka_require "$KA_BIN" /usr/bin/time timeout comm
mkdir -p "$KA_RESULTS"

csv="$KA_RESULTS/ablations.csv"
echo "corpus,ablation,family,outcome,wall,peak_rss_kb,pairs,delta_pairs,check,sha256" > "$csv"

ALL_ABL="noshare nofastjoin lazymint notpkeys noopstables nocone nosummaries"
ABL_LIST=${KA_ABLATE_LIST:-$ALL_ABL}

abl_flags() { # abl_flags <name> -> extra flags on stdout; rc=1 = skip
  case $1 in
    noshare)     echo "--cfl-intern-planes=false" ;;
    nofastjoin)  echo "--cfl-join-fastpath=false" ;;
    lazymint)    echo "--cfl-lazy-mint" ;;
    notpkeys)    echo "--cfl-tracepoint-keys=false" ;;
    noopstables) echo "--cfl-static-ops-tables=false" ;;
    nocone)      echo "--cfl-presolve-cone=false" ;;
    nosummaries) [[ "$KA_EXTRA_FLAGS" == *--func-summaries=* ]] || return 1
                 echo "__STRIP_SUMMARIES__" ;;
  esac
}

abl_family() {
  case $1 in
    noshare|nofastjoin|lazymint) echo exact ;;
    *)                                   echo precision ;;
  esac
}

one_sided() { # channels may only ADD pairs when ablated
  case $1 in notpkeys|noopstables|nocone) return 0 ;; *) return 1 ;; esac
}

run_abl() { # run_abl <corpus> <bclist> <ablation>
  local name=$1 bclist=$2 abl=$3
  local extra; extra=$(abl_flags "$abl") || { echo "-- $name/$abl: n/a, skipped"; return 0; }
  local base_flags="$KA_EXTRA_FLAGS"
  if [ "$extra" = "__STRIP_SUMMARIES__" ]; then
    base_flags=$(echo "$KA_EXTRA_FLAGS" | sed 's/--func-summaries=[^ ]*//'); extra=""
  fi
  local log="$KA_RESULTS/$name-abl-$abl.log"
  local pin="$KA_RESULTS/$name-abl-$abl-icalls.sort"
  local base_pin="$KA_RESULTS/$name-ft-icalls.sort"
  [ -s "$base_pin" ] || { echo "missing default pin $base_pin (run 30-run.sh first)" >&2; exit 1; }
  echo "== $name/$abl -> $log"
  set +e
  timeout "$KA_FT_TIMEOUT" /usr/bin/time -v \
    "$KA_BIN" --verbose=2 --cfl-compositional=false --cfl-flows-to \
      --cfl-dump-icalls $extra $base_flags $(ka_memflag) \
      --bc-list="$bclist" > "$log" 2>&1
  local rc=$?
  set -e
  echo "exitcode: $rc" >> "$log"

  local outcome=ok
  grep -q "Out of memory: VmRSS" "$log" && outcome=oom
  [ "$rc" = "124" ] && outcome=timeout
  [ "$outcome" = ok ] && [ "$rc" != "0" ] && outcome=error
  local wall rss pairs="" delta="" check="" sha=""
  wall=$(grep -oE 'Elapsed \(wall clock\) time.*: (.*)' "$log" | tail -1 | sed 's/.*: //' || echo "")
  rss=$(grep -oE 'Maximum resident set size \(kbytes\): [0-9]+' "$log" | grep -oE '[0-9]+' | tail -1 || echo "")

  if [ "$outcome" = ok ]; then
    grep "ICALL" "$log" | sed 's/^CallGraph: //' | sort > "$pin"
    sha=$(sha256sum "$pin" | cut -d' ' -f1)
    pairs=$(wc -l < "$pin")
    delta=$(( pairs - $(wc -l < "$base_pin") ))
    if [ "$(abl_family "$abl")" = exact ]; then
      if cmp -s "$pin" "$base_pin"; then check=IDENTICAL
      else check=MISMATCH
        echo "!! $name/$abl: EXACT-family answer MISMATCH vs default pin (soundness bug)" >&2
      fi
    elif one_sided "$abl"; then
      # default \ ablated must be empty: the feature only removes pairs
      local viol; viol=$(comm -23 "$base_pin" "$pin" | wc -l)
      if [ "$viol" = 0 ]; then check="one-sided(-$delta/+0)"
      else check="VIOLATED($viol default-only pairs)"
        echo "!! $name/$abl: one-sided check violated ($viol pairs in default but not in ablation)" >&2
      fi
    else
      check="+$(comm -13 "$base_pin" "$pin" | wc -l)/-$(comm -23 "$base_pin" "$pin" | wc -l)"
    fi
  fi
  echo "$name,$abl,$(abl_family "$abl"),$outcome,$wall,$rss,$pairs,$delta,$check,$sha" >> "$csv"
  echo "   done (rc=$rc, $outcome${check:+, $check})"
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
  for abl in $ABL_LIST; do
    run_abl "$c" "$bl" "$abl"
  done
done

{
  echo "# Ablations ($(hostname), $(date -u +%F))"
  echo
  echo "| corpus | ablation | family | outcome | wall | peak RSS | pairs | Δ vs default | check |"
  echo "|---|---|---|---|---|---|---|---|---|"
  tail -n +2 "$csv" | while IFS=, read -r c a f o w r p d k s; do
    rgb=""; [ -n "$r" ] && rgb=$(awk -v k="$r" 'BEGIN{printf "%.1f GB", k/1048576}')
    echo "| $c | $a | $f | $o | $w | $rgb | $p | $d | $k |"
  done
} > "$KA_RESULTS/ablations.md"
echo "OK:"; column -t -s, "$csv" | cut -c1-160
