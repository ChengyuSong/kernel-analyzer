#!/bin/bash
# Extract the facts from run logs into results.csv + results.md.
# Reads every <results>/<corpus>-<mode>.log produced by 30-run.sh.
# Columns: corpus, mode, outcome (ok|oom|timeout|error), wall, peak
# RSS, TUs, solve stats (classes/roots/facts/waves/pops/solve-ms),
# answers (type-based pairs, CFL pairs, sites, avg/max fanout),
# boundary ledgers (int-provenance modeled/ledgered, extern
# resolutions), and the answer-pin sha256.
set -euo pipefail
source "$(dirname "$0")/env.sh"

csv="$KA_RESULTS/results.csv"
md="$KA_RESULTS/results.md"
echo "corpus,mode,outcome,wall,peak_rss_kb,type_pairs,cfl_pairs,sites,avg_fanout,max_fanout,classes,roots,facts,waves,pops,solve_ms,intprov_modeled,intprov_ledgered,extern_resolutions,icalls_sha256" > "$csv"

last_num() { grep -oE "$2" "$1" | tail -1 | grep -oE '[0-9]+' | tail -1; }

for log in "$KA_RESULTS"/*-*.log; do
  base=$(basename "$log" .log)
  corpus=${base%-*}; mode=${base##*-}
  rc=$(grep -oE 'exitcode: [0-9]+' "$log" | tail -1 | grep -oE '[0-9]+' || echo "")
  outcome=ok
  grep -q "Out of memory: VmRSS" "$log" && outcome=oom
  [ "$rc" = "124" ] && outcome=timeout
  [ "$outcome" = ok ] && [ "$rc" != "0" ] && outcome=error

  wall=$(grep -oE 'Elapsed \(wall clock\) time.*: (.*)' "$log" | tail -1 | sed 's/.*: //' || echo "")
  rss=$(last_num "$log" 'Maximum resident set size \(kbytes\): [0-9]+' || echo "")

  type_pairs=""; cfl_pairs=""; sites=""; avgf=""; maxf=""
  classes=""; roots=""; facts=""; waves=""; pops=""; solvems=""
  ipm=""; ipl=""; extr=""; sha=""
  if [ "$mode" = ft ] && [ "$outcome" = ok ]; then
    tally=$(grep "Callee by type:" "$log" | tail -1 || true)
    type_pairs=$(echo "$tally" | grep -oE 'total [0-9]+' | grep -oE '[0-9]+' || true)
    cfl_pairs=$(echo "$tally" | grep -oE 'CFL [0-9]+' | grep -oE '[0-9]+' || true)
    sort_pin="$KA_RESULTS/$corpus-ft-icalls.sort"
    if [ -s "$sort_pin" ]; then
      read -r sites avgf maxf < <(sed 's/ -> [^ ]*$//' "$sort_pin" | sort | uniq -c \
        | awk '{n++; s+=$1; if($1>m) m=$1} END {printf "%d %.1f %d\n", n, s/n, m}')
      sha=$(cut -d' ' -f1 "$sort_pin.sha256" 2>/dev/null || echo "")
    fi
    summary=$(grep -E "FlowsTo: [0-9]+ classes" "$log" | tail -1 || true)
    classes=$(echo "$summary" | grep -oE '\([0-9]+ after' | grep -oE '[0-9]+' || true)
    roots=$(echo "$summary" | grep -oE '[0-9]+ roots' | grep -oE '[0-9]+' || true)
    facts=$(echo "$summary" | grep -oE '[0-9]+ native' | grep -oE '[0-9]+' || true)
    waves=$(echo "$summary" | grep -oE '[0-9]+ waves' | grep -oE '[0-9]+' || true)
    pops=$(echo "$summary" | grep -oE '[0-9]+ worklist pops' | grep -oE '[0-9]+' || true)
    solvems=$(echo "$summary" | grep -oE '[0-9]+ ms' | grep -oE '[0-9]+' || true)
    ip=$(grep "IntProvenance: modeled" "$log" | tail -1 || true)
    ipm=$(echo "$ip" | grep -oE '\bmodeled [0-9]+' | head -1 | grep -oE '[0-9]+' || true)
    ipl=$(echo "$ip" | grep -oE 'unmodeled [0-9]+' | head -1 | grep -oE '[0-9]+' || true)
    extr=$(grep "UniversalPtr LEDGER" "$log" | tail -1 \
      | grep -oE '[0-9]+ extern-global' | grep -oE '[0-9]+' || true)
  fi
  echo "$corpus,$mode,$outcome,$wall,$rss,$type_pairs,$cfl_pairs,$sites,$avgf,$maxf,$classes,$roots,$facts,$waves,$pops,$solvems,$ipm,$ipl,$extr,$sha" >> "$csv"
done

{
  echo "# Eval results ($(hostname), $(date -u +%F))"
  echo
  echo "| corpus | mode | outcome | wall | peak RSS | type pairs | CFL pairs | sites | avg/max fanout |"
  echo "|---|---|---|---|---|---|---|---|---|"
  tail -n +2 "$csv" | while IFS=, read -r c m o w r tp cp s af mf rest; do
    rgb=""; [ -n "$r" ] && rgb=$(awk -v k="$r" 'BEGIN{printf "%.1f GB", k/1048576}')
    echo "| $c | $m | $o | $w | $rgb | $tp | $cp | $s | $af/$mf |"
  done
} > "$md"
echo "OK:"; column -t -s, "$csv" | cut -c1-160
