#!/bin/bash
# FSE'27 kernel evaluation campaign: frozen full stack + ablation
# matrix + GT matching, sequential, resumable.
#
# Workflow on a fresh machine:
#   git pull && cmake --build release
#   rsync the kernel IR corpus over, write a filelist of ABSOLUTE
#   .bc paths, then:
#     KA_KERNEL_BCLIST=/path/to/bclist \
#     KA_GT=/path/to/gt-pairs.txt \        # optional; skips GT if unset
#     eval/60-kernel-fse.sh [arm ...]      # default: all arms
#
# Arms (PRECISION family; the full stack is the reference):
#   full        chain + regfield + obj            (arm 0, reference)
#   base        no precision mechanisms beyond defaults
#   noregf      full - regfield/obj tables
#   nochain     full - chain summaries (gating f83e741 keeps the
#               summaries file's CHAINREG lines out of this arm)
#   notpkeys    full - tracepoint keys
#   noopstables full - static_call KEY TABLES (modeling stays on:
#               --cfl-static-call remains default; this is a
#               precision ablation, not a soundness one)
#   noinvoke    full - INVOKE callback/argument pairing (runs with a
#               filtered summaries file; whole lines dropped so no
#               spec is left empty = transfer-free)
#   nosummaries SOUNDNESS row: no --func-summaries at all
#               (name-heuristic fallback). NOT one-sided: summaries
#               both remove conflation and recover real pairs.
#
# One-sided expectation for the precision arms: the FULL answer set
# must be a SUBSET of every ablated arm's (mechanisms only remove).
# Any pairs in full but not in an arm beyond that arm's mechanism's
# claim, or any GT FN regression, is reported loudly.
#
# Per arm: <arm>.log, <arm>-pairs.txt (sorted unique), <arm>-gt.txt,
# and a row in summary.tsv. Arms with an existing pairs file are
# skipped (delete the file or set KA_FORCE=1 to re-run).

set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

: "${KA_KERNEL_BCLIST:?set KA_KERNEL_BCLIST to the kernel IR filelist}"
KA_MEMLIMIT="${KA_MEMLIMIT:-92}"
KA_GT="${KA_GT:-}"
OUT="${KA_KERNEL_OUT:-$KA_RESULTS/kernel-fse}"
SUM="$KA_REPO/func_summaries.txt"
mkdir -p "$OUT"

export LC_ALL=C
export MALLOC_ARENA_MAX=2

COMMON=(--verbose=2 --cfl-compositional=false --cfl-flows-to
        --cfl-dump-icalls --log-timestamps --mem-limit="$KA_MEMLIMIT")
FULLPREC=(--cfl-propose-chain-summaries --cfl-regfield-apply
          --cfl-regfield-obj)

# INVOKE-filtered summaries (generated fresh each invocation).
NOINV="$OUT/func_summaries.noinvoke.txt"
grep -v 'INVOKE(' "$SUM" > "$NOINV"

arm_flags() {
  case "$1" in
    full)        echo "${FULLPREC[@]} --func-summaries=$SUM" ;;
    base)        echo "--func-summaries=$SUM" ;;
    noregf)      echo "--cfl-propose-chain-summaries --func-summaries=$SUM" ;;
    nochain)     echo "--cfl-regfield-apply --cfl-regfield-obj --func-summaries=$SUM" ;;
    notpkeys)    echo "${FULLPREC[@]} --cfl-tracepoint-keys=false --func-summaries=$SUM" ;;
    noopstables) echo "${FULLPREC[@]} --cfl-static-ops-tables=false --func-summaries=$SUM" ;;
    noinvoke)    echo "${FULLPREC[@]} --func-summaries=$NOINV" ;;
    nosummaries) echo "${FULLPREC[@]}" ;;
    *) echo "unknown arm: $1" >&2; return 1 ;;
  esac
}

extract_pairs() { # log -> sorted unique "caller target" pairs
  sed -n 's/^ICALL \([^ ]*\) :: .* -> \(.*\)$/\1 \2/p' "$1" \
    | sort -u -S2G --parallel=8
}

run_arm() {
  local arm="$1" pairs="$OUT/$arm-pairs.txt" log="$OUT/$arm.log"
  if [[ -s "$pairs" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "== $arm: pairs exist, skipping (KA_FORCE=1 to re-run)"
    return 0
  fi
  local flags; flags=$(arm_flags "$arm") || return 1
  echo "== $arm: running ($(date -Is))"
  # shellcheck disable=SC2086
  /usr/bin/time -v "$KA_BIN" "${COMMON[@]}" $flags \
      @"$KA_KERNEL_BCLIST" > "$log" 2>&1
  local rc=$?
  if [[ $rc -ne 0 ]]; then
    echo "!! $arm: KAMain exited $rc — see $log" >&2
    return $rc
  fi
  extract_pairs "$log" > "$pairs"
  echo "== $arm: $(wc -l < "$pairs") pairs"
}

# GT-aux dump (quick: loads corpus, dumps DCALL/SCTCALL, exits).
gt_aux() {
  local aux="$OUT/gtaux.txt" log="$OUT/gtaux.log"
  [[ -s "$aux" && "${KA_FORCE:-0}" != 1 ]] && return 0
  echo "== gtaux: dumping direct/trampoline edges"
  "$KA_BIN" "${COMMON[@]}" --cfl-dump-gt-aux --func-summaries="$SUM" \
      @"$KA_KERNEL_BCLIST" > "$log" 2>&1
  grep -E '^DCALL |^SCTCALL ' "$log" > "$aux"
  echo "== gtaux: $(wc -l < "$aux") edges"
}

gt_match() { # arm -> FN count (or "-" if no GT)
  local arm="$1"
  [[ -z "$KA_GT" ]] && { echo "-"; return; }
  local rep="$OUT/$arm-gt.txt"
  python3 "$KA_REPO/tools/gt-match.py" --gt "$KA_GT" \
      --pairs "$OUT/$arm-pairs.txt" --aux "$OUT/gtaux.txt" \
      --fn-out "$OUT/$arm-fns.txt" > "$rep" 2>&1
  grep -oE 'FN[ =:]+[0-9]+' "$rep" | grep -oE '[0-9]+' | head -1
}

fat_tail() { # arm -> "callers>=100targets maxfanout"
  awk '{n[$1]++} END{m=0; c=0; for(k in n){if(n[k]>=100)c++; if(n[k]>m)m=n[k]} print c, m}' \
    "$OUT/$1-pairs.txt"
}

ARMS=("$@")
[[ ${#ARMS[@]} -eq 0 ]] && ARMS=(full base noregf nochain notpkeys
                                 noopstables noinvoke nosummaries)

gt_aux
for a in "${ARMS[@]}"; do run_arm "$a" || exit 1; done

# Summary table. Deltas are vs full: removed = in arm, not in full
# (what the mechanisms delete); added = in full, not in arm (MUST be
# 0 for one-sided precision arms; nonzero is loud).
SUMTSV="$OUT/summary.tsv"
{
  echo -e "arm\tpairs\tremoved_vs_full\tadded_vs_full\tge100_callers\tmax_fanout\tgt_fn\twall\tmaxrss_kb"
  for a in "${ARMS[@]}"; do
    p="$OUT/$a-pairs.txt"; [[ -s "$p" ]] || continue
    n=$(wc -l < "$p")
    if [[ "$a" == full ]]; then rem=0; add=0; else
      rem=$(comm -23 "$p" "$OUT/full-pairs.txt" | wc -l)
      add=$(comm -13 "$p" "$OUT/full-pairs.txt" | wc -l)
    fi
    read -r c100 maxf <<< "$(fat_tail "$a")"
    fn=$(gt_match "$a")
    wall=$(grep -oE 'Elapsed \(wall clock\).*' "$OUT/$a.log" | awk '{print $NF}' | tail -1)
    rss=$(grep -oE 'Maximum resident set size.*[0-9]+' "$OUT/$a.log" | grep -oE '[0-9]+$' | tail -1)
    echo -e "$a\t$n\t$rem\t$add\t$c100\t$maxf\t$fn\t${wall:--}\t${rss:--}"
  done
} | tee "$SUMTSV"

# Loud one-sided check: precision arms must not have added_vs_full.
awk -F'\t' 'NR>1 && $1!="full" && $1!="nosummaries" && $4+0>0 {
  print "!! ONE-SIDED VIOLATION: arm " $1 " is missing " $4 \
        " pairs that the FULL stack reports — investigate before use."
  bad=1 } END{exit bad}' "$SUMTSV" || exit 2
echo "== all arms complete: $SUMTSV"
