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
# NOTE ON KA_THREADS: the kernel-FI arms are SINGLE-THREADED; this
# knob does not affect them. It exists for multi-threaded baseline
# tools (e.g., standalone GraCFL) in comparison rows. On a big
# machine, parallelism comes from running ARMS concurrently (see
# protocol below); memory (~50 GB RSS/arm) is the constraint, not
# cores. Example, 256 GB box: phase 1 = `full` alone, then answer
# arms 4-5 at a time with disjoint KA_CPUSET; phase 2 = the quiet
# timed runs sequentially on the idle machine.
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
# Arms (PERF family; answers must be BYTE-IDENTICAL to full — a
# mismatch is a soundness bug, reported loudly; the measurement is
# the wall/RSS delta):
#   noshare     full + --cfl-intern-planes=false   (COW plane sharing)
#   nofastjoin  full + --cfl-join-fastpath=false   (cluster-mark joins)
#   scratch     full + --cfl-flows-to-incremental=false
#               (FI-ONLY: incremental is refused under fs)
#   lazymint    full + --cfl-lazy-mint             (additive arm)
#   bidi        full + --cfl-bidi-prune            (additive arm)
#               NOTE: perf family AT FI ONLY (answer-preserving,
#               #43 cone re-admission). Under fs, bidi-prune is
#               strictly TIGHTER (a precision lever, one-sided
#               subset) — do not put it in the perf family there.
#
# This script is the FI campaign. The fs-only perf machinery
# (batching, workers, spill, presolve-once) is ablated separately
# at the km corpus (cheap, pinned baselines); kernel fs runs are
# endpoints (full = row5 pin, base = one big-machine run), not a
# matrix.
#
# One-sided expectation for the precision arms: the FULL answer set
# must be a SUBSET of every ablated arm's (mechanisms only remove).
# Any pairs in full but not in an arm beyond that arm's mechanism's
# claim, or any GT FN regression, is reported loudly.
#
# Per arm: <arm>.log, <arm>-pairs.txt (sorted unique), <arm>-gt.txt,
# and a row in summary.tsv. Arms with an existing pairs file are
# skipped (delete the file or set KA_FORCE=1 to re-run).
#
# TIMED RUNS: answer runs use --verbose=2 + dumps, whose logging is
# real I/O. Arms whose timing the paper reports (full, base, and
# the perf family) therefore get a SECOND, quiet run: --verbose=0,
# no --log-timestamps, no icall dump, all output to /dev/null, only
# /usr/bin/time -v recorded. summary.tsv reports it as timed_s;
# solve_s (from the answer run's timestamps) remains indicative for
# the other arms. GraCFL's engine debug output is silent by default
# (GRACFL_VERBOSE=1 restores it).
#
# THREADS / PINNING / PARALLEL ARMS:
#   KA_THREADS=N   bounds OpenMP/TBB threads (exported as
#                  OMP_NUM_THREADS; set it for ANY timed row so
#                  baselines like GraCFL don't grab all cores).
#   KA_CPUSET=A-B  pins the run via taskset -c.
#   PERF-family arms are TIMED: run them alone on an otherwise
#   idle machine (or an exclusive cpuset), one at a time.
#   PRECISION-family arms are answer-only: their wall column is
#   indicative, so instances MAY run in parallel — protocol:
#     1. run any single arm first so gtaux.txt exists (avoids the
#        dump race), e.g. eval/60-kernel-fse.sh full
#     2. launch instances with DISJOINT arm lists and DISJOINT
#        KA_CPUSET ranges; budget ~50 GB RSS per kernel-FI arm.
#     3. finish with one plain invocation: completed arms are
#        skipped and summary.tsv is rebuilt over everything.

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
[[ -n "${KA_THREADS:-}" ]] && export OMP_NUM_THREADS="$KA_THREADS" \
                                     TBB_NUM_THREADS="$KA_THREADS"
PIN=()
[[ -n "${KA_CPUSET:-}" ]] && PIN=(taskset -c "$KA_CPUSET")

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
    noshare)     echo "${FULLPREC[@]} --cfl-intern-planes=false --func-summaries=$SUM" ;;
    nofastjoin)  echo "${FULLPREC[@]} --cfl-join-fastpath=false --func-summaries=$SUM" ;;
    scratch)     echo "${FULLPREC[@]} --cfl-flows-to-incremental=false --func-summaries=$SUM" ;;
    lazymint)    echo "${FULLPREC[@]} --cfl-lazy-mint --func-summaries=$SUM" ;;
    bidi)        echo "${FULLPREC[@]} --cfl-bidi-prune --func-summaries=$SUM" ;;
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
  /usr/bin/time -v "${PIN[@]}" "$KA_BIN" "${COMMON[@]}" $flags \
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
  "${PIN[@]}" "$KA_BIN" "${COMMON[@]}" --cfl-dump-gt-aux --func-summaries="$SUM" \
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

EXACT_ARMS=" noshare nofastjoin scratch lazymint bidi "
ARMS=("$@")
[[ ${#ARMS[@]} -eq 0 ]] && ARMS=(full base noregf nochain notpkeys
                                 noopstables noinvoke nosummaries
                                 noshare nofastjoin scratch lazymint bidi)

TIMED_ARMS=" full base noshare nofastjoin scratch lazymint bidi "

timed_run() { # quiet second pass for reportable timing
  local arm="$1" tlog="$OUT/$arm-timed.log"
  [[ "$TIMED_ARMS" == *" $arm "* ]] || return 0
  [[ -s "$tlog" && "${KA_FORCE:-0}" != 1 ]] && return 0
  local flags; flags=$(arm_flags "$arm") || return 1
  echo "== $arm: timed run ($(date -Is))"
  # shellcheck disable=SC2086
  /usr/bin/time -v -o "$tlog" "${PIN[@]}" "$KA_BIN" \
      --verbose=0 --cfl-compositional=false --cfl-flows-to \
      --mem-limit="$KA_MEMLIMIT" $flags \
      @"$KA_KERNEL_BCLIST" > /dev/null 2>&1
  local rc=$?
  [[ $rc -ne 0 ]] && echo "!! $arm timed run exited $rc" >&2
  return 0
}

gt_aux
for a in "${ARMS[@]}"; do run_arm "$a" || exit 1; timed_run "$a"; done

# Summary table. Deltas are vs full: removed = in arm, not in full
# (what the mechanisms delete); added = in full, not in arm (MUST be
# 0 for one-sided precision arms; nonzero is loud).
SUMTSV="$OUT/summary.tsv"
{
  echo -e "arm\tfamily\tpairs\tremoved_vs_full\tadded_vs_full\tidentical\tge100_callers\tmax_fanout\tgt_fn\tsolve_s\ttimed_wall\ttimed_rss_kb"
  for a in "${ARMS[@]}"; do
    p="$OUT/$a-pairs.txt"; [[ -s "$p" ]] || continue
    n=$(wc -l < "$p")
    fam=precision; ident="-"
    if [[ "$EXACT_ARMS" == *" $a "* ]]; then
      fam=perf
      if cmp -s "$p" "$OUT/full-pairs.txt"; then ident=yes; else ident="NO(BUG)"; fi
    fi
    if [[ "$a" == full ]]; then rem=0; add=0; else
      rem=$(comm -23 "$p" "$OUT/full-pairs.txt" | wc -l)
      add=$(comm -13 "$p" "$OUT/full-pairs.txt" | wc -l)
    fi
    read -r c100 maxf <<< "$(fat_tail "$a")"
    fn=$(gt_match "$a")
    # Solve-phase wall = last --log-timestamps stamp BEFORE the icall
    # dump begins. End-to-end wall includes dumping millions of ICALL
    # lines, which scales with the answer size and would credit
    # precision arms with I/O savings, not solver savings.
    firsticall=$(grep -nm1 '^ICALL ' "$OUT/$a.log" | cut -d: -f1)
    if [[ -n "$firsticall" ]]; then
      solve=$(head -n $((firsticall-1)) "$OUT/$a.log" \
              | grep -oE '^\[\+[0-9]+\.[0-9]+s\]' | tail -1 | tr -d '[+s]')
    else
      solve=""
    fi
    tsrc="$OUT/$a-timed.log"; [[ -s "$tsrc" ]] || tsrc="$OUT/$a.log"
    wall=$(grep -oE 'Elapsed \(wall clock\).*' "$tsrc" | awk '{print $NF}' | tail -1)
    rss=$(grep -oE 'Maximum resident set size.*[0-9]+' "$tsrc" | grep -oE '[0-9]+$' | tail -1)
    echo -e "$a\t$fam\t$n\t$rem\t$add\t$ident\t$c100\t$maxf\t$fn\t${solve:--}\t${wall:--}\t${rss:--}"
  done
} | tee "$SUMTSV"

# Loud checks: precision arms must not miss pairs the full stack
# reports; perf arms must be byte-identical.
awk -F'\t' 'NR>1 && $2=="precision" && $1!="full" && $1!="nosummaries" && $5+0>0 {
  print "!! ONE-SIDED VIOLATION: arm " $1 " is missing " $5 \
        " pairs that the FULL stack reports — investigate before use."
  bad=1 }
NR>1 && $2=="perf" && $6!="yes" {
  print "!! EXACTNESS VIOLATION: perf arm " $1 " is not byte-identical" \
        " to full — soundness bug, do not use."
  bad=1 } END{exit bad}' "$SUMTSV" || exit 2
echo "== all arms complete: $SUMTSV"
