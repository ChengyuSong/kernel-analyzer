#!/bin/bash
# FSE'27 user-mode transfer RQ: httpd + postgresql, FI + fs.
# Same-machine companion to eval/60 (kernel FI matrix) and eval/61
# (kernel fs endpoints): run these on the SAME box as the kernel
# arms so wall/RSS columns are comparable, and so the whole campaign
# is reproducible from the repo.
#
# Per corpus (httpd, pg), four arms — endpoints, not a matrix (the
# mechanism ablation story is carried by the kernel matrix; here the
# question is whether the quotient + channels TRANSFER):
#   full    FI, chain + regfield + obj + per-run adoption
#   base    FI, no precision mechanisms
#   fsfull  field-sensitive full (kernel fs convention:
#           --cfl-nexus-fields=all+ids + bidi-prune + presolve-once)
#   fsbase  field-sensitive base (flag-matched fs stack)
#
# FI answer runs carry --cfl-verify-closure (the per-run C0-C7
# certificate); mono fs runs carry it too. Batched fs runs
# (KA_UM_FS_WORKERS>0) cannot: batch mode refuses the certificate by
# design — the exactness argument there is the Lean batching theorem
# + the byte-identity gates.
#
# MEMORY CONTAINMENT (OOM incident 2026-09-11): every run gets
# --mem-limit=$KA_UM_MEMPCT in the analyzer's DEFAULT mode
# (RLIMIT_AS), so a blow-up fails cleanly inside KAMain instead of
# summoning the kernel OOM-killer. Do NOT switch to
# --mem-limit-mode=rss here: the RSS watchdog polls and can be
# outrun. Run fs arms SOLO — never concurrently with other heavy
# jobs. Reference points on a 125 GB box: httpd at P=41 buckets
# needed >91 GB (that is why the fs instrument here is all+ids, ~1/3
# the cost); FI arms are small (httpd ~2 GB, pg ~7 GB).
#
# One-sided expectation: full ⊂ base at FI EXACTLY (+0 added); under
# fs, up to a named weld (kernel showed one 0.02% EFI weld) — any
# added pairs are reported loudly either way.
#
# Pinned FI reference (this box, 2026-09-12, post regfield
# witness-by-use fix — docs/regfield-literal-table-gap.md; the
# 09-11 full pins 45,479/435,979 are pre-fix, superseded):
#   httpd  full 46,313 / base 81,049
#   pg     full 438,583 / base 1,178,443
# fsfull pins (45,151 / 422,528) are pre-fix — re-cut pending.
#
# Usage:
#   KA_WORK=~/fast/ka-bench eval/64-usermode-fse.sh \
#       [httpd|pg ...] (default both; KA_UM_ARMS picks arms)
#   Batched fs (only if mono fs does not fit):
#     KA_UM_FS_WORKERS=4 KA_SPILL_ROOT=/data/spill ...

set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

OUT="${KA_UM_OUT:-$KA_RESULTS/usermode-fse}"
SUM="$KA_REPO/func_summaries.txt"
KA_UM_MEMPCT="${KA_UM_MEMPCT:-60}"
KA_UM_FS_WORKERS="${KA_UM_FS_WORKERS:-0}"
KA_UM_ARMS="${KA_UM_ARMS:-full base fsfull fsbase}"
mkdir -p "$OUT"

export LC_ALL=C
export MALLOC_ARENA_MAX=2
PIN=()
[[ -n "${KA_CPUSET:-}" ]] && PIN=(taskset -c "$KA_CPUSET")

bclist_for() {
  case "$1" in
    httpd) echo "$KA_WORK/httpd.bclist" ;;
    pg)    echo "$KA_WORK/pg.bclist" ;;
    *) echo "unknown corpus: $1" >&2; return 1 ;;
  esac
}

CHANNELS=(--cfl-propose-chain-summaries --cfl-regfield-apply
          --cfl-regfield-obj --cfl-propose-solved-summaries
          --cfl-adopt-proposed-summaries)
FSSTACK=(--cfl-bidi-prune --cfl-nexus-fields=all+ids --cfl-presolve-once)

arm_flags() { # arm -> per-arm flags; batch tier appended by run_arm
  case "$1" in
    full)   echo "${CHANNELS[@]} --func-summaries=$SUM" ;;
    base)   echo "--func-summaries=$SUM" ;;
    fsfull) echo "${FSSTACK[@]} ${CHANNELS[@]} --func-summaries=$SUM" ;;
    fsbase) echo "${FSSTACK[@]} --func-summaries=$SUM" ;;
    *) echo "unknown arm: $1" >&2; return 1 ;;
  esac
}

extract_pairs() { # log -> sorted unique "caller target" pairs
  sed -n 's/^ICALL \([^ ]*\) :: .* -> \(.*\)$/\1 \2/p' "$1" \
    | sort -u -S1G
}

run_arm() {
  local corpus="$1" arm="$2"
  local bcl; bcl=$(bclist_for "$corpus") || return 1
  [[ -s "$bcl" ]] || { echo "missing bclist $bcl (run 20-build-corpora.sh)" >&2; return 1; }
  local pairs="$OUT/$corpus-$arm-pairs.txt"
  local log="$OUT/$corpus-$arm.log"
  if [[ -s "$pairs" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "== $corpus/$arm: pairs exist, skipping (KA_FORCE=1 to re-run)"
    return 0
  fi
  local flags; flags=$(arm_flags "$arm") || return 1
  local batch=() spill="" cert=(--cfl-verify-closure)
  if [[ "$arm" == fs* && "$KA_UM_FS_WORKERS" -gt 0 ]]; then
    : "${KA_SPILL_ROOT:?batched fs needs KA_SPILL_ROOT (real disk, NOT tmpfs)}"
    case "$(df --output=fstype "$KA_SPILL_ROOT" 2>/dev/null | tail -1)" in
      tmpfs|ramfs) echo "!! KA_SPILL_ROOT is on tmpfs — refuse" >&2; return 1 ;;
    esac
    spill="$KA_SPILL_ROOT/um-$corpus-$arm"
    if [[ -d "$spill" && -n "$(ls -A "$spill" 2>/dev/null)" ]]; then
      echo "!! $corpus/$arm: spill dir $spill NONEMPTY — refusing (stale-spill rule)" >&2
      return 1
    fi
    mkdir -p "$spill"
    batch=(--cfl-batch-roots=4000 --cfl-batch-workers="$KA_UM_FS_WORKERS"
           --cfl-batch-spill="$spill")
    cert=()   # batch mode refuses --cfl-verify-closure by design
  fi
  echo "== $corpus/$arm: running ($(date -Is))"
  # shellcheck disable=SC2086
  /usr/bin/time -v "${PIN[@]}" "$KA_BIN" \
      --verbose=2 --cfl-compositional=false --cfl-flows-to \
      --cfl-dump-icalls --log-timestamps "${cert[@]}" \
      --mem-limit="$KA_UM_MEMPCT" "${batch[@]}" $flags \
      @"$bcl" > "$log" 2>&1
  local rc=$?
  if [[ $rc -ne 0 ]]; then
    echo "!! $corpus/$arm: KAMain exited $rc — see $log" >&2
    [[ -n "$spill" ]] && echo "!! spill dir KEPT for diagnosis: $spill" >&2
    return $rc
  fi
  extract_pairs "$log" > "$pairs"
  [[ -n "$spill" ]] && rm -rf "$spill"
  echo "== $corpus/$arm: $(wc -l < "$pairs") pairs"
}

timed_run() { # quiet second pass: no dump/cert/logging in the wall
  local corpus="$1" arm="$2"
  local tlog="$OUT/$corpus-$arm-timed.log"
  [[ -s "$tlog" && "${KA_FORCE:-0}" != 1 ]] && return 0
  if [[ "$arm" == fs* && "${KA_UM_TIMED_FS:-0}" != 1 ]]; then
    # fs walls come from the answer run's time -v (same convention
    # as eval/61); KA_UM_TIMED_FS=1 forces a quiet mono pass.
    return 0
  fi
  local bcl; bcl=$(bclist_for "$corpus") || return 1
  local flags; flags=$(arm_flags "$arm") || return 1
  echo "== $corpus/$arm: timed run ($(date -Is))"
  # shellcheck disable=SC2086
  /usr/bin/time -v -o "$tlog" "${PIN[@]}" "$KA_BIN" \
      --verbose=0 --cfl-compositional=false --cfl-flows-to \
      --mem-limit="$KA_UM_MEMPCT" $flags \
      @"$bcl" > /dev/null 2>&1
  local rc=$?
  [[ $rc -ne 0 ]] && echo "!! $corpus/$arm timed run exited $rc" >&2
  return 0
}

CORPORA=("$@")
[[ ${#CORPORA[@]} -eq 0 ]] && CORPORA=(httpd pg)

for c in "${CORPORA[@]}"; do
  for a in $KA_UM_ARMS; do
    run_arm "$c" "$a" || exit 1
    timed_run "$c" "$a"
  done
done

# Summary + loud checks. Deltas per mode are full vs base (removed =
# what the mechanisms delete; added MUST be 0 — one-sided).
SUMTSV="$OUT/summary.tsv"
{
  echo -e "corpus\tarm\tpairs\tremoved_vs_base\tadded_vs_base\ttimed_wall\ttimed_rss_kb"
  for c in httpd pg; do
    for a in full base fsfull fsbase; do
      p="$OUT/$c-$a-pairs.txt"; [[ -s "$p" ]] || continue
      n=$(wc -l < "$p")
      rem="-"; add="-"
      ref=""
      case "$a" in full) ref="$OUT/$c-base-pairs.txt" ;;
                   fsfull) ref="$OUT/$c-fsbase-pairs.txt" ;; esac
      if [[ -n "$ref" && -s "$ref" ]]; then
        rem=$(comm -13 "$p" "$ref" | wc -l)   # base-only = removed by mechanisms
        add=$(comm -23 "$p" "$ref" | wc -l)   # full-only = MUST be 0
      fi
      tsrc="$OUT/$c-$a-timed.log"; [[ -s "$tsrc" ]] || tsrc="$OUT/$c-$a.log"
      wall=$(grep -oE 'Elapsed \(wall clock\).*' "$tsrc" | awk '{print $NF}' | tail -1)
      rss=$(grep -oE 'Maximum resident set size.*[0-9]+' "$tsrc" | grep -oE '[0-9]+$' | tail -1)
      echo -e "$c\t$a\t$n\t$rem\t$add\t${wall:--}\t${rss:--}"
    done
    # fs-as-mechanism row: fsfull vs FI full (fs should only tighten).
    if [[ -s "$OUT/$c-fsfull-pairs.txt" && -s "$OUT/$c-full-pairs.txt" ]]; then
      t=$(comm -13 "$OUT/$c-fsfull-pairs.txt" "$OUT/$c-full-pairs.txt" | wc -l)
      w=$(comm -23 "$OUT/$c-fsfull-pairs.txt" "$OUT/$c-full-pairs.txt" | wc -l)
      echo -e "$c\tfs-vs-fi\t-\t$t\t$w\t-\t-" # removed=FI-only (tightened), added=fs-only
    fi
  done
} | tee "$SUMTSV"

awk -F'\t' 'NR>1 && ($2=="full"||$2=="fsfull") && $5!="-" && $5+0>0 {
  print "!! ONE-SIDED VIOLATION: " $1 "/" $2 " adds " $5 " pairs over base — investigate."
  bad=1 } END{exit bad}' "$SUMTSV" || exit 2
echo "== usermode campaign complete: $SUMTSV"
