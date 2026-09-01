#!/bin/bash
# FSE'27 kernel FIELD-SENSITIVE endpoints (big machine). Per the
# evaluation split, fs is NOT a matrix: two endpoint arms only.
#   fsfull  canonical fs stack + channels + adoption (the paper's
#           headline config; must flag-match the row5 fs pin)
#   fsbase  canonical fs stack, no precision mechanisms
# fs stack (docs/cli-reference.md, big-machine validated):
#   bidi-prune (NOTE: TIGHTER under fs — precision lever here, so it
#   belongs to BOTH arms for flag-matched comparability),
#   nexus-fields=all+ids, rss mem limit, batched roots K=4000,
#   W workers, spill, presolve-once.
#
# SPILL DISCIPLINE (stale-spill incident rule): requires
# KA_SPILL_ROOT on real disk (NOT tmpfs). Each arm gets a fresh
# subdirectory; a nonempty existing one is REFUSED, never reused.
# Spill dirs are removed on success.
#
# Timing: these runs use W worker processes — any reported wall
# states workers=$KA_FS_WORKERS. Answers are byte-identical across
# worker counts (batching theorems + gates), so W may be sized to
# the machine.
#
# Usage:
#   KA_KERNEL_BCLIST=... KA_GT=... KA_SPILL_ROOT=/data/spill \
#     eval/61-kernel-fs-endpoints.sh [fsfull|fsbase ...]

set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

: "${KA_KERNEL_BCLIST:?set KA_KERNEL_BCLIST to the kernel IR filelist}"
: "${KA_SPILL_ROOT:?set KA_SPILL_ROOT (real disk, NOT tmpfs)}"
KA_GT="${KA_GT:-}"
KA_FS_WORKERS="${KA_FS_WORKERS:-32}"
KA_FS_MEMPCT="${KA_FS_MEMPCT:-90}"
OUT="${KA_KERNEL_OUT:-$KA_RESULTS/kernel-fse}"
SUM="$KA_REPO/func_summaries.txt"
mkdir -p "$OUT"

export LC_ALL=C
export MALLOC_ARENA_MAX=2
PIN=()
[[ -n "${KA_CPUSET:-}" ]] && PIN=(taskset -c "$KA_CPUSET")

case "$(df --output=fstype "$KA_SPILL_ROOT" 2>/dev/null | tail -1)" in
  tmpfs|ramfs) echo "!! KA_SPILL_ROOT is on tmpfs — refuse" >&2; exit 1 ;;
esac

COMMON=(--verbose=2 --cfl-compositional=false --cfl-flows-to
        --cfl-dump-icalls --log-timestamps
        --cfl-bidi-prune --cfl-nexus-fields=all+ids
        --mem-limit-mode=rss --mem-limit="$KA_FS_MEMPCT"
        --cfl-batch-roots=4000 --cfl-batch-workers="$KA_FS_WORKERS"
        --cfl-presolve-once)
CHANNELS=(--cfl-propose-chain-summaries --cfl-regfield-apply
          --cfl-regfield-obj --cfl-propose-solved-summaries
          --cfl-adopt-proposed-summaries)

arm_flags() {
  case "$1" in
    fsfull) echo "${CHANNELS[@]} --func-summaries=$SUM" ;;
    fsbase) echo "--func-summaries=$SUM" ;;
    *) echo "unknown arm: $1" >&2; return 1 ;;
  esac
}

run_arm() {
  local arm="$1"
  local pairs="$OUT/$arm-pairs.txt"
  local log="$OUT/$arm.log"
  local spill="$KA_SPILL_ROOT/fse-$arm"
  if [[ -s "$pairs" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "== $arm: pairs exist, skipping"; return 0
  fi
  if [[ -d "$spill" && -n "$(ls -A "$spill" 2>/dev/null)" ]]; then
    echo "!! $arm: spill dir $spill is NONEMPTY — refusing to reuse" >&2
    echo "!! (stale-spill rule). Remove it explicitly to proceed." >&2
    return 1
  fi
  mkdir -p "$spill"
  local flags; flags=$(arm_flags "$arm") || return 1
  echo "== $arm: running (workers=$KA_FS_WORKERS, spill=$spill, $(date -Is))"
  # shellcheck disable=SC2086
  /usr/bin/time -v "${PIN[@]}" "$KA_BIN" "${COMMON[@]}" \
      --cfl-batch-spill="$spill" $flags \
      @"$KA_KERNEL_BCLIST" > "$log" 2>&1
  local rc=$?
  if [[ $rc -ne 0 ]]; then
    echo "!! $arm: exited $rc — spill dir KEPT for diagnosis: $spill" >&2
    return $rc
  fi
  extract_pairs() { sed -n 's/^ICALL \([^ ]*\) :: .* -> \(.*\)$/\1 \2/p' "$1" | sort -u -S2G --parallel=8; }
  extract_pairs "$log" > "$pairs"
  rm -rf "$spill"
  echo "== $arm: $(wc -l < "$pairs") pairs (spill cleaned)"
}

for a in "${@:-fsfull fsbase}"; do run_arm "$a" || exit 1; done

for a in fsfull fsbase; do
  p="$OUT/$a-pairs.txt"; [[ -s "$p" ]] || continue
  n=$(wc -l < "$p")
  gt="-"
  if [[ -n "$KA_GT" && -s "$OUT/gtaux.txt" ]]; then
    python3 "$KA_REPO/tools/gt-match.py" --gt "$KA_GT" --pairs "$p" \
        --aux "$OUT/gtaux.txt" --fn-out "$OUT/$a-fns.txt" \
        > "$OUT/$a-gt.txt" 2>&1
    gt=$(grep -oE 'FN[ =:]+[0-9]+' "$OUT/$a-gt.txt" | grep -oE '[0-9]+' | head -1)
  fi
  echo "== $a: pairs=$n gt_fn=$gt"
done
if [[ -s "$OUT/fsfull-pairs.txt" && -s "$OUT/fsbase-pairs.txt" ]]; then
  add=$(comm -13 "$OUT/fsbase-pairs.txt" "$OUT/fsfull-pairs.txt" | wc -l)
  rem=$(comm -23 "$OUT/fsbase-pairs.txt" "$OUT/fsfull-pairs.txt" | wc -l)
  echo "== fs endpoints: full removes $rem, adds $add (one-sided expects 0 added)"
  [[ "$add" -gt 0 ]] && echo "!! ONE-SIDED VIOLATION under fs — investigate" >&2
fi
