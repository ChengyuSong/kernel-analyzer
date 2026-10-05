#!/bin/bash
# Rerun the data-flow baseline rows that did not finish under the
# reporting cap, with a longer cap and more memory, into a SEPARATE
# output root (the capped results stay as reported).
#
# Rows: from <capped-root>/summary.tsv, status 'timeout' or
# 'killed-oom-or-signal' (crashes — exit-134/139 — are deterministic and
# are not rerun), for the approaches given (default: the comparators the
# paper's table uses, most important first).
#
#   eval/72-rerun-baselines.sh <capped-root> <new-root> [approach...]
# env: KA_SOK_ROOT, KA_RERUN_TIMEOUT (default 86400 s), KA_RERUN_MEM
#      (default 700g), KA_RERUN_PAR (default 2 concurrent), KA_RERUN_CPUS
#      (first cpu to pin from, default 12), KA_LOTUS_BCSET (default
#      llvm15down, as eval/69 runs the Lotus rows).
set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${KA_SOK_ROOT:?set KA_SOK_ROOT}"
CAPPED="${1:?capped baselines dir (…/baselines)}"; NEW="${2:?new root; results land in <new>/baselines}"; shift 2
APPRS=("$@")
[[ ${#APPRS[@]} -eq 0 ]] && APPRS=(SVF-Andersen SVF-VFS AserPTA-CI AserPTA-CI-shape
  AserPTA-Origin SeaDsa OTF AserPTA-1CFA SparrowAA DDA-Flow TPA-K0 TPA-K1 AserPTA-2CFA)
TIMEOUT="${KA_RERUN_TIMEOUT:-86400}"; MEM="${KA_RERUN_MEM:-700g}"
PAR="${KA_RERUN_PAR:-2}"; CPU0="${KA_RERUN_CPUS:-12}"
mkdir -p "$NEW/jobs"
export KA_LOTUS_BCSET="${KA_LOTUS_BCSET:-llvm15down}"
echo "== rerun: cap $TIMEOUT s, mem $MEM, $PAR concurrent; rows from $CAPPED/summary.tsv -> $NEW/baselines"
n=0
for appr in "${APPRS[@]}"; do
  rows=$(awk -F'\t' -v a="$appr" '$1==a && ($4=="timeout" || $4=="killed-oom-or-signal") {print $2"/"$3}' \
         "$CAPPED/summary.tsv" | sort -u | tr '\n' ' ')
  [[ -z "$rows" ]] && { echo "== $appr: nothing to rerun"; continue; }
  while (( $(jobs -rp | wc -l) >= PAR )); do wait -n || true; done
  cpu=$(( CPU0 + n )); n=$(( n + 1 ))
  echo "== $appr on cpu $cpu: $rows"
  ( KA_DF_ROWS="$rows" KA_DF_TIMEOUT="$TIMEOUT" KA_DF_MEM="$MEM" KA_CPUSET="$cpu" \
    KA_SOK_OUT="$NEW" bash -c "'$HERE/67-dataflow-baselines.sh' run '$appr'" \
    > "$NEW/jobs/$appr.log" 2>&1; echo "rc=$?" > "$NEW/jobs/$appr.done" ) &
done
wait
echo "== all reruns finished: $NEW/baselines/summary.tsv"
