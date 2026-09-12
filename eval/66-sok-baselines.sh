#!/bin/bash
# SoK-MLTA baseline runs ON THIS MACHINE: MLTA, DeepType, TFA, and
# TFA's MLTA-only variant, driven by THEIR run_experiment.py over
# THEIR released bitcodes, inside the sok-baselines image (built
# from source at their pins — see eval/sok-baselines.Dockerfile).
# This adds same-machine timing comparability; recall/AICT are
# answer-set properties and already come from their pre-computed
# results via eval/65.
#
# SANDBOX (user directive): third-party code runs containerized —
# --network none, host uid, read-only mounts for their scripts and
# dataset; only the output dir is writable. Building the image is
# the single networked step.
#
# Fair-timing knobs: KA_THREADS bounds OpenMP (TFA is the only
# OpenMP consumer; default 1 = single-threaded like our arms and
# the other tools); KA_CPUSET pins the container. Run datasets
# sequentially on an otherwise idle box for reportable walls.
# Their harness's per-tool analysis times are printed in each log;
# the per-dataset wall/RSS lands in <tag>.time.
#
# Inputs: KA_SOK_ROOT (artifact root: bitcodes/ + fuzz_groundtruth/
# + pre-computed/), KA_SOK_REPO (their code checkout).
# Output: $KA_RESULTS/sok/baselines/<tag>/{TFA,DeepType,MLTA,
# MLTA_Orig}/{log,parsed_log}/ — the parsed_log dirs slot into
# eval/65's RESULT_DIRS for locally-timed comparison tables.

set -eu
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
ka_require docker

: "${KA_SOK_ROOT:?set KA_SOK_ROOT to the SoK artifact root}"
: "${KA_SOK_REPO:?set KA_SOK_REPO to their code checkout}"
OUT="${KA_SOK_OUT:-$KA_RESULTS/sok}/baselines"
IMG="${KA_SOK_BASE_IMAGE:-sok-baselines}"
mkdir -p "$OUT"

if ! docker image inspect "$IMG" >/dev/null 2>&1; then
  echo "== building $IMG (LLVM 15 from source — expect 1-2 h)"
  docker build -f "$KA_REPO/eval/sok-baselines.Dockerfile" -t "$IMG" \
      "$KA_SOK_REPO"
fi

DOCKER_RUN=(docker run --rm --network none -u "$(id -u):$(id -g)"
            -e "OMP_NUM_THREADS=${KA_THREADS:-1}"
            -v "$KA_SOK_REPO/scripts":/scripts:ro
            -v "$KA_SOK_ROOT":/sok:ro
            -v "$OUT":/results)
[[ -n "${KA_CPUSET:-}" ]] && DOCKER_RUN+=(--cpuset-cpus "$KA_CPUSET")

# tag  dataset-subdir  UNIFUZZ  opt
DATASETS=(
  "ossfuzz_O0 soundness_ossfuzz/O0_12.15.2025 false O0"
  "ossfuzz_O3 soundness_ossfuzz/O3_12.15.2025 false O3"
  "unifuzz_O0 soundness_unifuzz/build_O0      true  O0"
  "unifuzz_O3 soundness_unifuzz/build_O3      true  O3"
)

for spec in "${DATASETS[@]}"; do
  read -r tag sub unifuzz opt <<< "$spec"
  if [[ -d "$OUT/$tag" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "== $tag: output exists, skipping (KA_FORCE=1 to re-run)"
    continue
  fi
  mkdir -p "$OUT/$tag"
  cat > "$OUT/cfg-run-$tag.json" <<EOF
{
  "PROGRAM_TFA": "/home/user/TFA-project/build/lib/analyzer",
  "PROGRAM_DEEPTYPE": "/home/user/DeepType/build/lib/kanalyzer",
  "PROGRAM_MLTA": "/home/user/TFA-project-MLTA/build/lib/analyzer",
  "PROGRAM_MLTA_ORIG": "/home/user/mlta/build/lib/kanalyzer",
  "DATASET_DIR": "/sok/bitcodes/llvm15/$sub",
  "OUTPUT_DIR": "/results/$tag",
  "FUZZING_DIR": "/sok/fuzz_groundtruth/",
  "PRECOMPUTED_DIR": "/sok/pre-computed/soundness/$opt/",
  "REPRODUCTION": false,
  "UNIFUZZ": $unifuzz,
  "FUZZING_ONLY": true
}
EOF
  echo "== $tag: run_experiment ($(date -Is))"
  /usr/bin/time -v -o "$OUT/$tag.time" \
    "${DOCKER_RUN[@]}" -w /scripts "$IMG" \
    python3 run_experiment.py --json "/results/cfg-run-$tag.json" \
    > "$OUT/$tag.log" 2>&1 \
    || { echo "!! $tag: run_experiment failed — see $OUT/$tag.log" >&2; exit 1; }

  cat > "$OUT/cfg-parse-$tag.json" <<EOF
{ "LOG_DIR": "/results/$tag/", "UNIBENCH": $unifuzz }
EOF
  echo "== $tag: parse_dt_log"
  "${DOCKER_RUN[@]}" -w /scripts "$IMG" \
    python3 parse_dt_log.py --json "/results/cfg-parse-$tag.json" \
    >> "$OUT/$tag.log" 2>&1 \
    || { echo "!! $tag: parse_dt_log failed — see $OUT/$tag.log" >&2; exit 1; }
done

echo "== baselines complete under $OUT/<tag>/<approach>/parsed_log/"
echo "== Wire into eval/65 by adding RESULT_DIRS entries, e.g."
echo '==   "MLTA": "/results/baselines/ossfuzz_O0/MLTA/parsed_log/"'
echo "== (65 mounts \$KA_SOK_MERGED at /results; put baselines there"
echo "==  or extend the cmp configs with another mount)."
