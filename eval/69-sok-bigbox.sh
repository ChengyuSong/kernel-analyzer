#!/bin/bash
# SoK-MLTA comparison, end to end, for a big server: completed httpd
# (APR/APR-util linked), ORCFL (eval/62) on both artifact LLVM sets, every
# whole-program baseline (eval/67: SVF + all Lotus analyses), their scoring
# (eval/65, incl. pairwise tables) and our per-site report without their
# LLVM-CFI fallback (tools/sok-report.py).
#
# Steps (run in order, or `all`):
#   build        images: sok-toolchain, svf-baseline, lotus-baseline-next
#                (network; Lotus source from KA_LOTUS_SRC at the pinned
#                commit) -- OR `images-load FILE` a bundle made elsewhere
#                with `images-save FILE`
#   prepare      overlay artifact root under $W/sok-root: real copies (hard
#                links when possible) of the artifact's bitcodes, ground
#                truth and pre-computed logs, with every httpd.bc replaced
#                by the APR-completed one (eval/68 inside sok-toolchain);
#                the original artifact is never modified
#   run          all analyses, KA_BIGBOX_PAR jobs at a time, one CPU each
#   report       eval/65 (pairwise on) + tools/sok-report.py -> $W/report.md
#   all          prepare + run + report
#
# Env:
#   KA_SOK_ROOT      original artifact root (bitcodes/, pre-computed/,
#                    fuzz_groundtruth/)                          [required]
#   KA_SOK_REPO      SoK-MLTA code checkout (scripts/compare_approaches.py)
#   KA_BIGBOX_WORK   work dir (default $KA_RESULTS/sok-bigbox) = $W
#   KA_BIGBOX_PAR    concurrent jobs (default 24); use 1 for a solo-timed pass
#   KA_DF_MEM        per-baseline container memory (default 256g)
#   KA_DF_TIMEOUT    per-baseline, per-program timeout (default 14400 s)
#   KA_BIGBOX_APPR   baseline approaches (default: all of eval/67)
#   KA_APR_SRC       dir with apr-1.7.6.tar.gz + apr-util-1.6.4.tar.gz
#                    (downloaded from archive.apache.org when missing)
#   KA_LOTUS_SRC     Lotus git checkout for `build` (commit pinned in eval/67)
#   KA_BIN           KAMain binary (env.sh default: $KA_REPO/release/lib/KAMain)
#
# Outputs: $W/sok (ORCFL, SVF and Lotus rows, all on the LLVM 15 files;
# Lotus reads their LLVM-14 conversion), $W/merged-llvm15 (their tables,
# pair-*/ tables), $W/report.md, $W/jobs/*.log. KA_BIGBOX_LLVM14=1 adds
# ORCFL on the artifact's own LLVM 14 build ($W/sok-llvm14).

set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
ka_require docker python3
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
W="${KA_BIGBOX_WORK:-$KA_RESULTS/sok-bigbox}"
PAR="${KA_BIGBOX_PAR:-24}"
export KA_DF_MEM="${KA_DF_MEM:-256g}"
export KA_DF_TIMEOUT="${KA_DF_TIMEOUT:-14400}"
APR_SRC="${KA_APR_SRC:-$W/apr-src}"
IMAGES="sok-toolchain svf-baseline lotus-baseline lotus-baseline-next"
ALL_APPR="SVF-Andersen SVF-VFS AserPTA-CI AserPTA-1CFA AserPTA-2CFA DyckAA \
SeaDsa AserPTA-CI-shape DyckAA-shape GPG-FSCS GPG-FICS GPG-FICI LotusAA \
TPA-K0 TPA-K1 FSPTA VFSPTA VFPTA SparrowAA BootstrapAA DDA-Flow \
AserPTA-Origin CHA RTA VTA OTF"
APPR="${KA_BIGBOX_APPR:-$ALL_APPR}"
SETS15="soundness_unifuzz/build_O0 soundness_unifuzz/build_O3 \
soundness_ossfuzz/O0_12.15.2025 soundness_ossfuzz/O3_12.15.2025"
SETS14="soundness_unifuzz/build_O0 soundness_ossfuzz/O0_12.15.2025 \
soundness_ossfuzz/O3_12.15.2025"
ROOT="$W/sok-root"
mkdir -p "$W/jobs"

need_root() { : "${KA_SOK_ROOT:?set KA_SOK_ROOT to the SoK artifact root}"; }

build() {
  docker build -f "$HERE/sok-toolchain.Dockerfile" -t sok-toolchain "$HERE"
  "$HERE/67-dataflow-baselines.sh" build
}

images_save() {
  local f="${1:?usage: images-save FILE}"
  local have=(); for i in $IMAGES; do
    docker image inspect "$i" >/dev/null 2>&1 && have+=("$i"); done
  echo "== saving: ${have[*]} -> $f"
  docker save "${have[@]}" | zstd -T0 -q -o "$f"
}

images_load() {
  local f="${1:?usage: images-load FILE}"
  zstd -dc "$f" | docker load
}

copy_tree() {  # src dst: hard links when on the same filesystem, else copy
  mkdir -p "$(dirname "$2")"
  cp -al "$1" "$2" 2>/dev/null || { rm -rf "$2"; cp -r "$1" "$2"; }
}

prepare() {
  need_root
  rm -rf "$ROOT"; mkdir -p "$ROOT/bitcodes"
  copy_tree "$KA_SOK_ROOT/pre-computed" "$ROOT/pre-computed"
  copy_tree "$KA_SOK_ROOT/fuzz_groundtruth" "$ROOT/fuzz_groundtruth"
  for s in $SETS15; do copy_tree "$KA_SOK_ROOT/bitcodes/llvm15/$s" "$ROOT/bitcodes/llvm15/$s"; done
  for s in $SETS14; do copy_tree "$KA_SOK_ROOT/bitcodes/llvm14/$s" "$ROOT/bitcodes/llvm14/$s"; done

  mkdir -p "$APR_SRC"
  for t in apr-1.7.6.tar.gz apr-util-1.6.4.tar.gz; do
    [[ -s "$APR_SRC/$t" ]] || curl -fsSL -o "$APR_SRC/$t" \
      "https://archive.apache.org/dist/apr/$t"
  done
  for v in 15 14; do
    echo "== APR bitcode, LLVM $v (inside sok-toolchain)"
    docker run --rm --network none -u "$(id -u):$(id -g)" \
      -v "$KA_REPO":/repo:ro -v "$APR_SRC":/aprsrc:ro \
      -v "$KA_SOK_ROOT":/sokroot:ro -v "$W":/w \
      -e KA_SOK_ROOT=/sokroot -e KA_SOK_OUT=/w/apr -e KA_RESULTS=/w \
      -e KA_APR_LLVM="$v" -e KA_APR_SRC=/aprsrc -e HOME=/tmp \
      sok-toolchain bash /repo/eval/68-sok-httpd-apr.sh \
      > "$W/jobs/apr-llvm$v.log" 2>&1 \
      || { echo "!! APR build llvm$v failed: $W/jobs/apr-llvm$v.log" >&2; exit 1; }
    grep '^==' "$W/jobs/apr-llvm$v.log"
    for opt in O0 O3; do
      local dst="$ROOT/bitcodes/llvm$v/soundness_ossfuzz/${opt}_12.15.2025/httpd/bin/httpd.bc"
      local src="$W/apr/httpd-linked/llvm$v/$opt/httpd.bc"
      [[ -s "$src" ]] || { echo "!! missing $src" >&2; exit 1; }
      rm -f "$dst"; cp "$src" "$dst"      # rm first: never write through a hard link
    done
  done
  # Lotus is LLVM 14 only: convert the (APR-completed) LLVM 15 sets so
  # Lotus rows read the same programs as ORCFL and SVF (eval/sok-downgrade.sh)
  for s in $SETS15; do
    docker run --rm --network none -u "$(id -u):$(id -g)" \
      -v "$KA_REPO":/repo:ro -v "$ROOT":/root_ \
      sok-toolchain bash /repo/eval/sok-downgrade.sh \
      "/root_/bitcodes/llvm15/$s" "/root_/bitcodes/llvm15down/$s" \
      >> "$W/jobs/downgrade.log" 2>&1 \
      || { echo "!! downgrade failed: $W/jobs/downgrade.log" >&2; exit 1; }
  done
  grep '^==' "$W/jobs/downgrade.log"
  {
    echo "overlay of $KA_SOK_ROOT, $(date -Is)"
    echo "httpd.bc (llvm14/llvm15 x O0/O3) = artifact httpd.bc + APR 1.7.6 + APR-util 1.6.4 (eval/68)"
    echo "llvm15down/ = llvm15/ converted for LLVM 14 (eval/sok-downgrade.sh), read by the Lotus rows"
    sha256sum "$ROOT"/bitcodes/llvm1?/soundness_ossfuzz/*/httpd/bin/httpd.bc
  } > "$ROOT/PROVENANCE"
  echo "== overlay ready: $ROOT"
}

# ---- job pool: one CPU per job, at most $PAR at once ----------------------
declare -a PIDS=()
NEXT_CPU=0
NCPU=$(nproc)
launch() {  # name, then a command line (run via bash -c with env set)
  local name=$1; shift
  while (( $(jobs -rp | wc -l) >= PAR )); do wait -n || true; done
  local cpu=$(( NEXT_CPU % NCPU )); NEXT_CPU=$(( NEXT_CPU + 1 ))
  echo "== launch $name on cpu $cpu"
  ( KA_CPUSET=$cpu bash -c "$*" > "$W/jobs/$name.log" 2>&1
    echo "rc=$?" > "$W/jobs/$name.done" ) &
}

run() {
  [[ -d "$ROOT/bitcodes" ]] || { echo "!! run 'prepare' first" >&2; exit 1; }
  [[ -x "$KA_BIN" ]] || { echo "!! KAMain not built: $KA_BIN" >&2; exit 1; }
  echo "== KAMain $(sha256sum "$KA_BIN" | cut -c1-16) ($KA_BIN)" | tee "$W/jobs/kamain.txt"
  rm -f "$W/jobs"/*.done
  local s
  for s in $SETS15; do
    launch "orcfl-llvm15-${s//\//_}" \
      "KA_SOK_BC=$ROOT/bitcodes/llvm15/$s KA_SOK_OUT=$W/sok '$HERE/62-sok-arm.sh'"
  done
  if [[ "${KA_BIGBOX_LLVM14:-0}" == 1 ]]; then   # artifact's own LLVM 14 build
    for s in $SETS14; do
      launch "orcfl-llvm14-${s//\//_}" \
        "KA_SOK_BC=$ROOT/bitcodes/llvm14/$s KA_SOK_OUT=$W/sok-llvm14 '$HERE/62-sok-arm.sh'"
    done
  fi
  local a
  for a in $APPR; do   # Lotus rows read llvm15down: all rows in ONE table
    launch "base-$a" \
      "KA_SOK_ROOT=$ROOT KA_SOK_OUT=$W/sok KA_LOTUS_BCSET=llvm15down '$HERE/67-dataflow-baselines.sh' run $a"
  done
  wait
  echo "== all jobs finished; non-zero:"
  grep -L '^rc=0$' "$W"/jobs/*.done || true
}

report() {
  : "${KA_SOK_REPO:?set KA_SOK_REPO to the SoK-MLTA code checkout}"
  local pair
  local pairs="sok:merged-llvm15"
  [[ -d "$W/sok-llvm14" ]] && pairs="$pairs sok-llvm14:merged-llvm14"
  for pair in $pairs; do
    rm -rf "$W/${pair##*:}"
    KA_SOK_ROOT="$ROOT" KA_SOK_OUT="$W/${pair%%:*}" \
      KA_SOK_MERGED="$W/${pair##*:}" KA_SOK_PAIRWISE=1 \
      "$HERE/65-sok-compare.sh" > "$W/jobs/compare-${pair##*:}.log" 2>&1
  done
  local m="$W/merged-llvm15" t="$W/sok"
  [[ -d "$W/merged-llvm14" ]] && { m="$m,$W/merged-llvm14"; t="$t,$W/sok-llvm14"; }
  KA_SOK_ROOT="$ROOT" python3 "$KA_REPO/tools/sok-report.py" \
    --merged "$m" --times "$t" > "$W/report.md"
  echo "== report: $W/report.md"
}

case "${1:-}" in
  build) build ;;
  images-save) images_save "${2:-}" ;;
  images-load) images_load "${2:-}" ;;
  prepare) prepare ;;
  run) run ;;
  report) report ;;
  all) prepare; run; report ;;
  *) echo "usage: $0 build|images-save F|images-load F|prepare|run|report|all" >&2; exit 2 ;;
esac
