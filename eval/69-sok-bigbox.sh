#!/bin/bash
# SoK-MLTA comparison, end to end, for a big server: completed httpd
# (APR/APR-util linked), ORCFL (eval/62) on both artifact LLVM sets, every
# whole-program baseline (eval/67: SVF + all Lotus analyses), their scoring
# (eval/65, incl. pairwise tables) and our per-site report without their
# LLVM-CFI fallback (tools/sok-report.py).
#
# Everything is fetched and built from pinned sources on the machine that
# runs it, including the SoK authors' dataset (Google Drive, via a pinned
# gdown; archives sha256-checked):
#   export KA_BIGBOX_WORK=/big/sok
#   eval/69-sok-bigbox.sh setup    # once: download + clone + build (network)
#   eval/69-sok-bigbox.sh all      # prepare + run + report
#
# Steps (run in order, or `all` after `setup`):
#   setup        checks docker/git/curl; downloads the SoK dataset unless
#                KA_SOK_ROOT is given; clones SoK-MLTA and Lotus at pinned
#                commits into $W/src; downloads APR/APR-util (sha256-
#                checked); docker-builds sok-toolchain, svf-baseline (SVF at
#                a pinned commit) and lotus-baseline-next; writes
#                $W/bigbox.env so later steps need only KA_BIGBOX_WORK
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
#   KA_SOK_ROOT      existing SoK dataset root (bitcodes/, pre-computed/,
#                    fuzz_groundtruth/); unset: setup downloads it
#   KA_SOK_REPO      SoK-MLTA checkout (default: setup's clone)
#   KA_BIGBOX_WORK   work dir (default $KA_RESULTS/sok-bigbox) = $W
#   KA_BIGBOX_PAR    concurrent jobs (default 24); use 1 for a solo-timed pass
#   KA_DF_MEM        per-baseline container memory (default 256g)
#   KA_DF_TIMEOUT    per-baseline, per-program timeout (default 14400 s)
#   KA_BIGBOX_APPR   baseline approaches (default: all of eval/67)
#   KA_APR_SRC       APR tarball dir (default $W/apr-src; downloaded and
#                    sha256-checked by setup/prepare)
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
# `setup` records its paths; explicit env wins.
if [[ -f "$W/bigbox.env" ]]; then
  _r="${KA_SOK_ROOT:-}"; _p="${KA_SOK_REPO:-}"; _a="${KA_APR_SRC:-}"
  set -a; source "$W/bigbox.env"; set +a   # exported: child stages read them
  [[ -n "$_r" ]] && KA_SOK_ROOT=$_r; [[ -n "$_p" ]] && KA_SOK_REPO=$_p
  [[ -n "$_a" ]] && KA_APR_SRC=$_a
fi
PAR="${KA_BIGBOX_PAR:-24}"
export KA_DF_MEM="${KA_DF_MEM:-256g}"
export KA_DF_TIMEOUT="${KA_DF_TIMEOUT:-14400}"
APR_SRC="${KA_APR_SRC:-$W/apr-src}"
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


# Pinned sources (everything that can be cloned or built is, by `setup`).
SOK_REPO_URL=https://github.com/yufeidu/SoK-MLTA
SOK_REPO_COMMIT=d438079b2f272a8a6bd90d193f3e9f27ef94f886
LOTUS_URL=https://github.com/ZJU-PL/lotus.git
LOTUS_COMMIT=0da4c2813005249bce390329d28810a2c4ac0e76   # = eval/67's pin
declare -A APR_SHA256=(
  [apr-1.7.6.tar.gz]=6a10e7f7430510600af25fabf466e1df61aaae910bf1dc5d10c44a4433ccc81d
  [apr-util-1.6.4.tar.gz]=9160444764bd1d804d7e6ee50783ec9442a88b5a8984e62470832b06983eeaa4 )
SOK_DRIVE=https://drive.google.com/drive/folders/1na-6VsbZcPwDwezQWNHCpjwkp5ZhFTOL
# The dataset archives in that folder (Drive file id, sha256, content), as
# downloaded and checked against our working copy on 2026-09-28:
#   bitcodes.tgz      4.4 GB  bitcodes/llvm{14,15}/...
#   pre-computed.tgz  2.3 MB  pre-computed/ + fuzz_groundtruth/
declare -A SOK_FILE_ID=(
  [bitcodes.tgz]=1xVMdB7ZYlt3ywc9WS_ofEKGy8bhC9JB4
  [pre-computed.tgz]=1sjsJdrkBtQHU2sBurPAFhWv1zDmZO1Kk )
declare -A SOK_SHA256=(
  [bitcodes.tgz]=41e0a2597ad37aea06b6868437b5ab518656476e9b495e3864fea79c2476765a
  [pre-computed.tgz]=ab10952f77871c96b4a32ff80f175e99f43aa94c3364af42d4d52048531d7dad )
GDOWN_IMAGE=python@sha256:f77ac9e44ae96ef2c90b8053ea08c31f8be030f824196b0ae4db6d462c84e51f
GDOWN_VERSION=6.4.0

fetch_dataset() {  # Drive -> $W/sok-dataset (only the sets eval/69 uses)
  local dl="$W/downloads" f d; mkdir -p "$dl"
  for f in "${!SOK_FILE_ID[@]}"; do
    if ! echo "${SOK_SHA256[$f]}  $dl/$f" | sha256sum -c --quiet 2>/dev/null; then
      echo "== downloading $f from the SoK authors' Drive folder"
      docker run --rm -u "$(id -u):$(id -g)" -e HOME=/tmp -v "$dl":/out "$GDOWN_IMAGE" \
        sh -c "pip install -q --user gdown==$GDOWN_VERSION >/dev/null 2>&1 && python -m gdown -q -O /out/$f ${SOK_FILE_ID[$f]}" \
        || { echo "!! download of $f failed (Drive quota? retry later, or download $SOK_DRIVE by hand into $dl)" >&2; exit 1; }
      echo "${SOK_SHA256[$f]}  $dl/$f" | sha256sum -c --quiet \
        || { echo "!! $f checksum mismatch: the dataset changed upstream" >&2; exit 1; }
    fi
  done
  local root="$W/sok-dataset" sub=() s; mkdir -p "$root"
  tar -xzf "$dl/pre-computed.tgz" -C "$root"
  for s in $SETS15; do sub+=("bitcodes/llvm15/$s"); done
  for s in $SETS14; do sub+=("bitcodes/llvm14/$s"); done
  tar -xzf "$dl/bitcodes.tgz" -C "$root" "${sub[@]}"
  export KA_SOK_ROOT="$root"
}

clone_at() {  # url dir commit: fetch exactly one commit, check it out
  local url=$1 dir=$2 sha=$3
  if [[ ! -d "$dir/.git" ]]; then git init -q "$dir"; git -C "$dir" remote add origin "$url"; fi
  git -C "$dir" fetch -q --depth 1 origin "$sha"
  git -C "$dir" checkout -q --detach "$sha"
  [[ "$(git -C "$dir" rev-parse HEAD)" == "$sha" ]] || { echo "!! $dir not at $sha" >&2; exit 1; }
}

fetch_apr() {  # download (if missing) and verify the APR tarballs
  mkdir -p "$APR_SRC"; local t
  for t in "${!APR_SHA256[@]}"; do
    [[ -s "$APR_SRC/$t" ]] || curl -fsSL -o "$APR_SRC/$t" "https://archive.apache.org/dist/apr/$t"
    echo "${APR_SHA256[$t]}  $APR_SRC/$t" | sha256sum -c --quiet \
      || { echo "!! checksum mismatch: $APR_SRC/$t" >&2; exit 1; }
  done
}

check_artifact() {  # the one manual input: the SoK authors' dataset (data, not code)
  local d; need_root
  for d in pre-computed fuzz_groundtruth; do
    [[ -d "$KA_SOK_ROOT/$d" ]] || { echo "!! $KA_SOK_ROOT/$d missing" >&2; artifact_help; }
  done
  for d in $SETS15; do [[ -d "$KA_SOK_ROOT/bitcodes/llvm15/$d" ]] || { echo "!! missing bitcodes/llvm15/$d" >&2; artifact_help; }; done
  for d in $SETS14; do [[ -d "$KA_SOK_ROOT/bitcodes/llvm14/$d" ]] || { echo "!! missing bitcodes/llvm14/$d" >&2; artifact_help; }; done
}
artifact_help() {
  echo "   The SoK-MLTA dataset (pre-built bitcodes, pre-computed LLVM-CFI/KallGraph/HPCFI" >&2
  echo "   results, fuzz ground truth) is hosted by its authors at $SOK_DRIVE ." >&2
  echo "   Download and decompress it, then set KA_SOK_ROOT to the directory holding" >&2
  echo "   bitcodes/, pre-computed/ and fuzz_groundtruth/." >&2
  exit 1
}

setup() {  # clone + build everything from pinned sources on this machine
  local miss=() t
  for t in docker git curl python3 tar sha256sum; do command -v $t >/dev/null || miss+=("$t"); done
  (( ${#miss[@]} )) && { echo "!! install first: ${miss[*]}" >&2; exit 1; }
  docker info >/dev/null 2>&1 || { echo "!! docker daemon not reachable by $(id -un)" >&2; exit 1; }
  # dataset: an existing KA_SOK_ROOT is used as is; otherwise it is
  # downloaded (gdown, pinned) and sha256-checked
  [[ -n "${KA_SOK_ROOT:-}" ]] || fetch_dataset
  check_artifact
  echo "== SoK-MLTA scripts @ ${SOK_REPO_COMMIT:0:12}"
  clone_at "$SOK_REPO_URL" "$W/src/SoK-MLTA" "$SOK_REPO_COMMIT"
  echo "== Lotus @ ${LOTUS_COMMIT:0:12}"
  clone_at "$LOTUS_URL" "$W/src/lotus" "$LOTUS_COMMIT"
  echo "== APR sources (sha256-checked)"
  fetch_apr
  echo "== building images from Dockerfiles (sok-toolchain, svf-baseline, lotus-baseline-next)"
  docker build -f "$HERE/sok-toolchain.Dockerfile" -t sok-toolchain "$HERE" > "$W/jobs/build-toolchain.log" 2>&1 \
    || { echo "!! see $W/jobs/build-toolchain.log" >&2; exit 1; }
  KA_SOK_ROOT="$KA_SOK_ROOT" KA_LOTUS_SRC="$W/src/lotus" KA_LOTUS_COMMIT="$LOTUS_COMMIT" \
    "$HERE/67-dataflow-baselines.sh" build > "$W/jobs/build-baselines.log" 2>&1 \
    || { echo "!! see $W/jobs/build-baselines.log" >&2; exit 1; }
  cat > "$W/bigbox.env" <<ENV
KA_SOK_ROOT=$KA_SOK_ROOT
KA_SOK_REPO=$W/src/SoK-MLTA
KA_APR_SRC=$APR_SRC
ENV
  echo "== ready ($W/bigbox.env). Next: KA_BIGBOX_WORK=$W $0 all"
}

copy_tree() {  # src dst: hard links when on the same filesystem, else copy
  mkdir -p "$(dirname "$2")"
  cp -al "$1" "$2" 2>/dev/null || { rm -rf "$2"; cp -r "$1" "$2"; }
}

prepare() {
  check_artifact
  rm -rf "$ROOT"; mkdir -p "$ROOT/bitcodes"
  copy_tree "$KA_SOK_ROOT/pre-computed" "$ROOT/pre-computed"
  copy_tree "$KA_SOK_ROOT/fuzz_groundtruth" "$ROOT/fuzz_groundtruth"
  for s in $SETS15; do copy_tree "$KA_SOK_ROOT/bitcodes/llvm15/$s" "$ROOT/bitcodes/llvm15/$s"; done
  for s in $SETS14; do copy_tree "$KA_SOK_ROOT/bitcodes/llvm14/$s" "$ROOT/bitcodes/llvm14/$s"; done

  fetch_apr
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
  setup) setup ;;
  prepare) prepare ;;
  run) run ;;
  report) report ;;
  all) prepare; run; report ;;
  *) echo "usage: $0 setup|prepare|run|report|all" >&2; exit 2 ;;
esac
