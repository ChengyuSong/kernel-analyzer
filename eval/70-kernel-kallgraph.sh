#!/bin/bash
# KallGraph (S&P'25) on a kernel bitcode corpus, in the sandbox, from
# source at its pinned commit. Companion to eval/59 with
# KA_KERNEL_LLVM=14: KallGraph reads LLVM 14 typed-pointer bitcode only,
# so the corpus must be the clang-14 build; KAMain reads the same files,
# so both tools are scored on identical IR (eval/60 with
# KA_KERNEL_BCLIST pointed at the clang-14 list).
#
# SANDBOX (user directive): third-party code runs containerized,
# --network none, host uid, read-only mounts for the kernel tree; only
# the output dir is writable. Cloning + building the image is the single
# networked step. The image (eval/kallgraph-caps.Dockerfile) exposes the
# released implementation's resource caps as environment knobs:
#   KG_EDGE_CAP   DFS path length cap (released: 35)
#   KG_NO_BLOCK   unset = released blacklisting/static blocking on;
#                 1 = off
#
# usage: eval/70-kernel-kallgraph.sh image            # clone + build only
#        eval/70-kernel-kallgraph.sh run <tag> [CAP] [NOBLOCK]
#   tag      output subdir name, e.g. released / cap1000 / noblock
#   CAP      KG_EDGE_CAP (default 35)
#   NOBLOCK  non-empty = KG_NO_BLOCK=1
# env: KA_KERNEL_BCLIST (clang-14 list), KA_KG_OUT (default
#      $KA_RESULTS/kernel-kallgraph), KA_KG_THREADS (default 48),
#      KA_CPUSET, KA_KG_REPO (clone dir, default $KA_WORK/src/kallgraph)
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
ka_require docker git
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMG="${KA_KG_IMAGE:-kallgraph-caps}"
REPO="${KA_KG_REPO:-$KA_WORK/src/kallgraph}"
URL=https://github.com/seclab-ucr/KallGraph
PIN=058f9b5   # the commit the paper's related-work audit cites

build_image() {
  if [[ ! -d "$REPO/.git" ]]; then
    echo "== cloning KallGraph at $PIN into $REPO"
    git clone -q "$URL" "$REPO"
  fi
  git -C "$REPO" checkout -q "$PIN"
  [[ "$(git -C "$REPO" rev-parse --short HEAD)" == "$PIN" ]] \
    || { echo "!! $REPO is not at $PIN" >&2; exit 1; }
  if ! docker image inspect "$IMG" >/dev/null 2>&1; then
    echo "== building $IMG (LLVM 14 + SVF 2.5 from source; expect ~30 min)"
    docker build -f "$HERE/kallgraph-caps.Dockerfile" -t "$IMG" "$REPO"
  fi
}

cmd="${1:-}"
case "$cmd" in
  image) build_image ;;
  run)
    tag="${2:?tag}"; CAP="${3:-35}"; NOBLOCK="${4:-}"
    : "${KA_KERNEL_BCLIST:?set KA_KERNEL_BCLIST to the clang-14 bclist}"
    build_image
    OUT="${KA_KG_OUT:-$KA_RESULTS/kernel-kallgraph}/$tag"
    mkdir -p "$OUT"
    # Every object lives under one tree; mount it read-only at the same
    # absolute path so the host list is valid inside the container.
    TREE=$(python3 -c 'import os,sys; print(os.path.commonpath([l.strip() for l in open(sys.argv[1]) if l.strip()]))' "$KA_KERNEL_BCLIST")
    cp "$KA_KERNEL_BCLIST" "$OUT/bc.list"
    KGBIN=$(docker run --rm --network none "$IMG" sh -c 'find /opt/kallgraph/build -name KallGraph -type f | head -1')
    echo "== KallGraph $PIN on $(wc -l < "$OUT/bc.list") objects under $TREE; cap=$CAP noblock=${NOBLOCK:-0} threads=${KA_KG_THREADS:-48} -> $OUT"
    /usr/bin/time -v -o "$OUT/time" \
    docker run --rm --network none -u "$(id -u):$(id -g)" \
      ${KA_CPUSET:+--cpuset-cpus "$KA_CPUSET"} \
      -v "$TREE":"$TREE":ro -v "$OUT":/out \
      -e KG_EDGE_CAP="$CAP" ${NOBLOCK:+-e KG_NO_BLOCK=1} \
      "$IMG" "$KGBIN" @/out/bc.list -OutputDir=/out -ThreadNum="${KA_KG_THREADS:-48}" \
      > "$OUT/stdout" 2> "$OUT/stderr" || echo "!! KallGraph exited $? (see $OUT/stderr)"
    echo "== done: $(ls -d "$OUT"/2*/ 2>/dev/null | tail -1) (callgraph1/callgraph2/log/stats)"
    ;;
  *) echo "usage: $0 image | run <tag> [CAP] [NOBLOCK]" >&2; exit 2 ;;
esac
