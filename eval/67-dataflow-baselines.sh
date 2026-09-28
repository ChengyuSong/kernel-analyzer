#!/bin/bash
# Whole-program pointer-analysis (data-flow) baselines for the SoK-MLTA
# comparison. The SoK evaluated type-based resolvers only; these rows
# resolve indirect calls from points-to sets:
#
#   SVF-Andersen   SVF 3.2 AndersenWaveDiff        (svf-baseline image)
#   SVF-VFS        SVF 3.2 versioned flow-sensitive (same precision as
#                  SVF's sparse flow-sensitive analysis, faster)
#   AserPTA-CI / AserPTA-1CFA / AserPTA-2CFA
#                  AserPTA inclusion-based, via Lotus (lotus-baseline)
#   DyckAA         unification-based (Canary), via Lotus
#   SeaDsa         context-sensitive unification-based with heap
#                  cloning (SeaDsa CompleteCallGraph), via Lotus; sites
#                  it marks incomplete are listed in <prog>.incomplete
# Further Lotus rows (image lotus-baseline-next; per-site dumpers in
# eval/lotus-baseline/icalls, conventions in icalls/IcallsCommon.h):
#   GPG-FSCS / GPG-FICS / GPG-FICI
#                  generalized points-to graphs (TOPLAS'20), three modes
#   LotusAA        LotusAA with its own call graph, EVERY cap lifted
#   TPA-K0 / TPA-K1  semi-sparse flow-sensitive, k-limit 0 / 1
#   FSPTA / VFSPTA sparse / versioned flow-sensitive on the SVFG
#   VFPTA          value-flow flow-sensitive, own on-the-fly call graph
#   SparrowAA      Andersen (Lotus SparrowAA), k = 0
#   BootstrapAA    Kahlon PLDI'08 bootstrapping (Steensgaard + Andersen
#                  + flow/context-sensitive clusters)
#   DDA-Flow       demand-driven flow-sensitive (FlowDDA, Funptr client)
#   AserPTA-Origin AserPTA origin-sensitive (KOrigin<1>)
#   CHA / RTA / VTA / OTF
#                  type/hierarchy call-graph resolvers (reference rows)
# Upstream limits the dumpers expose (not changed): LotusAA analyzes only
# the blocks a topological sort of the CFG reaches, so calls in or after
# loops get no answer (<prog>.no-entry.sites); BootstrapAA evaluates every
# pointer loaded from memory to top (<prog>.top.sites, filled with every
# function); GPG fills unresolved sites type-based (<prog>.fallback.sites).
# A site whose answer is a fill (fallback, universal/unknown/top object,
# budget cut-off, unreached) is listed in parsed_log/<prog>.<reason>.sites
# so "resolved by points-to" and "filled" can be separated.
#
# Resolution filters each tool applies (recorded, not changed):
#   SVF      arity only (SVFUtil::matchArgs)
#   AserPTA  exact return type + arity + pointer-ness per parameter
#            (aser::isCompatibleCall; typed pointers under LLVM 14)
#   DyckAA   candidates grouped by exact function type (level 4)
#   SeaDsa   llvm::isLegalToPromote (arity + castable signature)
#   GPG      arity + structural types (i8* matches any pointer); its
#            fallback fill uses the same rule
#   LotusAA / TPA / FSPTA / VFSPTA / VFPTA / BootstrapAA / DDA
#            none on the points-to answer (TPA's Universal fill: every
#            address-taken function; VFPTA's unknown fill: every
#            definition; BootstrapAA's top fill: every function)
#   SparrowAA  arity + pointer/non-pointer shape, applied while BUILDING
#            constraints (argument flows go to every such address-taken
#            function); none on the points-to answer
#   CHA/RTA/VTA/OTF  arity + same type kind per parameter/return
# The *-shape rows rerun AserPTA/DyckAA with their rule aligned to
# KAMain's (eval/lotus-baseline/resolution-rule.patch, opt-in flags).
# KAMain's own answer path applies arity + return + parameter shape.
#
# Inputs (bitcode = the SoK artifact's):
#   SVF rows    LLVM 15 bitcode, the same files as our main SoK table
#   Lotus rows  LLVM 14 bitcode (Lotus is LLVM 14 only); pair them with
#               KAMain on the SAME files:
#                 KA_SOK_BC=<llvm14 dirs> KA_SOK_OUT=$KA_RESULTS/sok-llvm14 \
#                   eval/62-sok-arm.sh
# Output (the layout eval/65 merges, like eval/66):
#   $KA_SOK_OUT/baselines/<dataset>_<opt>/<Approach>/parsed_log/<prog>.json
#   ... /<Approach>/<prog>.{log,time}   + summary.tsv (one row per run)
#
# Host safety: --oom-score-adj 1000 makes a baseline container the host
# OOM killer's first victim, never a long-running analysis beside it.
# Sandbox: --network none, non-root, bitcode read-only; the per-run
# timeout runs INSIDE the container (a host-side timeout would orphan
# it). Single-threaded tools; KA_CPUSET pins them.
#
# Usage:
#   eval/67-dataflow-baselines.sh build        # both images (network)
#   eval/67-dataflow-baselines.sh run [approach...]
# Env: KA_SOK_ROOT (artifact root with bitcodes/), KA_DF_TIMEOUT
#      (default 3600 s = their harness budget), KA_DF_MEM (docker
#      --memory, default 64g), KA_DF_PROGS (space-separated program
#      filter), KA_FORCE=1 to rerun finished programs.

set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
ka_require docker

: "${KA_SOK_ROOT:?set KA_SOK_ROOT to the SoK artifact root (bitcodes/)}"
OUT="${KA_SOK_OUT:-$KA_RESULTS/sok}/baselines"
TIMEOUT="${KA_DF_TIMEOUT:-3600}"
MEM="${KA_DF_MEM:-64g}"
BC="$KA_SOK_ROOT/bitcodes"
LOTUS_SRC="${KA_LOTUS_SRC:-/data/csong/opensource/lotus}"
LOTUS_COMMIT="${KA_LOTUS_COMMIT:-0da4c2813005249bce390329d28810a2c4ac0e76}"

# approach | image | llvm | datasets ("<dataset>_<opt>=<dir under llvmNN>")
declare -A IMAGE=( [SVF-Andersen]=svf-baseline [SVF-VFS]=svf-baseline
  [AserPTA-CI]=lotus-baseline [AserPTA-1CFA]=lotus-baseline
  [AserPTA-2CFA]=lotus-baseline [DyckAA]=lotus-baseline
  [SeaDsa]=lotus-baseline [AserPTA-CI-shape]=lotus-baseline
  [DyckAA-shape]=lotus-baseline
  [GPG-FSCS]=lotus-baseline-next [GPG-FICS]=lotus-baseline-next
  [GPG-FICI]=lotus-baseline-next [LotusAA]=lotus-baseline-next
  [TPA-K0]=lotus-baseline-next [TPA-K1]=lotus-baseline-next
  [FSPTA]=lotus-baseline-next [VFSPTA]=lotus-baseline-next
  [VFPTA]=lotus-baseline-next [SparrowAA]=lotus-baseline-next
  [BootstrapAA]=lotus-baseline-next [DDA-Flow]=lotus-baseline-next
  [AserPTA-Origin]=lotus-baseline-next [CHA]=lotus-baseline-next
  [RTA]=lotus-baseline-next [VTA]=lotus-baseline-next
  [OTF]=lotus-baseline-next )
# LotusAA: every cap lifted (icalls-lotusaa refuses to run otherwise; see
# eval/lotus-baseline/icalls/LotusAA.cpp for what each default drops).
LOTUS_AA_UNCAPPED="-lotus-cg -lotus-aa-fixed-cg=false \
-lotus-restrict-cg-iter=1000000 -lotus-restrict-pts-count=-1 \
-lotus-restrict-right-value-count=-1 -lotus-timeout=1000000000 \
-lotus-restrict-cg-size=1000000 -lotus-restrict-output-pts=-1 \
-lotus-restrict-summary-ap-depth=100 -lotus-restrict-obj-ap-depth=10000 \
-lotus-restrict-memory-max-bb-load=-1 -lotus-restrict-memory-max-bb-depth=-1 \
-lotus-restrict-memory-max-load=-1 -lotus-restrict-memory-store-depth=-1"
# DDA-Flow per-query step budget: Lotus default 100000. 10000000 did not
# finish cflow (the smallest program) in 30 min; cut-off sites are listed
# in <prog>.budget.sites.
DDA_BUDGET="${KA_DDA_BUDGET:-100000}"
SVF_SETS="ossfuzz_O0=llvm15/soundness_ossfuzz/O0_12.15.2025
ossfuzz_O3=llvm15/soundness_ossfuzz/O3_12.15.2025
unifuzz_O0=llvm15/soundness_unifuzz/build_O0
unifuzz_O3=llvm15/soundness_unifuzz/build_O3"
LOTUS_SETS="ossfuzz_O0=llvm14/soundness_ossfuzz/O0_12.15.2025
ossfuzz_O3=llvm14/soundness_ossfuzz/O3_12.15.2025
unifuzz_O0=llvm14/soundness_unifuzz/build_O0"

cmd_for() {  # approach, container json path, container bc path
  case "$1" in
    SVF-Andersen) echo "svf-icalls -icall-pta=ander -extapi=/opt/SVF/Release-build/lib/extapi.bc -ind-call-limit=4000000000 -icalls-json=$2 $3" ;;
    SVF-VFS)      echo "svf-icalls -icall-pta=vfs -extapi=/opt/SVF/Release-build/lib/extapi.bc -ind-call-limit=4000000000 -icalls-json=$2 $3" ;;
    AserPTA-CI)   echo "lotus-alias-call-graph -cg-type=aserpta-ci -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    AserPTA-1CFA) echo "lotus-alias-call-graph -cg-type=aserpta-1cfa -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    AserPTA-2CFA) echo "lotus-alias-call-graph -cg-type=aserpta-2cfa -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    DyckAA)       echo "lotus-alias-call-graph -cg-type=dyck -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    AserPTA-CI-shape) echo "lotus-alias-call-graph -cg-type=aserpta-ci -aser-shape-compat -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    DyckAA-shape) echo "lotus-alias-call-graph -cg-type=dyck -function-type-check-level=2 -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    SeaDsa)       echo "seadsa-icalls -icalls-json=$2 -incomplete-list=${2%.json}.incomplete $3" ;;
    GPG-FSCS)     echo "icalls-gpg -icalls-backend=gpg-fscs -icalls-json=$2 $3" ;;
    GPG-FICS)     echo "icalls-gpg -icalls-backend=gpg-fics -icalls-json=$2 $3" ;;
    GPG-FICI)     echo "icalls-gpg -icalls-backend=gpg-fici -icalls-json=$2 $3" ;;
    LotusAA)      echo "icalls-lotusaa -icalls-backend=lotusaa $LOTUS_AA_UNCAPPED -icalls-json=$2 $3" ;;
    TPA-K0)       echo "icalls-tpa -icalls-backend=tpa -icalls-tpa-k=0 -icalls-json=$2 $3" ;;
    TPA-K1)       echo "icalls-tpa -icalls-backend=tpa -icalls-tpa-k=1 -icalls-json=$2 $3" ;;
    FSPTA)        echo "icalls-fs -icalls-backend=fspta -icalls-json=$2 $3" ;;
    VFSPTA)       echo "icalls-fs -icalls-backend=vfspta -icalls-json=$2 $3" ;;
    VFPTA)        echo "icalls-fs -icalls-backend=vfpta -icalls-json=$2 $3" ;;
    SparrowAA)    echo "icalls-sparrow -icalls-backend=sparrow -andersen-k-cs=0 -icalls-json=$2 $3" ;;
    BootstrapAA)  echo "icalls-bootstrap -icalls-backend=bootstrap -icalls-json=$2 $3" ;;
    DDA-Flow)     echo "icalls-dda -icalls-backend=dda-flow -icalls-dda-budget=$DDA_BUDGET -icalls-json=$2 $3" ;;
    AserPTA-Origin) echo "lotus-alias-call-graph -cg-type=aserpta-origin -emit-icall-sites-json=$2 -o /dev/null $3" ;;
    CHA)          echo "icalls-th -icalls-backend=cha -icalls-json=$2 $3" ;;
    RTA)          echo "icalls-th -icalls-backend=rta -icalls-json=$2 $3" ;;
    VTA)          echo "icalls-th -icalls-backend=vta -icalls-json=$2 $3" ;;
    OTF)          echo "icalls-th -icalls-backend=otf -icalls-json=$2 $3" ;;
    *) echo "!! unknown approach $1" >&2; return 1 ;;
  esac
}

build() {
  local here; here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  docker build -f "$here/svf-baseline.Dockerfile" -t svf-baseline \
    "$here/svf-baseline" || exit 1
  local ctx; ctx=$(mktemp -d)
  git -C "$LOTUS_SRC" archive -o "$ctx/lotus.tar" "$LOTUS_COMMIT" || exit 1
  cp "$here/lotus-baseline/icall-sites.patch" \
     "$here/lotus-baseline/resolution-rule.patch" \
     "$here/lotus-baseline/seadsa-icalls.cpp" \
     "$here/lotus-baseline/more-cg-types.patch" "$ctx/"
  cp -r "$here/lotus-baseline/icalls" "$ctx/icalls"
  # One Dockerfile, one image: lotus-baseline-next. Its earlier layers are
  # exactly the lotus-baseline image; an existing lotus-baseline tag is
  # left alone (runs may be using it), a missing one points here.
  docker build -f "$here/lotus-baseline.Dockerfile" \
    --build-arg LOTUS_COMMIT="$LOTUS_COMMIT" -t lotus-baseline-next "$ctx" \
    || exit 1
  docker image inspect lotus-baseline >/dev/null 2>&1 \
    || docker tag lotus-baseline-next lotus-baseline || exit 1
  rm -rf "$ctx"
}

run_one() {  # approach dataset_opt bcfile
  local appr=$1 set=$2 bc=$3 prog; prog=$(basename "$bc" .bc)
  local adir="$OUT/$set/$appr" json log
  mkdir -p "$adir/parsed_log"
  json="$adir/parsed_log/$prog.json"; log="$adir/$prog.log"
  if [[ -s "$json" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "== $appr/$set/$prog: done, skipping"; return
  fi
  echo "== $appr/$set/$prog"
  local cmd; cmd=$(cmd_for "$appr" "/out/parsed_log/$prog.json" "/bc/$prog.bc") || return
  rm -f "$adir/parsed_log/$prog".*.sites   # sidecars of an earlier run
  local pin=(); [[ -n "${KA_CPUSET:-}" ]] && pin=(--cpuset-cpus "$KA_CPUSET")
  # shellcheck disable=SC2086
  docker run --rm --network none -u "$(id -u):$(id -g)" \
    --memory "$MEM" --memory-swap "$MEM" --oom-score-adj 1000 "${pin[@]}" \
    -v "$(dirname "$bc")":/bc:ro -v "$adir":/out \
    "${IMAGE[$appr]}" \
    timeout "$TIMEOUT" /usr/bin/time -v -o "/out/$prog.time" $cmd \
    > "$log" 2>&1
  local rc=$?
  case $rc in
    0)   status=ok ;;
    124) status=timeout ;;
    137) status=killed-oom-or-signal ;;
    *)   status="exit-$rc" ;;
  esac
  [[ $rc -ne 0 ]] && rm -f "$json" "$adir/parsed_log/$prog".*.sites
  local wall rss
  wall=$(grep -a "Elapsed (wall" "$adir/$prog.time" 2>/dev/null | awk '{print $NF}')
  rss=$(grep -a "Maximum resident" "$adir/$prog.time" 2>/dev/null | awk '{print $NF}')
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$appr" "$set" "$prog" "$status" \
    "${wall:-NA}" "${rss:-NA}" >> "$OUT/summary.tsv"
  [[ $rc -ne 0 ]] && echo "!! $appr/$set/$prog: $status — see $log" >&2
}

run() {
  local apprs=("$@")
  [[ ${#apprs[@]} -eq 0 ]] && apprs=(SVF-Andersen SVF-VFS AserPTA-CI \
                                     AserPTA-1CFA AserPTA-2CFA DyckAA SeaDsa \
                                     GPG-FSCS GPG-FICS GPG-FICI LotusAA \
                                     TPA-K0 TPA-K1 FSPTA VFSPTA VFPTA \
                                     SparrowAA BootstrapAA DDA-Flow \
                                     AserPTA-Origin CHA RTA VTA OTF)
  mkdir -p "$OUT"
  for appr in "${apprs[@]}"; do
    [[ -n "${IMAGE[$appr]:-}" ]] || { echo "!! unknown approach $appr" >&2; exit 1; }
    docker image inspect "${IMAGE[$appr]}" >/dev/null 2>&1 \
      || { echo "!! image ${IMAGE[$appr]} missing: run '$0 build'" >&2; exit 1; }
    local sets="$SVF_SETS"; [[ "${IMAGE[$appr]}" == lotus-baseline* ]] && sets="$LOTUS_SETS"
    while IFS='=' read -r set dir; do
      [[ -d "$BC/$dir" ]] || { echo "!! missing $BC/$dir" >&2; exit 1; }
      while IFS= read -r bc; do
        prog=$(basename "$bc" .bc)
        if [[ -n "${KA_DF_PROGS:-}" && " $KA_DF_PROGS " != *" $prog "* ]]; then
          continue
        fi
        run_one "$appr" "$set" "$bc"
      done < <(find "$BC/$dir" -name '*.bc' | sort)
    done <<< "$sets"
  done
  echo "== done: $OUT/summary.tsv; merge with eval/65-sok-compare.sh"
}

case "${1:-}" in
  build) build ;;
  run)   shift; run "$@" ;;
  *) echo "usage: $0 build | run [approach...]" >&2; exit 2 ;;
esac
