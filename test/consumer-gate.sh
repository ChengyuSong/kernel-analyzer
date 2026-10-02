#!/usr/bin/env bash
# Consumer-output gate (plan-named-cells G0): run one KAMain binary over
# a fixed input set and write every consumer-facing output into OUTDIR,
# so two binaries can be compared with `diff -r` (byte-identical) or the
# set comparison in test/consumer-diff.sh.
#
#   test/consumer-gate.sh BIN OUTDIR [SET...]
#
# MODE_FLAGS (env) is prepended to every invocation; a pre-Part-A binary
# needs MODE_FLAGS="--cfl-compositional=false --cfl-flows-to", a binary
# whose only mode is flows-to needs none.
#
# Sets: libpng (default), sok, httpd, km, kmfs. Configurations per set
# follow eval/64 ("full" = the canonical channels + adoption, "base" =
# summaries only) plus the FS stack eval/61 uses (all+ids, bidi, presolve
# once) and the exact presolve.
set -u
BIN=$(readlink -f "$1"); mkdir -p "$2"; OUT=$(readlink -f "$2"); shift 2
SETS=("$@"); [[ ${#SETS[@]} -eq 0 ]] && SETS=(libpng)
REPO=${KA_REPO:-$(cd "$(dirname "$0")/.." && pwd)}
SUM="$REPO/func_summaries.txt"
SOK=${KA_SOK_ROOT:-$HOME/fast/ka-scratch/sok-mlta}/bitcodes/llvm15
KM_DIR=${KA_KM_DIR:-$HOME/fast/linux/linux-6.8.2}
KM_LIST=${KA_KM_LIST:-/data/csong/tmp/km.filelist}
HTTPD_LIST=${KA_HTTPD_LIST:-$HOME/fast/ka-bench/httpd.bclist}
export LC_ALL=C MALLOC_ARENA_MAX=2
read -ra MODE <<< "${MODE_FLAGS:-}"
# Every configuration states all five mechanisms: KAMain's defaults
# changed (2026-10-02) and the gate compares binaries across that change.
CHANNELS=(--cfl-propose-chain-summaries=true --cfl-regfield-apply=true
          --cfl-regfield-obj=true --cfl-propose-solved-summaries=true
          --cfl-adopt-proposed-summaries=true)
NOCHANNELS=(--cfl-propose-chain-summaries=false --cfl-regfield-apply=false
            --cfl-regfield-obj=false --cfl-propose-solved-summaries=false
            --cfl-adopt-proposed-summaries=false)
FSSTACK=(--cfl-bidi-prune --cfl-nexus-fields=all+ids --cfl-presolve-once)
mkdir -p "$OUT"
fail=0

cfg_flags() {
  case "$1" in
    full)    echo "${CHANNELS[*]} --func-summaries=$SUM" ;;
    base)    echo "${NOCHANNELS[*]} --func-summaries=$SUM" ;;
    fsfull)  echo "${FSSTACK[*]} ${CHANNELS[*]} --func-summaries=$SUM" ;;
    pexact)  echo "--cfl-presolve-exact --cfl-presolve-cone=false ${CHANNELS[*]} --func-summaries=$SUM" ;;
    *) echo "unknown cfg $1" >&2; return 1 ;;
  esac
}

# run NAME CFG [extra KAMain args...] -- inputs...
# SC=1 in the environment also writes the IR sidecars (--ir-sidecar-dir).
# The sidecar export is quadratic in a module's unnamed values, so it is
# exercised on the small single-module inputs only.
run() {
  local name=$1 cfg=$2; shift 2
  local d="$OUT/$name.$cfg"
  if [[ -s "$d/icalls.txt" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "SKIP[$name.$cfg]"; return 0
  fi
  rm -rf "$d"; mkdir -p "$d/sidecar"
  local flags; flags=$(cfg_flags "$cfg") || return 1
  local t0=$SECONDS
  # shellcheck disable=SC2086
  "$BIN" "${MODE[@]}" --verbose=0 $flags --cfl-dump-icalls \
      --cfl-dump-icalls-json="$d/icalls.json" \
      --callgraph-json="$d/callgraph.json" \
      ${SC:+--ir-sidecar-dir="$d/sidecar"} "$@" > "$d/log" 2>&1
  local rc=$?
  echo "$rc" > "$d/rc"
  grep '^ICALL ' "$d/log" | sort -u > "$d/icalls.txt"
  if [[ $rc -ne 0 ]] || grep -q UNSOUND "$d/log"; then
    echo "FAIL[$name.$cfg] rc=$rc ($((SECONDS - t0))s)"; fail=1
  else
    echo "DONE[$name.$cfg] $(wc -l < "$d/icalls.txt") pairs ($((SECONDS - t0))s)"
  fi
}

for s in "${SETS[@]}"; do
  case "$s" in
    libpng)
      bc="$REPO/test/libpng/libpng_read_fuzzer.0.0.preopt.bc"
      for c in full base fsfull pexact; do SC=1 run libpng "$c" "$bc"; done ;;
    sok)
      for p in ncurses-6.1/tic flvmeta-1.2.1/flvmeta cflow-1.6/cflow \
               lame-3.99.5/lame libtiff-Release-v3-9-7/tiffsplit \
               binutils_5279478/nm-new; do
        for o in O0 O3; do
          bc="$SOK/soundness_unifuzz/build_$o/$p.bc"
          [[ -f "$bc" ]] || continue
          sc=1; [[ $p == */nm-new ]] && sc=
          for c in full base; do SC=$sc run "$(basename "$p")-$o" "$c" "$bc"; done
        done
      done
      for p in cjpeg djpeg; do
        for o in O0 O3; do
          bc="$SOK/replication/${o}_static_11.3.2025/libjpeg-turbo/$p.bc"
          for c in full base; do SC=1 run "$p-$o" "$c" "$bc"; done
        done
      done
      for o in O0 O3; do
        bc="$SOK/soundness_ossfuzz/${o}_12.15.2025/sqlite3/fuzzershell.bc"
        for c in full base; do run "fuzzershell-$o" "$c" "$bc"; done
      done
      run nm-new-O0 pexact "$SOK/soundness_unifuzz/build_O0/binutils_5279478/nm-new.bc"
      run cflow-O0 pexact "$SOK/soundness_unifuzz/build_O0/cflow-1.6/cflow.bc" ;;
    httpd)
      for c in full base; do run httpd "$c" "@$HTTPD_LIST"; done ;;
    km)
      pushd "$KM_DIR" >/dev/null; run km full --mem-limit=80 "@$KM_LIST"; popd >/dev/null ;;
    kmfs)
      pushd "$KM_DIR" >/dev/null; run km fsfull --mem-limit=80 "@$KM_LIST"; popd >/dev/null ;;
    *) echo "unknown set $s" >&2; fail=1 ;;
  esac
done
exit $fail
