#!/bin/bash
# GraCFL baseline re-runs on the released Graspan graphs, on OUR
# machine (same-machine rule): the engine-comparison rows behind
# the Q1 story. Two configurations per graph, mirroring GraCFL's
# own Table-5 presentation:
#   bi-1t   serial,  traversal=bi, 1 thread   (their "(BI, 1t)")
#   fw-32t  parallel, traversal=fw, N threads (their "(FW, 32t)")
# Threads default 32 to match their published setting; override
# with KA_GRACFL_THREADS. Pin with KA_CPUSET sized to the thread
# count. GraCFL's own stdout (results/banners) is captured per run.
#
# Grammar: KA_GRACFL_GRAMMAR if set (use Graspan's original rules
# file from their Drive folder for exact reproduction); otherwise
# our DefaultP2Grammar is emitted — same language and alphabet
# (a/-a/d/-d), our normalization — and the summary marks it.
#
# Usage:
#   KA_GRASPAN_DIR=~/fast/ka-scratch/graspan \
#     eval/63-gracfl-graspan.sh [graph-file ...]
# Default graphs: linux kernel_afterInline (their "linux PT" row),
# postgres wholegraph, httpd wholegraph.

set -u
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

KA_GRASPAN_DIR="${KA_GRASPAN_DIR:-$HOME/fast/ka-scratch/graspan}"
KA_GRACFL_SRC="${KA_GRACFL_SRC:-/data/csong/opensource/GraCFL}"
KA_GRACFL_THREADS="${KA_GRACFL_THREADS:-32}"
OUT="${KA_GRACFL_OUT:-$KA_RESULTS/gracfl-graspan}"
mkdir -p "$OUT"
export LC_ALL=C
PIN=()
[[ -n "${KA_CPUSET:-}" ]] && PIN=(taskset -c "$KA_CPUSET")

# --- build upstream GraCFL once ---
BIN="$KA_GRACFL_SRC/build/bin/gracfl"
if [[ ! -x "$BIN" ]]; then
  echo "== building GraCFL ($KA_GRACFL_SRC)"
  cmake -S "$KA_GRACFL_SRC" -B "$KA_GRACFL_SRC/build" \
        -DCMAKE_BUILD_TYPE=Release > "$OUT/build.log" 2>&1 \
    && cmake --build "$KA_GRACFL_SRC/build" -j "$KA_JOBS" \
         >> "$OUT/build.log" 2>&1
  [[ -x "$BIN" ]] || { echo "!! GraCFL build failed — $OUT/build.log" >&2
                       tail -15 "$OUT/build.log" >&2; exit 1; }
fi

# --- grammar ---
GRAMMAR="${KA_GRACFL_GRAMMAR:-}"
GRAMMAR_NOTE="graspan-original"
if [[ -z "$GRAMMAR" ]]; then
  GRAMMAR="$OUT/p2-grammar.txt"
  GRAMMAR_NOTE="our-normalization"
  awk '/DefaultP2Grammar = \{/,/^\};/' "$KA_REPO/src/lib/Global.h" \
    | grep -oE '"[^"]+"' | tr -d '"' > "$GRAMMAR"
  [[ -s "$GRAMMAR" ]] || { echo "!! grammar extraction failed" >&2; exit 1; }
  echo "== grammar: $GRAMMAR ($GRAMMAR_NOTE, $(wc -l < "$GRAMMAR") rules)"
fi

run_one() {
  local graph="$1" mode="$2"   # mode: bi-1t | fw-Nt
  local name; name=$(basename "$graph" | tr '.' '_')
  local tag="$name.$mode"
  local log="$OUT/$tag.log" tlog="$OUT/$tag.time"
  if [[ -s "$tlog" && "${KA_FORCE:-0}" != 1 ]]; then
    echo "== $tag: done, skipping"; return 0
  fi
  local cfg="$(dirname "$BIN")/ConfigGraCFL"
  case "$mode" in
    bi-1t)
      printf 'graphFilepath = %s\ngrammarFilepath = %s\nexecutionMode = serial\ntraversalDirection = bi\nprocessingStrategy = gram-driven\n' \
        "$graph" "$GRAMMAR" > "$cfg" ;;
    fw-*)
      printf 'graphFilepath = %s\ngrammarFilepath = %s\nexecutionMode = parallel\ntraversalDirection = fw\nprocessingStrategy = gram-driven\nnumThreads = %s\n' \
        "$graph" "$GRAMMAR" "$KA_GRACFL_THREADS" > "$cfg" ;;
  esac
  echo "== $tag: running ($(date -Is))"
  ( cd "$(dirname "$BIN")" && \
    /usr/bin/time -v -o "$tlog" "${PIN[@]}" ./gracfl > "$log" 2>&1 )
  local rc=$?
  [[ $rc -ne 0 ]] && echo "!! $tag exited $rc — see $log" >&2
  return 0
}

GRAPHS=("$@")
if [[ ${#GRAPHS[@]} -eq 0 ]]; then
  GRAPHS=(
    "$KA_GRASPAN_DIR/linux-4-4-p2/kernel_afterInline.txt"
    "$KA_GRASPAN_DIR/postgresql-8.3.9-p2/wholegraph/PostgreSQL_8.3.9_pointsto_graph"
    "$KA_GRASPAN_DIR/httpd-2.2.18-p2/Apache_httpd_2.2.18_pointsto_graph"
  )
fi

for g in "${GRAPHS[@]}"; do
  [[ -s "$g" ]] || { echo "!! missing graph: $g" >&2; continue; }
  run_one "$g" bi-1t
  run_one "$g" "fw-${KA_GRACFL_THREADS}t"
done

echo -e "graph\tmode\tgrammar\twall\tmaxrss_kb" | tee "$OUT/summary.tsv"
for t in "$OUT"/*.time; do
  [[ -s "$t" ]] || continue
  tag=$(basename "$t" .time)
  wall=$(grep -oE 'Elapsed \(wall clock\).*' "$t" | awk '{print $NF}')
  rss=$(grep -oE 'Maximum resident set size.*[0-9]+' "$t" | grep -oE '[0-9]+$')
  echo -e "${tag%.*}\t${tag##*.}\t$GRAMMAR_NOTE\t$wall\t$rss" | tee -a "$OUT/summary.tsv"
done
