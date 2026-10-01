#!/usr/bin/env bash
# Regression: a solved summary must not drop a fresh object that a
# function hands to its caller through a formal after an unmodeled
# callee filled a local slot (ffmpeg avio_open_dyn_buf at -O3:
# posix_memalign(&p, ...); p->write_packet = dyn_buf_write; *s = p).
#
# Before the fix the Stage A local solve read the slot back as empty, so
# open_ctx was proposed OK-EMPTY; adopting it cut the call-site wiring
# that carried the object and the full configuration lost dyn_write at
# the dispatch in use() (base kept it). The fix: an unmodeled callee may
# write an external value anywhere in the locals it reaches, so the
# hand-off is OPAQUE-EXT into a formal and the summary is refused.
#
# Usage:
#   bash src/tests/solvedprop_fresh_out_regression.sh [path/to/KAMain]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
KA="${1:-$ROOT_DIR/debug/lib/KAMain}"
SUM="$ROOT_DIR/func_summaries.txt"

if [[ ! -x "$KA" ]]; then
  echo "ERROR: KAMain not found or not executable: $KA" >&2
  exit 2
fi
CC="${KA_CC:-clang}"
if ! command -v "$CC" >/dev/null 2>&1; then
  echo "ERROR: $CC is required for this regression test." >&2
  exit 2
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-freshout-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/fresh_out.c" << 'EOF'
#include <stdlib.h>
typedef struct Ctx { int (*write)(void *, int); void *opaque; } Ctx;
static int dyn_write(void *o, int n) { return n; }
static int other_write(void *o, int n) { return -n; }
__attribute__((noinline)) int open_ctx(Ctx **s) {
  void *p = NULL;
  if (posix_memalign(&p, 64, sizeof(Ctx))) { *s = NULL; return -1; }
  Ctx *c = p;
  c->write = dyn_write;
  c->opaque = 0;
  *s = c;
  return 0;
}
__attribute__((noinline)) int use(Ctx *c) { return c->write(c->opaque, 3); }
Ctx g = { other_write, 0 };
int main(void) { Ctx *c; if (open_ctx(&c)) return 1; use(&g); return use(c); }
EOF

FULL=(--cfl-propose-chain-summaries --cfl-regfield-apply --cfl-regfield-obj
      --cfl-propose-solved-summaries --cfl-adopt-proposed-summaries)
rc=0
for opt in O0 O3; do
  "$CC" -g "-$opt" -emit-llvm -c "$WORK/fresh_out.c" -o "$WORK/f.$opt.bc"
  for cfg in base full; do
    flags=(); [[ $cfg == full ]] && flags=("${FULL[@]}")
    "$KA" --verbose=0 --cfl-compositional=false --cfl-flows-to \
      --cfl-dump-icalls-json="$WORK/$cfg.$opt.json" --func-summaries="$SUM" \
      "${flags[@]}" "$WORK/f.$opt.bc" > "$WORK/$cfg.$opt.log" 2>&1
    if python3 - "$WORK/$cfg.$opt.json" << 'PY'
import json, sys
d = json.load(open(sys.argv[1]))
# the program's only indirect call is c->write(...) in use()
sites = [v for k, v in d.items() if 'fresh_out.c:' in k]
sys.exit(0 if len(sites) == 1 and {'dyn_write', 'other_write'} <= set(sites[0])
         else 1)
PY
    then echo "PASS $opt $cfg: use() resolves to dyn_write and other_write"
    else echo "FAIL $opt $cfg: dyn_write missing at the use() dispatch" \
              "($(cat "$WORK/$cfg.$opt.json" | tr -d '\n '))"; rc=1
    fi
  done
done
exit $rc
