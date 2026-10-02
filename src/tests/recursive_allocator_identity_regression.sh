#!/usr/bin/env bash
# Regression: objects from an allocator wrapper around posix_memalign that
# retries by calling itself (ffmpeg av_malloc) must keep their identity.
#
# posix_memalign returns its object through *arg0. Unmodeled, the pointer
# had no origin; the recursive retry (ptr = my_malloc(1)) gave the value
# an incoming edge from its own return, so no lazy root was minted either.
# The pool's alloc field then never met its load and pool_get's
# p->alloc(...) resolved to nothing at -O0, in base and full alike
# (ffmpeg pool_alloc_buffer, buffer.c:313). Fixed in func_summaries.txt:
# posix_memalign FRESHSUB(*arg0).
#
# Usage:
#   bash src/tests/recursive_allocator_identity_regression.sh [path/to/KAMain]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
KA="${1:-$ROOT_DIR/debug/lib/KAMain}"
SUM="${KA_SUMMARIES:-$ROOT_DIR/func_summaries.txt}"

if [[ ! -x "$KA" ]]; then
  echo "ERROR: KAMain not found or not executable: $KA" >&2
  exit 2
fi
CC="${KA_CC:-clang}"
if ! command -v "$CC" >/dev/null 2>&1; then
  echo "ERROR: $CC is required for this regression test." >&2
  exit 2
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-recalloc-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/pool.c" << 'EOF'
#include <stdlib.h>
#include <string.h>
void *my_malloc(size_t size) {
  void *ptr = NULL;
  if (size > (1u << 30)) return NULL;
  if (posix_memalign(&ptr, 64, size)) ptr = NULL;
  if (!ptr && !size) { size = 1; ptr = my_malloc(1); }
  return ptr;
}
void *my_mallocz(size_t size) { void *p = my_malloc(size); if (p) memset(p, 0, size); return p; }
typedef struct Pool { int size; void *(*alloc)(int); } Pool;
static void *alloc_a(int n) { return my_malloc(n); }
static void *alloc_b(int n) { return my_mallocz(n); }
__attribute__((noinline)) Pool *pool_init(int size, void *(*alloc)(int)) {
  Pool *p = my_mallocz(sizeof(*p));
  if (!p) return NULL;
  p->size = size;
  p->alloc = alloc ? alloc : alloc_a;
  return p;
}
struct Ctx { Pool *pool; } ctx;
__attribute__((noinline)) void *pool_get(Pool *p) { return p->alloc(p->size); }
int main(int argc, char **argv) {
  ctx.pool = pool_init(8, argc > 1 ? alloc_b : NULL);
  return pool_get(ctx.pool) != 0;
}
EOF

FULL=(--cfl-propose-chain-summaries --cfl-regfield-apply --cfl-regfield-obj
      --cfl-propose-solved-summaries --cfl-adopt-proposed-summaries)
rc=0
for opt in O0 O3; do
  "$CC" -g "-$opt" -emit-llvm -c "$WORK/pool.c" -o "$WORK/p.$opt.bc"
  for cfg in base full; do
    flags=(); [[ $cfg == full ]] && flags=("${FULL[@]}")
    "$KA" --verbose=0 --cfl-compositional=false --cfl-flows-to \
      --cfl-dump-icalls-json="$WORK/$cfg.$opt.json" --func-summaries="$SUM" \
      "${flags[@]}" "$WORK/p.$opt.bc" > "$WORK/$cfg.$opt.log" 2>&1
    if python3 - "$WORK/$cfg.$opt.json" << 'PY'
import json, sys
d = json.load(open(sys.argv[1]))
# the program's only indirect call is p->alloc(...) in pool_get()
sites = [v for k, v in d.items() if 'pool.c:' in k]
sys.exit(0 if len(sites) == 1 and {'alloc_a', 'alloc_b'} <= set(sites[0])
         else 1)
PY
    then echo "PASS $opt $cfg: pool_get resolves to alloc_a and alloc_b"
    else echo "FAIL $opt $cfg: pool_get misses a target" \
              "($(tr -d '\n ' < "$WORK/$cfg.$opt.json"))"; rc=1
    fi
  done
done
exit $rc
