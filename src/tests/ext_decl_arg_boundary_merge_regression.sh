#!/usr/bin/env bash
# Regression: extern declaration argument nodes from different TUs must
# canonicalize to a shared boundary symbol and merge in compositional solve.
#
# Usage:
#   bash src/tests/ext_decl_arg_boundary_merge_regression.sh [path/to/KAMain]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
KA="${1:-$ROOT_DIR/debug/lib/KAMain}"

if [[ ! -x "$KA" ]]; then
  echo "ERROR: KAMain not found or not executable: $KA" >&2
  exit 2
fi

if ! command -v clang >/dev/null 2>&1; then
  echo "ERROR: clang is required for this regression test." >&2
  exit 2
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-extarg-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/a.c" << 'EOF'
extern void ext(void *p);
void fa(void *x) { ext(x); }
EOF

cat > "$WORK/b.c" << 'EOF'
extern void ext(void *p);
void fb(void *y) { ext(y); }
EOF

clang -O0 -emit-llvm -c "$WORK/a.c" -o "$WORK/a.bc"
clang -O0 -emit-llvm -c "$WORK/b.c" -o "$WORK/b.bc"

"$KA" "$WORK/a.bc" "$WORK/b.bc" \
  --cfl-compositional \
  --verbose 3 >"$WORK/run.log" 2>&1 || true

if ! rg -q "BoundaryMerge: arg:[0-9]+:0" "$WORK/run.log"; then
  echo "FAIL: expected extern arg boundary merge (arg:<GUID>:0) across TUs" >&2
  echo "----- begin log -----" >&2
  sed -n '1,200p' "$WORK/run.log" >&2
  echo "----- end log -----" >&2
  exit 1
fi

echo "PASS: extern arg boundary symbol merged across TUs"

