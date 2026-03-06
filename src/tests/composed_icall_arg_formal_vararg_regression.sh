#!/usr/bin/env bash
# Regression: compositional solve must propagate indirect-call pointer actuals
# to callee formals/varargs via icallarg -> (arg/larg/vararg/lvararg) summary.
#
# Usage:
#   bash src/tests/composed_icall_arg_formal_vararg_regression.sh [path/to/KAMain]

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

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-icallarg-prop-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/t.c" << 'EOF'
typedef void (*fixed_fp_t)(void *);
typedef void (*var_fp_t)(void *, ...);

void sink_fixed(void *p) { (void)p; }
void sink_var(void *p, ...) { (void)p; }

void call_fixed(fixed_fp_t fp, void *x) {
  fp(x);
}

void call_var(var_fp_t fp, void *x, void *y) {
  fp(x, y);
}
EOF

clang -O0 -emit-llvm -c "$WORK/t.c" -o "$WORK/t.bc"

# Handcrafted composed input:
# - 8 nodes with self-loops to keep all nodes materialized in solver state.
# - two indirect calls forced to resolve via funcNodes:
#     icall:call_fixed#0 -> sink_fixed
#     icall:call_var#0   -> sink_var
# - boundary symbols for pointer actuals and target formal/vararg nodes.
python3 - "$WORK/in.cflcg" << 'PY'
import struct
import sys

out = sys.argv[1]

def varuint(v: int) -> bytes:
    b = bytearray()
    while v >= 0x80:
        b.append((v & 0x7F) | 0x80)
        v >>= 7
    b.append(v)
    return bytes(b)

num_nodes = 8
edges = [(i, i, 0) for i in range(num_nodes)]
symbols = [
    (0, b"icall:call_fixed#0"),
    (1, b"icallarg:call_fixed#0:0"),
    (2, b"larg:sink_fixed:0"),
    (3, b"icall:call_var#0"),
    (4, b"icallarg:call_var#0:0"),
    (5, b"icallarg:call_var#0:1"),
    (6, b"larg:sink_var:0"),
    (7, b"lvararg:sink_var"),
]
func_nodes = {
    0: [b"sink_fixed"],
    3: [b"sink_var"],
}

buf = bytearray()
buf += b"KACFLCG1"
buf += struct.pack("<IIIII", 1, num_nodes, len(edges), len(symbols), len(func_nodes))
buf += varuint(0)  # metadata length

for src, dst, lbl in edges:
    buf += varuint(src) + varuint(dst) + varuint(lbl)

for node, name in symbols:
    buf += varuint(node) + varuint(len(name)) + name

for node, names in func_nodes.items():
    buf += varuint(node) + varuint(len(names))
    for n in names:
        buf += varuint(len(n)) + n

with open(out, "wb") as f:
    f.write(buf)
PY

"$KA" "$WORK/t.bc" \
  --cfl-compositional \
  --cfl-cache-strict=false \
  --cfl-compressed-input "$WORK/in.cflcg" \
  --verbose 3 >"$WORK/run.log" 2>&1

python3 - "$WORK/run.log" << 'PY'
import re
import sys

log_path = sys.argv[1]
log = open(log_path, "r", encoding="utf-8", errors="replace").read()

iter_re = re.compile(
    r"Compositional iterate #(\d+):[^\n]*resolved-calls=(\d+)[^\n]*"
    r"total-targets=(\d+)[^\n]*new-summary-edges=(\d+)"
)
iters = [tuple(map(int, m.groups())) for m in iter_re.finditer(log)]
if not iters:
    raise SystemExit("FAIL: could not find compositional iteration diagnostics")

max_resolved = max(x[1] for x in iters)
max_targets = max(x[2] for x in iters)
max_summary = max(x[3] for x in iters)

if max_resolved < 2:
    raise SystemExit(
        f"FAIL: expected >=2 resolved indirect calls, saw max {max_resolved}"
    )
if max_targets < 2:
    raise SystemExit(
        f"FAIL: expected >=2 total indirect targets, saw max {max_targets}"
    )
if max_summary < 6:
    raise SystemExit(
        f"FAIL: expected >=6 new summary edges from icallarg/formal/vararg propagation, saw max {max_summary}"
    )

print(
    "PASS: compositional icallarg propagation adds summary edges "
    f"(resolved={max_resolved}, targets={max_targets}, summary={max_summary})"
)
PY
