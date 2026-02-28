#!/usr/bin/env bash
# Regression: compositional field filter must not stop at first rejected
# function name when multiple function names share one compressed node.
#
# This catches a prior bug in runCompositionalSolve where field-filter reject
# did `return` (from lambda) instead of `continue`, dropping valid targets that
# appeared later in the same func-name list.
#
# Usage:
#   bash src/tests/composed_fieldfilter_multiname_regression.sh [path/to/KAMain]

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

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-fieldfilter-multiname-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/t.c" << 'EOF'
struct Ops {
  void (*slot0)(void);
  void (*slot1)(void);
  void (*slot2)(void);
};

void a_bad(void) {}
void z_good(void) {}

struct Ops G = { 0, z_good, 0 };

void init_bad(void) {
  G.slot2 = a_bad;
}

void trigger(void) {
  G.slot1();
}

int main(void) {
  init_bad();
  trigger();
  return 0;
}
EOF

clang -O0 -emit-llvm -c "$WORK/t.c" -o "$WORK/t.bc"

# Handcrafted compressed graph:
# - one node (0)
# - one self edge so solver materializes node 0
# - icall symbol points to node 0
# - node 0 carries two function names, sorted as a_bad then z_good
#   (the old buggy code would reject a_bad then return early, missing z_good)
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

buf = bytearray()
buf += b"KACFLCG1"
buf += struct.pack("<IIIII", 1, 1, 1, 1, 1)  # version, nodes, edges, symbols, funcNodes
buf += varuint(0)                              # metadata length

# one dummy edge: 0 -> 0, label 0
buf += varuint(0) + varuint(0) + varuint(0)

# symbol table: icall:trigger#0 -> node 0
sym = b"icall:trigger#0"
buf += varuint(0) + varuint(len(sym)) + sym

# funcNodes: node 0 -> [a_bad, z_good]
names = [b"a_bad", b"z_good"]
buf += varuint(0) + varuint(len(names))
for n in names:
    buf += varuint(len(n)) + n

with open(out, "wb") as f:
    f.write(buf)
PY

"$KA" "$WORK/t.bc" \
  --cfl-compositional \
  --cfl-cache-strict=false \
  --cfl-compressed-input "$WORK/in.cflcg" \
  --callgraph-json "$WORK/out.json" \
  --verbose 0 >/dev/null 2>&1

python3 - "$WORK/out.json" << 'PY'
import json
import sys

j = json.load(open(sys.argv[1]))
trigger = j.get("functions", {}).get("trigger", {})
targets = sorted({
    e.get("callee")
    for e in trigger.get("callees", [])
    if e.get("call_type") == "indirect"
})

if "z_good" not in targets:
    raise SystemExit("FAIL: expected z_good indirect target, but it is missing")
if "a_bad" in targets:
    raise SystemExit("FAIL: expected a_bad to be rejected by field filter")

print("PASS: compositional field-filter keeps later valid target in multi-name node")
PY
