#!/usr/bin/env bash
# Regression: composed .cflcg export must preserve SCC-remapped self-loops.
#
# This test has two checks:
# 1) Structural: composed export keeps self-loops.
# 2) Semantic: a tiny CFL witness loses V(0,1) when a crucial self-loop is
#    removed, showing this is real reachability unsoundness.
#
# Usage:
#   bash src/tests/composed_cflcg_selfloop_regression.sh [path/to/KAMain]

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

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-cflcg-loop-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/dummy.c" << 'EOF'
void touch(void **p, void **q) { *p = *q; }
EOF
clang -O0 -emit-llvm -c "$WORK/dummy.c" -o "$WORK/dummy.bc"

# Discover grammar label IDs from this exact KAMain build.
"$KA" "$WORK/dummy.bc" --cfl-compositional --verbose 2 >"$WORK/labels.log" 2>&1 || true
read -r LABEL_A LABEL_NA LABEL_D LABEL_ND < <(
  python3 - "$WORK/labels.log" << 'PY'
import re, sys
s = open(sys.argv[1]).read()
m = re.search(r"CFL Labels initialized: a=(\d+), -a=(\d+), d=(\d+), -d=(\d+)", s)
if not m:
    raise SystemExit("FAIL: could not extract CFL label IDs from log")
print(*m.groups())
PY
)

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
buf += b"KACFLCG1"                      # magic
buf += struct.pack("<IIIII", 1, 1, 1, 0, 0)  # version, nodes, edges, symbols, funcNodes
buf += varuint(0)                        # metadata length
buf += varuint(0) + varuint(0) + varuint(0)   # edge: 0 -> 0, label 0

with open(out, "wb") as f:
    f.write(buf)
PY

"$KA" "$WORK/dummy.bc" \
  --cfl-compositional \
  --cfl-cache-strict=false \
  --cfl-compressed-input "$WORK/in.cflcg" \
  --cfl-compressed-output "$WORK/out.cflcg" \
  --verbose 0 >/dev/null 2>&1

check_self_loops() {
  local path="$1"
  python3 - "$path" << 'PY'
import struct
import sys

path = sys.argv[1]
data = open(path, "rb").read()

if data[:8] != b"KACFLCG1":
    raise SystemExit("FAIL: bad .cflcg magic in output")

off = 8
version, num_nodes, edge_count, sym_count, func_count = struct.unpack_from("<IIIII", data, off)
off += 20

def read_varuint(buf: bytes, i: int):
    v = 0
    shift = 0
    while i < len(buf):
        b = buf[i]
        i += 1
        v |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            return v, i
        shift += 7
    raise ValueError("truncated varuint")

meta_len, off = read_varuint(data, off)
off += meta_len

self_loops = 0
for _ in range(edge_count):
    src, off = read_varuint(data, off)
    dst, off = read_varuint(data, off)
    _lbl, off = read_varuint(data, off)
    if src == dst:
        self_loops += 1

if self_loops == 0:
    raise SystemExit(
        f"FAIL: expected >=1 self-loop in composed export, got 0 (nodes={num_nodes}, edges={edge_count})"
    )

print(f"PASS: composed export keeps self-loops (nodes={num_nodes}, edges={edge_count}, self_loops={self_loops})")
PY
}

check_self_loops "$WORK/out.cflcg"

"$KA" "$WORK/dummy.bc" \
  --cfl-compositional \
  --cfl-cache-strict=false \
  --cfl-compressed-input "$WORK/out.cflcg" \
  --cfl-compressed-output "$WORK/out2.cflcg" \
  --verbose 0 >/dev/null 2>&1

check_self_loops "$WORK/out2.cflcg"

# Semantic witness:
# with_loop has 0 -d-> 1 and 1 d-> 1, which should derive V(0,1) via M.
# no_loop drops 1 d-> 1 and should lose V(0,1).
python3 - "$WORK/w_with_loop.cflcg" "$WORK/w_no_loop.cflcg" "$LABEL_D" "$LABEL_ND" << 'PY'
import struct
import sys

path_with, path_no, label_d, label_nd = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])

def varuint(v: int) -> bytes:
    b = bytearray()
    while v >= 0x80:
        b.append((v & 0x7F) | 0x80)
        v >>= 7
    b.append(v)
    return bytes(b)

def write_graph(path: str, with_loop: bool):
    out = bytearray()
    out += b"KACFLCG1"
    edge_count = 2 if with_loop else 1
    out += struct.pack("<IIIII", 1, 2, edge_count, 1, 0)
    out += varuint(0)  # metadata size
    # 0 -d-> 1  (terminal -d)
    out += varuint(0) + varuint(1) + varuint(label_nd)
    if with_loop:
        # 1 d-> 1 (terminal d self-loop)
        out += varuint(1) + varuint(1) + varuint(label_d)
    # one boundary symbol so composed snapshot path has named entries
    name = b"icall:witness"
    out += varuint(0) + varuint(len(name)) + name
    with open(path, "wb") as f:
        f.write(out)

write_graph(path_with, True)
write_graph(path_no, False)
PY

"$KA" "$WORK/dummy.bc" \
  --cfl-compositional \
  --cfl-cache-strict=false \
  --cfl-compressed-input "$WORK/w_with_loop.cflcg" \
  --v-snapshot "$WORK/w_with_loop.vsnap" \
  --verbose 0 >/dev/null 2>&1

"$KA" "$WORK/dummy.bc" \
  --cfl-compositional \
  --cfl-cache-strict=false \
  --cfl-compressed-input "$WORK/w_no_loop.cflcg" \
  --v-snapshot "$WORK/w_no_loop.vsnap" \
  --verbose 0 >/dev/null 2>&1

python3 - "$ROOT_DIR" "$WORK/w_with_loop.vsnap" "$WORK/w_no_loop.vsnap" << 'PY'
import sys
root, with_p, no_p = sys.argv[1], sys.argv[2], sys.argv[3]
sys.path.insert(0, root)
from tools.vsnapshot import VSnapshot

sw = VSnapshot.load(with_p)
sn = VSnapshot.load(no_p)

def has_v_01(s):
    if s.node_count < 2:
        return False
    r0 = s.rep(0)
    r1 = s.rep(1)
    return r1 in s.aliases_of_rep(r0)

with_alias = has_v_01(sw)
no_alias = has_v_01(sn)

if not with_alias:
    raise SystemExit("FAIL: expected V(0,1) in witness_with_loop but missing")
if no_alias:
    raise SystemExit("FAIL: expected V(0,1) to be absent after removing d self-loop")

print("PASS: semantic witness V(0,1) exists with self-loop and disappears without it")
PY
