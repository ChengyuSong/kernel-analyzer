#!/usr/bin/env bash
# Regression: strict compositional cache validation must detect mismatch classes
# (missing/stale/duplicate) and repair mode must recover by recomputing from IR.
#
# Usage:
#   bash src/tests/compositional_cache_validation_regression.sh [path/to/KAMain]

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

WORK="$(mktemp -d "${TMPDIR:-/tmp}/kanalyzer-cachecheck-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

cat > "$WORK/a.c" << 'EOF'
void a_store(void **p, void *q) { *p = q; }
EOF

cat > "$WORK/b.c" << 'EOF'
void b_store(void **p, void *q) { *p = q; }
EOF

clang -O0 -emit-llvm -c "$WORK/a.c" -o "$WORK/a.bc"
clang -O0 -emit-llvm -c "$WORK/b.c" -o "$WORK/b.bc"

# Build one valid .cflcg for module a, then corrupt metadata hashes and duplicate it.
"$KA" "$WORK/a.bc" \
  --cfl-compositional=false \
  --cfl-compressed-output "$WORK/base.cflcg" \
  --verbose 0 >/dev/null 2>&1

python3 - "$WORK/base.cflcg" "$WORK/bad1.cflcg" "$WORK/bad2.cflcg" << 'PY'
import json
import struct
import sys

base, bad1, bad2 = sys.argv[1], sys.argv[2], sys.argv[3]
data = open(base, "rb").read()

if data[:8] != b"KACFLCG1":
    raise SystemExit("FAIL: bad base cflcg magic")

hdr = data[8:28]

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

def write_varuint(v: int) -> bytes:
    out = bytearray()
    while v >= 0x80:
        out.append((v & 0x7F) | 0x80)
        v >>= 7
    out.append(v)
    return bytes(out)

off = 28
meta_len, off2 = read_varuint(data, off)
meta_start = off2
meta_end = meta_start + meta_len
meta = json.loads(data[meta_start:meta_end].decode("utf-8"))

covered = meta.get("covered_modules", [])
if not covered:
    raise SystemExit("FAIL: expected covered_modules in base metadata")

bad_hashes = {m: "deadbeef" for m in covered}
meta["module_hashes"] = bad_hashes
new_meta = json.dumps(meta, separators=(",", ":")).encode("utf-8")

rebuilt = bytearray()
rebuilt += data[:28]
rebuilt += write_varuint(len(new_meta))
rebuilt += new_meta
rebuilt += data[meta_end:]

open(bad1, "wb").write(rebuilt)
open(bad2, "wb").write(rebuilt)
PY

set +e
"$KA" "$WORK/a.bc" "$WORK/b.bc" \
  --cfl-compositional \
  --cfl-compressed-input "$WORK/bad1.cflcg" \
  --cfl-compressed-input "$WORK/bad2.cflcg" \
  --verbose 0 >"$WORK/strict.log" 2>&1
STRICT_RC=$?
set -e

if [[ "$STRICT_RC" -eq 0 ]]; then
  echo "FAIL: strict cache validation should fail but command succeeded" >&2
  sed -n '1,200p' "$WORK/strict.log" >&2
  exit 1
fi

if ! rg -q "Compositional cache validation failed" "$WORK/strict.log"; then
  echo "FAIL: strict run did not emit cache validation failure banner" >&2
  sed -n '1,220p' "$WORK/strict.log" >&2
  exit 1
fi
if ! rg -q "missing \\(" "$WORK/strict.log"; then
  echo "FAIL: strict run missing 'missing' diagnostics" >&2
  sed -n '1,220p' "$WORK/strict.log" >&2
  exit 1
fi
if ! rg -q "stale \\(" "$WORK/strict.log"; then
  echo "FAIL: strict run missing 'stale' diagnostics" >&2
  sed -n '1,220p' "$WORK/strict.log" >&2
  exit 1
fi
if ! rg -q "duplicate \\(" "$WORK/strict.log"; then
  echo "FAIL: strict run missing 'duplicate' diagnostics" >&2
  sed -n '1,220p' "$WORK/strict.log" >&2
  exit 1
fi

"$KA" "$WORK/a.bc" "$WORK/b.bc" \
  --cfl-compositional \
  --cfl-cache-repair \
  --cfl-compressed-input "$WORK/bad1.cflcg" \
  --cfl-compressed-input "$WORK/bad2.cflcg" \
  --callgraph-json "$WORK/out.json" \
  --verbose 0 >"$WORK/repair.log" 2>&1

if [[ ! -s "$WORK/out.json" ]]; then
  echo "FAIL: repair run did not produce callgraph output" >&2
  exit 1
fi

echo "PASS: strict cache checks detect missing/stale/duplicate and repair mode recovers"
