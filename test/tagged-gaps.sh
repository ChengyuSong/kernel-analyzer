#!/usr/bin/env bash
# The plan 3.51 last-writer cases (test/t_tagged_*.c): each read marked
# "// CHECK: f g ..." must resolve to at least those targets (and none
# listed after CHECK-NOT:, the precision the case is about) under
# --cfl-cells, and its tagged pair must be keyed (else the case tests
# nothing). Exits nonzero on any miss. KAMAIN= overrides the binary.
set -u
cd "$(dirname "$0")"
BIN=${KAMAIN:-../release/lib/KAMain}
CLANG=${CLANG:-/usr/lib/llvm-18/bin/clang}
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
fail=0
for c in t_tagged_*.c; do
  n=${c%.c}
  "$CLANG" -O0 -g -emit-llvm -c "$c" -o "$OUT/$n.bc" || { echo "FAIL[$n]: compile"; fail=1; continue; }
  "$BIN" --verbose=2 --func-summaries=../func_summaries.txt --cfl-cells --cfl-union-keys=tag --cfl-alloc-origins \
    --cfl-whole-program --cfl-dump-icalls-json="$OUT/$n.json" "$OUT/$n.bc" > "$OUT/$n.log" 2>&1
  if ! grep -q "TaggedFields:   KEYED struct.S+8 by +0" "$OUT/$n.log"; then
    echo "FAIL[$n]: pair struct.S+8 by +0 not keyed"; fail=1; continue
  fi
  line=$(grep -n "// CHECK:" "$c" | cut -d: -f1)
  want=$(grep "// CHECK:" "$c" | sed 's/.*CHECK: //; s/ CHECK-NOT:.*//')
  wantnot=$(grep "CHECK-NOT:" "$c" | sed 's/.*CHECK-NOT: //')
  got=$(python3 - "$OUT/$n.json" "$c" "$line" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
want = f"{sys.argv[2]}:{sys.argv[3]}"
for k, v in d.items():
    if want in k:
        print(" ".join(sorted(t.split(":")[-1] if ":" in t else t for t in v)))
PY
)
  miss=""
  for f in $want; do grep -qw "$f" <<<"$got" || miss="$miss $f"; done
  extra=""
  for f in $wantnot; do grep -qw "$f" <<<"$got" && extra="$extra $f"; done
  if [ -z "$miss$extra" ]; then echo "PASS[$n] ($got)"
  else echo "FAIL[$n]: missing$miss, unexpected$extra (got: $got)"; fail=1; fi
done
exit $fail
