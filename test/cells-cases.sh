#!/usr/bin/env bash
# Cell-solver regression cases (test/t_pool_*.c, test/t_cells_*.c, plan 3.53): each read
# marked "// CHECK: f g ..." must resolve to at least those targets under
# --cfl-cells; "// CFLAGS:" sets the compile flags (default -O0 -g);
# "// MAXCELLS: N" bounds the cells of the first solve (a runaway is a
# failure, as is not finishing in 120 s); "// LOG: re" and "// NOLOG: re"
# require (forbid) a match in the --verbose=2 log. Exits nonzero on any
# miss. "CHECK-NOT: f ..." after the CHECK targets: targets that must not
# appear.
# KAMAIN= overrides the binary.
set -u
cd "$(dirname "$0")"
BIN=${KAMAIN:-../release/lib/KAMain}
CLANG=${CLANG:-/usr/lib/llvm-18/bin/clang}
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
fail=0
for c in t_pool_*.c t_cells_*.c; do
  n=${c%.c}
  flags=$(grep -o "// CFLAGS: .*" "$c" | sed 's|// CFLAGS: ||')
  [ -z "$flags" ] && flags="-O0"
  kaflags=$(grep -o "// KAFLAGS: .*" "$c" | sed 's|// KAFLAGS: ||')
  "$CLANG" $flags -g -emit-llvm -c "$c" -o "$OUT/$n.bc" || { echo "FAIL[$n]: compile"; fail=1; continue; }
  timeout 120 "$BIN" --verbose=2 --func-summaries=../func_summaries.txt --cfl-cells --cfl-union-keys=tag \
    --cfl-alloc-origins --cfl-whole-program $kaflags --cfl-dump-icalls-json="$OUT/$n.json" "$OUT/$n.bc" > "$OUT/$n.log" 2>&1
  rc=$?
  if [ $rc -ne 0 ]; then echo "FAIL[$n]: exit $rc (124: did not finish in 120 s)"; fail=1; continue; fi
  maxc=$(grep -o "// MAXCELLS: [0-9]*" "$c" | grep -o "[0-9]*$")
  cells=$(grep -oE "Cells: iteration 0: .*, ([0-9]+) cells \(" "$OUT/$n.log" | grep -oE "[0-9]+ cells \(" | grep -oE "^[0-9]+")
  if [ -n "$maxc" ] && [ "${cells:-0}" -gt "$maxc" ]; then
    echo "FAIL[$n]: $cells cells > $maxc"; fail=1; continue
  fi
  bad=""
  while read -r re; do
    [ -n "$re" ] && ! grep -qE "$re" "$OUT/$n.log" && bad="$bad [LOG $re]"
  done < <(grep -o "// LOG: .*" "$c" | sed 's|// LOG: ||')
  while read -r re; do
    [ -n "$re" ] && grep -qE "$re" "$OUT/$n.log" && bad="$bad [NOLOG $re]"
  done < <(grep -o "// NOLOG: .*" "$c" | sed 's|// NOLOG: ||')
  if [ -n "$bad" ]; then echo "FAIL[$n]:$bad"; fail=1; continue; fi
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
  for f in $wantnot; do grep -qw "$f" <<<"$got" && miss="$miss not:$f"; done
  if [ -z "$miss" ]; then echo "PASS[$n] ($got; ${cells:-?} cells)"
  else echo "FAIL[$n]: missing$miss (got: $got)"; fail=1; fi
done
exit $fail
