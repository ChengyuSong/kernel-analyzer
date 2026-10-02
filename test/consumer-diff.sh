#!/usr/bin/env bash
# Compare two test/consumer-gate.sh output trees run by run.
#   test/consumer-diff.sh OLD NEW
# Per run: the ICALL answer set and the --cfl-dump-icalls-json file must
# be byte-identical, the IR sidecars byte-identical, and --callgraph-json
# identical after sorting each function's callers/callees (writers
# before 2026-10-02 emitted those arrays in pointer order). Runs present
# on only one side are reported. Exit 1 on any difference.
set -u
OLD=$1 NEW=$2
norm() {
  python3 - "$1" <<'EOF'
import json, sys
d = json.load(open(sys.argv[1]))
for v in d["functions"].values():
    for a in ("callees", "callers"):
        v[a] = sorted(v[a], key=lambda e: json.dumps(e, sort_keys=True))
print(json.dumps(d, sort_keys=True, indent=0))
EOF
}
fail=0
for d in "$OLD"/*/; do
  r=$(basename "$d")
  [[ -f "$d/icalls.txt" ]] || continue
  if [[ ! -f "$NEW/$r/icalls.txt" ]]; then echo "MISSING[$r] in $NEW"; fail=1; continue; fi
  bad=()
  [[ "$(cat "$d/rc")" == "$(cat "$NEW/$r/rc")" ]] || bad+=(rc)
  cmp -s "$d/icalls.txt" "$NEW/$r/icalls.txt" || bad+=(icalls)
  cmp -s "$d/icalls.json" "$NEW/$r/icalls.json" || bad+=(icalls.json)
  diff -rq "$d/sidecar" "$NEW/$r/sidecar" >/dev/null || bad+=(sidecar)
  if [[ -s "$d/callgraph.json" || -s "$NEW/$r/callgraph.json" ]]; then
    cmp -s <(norm "$d/callgraph.json") <(norm "$NEW/$r/callgraph.json") ||
      bad+=(callgraph.json)
  fi
  if [[ ${#bad[@]} -eq 0 ]]; then
    echo "SAME[$r] $(wc -l < "$d/icalls.txt") pairs"
  else
    echo "DIFF[$r] ${bad[*]}"; fail=1
  fi
done
for d in "$NEW"/*/; do
  r=$(basename "$d")
  [[ -f "$d/icalls.txt" && ! -f "$OLD/$r/icalls.txt" ]] && echo "EXTRA[$r] in $NEW"
done
exit $fail
