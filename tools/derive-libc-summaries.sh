#!/bin/bash
# Derive a libc interface summary from musl built as LTO bitcode.
#   1. cp -r <musl-src> <work>; cd <work>
#      ./configure CC=clang-18 CFLAGS="-O0 -g -flto" --disable-shared
#      make -j lib/libc.a   (the archive step may fail on the gold
#      plugin; the obj/src/**/*.lo bitcode objects are what we need)
#   2. tools/derive-libc-summaries.sh <work> <out.log>
#   3. harvest: "NoopProp: OK f" -> "f NOOP"; "SolvedProp: OK f ATOMS" and
#      "AtomProp: OK f ATOMS" -> "f ATOMS" (drop lines with @global refs:
#      a partial line would claim completeness it lacks); "ConfirmFresh:
#      LINE ..." verbatim. Skip names already in func_summaries.txt.
set -u
WORK=${1:?musl work tree}; OUT=${2:?output log}
LIST=$(mktemp)
find "$WORK/obj/src" \( -name '*.lo' -o -name '*.o' \) | while read -r f; do
  [ "$(head -c 2 "$f")" = "BC" ] && echo "$f"
done > "$LIST"
echo "bitcode objects: $(wc -l < "$LIST")"
export MALLOC_ARENA_MAX=2
release/lib/KAMain --verbose=2 --mem-limit=40 --mem-limit-mode=as \
  --cfl-field-buckets=13 --cfl-presolve-exact --cfl-presolve-cone=false \
  --cfl-compositional=false --cfl-flows-to --func-summaries=func_summaries.txt \
  --cfl-confirm-fresh --cfl-propose-noop-summaries --cfl-propose-atom-summaries \
  --cfl-propose-solved-summaries --cfl-trace-func=zzz_none \
  $(cat "$LIST") > "$OUT" 2>&1
echo "rc=$? (see $OUT)"
rm -f "$LIST"
