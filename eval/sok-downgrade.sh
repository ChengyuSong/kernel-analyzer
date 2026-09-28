#!/bin/bash
# LLVM 15 (typed-pointer) bitcode -> LLVM 14 bitcode, through text, so
# the LLVM-14-only Lotus analyses read EXACTLY the files every other tool
# reads (the artifact's own LLVM 14 set is a different build: e.g. its
# httpd lacks mod_proxy_html/xml2enc, which the fuzz ground truth has).
#
# The artifact's LLVM 15 bitcode uses typed pointers, so its text is LLVM
# 14 syntax except for three LLVM-15 additions, none of which carries
# pointer semantics:
#   - anonymous !DIGlobalVariable (string-literal debug records):
#     given the placeholder name "__anon_literal" (debug info only);
#   - the `allocptr` parameter attribute (allocator argument marker);
#   - the `allockind("...")` function attribute (allocator kind hint).
# llvm-as-14 verifies the result; the gate for faithfulness is that
# KAMain's answers on the converted file are byte-identical to the
# original's (checked on cflow, nm-new, tcpdump, pdftotext 2026-09-28).
#
# usage: sok-downgrade.sh <src-dir> <dst-dir>   (mirrors *.bc under src)
# Needs /usr/lib/llvm-15/bin/llvm-dis and /usr/lib/llvm-14/bin/llvm-as
# (the sok-toolchain image has both).
set -euo pipefail
src=${1:?src dir}; dst=${2:?dst dir}
DIS=/usr/lib/llvm-15/bin/llvm-dis
AS=/usr/lib/llvm-14/bin/llvm-as
n=0
while IFS= read -r bc; do
  rel=${bc#"$src"/}; out="$dst/$rel"
  mkdir -p "$(dirname "$out")"
  "$DIS" "$bc" -o - | sed -E \
      -e 's/!DIGlobalVariable\(scope:/!DIGlobalVariable(name: "__anon_literal", scope:/' \
      -e 's/ allocptr//g' \
      -e 's/ allockind\("[^"]*"\)//g' \
    | "$AS" - -o "$out" \
    || { echo "!! downgrade failed: $bc" >&2; exit 1; }
  n=$((n + 1))
done < <(find "$src" -name '*.bc' | sort)
echo "== downgraded $n files: $src -> $dst"
