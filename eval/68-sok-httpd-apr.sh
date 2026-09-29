#!/bin/bash
# Complete the SoK-MLTA httpd bitcode with APR + APR-util.
#
# The artifact's httpd.bc (httpd 2.4.52, "apache-afl" build) leaves 887
# symbols undefined, 423 of them APR/APR-util. Hook registration and
# dispatch, buckets/brigades, pools, tables and optional functions all go
# through APR bodies, so a whole-program analysis of httpd.bc alone is
# not analyzing the program (our per-site scoring: 76 fuzz-observed
# targets missed, all at sites whose flow passes through unmodeled APR).
#
# This builds APR and APR-util to bitcode with the SAME compiler major as
# the artifact (clang 15 for its LLVM 15 set) at the matching
# optimization level, and llvm-links them into THEIR httpd.bc. httpd's
# own IR is untouched, so call-site keys (file:line) still match the
# fuzz ground truth.
#
# Version note: the artifact does not record its APR version. httpd
# 2.4.52 (Dec 2021) pairs with APR 1.7.x / APR-util 1.6.x; both lines
# keep a stable ABI within the minor version, so 1.7.6 / 1.6.4 have the
# struct layouts httpd.bc was compiled
# against. Reported, not hidden.
#
# Output: $OUT/<llvmNN>/<O0|O3>/httpd.bc  + undefined.txt (what is still
#         external after linking) + build logs.
# Usage:  eval/68-sok-httpd-apr.sh          (LLVM 15, O0 and O3)
# Env:    KA_SOK_ROOT, KA_APR_LLVM (default 15), KA_APR_OPTS ("O0 O3"),
#         KA_APR_SRC (tarball dir; default $KA_WORK/apr-src, downloaded
#         from archive.apache.org and sha256-checked)

set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

: "${KA_SOK_ROOT:?set KA_SOK_ROOT to the SoK artifact root (bitcodes/)}"
V="${KA_APR_LLVM:-15}"
OPTS="${KA_APR_OPTS:-O0 O3}"
source "$(dirname "${BASH_SOURCE[0]}")/lib-fetch.sh"
SRC="${KA_APR_SRC:-$KA_WORK/apr-src}"
APR=apr-1.7.6
APU=apr-util-1.6.4
fetch_url "https://archive.apache.org/dist/apr/$APR.tar.gz" "$SRC/$APR.tar.gz" \
  6a10e7f7430510600af25fabf466e1df61aaae910bf1dc5d10c44a4433ccc81d || exit 1
fetch_url "https://archive.apache.org/dist/apr/$APU.tar.gz" "$SRC/$APU.tar.gz" \
  9160444764bd1d804d7e6ee50783ec9442a88b5a8984e62470832b06983eeaa4 || exit 1
OUT="${KA_SOK_OUT:-$KA_RESULTS/sok}/httpd-linked/llvm$V"
CC="/usr/lib/llvm-$V/bin/clang"
AR="/usr/lib/llvm-$V/bin/llvm-ar"
LINK="/usr/lib/llvm-$V/bin/llvm-link"
NM="/usr/lib/llvm-$V/bin/llvm-nm"
for t in "$CC" "$AR" "$LINK" "$NM"; do
  [[ -x "$t" ]] || { echo "!! missing $t" >&2; exit 1; }
done

sokdir() {  # artifact set dir for an opt level
  case "$1" in
    O0) echo "$KA_SOK_ROOT/bitcodes/llvm$V/soundness_ossfuzz/O0_12.15.2025" ;;
    O3) echo "$KA_SOK_ROOT/bitcodes/llvm$V/soundness_ossfuzz/O3_12.15.2025" ;;
    *) echo "!! unknown opt $1" >&2; exit 1 ;;
  esac
}

extract_bc() {  # archive -> dir of bitcode members; fail if any is not IR
  local a=$1 d=$2
  mkdir -p "$d"
  (cd "$d" && "$AR" x "$a")
  for m in "$d"/*.o; do
    file -b "$m" | grep -q "LLVM IR" \
      || { echo "!! $m in $a is not bitcode" >&2; exit 1; }
  done
}

for opt in $OPTS; do
  W="$OUT/$opt"
  rm -rf "$W"; mkdir -p "$W/src" "$W/prefix"
  # typed pointers: the artifact's LLVM 15 bitcode was built without
  # opaque pointers, and llvm-link 15 refuses to mix the two forms
  # (LLVM 14 is typed by default and has no such flag)
  flags="-$opt -g -flto"
  [[ "$V" -ge 15 ]] && flags="$flags -Xclang -no-opaque-pointers"
  tar -xzf "$SRC/$APR.tar.gz" -C "$W/src"
  tar -xzf "$SRC/$APU.tar.gz" -C "$W/src"
  echo "== llvm$V $opt: building $APR"
  (cd "$W/src/$APR" && CC="$CC" CFLAGS="$flags" AR="$AR" \
     RANLIB="/usr/lib/llvm-$V/bin/llvm-ranlib" \
     ./configure --prefix="$W/prefix" --disable-shared --enable-static \
     > "$W/apr-configure.log" 2>&1 \
   && make -j "${KA_JOBS:-16}" > "$W/apr-build.log" 2>&1 \
   && make install > "$W/apr-install.log" 2>&1)
  echo "== llvm$V $opt: building $APU"
  (cd "$W/src/$APU" && CC="$CC" CFLAGS="$flags" AR="$AR" \
     RANLIB="/usr/lib/llvm-$V/bin/llvm-ranlib" \
     ./configure --prefix="$W/prefix" --with-apr="$W/prefix" \
     --with-expat=/usr --without-crypto --without-openssl \
     --without-ldap --without-pgsql --without-mysql --without-sqlite3 \
     --without-sqlite2 --without-oracle --without-odbc \
     --without-berkeley-db --without-gdbm --without-ndbm \
     > "$W/apu-configure.log" 2>&1 \
   && make -j "${KA_JOBS:-16}" > "$W/apu-build.log" 2>&1 \
   && make install > "$W/apu-install.log" 2>&1)
  extract_bc "$W/prefix/lib/libapr-1.a" "$W/bc-apr"
  extract_bc "$W/prefix/lib/libaprutil-1.a" "$W/bc-apu"

  base="$(sokdir "$opt")/httpd/bin/httpd.bc"
  [[ -s "$base" ]] || { echo "!! missing $base" >&2; exit 1; }
  # One library module first: --only-needed resolves per input file in
  # order, so a symbol first needed by a later APR object would never
  # be pulled from an earlier one. Then pull exactly the definitions
  # httpd reaches (transitively); httpd.bc's own are never overridden.
  "$LINK" "$W"/bc-apr/*.o "$W"/bc-apu/*.o -o "$W/apr-all.bc"
  "$LINK" "$base" --only-needed "$W/apr-all.bc" -o "$W/httpd.bc"
  "$NM" --undefined-only "$W/httpd.bc" | awk '{print $NF}' | sort -u \
    > "$W/undefined.txt"
  before=$("$NM" --undefined-only "$base" | awk '{print $NF}' | sort -u | wc -l)
  apr_left=$(grep -cE '^(apr|apu)_' "$W/undefined.txt" || true)
  echo "== llvm$V $opt: undefined $before -> $(wc -l < "$W/undefined.txt")" \
       "(APR/APR-util still undefined: $apr_left) -> $W/httpd.bc"
done
