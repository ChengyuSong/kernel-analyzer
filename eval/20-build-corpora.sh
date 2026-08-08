#!/bin/bash
# Build corpora to LLVM bitcode (clang -flto: the .o files ARE
# bitcode) and emit bclists. Gotchas baked in:
#  - llvm-ar/llvm-ranlib so archives of bitcode work;
#  - lld for the (unused but configure-required) final links;
#  - httpd: static-all-modules so module code is in ONE program;
#    exclude support/ tools (separate mains) and .libs/ PIC twins
#    (duplicate TUs would fake duplicate answers);
#  - postgres: corpus = objects that link into the `postgres` backend
#    binary only (objfiles.txt lists are SPACE-separated multi-path
#    lines) + the _srv variants of common/port; frontend clients are
#    separate programs and stay out.
set -euo pipefail
source "$(dirname "$0")/env.sh"
ka_require "$KA_CC" "$KA_AR" "$KA_RANLIB" make file bison flex

CFLAGS_LTO="-O2 -flto"
LDFLAGS_LTO="-flto -fuse-ld=$KA_LLD"

# ---- httpd -----------------------------------------------------------
H="$KA_WORK/src/httpd-$HTTPD_VER"
if [ ! -f "$H/server/main.o" ]; then
  cd "$H"
  CC="$KA_CC" CFLAGS="$CFLAGS_LTO" LDFLAGS="$LDFLAGS_LTO" \
    AR="$KA_AR" RANLIB="$KA_RANLIB" NM="$KA_NM" \
    ./configure --with-included-apr --enable-mods-static=reallyall \
      --prefix="$KA_WORK/httpd-install" > "$KA_WORK/httpd-configure.log" 2>&1
  make -j "$KA_JOBS" > "$KA_WORK/httpd-build.log" 2>&1
fi
file -b "$H/server/main.o" | grep -q "LLVM IR" \
  || { echo "httpd .o is not bitcode — check toolchain" >&2; exit 1; }
find "$H/server" "$H/modules" "$H/os" "$H/srclib" -name '*.o' \
     ! -path '*/.libs/*' ! -path '*/tools/*' \
  | while read -r f; do file -b "$f" | grep -q "LLVM IR" && echo "$f"; done \
  | sort > "$KA_WORK/httpd.bclist"
echo "httpd bclist: $(wc -l < "$KA_WORK/httpd.bclist") TUs"

# ---- postgres (backend) ----------------------------------------------
P="$KA_WORK/src/postgresql-$PG_VER"
if [ ! -f "$P/src/backend/tcop/postgres.o" ]; then
  cd "$P"
  ./configure CC="$KA_CC" CFLAGS="$CFLAGS_LTO" LDFLAGS="$LDFLAGS_LTO" \
    AR="$KA_AR" --without-readline --without-zlib --without-icu \
    --prefix="$KA_WORK/pg-install" > "$KA_WORK/pg-configure.log" 2>&1
  make -j "$KA_JOBS" > "$KA_WORK/pg-build.log" 2>&1
fi
file -b "$P/src/backend/tcop/postgres.o" | grep -q "LLVM IR" \
  || { echo "postgres .o is not bitcode — check toolchain" >&2; exit 1; }
{
  find "$P/src/backend" -name objfiles.txt -exec cat {} + \
    | tr ' ' '\n' | grep '\.o$' | sed 's|^\./||' \
    | sed "s|^src/|$P/src/|"
  ls "$P"/src/common/*_srv.o "$P"/src/port/*_srv.o
} | awk '!seen[$0]++' | sort > "$KA_WORK/pg.bclist"
while read -r f; do
  [ -f "$f" ] || { echo "MISSING: $f" >&2; exit 1; }
done < "$KA_WORK/pg.bclist"
echo "postgres bclist: $(wc -l < "$KA_WORK/pg.bclist") TUs"
echo "OK: bclists in $KA_WORK"
