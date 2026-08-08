#!/bin/bash
# Fetch pinned corpus sources. Apache mirrors move old releases to
# archive.apache.org when a newer one ships — try dlcdn, fall back.
set -euo pipefail
source "$(dirname "$0")/env.sh"
ka_require curl tar

mkdir -p "$KA_WORK/src"
cd "$KA_WORK/src"

fetch() { # fetch <output> <url> [fallback-url]
  local out=$1 url=$2 fb=${3:-}
  if [ -s "$out" ] && tar tzf "$out" >/dev/null 2>&1; then
    echo "have $out"; return 0
  fi
  curl -fsSLo "$out" "$url" || { [ -n "$fb" ] && curl -fsSLo "$out" "$fb"; }
  tar tzf "$out" >/dev/null || { echo "BAD TARBALL: $out ($url)" >&2; exit 1; }
  echo "fetched $out"
}

fetch "httpd-$HTTPD_VER.tar.gz" \
  "https://dlcdn.apache.org/httpd/httpd-$HTTPD_VER.tar.gz" \
  "https://archive.apache.org/dist/httpd/httpd-$HTTPD_VER.tar.gz"
fetch "apr-$APR_VER.tar.gz" \
  "https://dlcdn.apache.org/apr/apr-$APR_VER.tar.gz" \
  "https://archive.apache.org/dist/apr/apr-$APR_VER.tar.gz"
fetch "apr-util-$APRUTIL_VER.tar.gz" \
  "https://dlcdn.apache.org/apr/apr-util-$APRUTIL_VER.tar.gz" \
  "https://archive.apache.org/dist/apr/apr-util-$APRUTIL_VER.tar.gz"
fetch "postgresql-$PG_VER.tar.gz" \
  "https://ftp.postgresql.org/pub/source/v$PG_VER/postgresql-$PG_VER.tar.gz"

# Unpack fresh (idempotent: wipe and re-extract source trees only).
rm -rf "httpd-$HTTPD_VER" "postgresql-$PG_VER"
tar xzf "httpd-$HTTPD_VER.tar.gz"
tar xzf "apr-$APR_VER.tar.gz"
tar xzf "apr-util-$APRUTIL_VER.tar.gz"
tar xzf "postgresql-$PG_VER.tar.gz"
mv "apr-$APR_VER" "httpd-$HTTPD_VER/srclib/apr"
mv "apr-util-$APRUTIL_VER" "httpd-$HTTPD_VER/srclib/apr-util"
echo "OK: sources in $KA_WORK/src"
