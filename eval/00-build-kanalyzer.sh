#!/bin/bash
# Build KAMain (release) from the repo this script lives in.
set -euo pipefail
source "$(dirname "$0")/env.sh"
ka_require "$KA_CC" cmake make

cd "$KA_REPO"
if [ ! -d release ]; then
  make BUILD_DIR=release LLVM_BUILD="$KA_LLVM_BUILD"
else
  cmake --build release -j "$KA_JOBS"
fi
[ -x "$KA_BIN" ] || { echo "build failed: $KA_BIN not found" >&2; exit 1; }
"$KA_BIN" --version 2>/dev/null || true
echo "OK: $KA_BIN"
