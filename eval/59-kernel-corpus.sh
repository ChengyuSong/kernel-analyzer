#!/bin/bash
# Build the Linux 5.18 bitcode corpus the kernel evaluation analyzes.
#
#   source   linux-5.18.tar.xz from kernel.org, checked against the
#            sha256 kernel.org publishes (v5.x/sha256sums.asc)
#   config   x86-64 defconfig with Clang ThinLTO enabled
#            (LTO_NONE -> LTO_CLANG_THIN), nothing else changed
#   compiler Ubuntu 24.04 clang 18 (kernel-toolchain image), LLVM=1
#   patch    eval/kernel/linux-5.18-clang18.patch = exactly the source
#            changes of the evaluated tree (13 files) that let 5.18, which
#            predates clang 18, build with it: function casts replaced by
#            typed wrappers (sched balance_callback, paravirt, dmi-id,
#            ext4, perf, ALSA seq), -Wno-cast-function-type-strict in
#            scripts/Makefile.clang, and the vDSO version script's SGX
#            symbol guarded by CONFIG_X86_SGX. The wrappers change the IR;
#            they are part of the evaluated corpus.
#   build id KBUILD_BUILD_{USER,HOST,TIMESTAMP} fixed, so init/version.o
#            does not embed who or when it was built
#   corpus   every .o under the tree that is LLVM bitcode (ThinLTO leaves
#            compiled C as bitcode; assembly objects stay ELF)
#
# The build runs in a container that mounts the tree at the SAME
# absolute path, so the file list is valid on the host.
# Output: $KA_WORK/linux-5.18/ and $KA_WORK/linux-5.18.bclist
#         (use as KA_KERNEL_BCLIST for eval/60 and eval/61).
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
source "$(dirname "${BASH_SOURCE[0]}")/lib-fetch.sh"
ka_require docker python3
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

V=5.18
URL="https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-$V.tar.xz"
SHA=51f3f1684a896e797182a0907299cc1f0ff5e5b51dd9a55478ae63a409855cee
TAR="$KA_WORK/linux-$V.tar.xz"
TREE="$KA_WORK/linux-$V"
LIST="$KA_WORK/linux-$V.bclist"

fetch_url "$URL" "$TAR" "$SHA"
if [[ ! -f "$TREE/Makefile" ]]; then
  echo "== extracting $TAR"
  tar -xf "$TAR" -C "$KA_WORK"
  patch -d "$TREE" -p1 --forward -s < "$HERE/kernel/linux-5.18-clang18.patch" \
    || { echo "!! kernel source patch failed" >&2; exit 1; }
fi
grep -q "struct balance_callback" "$TREE/kernel/sched/sched.h" \
  || { echo "!! $TREE lacks eval/kernel/linux-5.18-clang18.patch" >&2; exit 1; }

docker image inspect kernel-toolchain >/dev/null 2>&1 || \
  docker build -f "$HERE/kernel-toolchain.Dockerfile" -t kernel-toolchain "$HERE"

echo "== building linux-$V (defconfig + ThinLTO, clang 18) in $TREE"
docker run --rm --network none -u "$(id -u):$(id -g)" -e HOME=/tmp \
  -v "$TREE":"$TREE" -w "$TREE" kernel-toolchain bash -c '
    set -e
    make -s LLVM=1 defconfig
    scripts/config --disable LTO_NONE --enable LTO_CLANG_THIN
    make -s LLVM=1 olddefconfig
    grep -q "^CONFIG_LTO_CLANG_THIN=y" .config || { echo "!! ThinLTO not enabled" >&2; exit 1; }
    make LLVM=1 KBUILD_BUILD_USER=builder KBUILD_BUILD_HOST=builder KBUILD_BUILD_TIMESTAMP="2022-05-22 00:00:00" -j'"${KA_JOBS:-$(nproc)}"' > build.log 2>&1 || { tail -30 build.log >&2; exit 1; }
  '

python3 - "$TREE" "$LIST" <<'EOF'
import os, sys
tree, out = sys.argv[1], sys.argv[2]
bc = []
for root, _, files in os.walk(tree):
    for f in files:
        if f.endswith('.o'):
            p = os.path.join(root, f)
            with open(p, 'rb') as h:
                if h.read(4) in (b'BC\xc0\xde', b'\xde\xc0\x17\x0b'):
                    bc.append(p)
open(out, 'w').write('\n'.join(sorted(bc)) + '\n')
print(f'== corpus: {len(bc)} bitcode objects -> {out}')
EOF
