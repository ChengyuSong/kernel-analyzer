# Toolchain for eval/59-kernel-corpus.sh with KA_KERNEL_LLVM=14: Ubuntu
# 22.04's clang/LLVM 14 (14.0.0). KallGraph pins LLVM 14.0.6 and SVF 2.5
# and reads typed-pointer bitcode only, so the kernel corpus it is
# compared on must be built with clang 14; KAMain (LLVM 18) reads the
# same files, so both tools see identical IR.
#   docker build -f eval/kernel-toolchain-14.Dockerfile -t kernel-toolchain-14 eval
FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates make gcc libc6-dev flex bison bc cpio kmod perl \
      python3 xz-utils libelf-dev libssl-dev \
      clang-14 lld-14 llvm-14 \
    && rm -rf /var/lib/apt/lists/*
ENV PATH=/usr/lib/llvm-14/bin:$PATH
RUN clang --version | head -1
