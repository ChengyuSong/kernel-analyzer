# Toolchain for eval/59-kernel-corpus.sh: Ubuntu 24.04's clang/LLVM 18
# (18.1.3, the compiler the evaluated Linux 5.18 corpus was built with).
#   docker build -f eval/kernel-toolchain.Dockerfile -t kernel-toolchain eval
FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates make gcc libc6-dev flex bison bc cpio kmod perl \
      python3 xz-utils libelf-dev libssl-dev \
      clang-18 lld-18 llvm-18 \
    && rm -rf /var/lib/apt/lists/*
ENV PATH=/usr/lib/llvm-18/bin:$PATH
RUN clang --version | head -1
