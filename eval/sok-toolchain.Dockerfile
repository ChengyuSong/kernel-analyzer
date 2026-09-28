# Toolchain for eval/68-sok-httpd-apr.sh on hosts without clang 14/15:
# builds APR/APR-util to bitcode with the SAME compiler majors as the
# SoK-MLTA artifact (clang 14 for its LLVM 14 set, clang 15 for its
# LLVM 15 set). eval/69-sok-bigbox.sh runs eval/68 inside this image.
#   docker build -f eval/sok-toolchain.Dockerfile -t sok-toolchain eval
FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates make file tar gzip python3 \
      build-essential binutils \
      clang-14 llvm-14 llvm-14-tools llvm-14-linker-tools \
      clang-15 llvm-15 llvm-15-tools llvm-15-linker-tools \
      libexpat1-dev uuid-dev \
    && rm -rf /var/lib/apt/lists/* \
    && for v in 14 15; do test -x /usr/lib/llvm-$v/bin/clang \
         && test -x /usr/lib/llvm-$v/bin/llvm-link \
         && test -x /usr/lib/llvm-$v/bin/llvm-ar; done
