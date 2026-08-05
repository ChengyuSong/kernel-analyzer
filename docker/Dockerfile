# Runtime container for KAMain kernel-scale runs: matches the host
# (Ubuntu 24.04) so the host-built binary runs unmodified; LLVM is
# statically linked, so only the small runtime set is needed.
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
    zstd libzstd1 zlib1g libtinfo6 libjemalloc2 libtbb12 libtbbmalloc2 \
    libomp5-18 time \
 && rm -rf /var/lib/apt/lists/*
