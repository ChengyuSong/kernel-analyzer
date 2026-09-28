# Lotus (github.com/ZJU-PL/lotus) call-graph tool: whole-program
# pointer-analysis baselines for the SoK-MLTA comparison — AserPTA
# (inclusion-based; CI, 1-CFA, 2-CFA), DyckAA (unification-based), plus
# its GPG/LotusAA engines. LLVM 14 only, so these rows run on the SoK
# artifact's LLVM 14 bitcode, paired with KAMain on the SAME files.
#
# Build context = a directory holding
#   lotus.tar          git -C <lotus> archive -o lotus.tar <commit>
#   icall-sites.patch  eval/lotus-baseline/icall-sites.patch
#   resolution-rule.patch  eval/lotus-baseline/resolution-rule.patch
#   seadsa-icalls.cpp  eval/lotus-baseline/seadsa-icalls.cpp
#   more-cg-types.patch  eval/lotus-baseline/more-cg-types.patch
#   icalls/            eval/lotus-baseline/icalls/ (per-site dumpers)
# `eval/67-dataflow-baselines.sh build` prepares it. icall-sites.patch
# adds --emit-icall-sites-json (per-site targets in the SoK parsed_log
# key space); it changes no analysis. resolution-rule.patch adds OPT-IN
# switches that align a baseline's indirect-call resolution rule with
# KAMain's (signature shape, not exact type): -aser-shape-compat for
# AserPTA, and ">=" level semantics for DyckAA's
# -function-type-check-level. Both defaults reproduce upstream.
# more-cg-types.patch (later layer) records which GPG call sites got
# GPG's type-based fallback fill (no analysis change) and adds
# -cg-type=aserpta-origin (AserPTA KOrigin<1>) to the call-graph tool.
# icalls/ builds one per-site dumper per analysis family (icalls-gpg,
# -lotusaa, -tpa, -fs, -sparrow, -bootstrap, -dda, -th); each writes the
# same JSON as --emit-icall-sites-json plus <base>.<reason>.sites
# sidecars for sites whose answer is a fill (fallback / universal /
# unknown / top / budget), see icalls/IcallsCommon.h.
#
# Recorded upstream commit (the archive's source): LOTUS_COMMIT below.
# Network is needed only for apt.

FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates gcc g++ cmake ninja-build patch time \
      libgmp-dev libboost-all-dev libz3-dev python3 \
      llvm-14 llvm-14-dev llvm-14-tools clang-14 \
      zlib1g-dev libzstd-dev libedit-dev libxml2-dev libffi-dev \
      libncurses-dev \
    && rm -rf /var/lib/apt/lists/*

ARG LOTUS_COMMIT=0da4c2813005249bce390329d28810a2c4ac0e76
LABEL lotus.commit=${LOTUS_COMMIT}
COPY lotus.tar icall-sites.patch resolution-rule.patch /tmp/
RUN mkdir /lotus && tar -xf /tmp/lotus.tar -C /lotus \
    && cd /lotus && patch -p1 < /tmp/icall-sites.patch \
    && patch -p1 < /tmp/resolution-rule.patch \
    && rm /tmp/lotus.tar

WORKDIR /lotus/build
RUN cmake -G Ninja .. \
      -DCMAKE_BUILD_TYPE=Release \
      -DLLVM_BUILD_PATH=/usr/lib/llvm-14/lib/cmake/llvm \
      -DLLVM_CONFIG_PATH=/usr/bin/llvm-config-14 \
      -DLLVM_DIR=/usr/lib/llvm-14/lib/cmake/llvm \
      -DZ3_DIR=/usr \
      -DLOTUS_DOWNLOAD_BOOST=OFF \
    && ninja lotus-alias-call-graph
RUN ln -s "$(find /lotus/build -name lotus-alias-call-graph -type f -perm -u+x | head -1)" \
      /usr/local/bin/lotus-alias-call-graph \
    && lotus-alias-call-graph --help | grep -q emit-icall-sites-json

# SeaDsa CompleteCallGraph dumper (eval/lotus-baseline/seadsa-icalls.cpp),
# a separate layer so the call-graph build above stays cached.
COPY seadsa-icalls.cpp /lotus/tools/alias/seadsa-icalls.cpp
RUN printf '%s\n' '' 'add_executable(seadsa-icalls seadsa-icalls.cpp)' \
      'target_link_libraries(seadsa-icalls PRIVATE SeaDsaAnalysis CanaryAliasCLIUtils)' \
      >> /lotus/tools/alias/CMakeLists.txt \
    && cd /lotus/build && cmake . && ninja seadsa-icalls \
    && ln -s "$(find /lotus/build -name seadsa-icalls -type f -perm -u+x | head -1)" \
         /usr/local/bin/seadsa-icalls \
    && seadsa-icalls --help | grep -q icalls-json

# [more-cg-types] GPG fallback record + aserpta-origin (more-cg-types.patch),
# and the analysis libraries the per-site dumpers link. -j12: the host is
# shared.
COPY more-cg-types.patch /tmp/
RUN cd /lotus && patch -p1 < /tmp/more-cg-types.patch \
    && cd /lotus/build && cmake . \
    && ninja -j12 lotus-alias-call-graph CanaryGPG LotusAA \
         FSCSPointerAnalysis TPATransforms FlowSensitivePTA Andersen \
         CanaryBootstrapAA DDA CanaryTypeHierarchy \
    && lotus-alias-call-graph --help | grep -q aserpta-origin
# TPA's ptr.spec and SparrowAA's ptr/modref.spec (Lotus's own defaults).
ENV LOTUS_CONFIG_DIR=/lotus/config

# Per-site dumpers (eval/lotus-baseline/icalls), a separate layer so the
# library build above stays cached.
COPY icalls /lotus/tools/alias/icalls
RUN printf '%s\n' '' 'add_subdirectory(icalls)' \
      >> /lotus/tools/alias/CMakeLists.txt \
    && cd /lotus/build && cmake . && ninja -j12 icalls-all \
    && for t in gpg lotusaa tpa fs sparrow bootstrap dda th; do \
         ln -s "$(find /lotus/build -name icalls-$t -type f -perm -u+x | head -1)" \
           /usr/local/bin/icalls-$t || exit 1; \
         icalls-$t --help | grep -q icalls-backend || exit 1; \
       done
