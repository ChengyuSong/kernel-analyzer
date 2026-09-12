# SoK-MLTA (WOOT'26) baseline analyzers — MLTA, DeepType, TFA, and
# TFA's MLTA-only variant — built from source at THEIR pinned
# commits with THEIR patches, entirely inside this image. Used by
# eval/66-sok-baselines.sh for the same-machine timing rows; the
# analyzers consume the artifact's PRE-BUILT bitcodes at run time
# (mounted read-only) — nothing about the benchmarks is rebuilt,
# and their llvm.patch (corpus generation / LLVM-CFI) is not used.
#
# Build context = the SoK-MLTA artifact checkout (for patches/):
#   docker build -f eval/sok-baselines.Dockerfile -t sok-baselines \
#       /path/to/SoK-MLTA
#
# Layout matches their hardcoded paths (/home/user/...):
#   /home/user/llvm-project/build/bin/llvm-objdump
#   /home/user/mlta/build/lib/kanalyzer            (PROGRAM_MLTA_ORIG)
#   /home/user/DeepType/build/lib/kanalyzer        (PROGRAM_DEEPTYPE)
#   /home/user/TFA-project/build/lib/analyzer      (PROGRAM_TFA)
#   /home/user/TFA-project-MLTA/build/lib/analyzer (PROGRAM_MLTA)
#
# Documented deviations from their Ubuntu 24.04 host setup (none
# affect the analyzers' behavior):
#  - base is ubuntu:22.04: GCC 13 (24.04) cannot compile LLVM 15
#    (missing-<cstdint> breakage); GCC 11 builds it cleanly.
#  - LLVM_ENABLE_PROJECTS drops lldb (their build-llvm.sh includes
#    it; the analyzers never touch it).
#  - TFA's OpenMP comes from distro libomp-14 instead of their
#    /usr/lib/llvm-19 paths (their own setup also mixed a distro
#    libomp with the source-built LLVM 15).
#  - No MySQL server: TFA's update_database() prints a warning and
#    returns on connect failure (their patch keeps the client lib).

FROM ubuntu:22.04 AS build
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      git ca-certificates cmake ninja-build build-essential python3 \
      zlib1g-dev libzstd-dev libxml2-dev libmysqlclient-dev \
      libomp-14-dev libz3-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /home/user
COPY patches /home/user/patches

# Their pinned commits (SoK-MLTA Readme).
ARG LLVM_COMMIT=8dfdcc7b7bf66834a761bd8de445840ef68e4d1a
ARG MLTA_COMMIT=1f2b4b7babb3308710940573efacfe78a53c9f6b
ARG DEEPTYPE_COMMIT=6c332d980169853c14eefd18b59947d07c0df834
ARG TFA_COMMIT=1b2d45da7f7891114237a88955fc6578b618d94f

# LLVM 15 at their Readme pin (their patched build-llvm.sh uses the
# releases/15.x branch — a moving ref; the Readme commit is the
# deterministic choice). Shallow single-commit fetch. cmake flags
# follow their build-llvm.sh (targets ARM;X86;AArch64) minus lldb.
RUN git init llvm-project && cd llvm-project \
    && git remote add origin https://github.com/llvm/llvm-project.git \
    && git fetch --depth 1 origin ${LLVM_COMMIT} \
    && git checkout FETCH_HEAD \
    && cmake -S llvm -B build -G Ninja \
         -DCMAKE_BUILD_TYPE=Release \
         -DLLVM_TARGETS_TO_BUILD="ARM;X86;AArch64" \
         -DLLVM_ENABLE_PROJECTS="clang" \
         -DLLVM_INCLUDE_TESTS=OFF -DLLVM_INCLUDE_EXAMPLES=OFF \
         -DLLVM_INCLUDE_BENCHMARKS=OFF \
    && ninja -C build

# MLTA (PROGRAM_MLTA_ORIG). The Makefiles hardcode author-specific
# LLVM paths (mlta: its own llvm-project/prefix; DeepType:
# /home/yufei/...) — the command-line LLVM_BUILD override retargets
# them at this image's build tree (cmake resolves headers/libs via
# llvm-config on PATH, so the build tree works like an install).
RUN git clone https://github.com/umnsec/mlta.git && cd mlta \
    && git checkout ${MLTA_COMMIT} \
    && git apply /home/user/patches/mlta.patch \
    && make LLVM_BUILD=/home/user/llvm-project/build \
    && test -x build/lib/kanalyzer

# DeepType.
RUN git clone https://github.com/s3team/DeepType.git && cd DeepType \
    && git checkout ${DEEPTYPE_COMMIT} \
    && git apply /home/user/patches/deeptype.patch \
    && make LLVM_BUILD=/home/user/llvm-project/build \
    && test -x build/lib/kanalyzer

# TFA, twice from one pinned tree. The full/MLTA-only split is the
# ENABLE_DATA_FLOW_ANALYSIS define in src/lib/Analyzer.cc (commented
# out at the pin = MLTA-only; uncommented = full TFA co-analysis).
# Their patch's OpenMP paths (their llvm-19 install) are remapped to
# this image's libomp-14.
RUN git clone https://github.com/dinghaoliu/TFA-project.git && cd TFA-project \
    && git checkout ${TFA_COMMIT} \
    && git apply /home/user/patches/tfa.patch \
    && sed -i 's|/usr/lib/llvm-19/lib/clang/19/include|/usr/lib/llvm-14/lib/clang/14.0.0/include|; s|/usr/lib/llvm-19/lib/|/usr/lib/llvm-14/lib/|' src/CMakeLists.txt \
    && grep -q 'llvm-14/lib/clang/14.0.0/include' src/CMakeLists.txt \
    && cd /home/user && cp -r TFA-project TFA-project-MLTA \
    && cd TFA-project \
    && sed -i 's|^//#define ENABLE_DATA_FLOW_ANALYSIS|#define ENABLE_DATA_FLOW_ANALYSIS|' src/lib/Analyzer.cc \
    && grep -q '^#define ENABLE_DATA_FLOW_ANALYSIS' src/lib/Analyzer.cc \
    && make LLVM_BUILD=/home/user/llvm-project/build \
    && test -x build/lib/analyzer \
    && cd /home/user/TFA-project-MLTA \
    && make LLVM_BUILD=/home/user/llvm-project/build \
    && test -x build/lib/analyzer

# Runtime image: the four analyzers + llvm-objdump (their harness's
# hardcoded path) + python for their driver. LLVM links statically,
# so only distro shared libs are needed.
FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      python3 python3-tqdm libomp5-14 libmysqlclient21 \
      zlib1g libzstd1 libxml2 libtinfo6 libz3-4 \
    && rm -rf /var/lib/apt/lists/*
ENV LD_LIBRARY_PATH=/usr/lib/llvm-14/lib
COPY --from=build /home/user/llvm-project/build/bin/llvm-objdump /home/user/llvm-project/build/bin/llvm-objdump
COPY --from=build /home/user/mlta/build/lib/kanalyzer /home/user/mlta/build/lib/kanalyzer
COPY --from=build /home/user/DeepType/build/lib/kanalyzer /home/user/DeepType/build/lib/kanalyzer
COPY --from=build /home/user/TFA-project/build/lib/analyzer /home/user/TFA-project/build/lib/analyzer
COPY --from=build /home/user/TFA-project-MLTA/build/lib/analyzer /home/user/TFA-project-MLTA/build/lib/analyzer
# No unresolved shared libs (grep exits 1 = none found).
RUN ! ldd /home/user/mlta/build/lib/kanalyzer \
          /home/user/DeepType/build/lib/kanalyzer \
          /home/user/TFA-project/build/lib/analyzer \
          /home/user/TFA-project-MLTA/build/lib/analyzer \
      | grep 'not found'
RUN chmod -R a+rX /home/user
WORKDIR /home/user
