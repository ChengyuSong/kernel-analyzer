# SVF (upstream, pinned release) + svf-icalls: the whole-program
# pointer-analysis baseline for the SoK-MLTA comparison. SVF resolves
# indirect calls from points-to sets with an arity-only check and no
# type shortcut. eval/67-dataflow-baselines.sh runs it sandboxed.
#
# Build context = eval/svf-baseline (holds svf-icalls.cpp):
#   docker build -f eval/svf-baseline.Dockerfile -t svf-baseline \
#       eval/svf-baseline
#
# Version: SVF-3.2 (LLVM 18). SVF-3.3 (LLVM 21) is NOT usable here: its
# own `wpa -ander` aborts on the SoK bitcode (LLVM 14 and 15 alike) with
# "Value::materialized_user_begin: Assertion `hasUseList()' failed" —
# LLVM 21 dropped use lists from constant data, which SVF-3.3 still
# walks. LLVM 18 reads the artifact's LLVM 14 and LLVM 15 bitcode.
#
# Network is needed only here: the SVF checkout and build.sh's
# prebuilt LLVM (RTTI) + Z3 downloads.

FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates cmake g++ gcc git zlib1g-dev libncurses5-dev \
      libtinfo6 build-essential libssl-dev libpcre2-dev zip unzip \
      libzstd-dev python3-dev wget curl xz-utils tcl time \
    && rm -rf /var/lib/apt/lists/*

# SVF-3.2 (2025-12-17), fetched by commit for determinism.
ARG SVF_COMMIT=197a6590bd9c695a9c3daf52622dea912ef9a002
WORKDIR /opt
RUN git init SVF && cd SVF \
    && git remote add origin https://github.com/SVF-tools/SVF.git \
    && git fetch --depth 1 origin ${SVF_COMMIT} \
    && git checkout FETCH_HEAD

# Unmodified SVF build (cached layer).
WORKDIR /opt/SVF
RUN bash ./build.sh \
    && test -f /opt/SVF/Release-build/lib/extapi.bc
# Same runtime link fix as SVF's own Dockerfile.
RUN ln -sf /opt/SVF/z3.obj/bin/libz3.so /opt/SVF/z3.obj/bin/libz3.so.4 || true

# Register svf-icalls as one more SVF tool (same link setup as wpa) and
# build only it, on top of the finished SVF build.
COPY svf-icalls.cpp /opt/SVF/svf-llvm/tools/ICalls/svf-icalls.cpp
RUN cd /opt/SVF/svf-llvm/tools \
    && printf '%s\n' 'set(THREADS_PREFER_PTHREAD_FLAG ON)' \
         'add_llvm_executable(svf-icalls svf-icalls.cpp)' \
         'find_package(Threads REQUIRED)' \
         'target_link_libraries(svf-icalls PUBLIC Threads::Threads)' \
         > ICalls/CMakeLists.txt \
    && sed -i 's/^add_subdirectory(AE)$/add_subdirectory(AE)\nadd_subdirectory(ICalls)/' CMakeLists.txt \
    && sed -i 's/^    wpa$/    wpa\n    svf-icalls/' CMakeLists.txt \
    && grep -q 'add_subdirectory(ICalls)' CMakeLists.txt \
    && grep -q '^    svf-icalls$' CMakeLists.txt \
    && cd /opt/SVF/Release-build && cmake . && make -j"$(nproc)" svf-icalls

ENV PATH=/opt/SVF/Release-build/bin:$PATH
ENV SVF_EXTAPI=/opt/SVF/Release-build/lib/extapi.bc
RUN test -x /opt/SVF/Release-build/bin/svf-icalls
