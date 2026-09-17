# KallGraph (seclab-ucr, commit 058f9b5) built from the local checkout with
# its undisclosed caps made configurable (Z3 fetched by SVF's build.sh), so the caps' contribution to its
# precision can be measured: KG_EDGE_CAP (default 35 = theirs) bounds the
# DFS path length; KG_NO_BLOCK=1 disables the static hub block (> baseNum*5
# call edges per parameter) and the dynamic top-50 blacklist. Everything
# else is their code. Build context = the KallGraph checkout. Image build is
# the single networked step (apt + SVF's Z3 comes from apt); runs use
# --network none, host uid, read-only mounts (eval/kallgraph-caps.sh).
FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential cmake ninja-build git python3 wget unzip ca-certificates \
      llvm-14-dev clang-14 libz3-dev zlib1g-dev libncurses5-dev libtinfo-dev libxml2-dev \
    && rm -rf /var/lib/apt/lists/*
COPY . /opt/kallgraph
WORKDIR /opt/kallgraph
# caps -> environment
RUN sed -i '1i #include <cstdlib>\nstatic unsigned kgEdgeCap(){ static int v=-1; if(v<0){const char*e=getenv("KG_EDGE_CAP"); v=e?atoi(e):35;} return v; }\nstatic bool kgBlock(){ static int v=-1; if(v<0){ v=getenv("KG_NO_BLOCK")?0:1;} return v; }' src/lib/KallGraphAlgo.cpp \
    && sed -i 's/visitedEdges.size() > 35/visitedEdges.size() > kgEdgeCap()/' src/lib/KallGraphAlgo.cpp \
    && sed -i 's/if (BlockedNodes.find(nxt->getId()) != BlockedNodes.end()) {/if (kgBlock() \&\& BlockedNodes.find(nxt->getId()) != BlockedNodes.end()) {/' src/lib/KallGraphAlgo.cpp \
    && sed -i 's/if (counter > 20000) {/if (kgBlock() \&\& counter > 20000) {/' src/lib/KallGraphAlgo.cpp \
    && sed -i 's/> baseNum \* 5) {/> baseNum * 5 \&\& getenv("KG_NO_BLOCK") == nullptr) {/' src/lib/Util.cpp \
    && grep -c 'kgEdgeCap()\|kgBlock()' src/lib/KallGraphAlgo.cpp && grep -c 'KG_NO_BLOCK' src/lib/Util.cpp \
    && sed -i 's#set(ENV{LLVM_DIR} .*#set(ENV{LLVM_DIR} /usr/lib/llvm-14/lib/cmake/llvm)#; s#set(ENV{SVF_DIR} .*#set(ENV{SVF_DIR} /opt/kallgraph/SVF-2.5)#' CMakeLists.txt
# SVF-2.5 against the distro LLVM 14 and Z3
ENV LLVM_DIR=/usr/lib/llvm-14
RUN cd SVF-2.5 && bash ./build.sh 2>&1 | tail -20 && ls Release-build/lib/libSvf.a
# KallGraph
RUN mkdir build && cd build \
    && LLVM_DIR=/usr/lib/llvm-14/lib/cmake/llvm SVF_DIR=/opt/kallgraph/SVF-2.5 Z3_DIR=/opt/kallgraph/SVF-2.5/z3.obj \
       cmake .. -DCMAKE_BUILD_TYPE=Release -DSVF_DIR=/opt/kallgraph/SVF-2.5 -DZ3_DIR=/opt/kallgraph/SVF-2.5/z3.obj \
    && make -j8 2>&1 | tail -5 && find . -name KallGraph -type f
