# [kanalyzer eval] Per-site indirect-call dumpers, one executable per
# analysis family so the families' headers, logging macros and cl::opts
# never meet in one binary. Added as tools/alias/icalls by
# eval/lotus-baseline.Dockerfile; LLVM_LINK_COMPONENTS comes from
# tools/alias/CMakeLists.txt.

llvm_map_components_to_libnames(ICALLS_LLVM_LIBS Core IRReader Support)

function(add_icalls_tool name source)
  add_executable(${name} IcallsCommon.cpp ${source})
  target_link_libraries(${name} PRIVATE ${ARGN} ${LLVM_LINK_COMPONENTS}
                        ${ICALLS_LLVM_LIBS})
endfunction()

add_icalls_tool(icalls-gpg GPG.cpp CanaryGPG)
add_icalls_tool(icalls-lotusaa LotusAA.cpp LotusAA)
add_icalls_tool(icalls-tpa TPA.cpp FSCSPointerAnalysis TPATransforms TPAUtil)
add_icalls_tool(icalls-fs FlowSensitive.cpp FlowSensitivePTA)
add_icalls_tool(icalls-sparrow Sparrow.cpp Andersen)
add_icalls_tool(icalls-bootstrap Bootstrap.cpp CanaryBootstrapAA)
add_icalls_tool(icalls-dda DDA.cpp DDA)
add_icalls_tool(icalls-th TypeHierarchy.cpp CanaryTypeHierarchy)

add_custom_target(icalls-all DEPENDS icalls-gpg icalls-lotusaa icalls-tpa
                  icalls-fs icalls-sparrow icalls-bootstrap icalls-dda
                  icalls-th)
