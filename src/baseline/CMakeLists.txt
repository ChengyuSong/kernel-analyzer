# KABaseline: the CFL-reachability call-graph baseline (RQ1). Shares the
# analysis core with KAMain and solves with GraCFL.
add_executable(KABaseline
  BaselineMain.cc
  CFLCGPass.cc
  CFLEdgeBuilder.cc
  CompressedGraph.cc
  VSnapshot.cc
)
target_include_directories(KABaseline PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(KABaseline kacore graCFLlib)
