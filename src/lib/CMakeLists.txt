# Analysis core shared by KAMain and the CFL baseline (src/baseline):
# IR loading, constraint-graph build, the flows-to solver, outputs.
set (KACoreSource
  Flags.cc
  Driver.cc
  Annotation.cc
  StructAnalyzer.cc
  NodeFactory.cc
  LLMClient.cc
  LLMAnalysis.cc
  ConstraintGraph.cc
  CallGraph.cc
  GraphBuild.cc
  Presolve.cc
  FlowsToSolver.cc
  CellSolver.cc
  Names.cc
  NamedCells.cc
  TypeLabels.cc
  UnionCensus.cc
  Summaries.cc
  Census.cc
  Slots.cc
  TaggedFields.cc
  Dump.cc
  IRSidecar.cc
  IRCensus.cc
)

add_library(kacore STATIC ${KACoreSource})
get_filename_component(KA_DEFAULT_SUMMARIES
  "${PROJECT_SOURCE_DIR}/../func_summaries.txt" ABSOLUTE)
target_compile_definitions(kacore PRIVATE
  KA_DEFAULT_SUMMARIES="${KA_DEFAULT_SUMMARIES}")
target_include_directories(kacore PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(kacore PUBLIC
  LLVMTransformUtils
  LLVMAsmParser
  LLVMSupport
  LLVMCore
  LLVMAnalysis
  LLVMIRReader
  LLVMBitWriter
  )

# Build executable, KAMain (the flows-to solver). jemalloc is its
# allocator, as it was when KAMain linked GraCFL.
set (EXECUTABLE_OUTPUT_PATH ${KA_BINARY_DIR})
link_directories (${KA_BINARY_DIR}/lib)
add_executable(KAMain KAMain.cc)
target_link_libraries(KAMain kacore ${JEMALLOC_LIBS})
if(TARGET libjemalloc)
  add_dependencies(KAMain libjemalloc)
endif()

# Unit tests (run manually: <build>/lib/StructAnalyzerTest)
add_executable(StructAnalyzerTest StructAnalyzerTest.cc StructAnalyzer.cc)
target_link_libraries(StructAnalyzerTest
  LLVMSupport
  LLVMCore
  )
add_test(NAME StructAnalyzerTest COMMAND StructAnalyzerTest)
