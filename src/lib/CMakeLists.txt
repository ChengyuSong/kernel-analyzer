set (KASource
  KAMain.cc
  Annotation.cc
  StructAnalyzer.cc
  NodeFactory.cc
  PointTo.cc
  LLMClient.cc
  LLMAnalysis.cc
  CFLEdgeBuilder.cc
  VSnapshot.cc
  CompressedGraph.cc
  CallGraph.cc
  IRSidecar.cc
  WitnessTaint.cc
  IRCensus.cc
)

# Build executable, KAMain.
set (EXECUTABLE_OUTPUT_PATH ${KA_BINARY_DIR})
link_directories (${KA_BINARY_DIR}/lib)
add_executable(KAMain ${KASource})
target_link_libraries(KAMain
  LLVMAsmParser
  LLVMSupport
  LLVMCore
  LLVMAnalysis
  LLVMIRReader
  LLVMBitWriter
  graCFLlib
  )

# Unit tests (run manually: <build>/lib/StructAnalyzerTest)
add_executable(StructAnalyzerTest StructAnalyzerTest.cc StructAnalyzer.cc)
target_link_libraries(StructAnalyzerTest
  LLVMSupport
  LLVMCore
  )
add_test(NAME StructAnalyzerTest COMMAND StructAnalyzerTest)
