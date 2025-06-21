set (KASource
  KAMain.cc
  Annotation.cc
  StructAnalyzer.cc
  NodeFactory.cc
  PointTo.cc
  CallGraph.cc
  Reachable.cc
  TyPMCommon.cc
  MLTA.cc
  TyPM.cc
  TyPMPass.cc
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
  )
