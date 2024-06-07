set (KASource
  KAMain.cc
  Annotation.cc
  StructAnalyzer.cc
  CallGraph.cc
  #SafeStack.cc
  #Range.cc
  #LinuxSS.cc
  NodeFactory.cc
  PointTo.cc
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
  )
