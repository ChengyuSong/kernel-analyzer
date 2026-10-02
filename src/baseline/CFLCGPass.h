#ifndef KA_CFLCG_PASS_H
#define KA_CFLCG_PASS_H

// The CFL-reachability call-graph baseline: the same IR-built constraint
// graph as KAMain, solved by all-pairs saturation with GraCFL, either
// monolithically or per translation unit with composition
// (--cfl-compositional). This is the RQ1 baseline; KAMain does not link
// it.

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "CallGraph.h"
#include "CFLEdgeBuilder.h"
#include "CompressedGraph.h"
#include "gracfl/include/solvers/SolverFWGramParallel.hpp"
#include "gracfl/include/utils/Reachability.hpp"

class CFLCGPass : public CallGraphPass {
  using cfl_result_t = gracfl::ReachabilityMatrix;

  // GraCFL's labelled view of Graph.
  CFLEdgeBuilder EB;
  unsigned cflThreads;

  // Monolithic saturation state.
  std::unique_ptr<gracfl::SolverFWGramParallel> cflSolver;
  size_t cflSolvedInputEdgeCount = 0;
  bool cflForceRebuild = true;

  // Dense ID mapping (after global dedup)
  std::vector<uint32_t> origToDense;
  std::vector<NodeIndex> denseToOrig;
  uint32_t numDenseNodes = 0;
  std::vector<gracfl::Edge> denseEdges;
  void buildDenseMapping();
  uint32_t getDenseID(NodeIndex origNode) const;

  // Per-module ranges of EB's labelled edges (repair mode recomputes
  // selected modules).
  std::unordered_map<llvm::Module *, std::pair<size_t, size_t>>
      moduleEdgeRanges;

  // Per-TU compositional solving
  std::vector<CompressedGraphData> perTUGraphs;
  void solveAndCompressPerTU(llvm::Module *M, size_t edgeStart,
                             size_t edgeEnd);
  std::unordered_set<NodeIndex> fptrSliceKept;
  void sliceEdgesToFptrComponents(std::vector<size_t> &idx);

  // Compositional solve results (for V-snapshot export)
  std::unique_ptr<gracfl::SolverFWGramParallel> composedSolver;
  std::unordered_map<std::string, uint32_t> composedSymbolToDense;
  uint32_t composedNumDense = 0;

  bool findCustomAllocators(const cfl_result_t &outputCFLGraph,
                            bool rewriteEdges = true);
  bool findCustomAllocatorsComposed(
      const cfl_result_t &composedGraph,
      const std::unordered_map<std::string, uint32_t> &symbolToDense);
  bool lookupRetDense(const llvm::Function *F,
                      const std::unordered_map<std::string, uint32_t> &symMap,
                      uint32_t graphSize, uint32_t &retDense) const;
  bool lookupArgDense(const llvm::Function *F, unsigned argNo,
                      const std::unordered_map<std::string, uint32_t> &symMap,
                      uint32_t graphSize, uint32_t &argDense) const;
  bool lookupVarargDense(const llvm::Function *F,
                         const std::unordered_map<std::string, uint32_t> &symMap,
                         uint32_t graphSize, uint32_t &varargDense) const;
  bool handleIndirectCall(const cfl_result_t &outputCFLGraph,
                          const CallInstSet &indirectCalls);

  // V-SCC computation and constraint graph compression
  void computeVSCC(const cfl_result_t &outputCFLGraph, unsigned labelV,
                   std::vector<uint32_t> &nodeToSCC, uint32_t &numSCCs);
  void compressConstraintGraph(const cfl_result_t &outputCFLGraph,
                               const std::vector<uint32_t> &nodeToSCC,
                               uint32_t numSCCs, CompressedGraphData &out);

  // Typed-edge indices of the labelled indices in idx (each typed edge
  // is the labelled pair 2i, 2i+1; both must be present).
  std::vector<size_t> typedEdgeIndices(const std::vector<size_t> &idx) const;

protected:
  bool solve() override;
  void moduleBuilt(llvm::Module *M, size_t edgeStart, size_t edgeEnd) override;
  bool flowsTo() const override { return false; }
  bool compositional() const override;
  bool perTUSolve() const override;
  bool exportsCallBoundaries() const override;

public:
  // grammarLines are used when grammarFile is empty.
  CFLCGPass(GlobalContext *Ctx_, const std::vector<std::string> &grammarLines,
            const std::string &grammarFile);

  bool runCompositionalSolve();
  void dumpVSnapshot(llvm::StringRef Path);
  void dumpComposedVSnapshot(llvm::StringRef Path);
  void exportCompressedGraph(llvm::StringRef Path);
  const CFLEdgeBuilder &edgeView() const { return EB; }
};

#endif
