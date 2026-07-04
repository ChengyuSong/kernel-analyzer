#ifndef CFL_EDGE_BUILDER_H
#define CFL_EDGE_BUILDER_H

#include <vector>
#include <fstream>
#include <memory>
#include <stack>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>

#include "NodeFactory.h"
#include "gracfl/include/utils/Edges.hpp"
#include "gracfl/include/utils/Grammar.hpp"

/**
 * @brief Helper class to convert GlobalInitPtsGraph to CFL-reachability edges
 * 
 * Converts existing points-to relationships from populateNodeFactory into
 * CFL-reachability edges for the GraCFL engine. Uses Grammar class to lookup
 * label IDs for symbols 'a', '-a', 'd', '-d'.
 */
class CFLEdgeBuilder {
private:
  std::unique_ptr<gracfl::Grammar> grammar;
  std::vector<gracfl::Edge> edges;

  // Cache label IDs from grammar
  uint labelAssign;     // 'a'
  uint labelAssignInv;  // '-a'  
  uint labelDeref;      // 'd'
  uint labelDerefInv;   // '-d'
  uint labelM;          // 'M'
  uint labelV;          // 'V'

  // Field-sensitive extension labels (empty when grammar has no field rules)
  std::vector<uint> labelField;     // 'f<i>'
  std::vector<uint> labelFieldInv;  // '-f<i>'
  uint labelFieldAny;               // 'fx'
  uint labelFieldAnyInv;            // '-fx'

  bool labelsInitialized;

  /**
   * @brief Initialize label IDs from grammar file
   */
  void initializeLabels();

public:
  CFLEdgeBuilder()
    : labelsInitialized(false) {}

  /**
   * @brief Initialize with grammar file path
   */
  bool initializeGrammar(const std::string& grammarFilePath);

  /**
   * @brief Initialize with grammar rules from vector of strings
   */
  bool initializeGrammar(const std::vector<std::string>& grammarLines);

  /**
   * @brief Helper to add assignment edge pair
   * For assignment src -> dst, add edges (src, dst, 'a') and (dst, src, '-a')
   */
  void addAssignmentEdges(NodeIndex src, NodeIndex dst);

  /**
   * @brief Helper to add dereference edge pair (for future use)
   * For address-of x (dst) = &y (src), add edges (src, dst, 'd') and (dst, src, '-d')
   * For dereference *x (dst) of x (src), add edges (src, dst, 'd') and (dst, src, '-d')
   */
  void addDereferenceEdges(NodeIndex src, NodeIndex dst);

  /**
   * @brief Helper to remove assignment edge pair
   * Removes edges (src, dst, 'a') and (dst, src, '-a') if they exist
   * @return true if any edges were removed, false otherwise
   */
  bool removeAssignmentEdges(NodeIndex src, NodeIndex dst);

  /**
   * @brief Helper to remove dereference edge pair
   * Removes edges (src, dst, 'd') and (dst, src, '-d') if they exist
   * @return true if any edges were removed, false otherwise
   */
  bool removeDereferenceEdges(NodeIndex src, NodeIndex dst);

  /**
   * @brief Remove specific edge by source, destination and label
   * @return true if edge was found and removed, false otherwise
   */
  bool removeEdge(NodeIndex src, NodeIndex dst, uint label);

  /**
   * @brief Remove all edges involving a specific node (as source or destination)
   * @return number of edges removed
   */
  size_t removeEdgesInvolvingNode(NodeIndex node);

  /**
   * @brief Get the constructed edge list
   */
  const std::vector<gracfl::Edge>& getEdges() const { return edges; }

  /**
   * @brief Output edges to file for GraCFL
   * Format: "from to label\n"
   */
  void outputEdgesToFile(const std::string& filename) const;

  /**
   * @brief Print edges for debugging
   */
  void printEdges() const;

  /**
   * @brief Reserve capacity for the edge vector to avoid reallocations
   */
  void reserve(size_t n) { edges.reserve(n); }

  /**
   * @brief Clear accumulated edges
   */
  void clear() { edges.clear(); }

  /**
   * @brief Get grammar instance (for debugging)
   */
  const gracfl::Grammar* getGrammar() const { return grammar.get(); }

  /**
   * @brief Field-sensitive edge helpers.
   * bucket < 0 means the wildcard label 'fx'.
   */
  unsigned getNumFieldBuckets() const { return labelField.size(); }
  bool hasFieldLabels() const { return !labelField.empty(); }
  void addFieldEdges(NodeIndex src, NodeIndex dst, int bucket);
  void addFieldWildcardSelfLoop(NodeIndex n);
  uint getLabelField(unsigned bucket) const { return labelField[bucket]; }
  uint getLabelFieldInv(unsigned bucket) const { return labelFieldInv[bucket]; }
  uint getLabelFieldAny() const { return labelFieldAny; }
  uint getLabelFieldAnyInv() const { return labelFieldAnyInv; }

  /**
   * @brief Get label ID for aliasing labels
   */
  const uint getLabelM() const { return labelM; }
  const uint getLabelV() const { return labelV; }
  const uint getLabelAssign() const { return labelAssign; }
  const uint getLabelAssignInv() const { return labelAssignInv; }
  const uint getLabelDeref() const { return labelDeref; }
  const uint getLabelDerefInv() const { return labelDerefInv; }

  /**
   * @brief Detect and break cycles in the constraint graph
   * Uses Tarjan's algorithm to find SCCs and removes select edges to break cycles
   * @param maxSCCSize Maximum SCC size to break (default: 100)
   * @return Number of edges removed
   */
  size_t detectAndBreakCycles(size_t maxSCCSize = 100);

  /**
   * @brief Aggressive edge reduction when facing too many edges
   * @param maxEdges Maximum number of edges to keep
   * @return Number of edges removed
   */
  size_t aggressiveEdgeReduction(size_t maxEdges);

  /**
   * @brief Analyze and report nodes with extremely high out-degree
   * @param threshold Report nodes with out-degree above this value (default: 1000)
   * @param topN Show top N nodes by out-degree (default: 20)
   * @param outTopNodes Optional output vector to receive top N nodes as (NodeIndex, out-degree) pairs
   */
  void analyzeHighDegreeNodes(size_t threshold = 1000, size_t topN = 20,
                               std::vector<std::pair<NodeIndex, size_t>>* outTopNodes = nullptr);

private:
  /**
   * @brief Tarjan's SCC detection implementation
   */
  void tarjanSCC(std::vector<std::vector<NodeIndex>>& sccs);
  void tarjanDFS(NodeIndex node, std::vector<std::vector<NodeIndex>>& adjList,
                 std::vector<int>& disc, std::vector<int>& low, std::vector<bool>& onStack,
                 std::stack<NodeIndex>& st, std::vector<std::vector<NodeIndex>>& sccs, int& time);
};

#endif // CFL_EDGE_BUILDER_H