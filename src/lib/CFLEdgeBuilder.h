#ifndef CFL_EDGE_BUILDER_H
#define CFL_EDGE_BUILDER_H

#include <vector>
#include <fstream>
#include <memory>

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
  uint labelMAs;

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
   * @brief Clear accumulated edges
   */
  void clear() { edges.clear(); }

  /**
   * @brief Get grammar instance (for debugging)
   */
  const gracfl::Grammar* getGrammar() const { return grammar.get(); }

  /**
   * @brief Get label ID for assignment 'a'
   */
  const uint getLabelMAs() const { return labelMAs; }
};

#endif // CFL_EDGE_BUILDER_H