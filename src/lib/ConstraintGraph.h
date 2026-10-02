#ifndef KA_CONSTRAINT_GRAPH_H
#define KA_CONSTRAINT_GRAPH_H

// The solver's own constraint graph, built directly by the IR walk.
//
// Every edge is stored once, in its forward direction, with a typed kind.
// The inverse directions that a grammar-driven CFL engine needs (-a, -d,
// -f<b>, -fx) are implied, not stored; the baseline tool (src/baseline)
// derives them when it flattens this graph into GraCFL's labelled edges.
// Edge order is the order of construction and is part of the contract:
// the flows-to solver numbers nodes in first-seen order over this list.

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "NodeFactory.h"

enum class EdgeKind : uint8_t {
  Copy,     // value flow src -> dst                       (grammar 'a')
  Deref,    // pointer -> the cell it points to            (grammar 'd')
  Field,    // base -> field address, byte-offset residue  (grammar 'f<b>')
  FieldAny, // base -> address at an unknown offset        (grammar 'fx')
};

struct GraphEdge {
  NodeIndex from;
  NodeIndex to;
  EdgeKind kind;
  uint32_t bucket; // Field: offset residue mod numFieldBuckets(); else 0
};

class ConstraintGraph {
  unsigned numBuckets = 0; // field residues P; 0 = field-insensitive
  bool configured = false;
  std::vector<GraphEdge> edgeList;
  uint64_t removals = 0;

  void checkNode(NodeIndex n, const char *what) const;

public:
  // Called once, before any edge: P > 0 enables field edges.
  void setFieldBuckets(unsigned P);
  unsigned numFieldBuckets() const { return numBuckets; }
  bool fieldSensitive() const { return numBuckets > 0; }

  void addCopy(NodeIndex src, NodeIndex dst);
  void addDeref(NodeIndex ptr, NodeIndex cell);
  // bucket < 0: unknown offset (FieldAny); otherwise the residue is
  // bucket mod P. Requires fieldSensitive().
  void addField(NodeIndex base, NodeIndex dst, int bucket);
  void addFieldAnyLoop(NodeIndex n);
  // Removes the first Copy edge src -> dst; false if there is none.
  bool removeCopy(NodeIndex src, NodeIndex dst);

  const std::vector<GraphEdge> &edges() const { return edgeList; }
  size_t size() const { return edgeList.size(); }
  void reserve(size_t n) { edgeList.reserve(n); }
  // Number of removals so far: a consumer that mirrors the edge list
  // incrementally must rebuild when this changes.
  uint64_t removalCount() const { return removals; }

  // Verbose diagnostic: nodes whose degree (both directions of every
  // edge, as a CFL engine sees them) exceeds `threshold`; the top `topN`
  // are logged and returned.
  void analyzeHighDegreeNodes(
      size_t threshold, size_t topN,
      std::vector<std::pair<NodeIndex, size_t>> *outTopNodes) const;
};

#endif
