#ifndef CFL_EDGE_BUILDER_H
#define CFL_EDGE_BUILDER_H

#include <memory>
#include <string>
#include <vector>

#include "ConstraintGraph.h"
#include "gracfl/include/utils/Edges.hpp"
#include "gracfl/include/utils/Grammar.hpp"

// GraCFL's view of the constraint graph: a grammar plus labelled edges.
//
// Each typed edge of the ConstraintGraph becomes two labelled edges, the
// forward label and its inverse, in graph order:
//   Copy u->v      (u,v,a)    (v,u,-a)
//   Deref u->v     (u,v,d)    (v,u,-d)
//   Field b u->v   (u,v,f<b>) (v,u,-f<b>)
//   FieldAny u->v  (u,v,fx)   (v,u,-fx)
// so labelled index 2i/2i+1 is typed edge i. The view follows the graph:
// edges appended since the last read are appended here; any removal in
// the graph rebuilds the view.
class CFLEdgeBuilder {
  const ConstraintGraph *graph = nullptr;
  std::unique_ptr<gracfl::Grammar> grammar;
  mutable std::vector<gracfl::Edge> edges;
  mutable size_t syncedTyped = 0;
  mutable uint64_t syncedRemovals = 0;

  uint labelAssign = 0, labelAssignInv = 0;
  uint labelDeref = 0, labelDerefInv = 0;
  uint labelM = 0, labelV = 0;
  std::vector<uint> labelField, labelFieldInv; // 'f<i>', '-f<i>'
  uint labelFieldAny = 0, labelFieldAnyInv = 0; // 'fx', '-fx'

  void initializeLabels();
  void sync() const;

public:
  // The grammar's field labels must match the graph's field buckets.
  void initialize(const ConstraintGraph &G,
                  const std::vector<std::string> &grammarLines);
  void initialize(const ConstraintGraph &G, const std::string &grammarFile);

  const std::vector<gracfl::Edge> &getEdges() const {
    sync();
    return edges;
  }
  const gracfl::Grammar *getGrammar() const { return grammar.get(); }

  // Writes "from to label" lines (GraCFL's edge-list input).
  void outputEdgesToFile(const std::string &filename) const;

  unsigned getNumFieldBuckets() const { return labelField.size(); }
  bool hasFieldLabels() const { return !labelField.empty(); }
  uint getLabelField(unsigned bucket) const { return labelField[bucket]; }
  uint getLabelFieldInv(unsigned bucket) const { return labelFieldInv[bucket]; }
  uint getLabelFieldAny() const { return labelFieldAny; }
  uint getLabelFieldAnyInv() const { return labelFieldAnyInv; }
  uint getLabelM() const { return labelM; }
  uint getLabelV() const { return labelV; }
  uint getLabelAssign() const { return labelAssign; }
  uint getLabelAssignInv() const { return labelAssignInv; }
  uint getLabelDeref() const { return labelDeref; }
  uint getLabelDerefInv() const { return labelDerefInv; }
};

#endif // CFL_EDGE_BUILDER_H
