#include "ConstraintGraph.h"

#include <algorithm>
#include <cassert>
#include <unordered_map>

#include "Common.h"

#define CGRAPH_LOG(stmt) KA_LOG(2, "ConstraintGraph: " << stmt)

void ConstraintGraph::setFieldBuckets(unsigned P) {
  assert(!configured && edgeList.empty() &&
         "field buckets are fixed before the first edge");
  numBuckets = P;
  configured = true;
}

void ConstraintGraph::checkNode(NodeIndex n, const char *what) const {
  assert(configured && "ConstraintGraph used before setFieldBuckets");
  if (n == AndersNodeFactory::InvalidIndex) {
    errs() << "ConstraintGraph: invalid node index for " << what << " edge\n";
    abort();
  }
}

void ConstraintGraph::addCopy(NodeIndex src, NodeIndex dst) {
  checkNode(src, "copy");
  checkNode(dst, "copy");
  edgeList.push_back({src, dst, EdgeKind::Copy, 0});
}

void ConstraintGraph::addDeref(NodeIndex ptr, NodeIndex cell) {
  checkNode(ptr, "deref");
  checkNode(cell, "deref");
  edgeList.push_back({ptr, cell, EdgeKind::Deref, 0});
}

void ConstraintGraph::addField(NodeIndex base, NodeIndex dst, int bucket) {
  assert(fieldSensitive() && "field edge in a field-insensitive graph");
  checkNode(base, "field");
  checkNode(dst, "field");
  if (bucket < 0)
    edgeList.push_back({base, dst, EdgeKind::FieldAny, 0});
  else
    edgeList.push_back(
        {base, dst, EdgeKind::Field, (uint32_t)bucket % numBuckets});
}

void ConstraintGraph::addFieldAnyLoop(NodeIndex n) {
  assert(fieldSensitive() && "field edge in a field-insensitive graph");
  checkNode(n, "field wildcard");
  edgeList.push_back({n, n, EdgeKind::FieldAny, 0});
}

bool ConstraintGraph::removeCopy(NodeIndex src, NodeIndex dst) {
  checkNode(src, "copy removal");
  checkNode(dst, "copy removal");
  auto it = std::find_if(edgeList.begin(), edgeList.end(),
                         [&](const GraphEdge &E) {
                           return E.kind == EdgeKind::Copy && E.from == src &&
                                  E.to == dst;
                         });
  if (it == edgeList.end())
    return false;
  edgeList.erase(it);
  removals++;
  return true;
}

void ConstraintGraph::analyzeHighDegreeNodes(
    size_t threshold, size_t topN,
    std::vector<std::pair<NodeIndex, size_t>> *outTopNodes) const {
  CGRAPH_LOG("=== Analyzing node degrees ===\n");
  CGRAPH_LOG("Total edges: " << 2 * edgeList.size() << "\n");
  // Both directions of every edge: the forward edge leaves `from`, the
  // implied inverse leaves `to`. Columns a/-a/d/-d as before.
  std::unordered_map<NodeIndex, size_t> outDegree, inDegree;
  std::unordered_map<NodeIndex, size_t> byKind[4];
  for (const GraphEdge &E : edgeList) {
    outDegree[E.from]++;
    inDegree[E.to]++;
    outDegree[E.to]++;
    inDegree[E.from]++;
    if (E.kind == EdgeKind::Copy) {
      byKind[0][E.from]++;
      byKind[1][E.to]++;
    } else if (E.kind == EdgeKind::Deref) {
      byKind[2][E.from]++;
      byKind[3][E.to]++;
    }
  }
  std::vector<std::pair<NodeIndex, size_t>> high;
  for (const auto &[node, degree] : outDegree)
    if (degree > threshold)
      high.push_back({node, degree});
  std::sort(high.begin(), high.end(), [](const auto &a, const auto &b) {
    return a.second != b.second ? a.second > b.second : a.first < b.first;
  });
  CGRAPH_LOG("Found " << high.size() << " nodes with out-degree > "
                      << threshold << "\n");
  const size_t numToReport = std::min(topN, high.size());
  if (numToReport == 0)
    return;
  CGRAPH_LOG("\nTop " << numToReport << " nodes by out-degree:\n");
  CGRAPH_LOG("NodeID\tOutDegree\tInDegree\t'a'\t'-a'\t'd'\t'-d'\n");
  for (size_t i = 0; i < numToReport; ++i) {
    const NodeIndex node = high[i].first;
    CGRAPH_LOG(node << "\t" << high[i].second << "\t\t" << inDegree[node]
                    << "\t\t" << byKind[0][node] << "\t" << byKind[1][node]
                    << "\t" << byKind[2][node] << "\t" << byKind[3][node]
                    << "\n");
  }
  if (outTopNodes)
    outTopNodes->assign(high.begin(), high.begin() + numToReport);
}
