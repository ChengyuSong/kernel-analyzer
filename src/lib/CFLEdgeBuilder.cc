#include "Common.h"
#include "CFLEdgeBuilder.h"

#include <iostream>
#include <stdexcept>
#include <algorithm>

#define EB_LOG(stmt) KA_LOG(2, "CFLEdgeBuilder: " << stmt)

bool CFLEdgeBuilder::initializeGrammar(const std::string& grammarFilePath) {
  try {
    grammar = std::make_unique<gracfl::Grammar>(grammarFilePath);
    initializeLabels();
    return true;
  } catch (const std::exception& e) {
    WARNING("Error initializing grammar: " << e.what() << "\n");
    return false;
  }
}

bool CFLEdgeBuilder::initializeGrammar(const std::vector<std::string>& grammarLines) {
  try {
    grammar = std::make_unique<gracfl::Grammar>(grammarLines);
    initializeLabels();
    return true;
  } catch (const std::exception& e) {
    WARNING("Error initializing grammar: " << e.what() << "\n");
    return false;
  }
}

void CFLEdgeBuilder::initializeLabels() {
  if (!grammar) {
    throw std::runtime_error("Grammar not initialized");
  }

  const auto& symbolMap = grammar->getSymbolToIDMap();

  // Lookup label IDs for CFL-reachability symbols
  auto findLabel = [&symbolMap](const std::string& symbol) -> uint {
    auto it = symbolMap.find(symbol);
    if (it == symbolMap.end()) {
      throw std::runtime_error("Symbol '" + symbol + "' not found in grammar");
    }
    return it->second;
  };
    
  try {
    labelAssign = findLabel("a");
    labelAssignInv = findLabel("-a");
    labelDeref = findLabel("d");
    labelDerefInv = findLabel("-d");
    labelM = findLabel("M");
    labelV = findLabel("V");
    labelsInitialized = true;

    EB_LOG("CFL Labels initialized: a=" << labelAssign 
           << ", -a=" << labelAssignInv 
           << ", d=" << labelDeref 
           << ", -d=" << labelDerefInv << "\n");
  } catch (const std::exception& e) {
    throw std::runtime_error("Failed to find required CFL symbols in grammar: " + std::string(e.what()));
  }
}

void CFLEdgeBuilder::addAssignmentEdges(NodeIndex src, NodeIndex dst) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex) {
    throw std::runtime_error("Invalid node index for assignment edge");
  }

  static size_t assignmentCount = 0;
  assignmentCount += 2; // Two edges per assignment

  if (assignmentCount % 100000 == 0) {
    EB_LOG("Assignment edge count: " << assignmentCount << " (total edges: " << edges.size() + 2 << ")\n");
  }

  // Add assignment edge: src -> dst with label 'a'
  edges.emplace_back(src, dst, labelAssign);

  // Add inverse assignment edge: dst -> src with label '-a'
  edges.emplace_back(dst, src, labelAssignInv);
}

void CFLEdgeBuilder::addDereferenceEdges(NodeIndex src, NodeIndex dst) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex) {
    throw std::runtime_error("Invalid node index for dereference edge");
  }

  static size_t dereferenceCount = 0;
  dereferenceCount += 2; // Two edges per dereference

  if (dereferenceCount % 100000 == 0) {
    EB_LOG("Dereference edge count: " << dereferenceCount << " (total edges: " << edges.size() + 2 << ")\n");
  }

  // Add dereference edge: src -> dst with label 'd'
  edges.emplace_back(src, dst, labelDeref);

  // Add inverse dereference edge: dst -> src with label '-d'
  edges.emplace_back(dst, src, labelDerefInv);
}

bool CFLEdgeBuilder::removeAssignmentEdges(NodeIndex src, NodeIndex dst) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex) {
    throw std::runtime_error("Invalid node index for assignment edge removal");
  }

  bool removed = false;

  // Remove assignment edge: src -> dst with label 'a'
  auto it = std::find_if(edges.begin(), edges.end(),
    [src, dst, this](const gracfl::Edge& edge) {
      return edge.from == src && edge.to == dst && edge.label == labelAssign;
    });
  if (it != edges.end()) {
    edges.erase(it);
    removed = true;
  }

  // Remove inverse assignment edge: dst -> src with label '-a'
  it = std::find_if(edges.begin(), edges.end(),
    [src, dst, this](const gracfl::Edge& edge) {
      return edge.from == dst && edge.to == src && edge.label == labelAssignInv;
    });
  if (it != edges.end()) {
    edges.erase(it);
    removed = true;
  }

  return removed;
}

bool CFLEdgeBuilder::removeDereferenceEdges(NodeIndex src, NodeIndex dst) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex) {
    throw std::runtime_error("Invalid node index for dereference edge removal");
  }

  bool removed = false;

  // Remove dereference edge: src -> dst with label 'd'
  auto it = std::find_if(edges.begin(), edges.end(),
    [src, dst, this](const gracfl::Edge& edge) {
      return edge.from == src && edge.to == dst && edge.label == labelDeref;
    });
  if (it != edges.end()) {
    edges.erase(it);
    removed = true;
  }

  // Remove inverse dereference edge: dst -> src with label '-d'
  it = std::find_if(edges.begin(), edges.end(),
    [src, dst, this](const gracfl::Edge& edge) {
      return edge.from == dst && edge.to == src && edge.label == labelDerefInv;
    });
  if (it != edges.end()) {
    edges.erase(it);
    removed = true;
  }

  return removed;
}

bool CFLEdgeBuilder::removeEdge(NodeIndex src, NodeIndex dst, uint label) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  if (src == AndersNodeFactory::InvalidIndex || dst == AndersNodeFactory::InvalidIndex) {
    throw std::runtime_error("Invalid node index for edge removal");
  }

  auto it = std::find_if(edges.begin(), edges.end(),
    [src, dst, label](const gracfl::Edge& edge) {
      return edge.from == src && edge.to == dst && edge.label == label;
    });

  if (it != edges.end()) {
    edges.erase(it);
    return true;
  }

  return false;
}

size_t CFLEdgeBuilder::removeEdgesInvolvingNode(NodeIndex node) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  if (node == AndersNodeFactory::InvalidIndex) {
    throw std::runtime_error("Invalid node index for edge removal");
  }

  size_t initialSize = edges.size();

  // Remove all edges where node is either source or destination
  edges.erase(
    std::remove_if(edges.begin(), edges.end(),
      [node](const gracfl::Edge& edge) {
        return edge.from == node || edge.to == node;
      }),
    edges.end()
  );

  return initialSize - edges.size();
}

void CFLEdgeBuilder::outputEdgesToFile(const std::string& filename) const {
  if (!labelsInitialized) {
    throw std::runtime_error("Grammar not initialized - call initializeGrammar first");
  }

  std::ofstream outFile(filename);
  if (!outFile) {
    throw std::runtime_error("Cannot open output file: " + filename);
  }

  const auto& idToSymbolMap = grammar->getIDToSymbolMap();

  for (const auto& edge : edges) {
    auto itr = idToSymbolMap.find(edge.label);
    if (itr == idToSymbolMap.end()) {
      throw std::runtime_error("Unknown label ID: " + std::to_string(edge.label));
    }
    outFile << edge.from << " " << edge.to << " " << itr->second << "\n";
  }

  EB_LOG("Output " << edges.size() << " edges to " << filename << "\n");
}

void CFLEdgeBuilder::printEdges() const {
  if (edges.empty()) {
    WARNING("No grammar loaded for symbol lookup\n");
    return;
  }

  const auto& idToSymbolMap = grammar->getIDToSymbolMap();

  std::cout << "CFL Edges (" << edges.size() << " total):" << std::endl;
  for (const auto& edge : edges) {
    auto itr = idToSymbolMap.find(edge.label);
    if (itr == idToSymbolMap.end()) {
      WARNING("Unknown label ID: " << edge.label << "\n");
      continue;
    }

    llvm::outs() << edge.from;
    llvm::outs() << " -> " << edge.to;
    llvm::outs() << " [" << itr->second << ":" << edge.label << "]\n";
  }
}

size_t CFLEdgeBuilder::detectAndBreakCycles(size_t maxSCCSize) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  EB_LOG("Starting cycle detection with maxSCCSize=" << maxSCCSize << "\n");
  size_t initialEdgeCount = edges.size();

  // Count unique nodes
  std::unordered_set<NodeIndex> allNodes;
  for (const auto& edge : edges) {
    allNodes.insert(edge.from);
    allNodes.insert(edge.to);
  }
  EB_LOG("Total unique nodes in constraint graph: " << allNodes.size() << "\n");
  EB_LOG("Total edges: " << edges.size() << "\n");
  EB_LOG("Average edges per node: " << (allNodes.empty() ? 0 : edges.size() / allNodes.size()) << "\n");

  // Analyze edge distribution first
  std::unordered_map<uint, size_t> labelCounts;
  for (const auto& edge : edges) {
    labelCounts[edge.label]++;
  }

  const auto& idToSymbolMap = grammar->getIDToSymbolMap();
  EB_LOG("Edge distribution by label:\n");
  for (const auto& [label, count] : labelCounts) {
    auto it = idToSymbolMap.find(label);
    std::string labelName = (it != idToSymbolMap.end()) ? it->second : "unknown";
    EB_LOG("  " << labelName << " (" << label << "): " << count << " edges\n");
  }

  // Find strongly connected components
  std::vector<std::vector<NodeIndex>> sccs;
  tarjanSCC(sccs);

  // Analyze SCC size distribution
  std::unordered_map<size_t, size_t> sccSizeDistribution;
  size_t maxSCCFound = 0;
  for (const auto& scc : sccs) {
    sccSizeDistribution[scc.size()]++;
    maxSCCFound = std::max(maxSCCFound, scc.size());
  }

  EB_LOG("SCC size distribution:\n");
  for (const auto& [size, count] : sccSizeDistribution) {
    EB_LOG("  Size " << size << ": " << count << " SCCs\n");
  }
  EB_LOG("Largest SCC size: " << maxSCCFound << "\n");

  size_t edgesRemoved = 0;
  size_t largeSCCs = 0;

  for (const auto& scc : sccs) {
    if (scc.size() > maxSCCSize) {
      largeSCCs++;
      EB_LOG("Breaking large SCC of size " << scc.size() << "\n");

      // Strategy: Remove assignment edges within the SCC to break cycles
      // Keep dereference edges as they are essential for soundness
      std::unordered_set<NodeIndex> sccNodes(scc.begin(), scc.end());

      auto originalEdges = edges;
      edges.clear();

      for (const auto& edge : originalEdges) {
        bool inSCC = sccNodes.count(edge.from) && sccNodes.count(edge.to);
        bool isAssignmentEdge = (edge.label == labelAssign || edge.label == labelAssignInv);

        // Remove assignment edges within large SCCs
        if (inSCC && isAssignmentEdge) {
          edgesRemoved++;
          EB_LOG("Removing assignment edge: " << edge.from << " -> " << edge.to << "\n");
        } else {
          edges.push_back(edge);
        }
      }
    }
  }

  EB_LOG("Cycle breaking complete: removed " << edgesRemoved << " edges from "
         << largeSCCs << " large SCCs (original: " << initialEdgeCount
         << ", final: " << edges.size() << ")\n");

  return edgesRemoved;
}

void CFLEdgeBuilder::tarjanSCC(std::vector<std::vector<NodeIndex>>& sccs) {
  // Build adjacency list from edges
  std::unordered_set<NodeIndex> allNodes;
  for (const auto& edge : edges) {
    allNodes.insert(edge.from);
    allNodes.insert(edge.to);
  }

  std::vector<NodeIndex> nodeList(allNodes.begin(), allNodes.end());
  std::sort(nodeList.begin(), nodeList.end());

  // Create node index mapping
  std::unordered_map<NodeIndex, size_t> nodeToIndex;
  for (size_t i = 0; i < nodeList.size(); ++i) {
    nodeToIndex[nodeList[i]] = i;
  }

  size_t numNodes = nodeList.size();
  std::vector<std::vector<NodeIndex>> adjList(numNodes);

  // Build adjacency list
  for (const auto& edge : edges) {
    size_t fromIdx = nodeToIndex[edge.from];
    size_t toIdx = nodeToIndex[edge.to];
    adjList[fromIdx].push_back(nodeList[toIdx]);
  }

  // Tarjan's algorithm data structures
  std::vector<int> disc(numNodes, -1);
  std::vector<int> low(numNodes, -1);
  std::vector<bool> onStack(numNodes, false);
  std::stack<NodeIndex> st;
  int time = 0;

  // Run Tarjan's DFS for each unvisited node
  for (size_t i = 0; i < numNodes; ++i) {
    if (disc[i] == -1) {
      tarjanDFS(nodeList[i], adjList, disc, low, onStack, st, sccs, time);
    }
  }

  EB_LOG("Found " << sccs.size() << " SCCs\n");
}

void CFLEdgeBuilder::tarjanDFS(NodeIndex node, std::vector<std::vector<NodeIndex>>& adjList,
                               std::vector<int>& disc, std::vector<int>& low, std::vector<bool>& onStack,
                               std::stack<NodeIndex>& st, std::vector<std::vector<NodeIndex>>& sccs, int& time) {
  // This is a simplified version - we need to map nodes back to indices
  // For now, just create trivial SCCs to test the integration
  std::vector<NodeIndex> singletonSCC = {node};
  sccs.push_back(singletonSCC);
}

size_t CFLEdgeBuilder::aggressiveEdgeReduction(size_t maxEdges) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  EB_LOG("Starting aggressive edge reduction. Current: " << edges.size() << ", target: " << maxEdges << "\n");

  if (edges.size() <= maxEdges) {
    EB_LOG("Already under limit, no reduction needed\n");
    return 0;
  }

  size_t initialCount = edges.size();

  // Strategy 1: Remove assignment edges first (less critical than dereference edges)
  auto originalEdges = edges;
  edges.clear();

  size_t kept = 0;
  // First pass: keep all dereference edges
  for (const auto& edge : originalEdges) {
    bool isDerefEdge = (edge.label == labelDeref || edge.label == labelDerefInv);
    if (isDerefEdge && kept < maxEdges) {
      edges.push_back(edge);
      kept++;
    }
  }

  // Second pass: add assignment edges until we hit the limit
  for (const auto& edge : originalEdges) {
    bool isAssignEdge = (edge.label == labelAssign || edge.label == labelAssignInv);
    if (isAssignEdge && kept < maxEdges) {
      edges.push_back(edge);
      kept++;
    }
  }

  size_t removed = initialCount - edges.size();
  EB_LOG("Aggressive reduction complete: removed " << removed << " edges (kept "
         << edges.size() << ")\n");

  return removed;
}

void CFLEdgeBuilder::analyzeHighDegreeNodes(size_t threshold, size_t topN,
                                            std::vector<std::pair<NodeIndex, size_t>>* outTopNodes) {
  if (!labelsInitialized) {
    throw std::runtime_error("Labels not initialized - call initializeGrammar first");
  }

  EB_LOG("=== Analyzing node degrees ===\n");
  EB_LOG("Total edges: " << edges.size() << "\n");

  // Count out-degree and in-degree for each node
  std::unordered_map<NodeIndex, size_t> outDegree;
  std::unordered_map<NodeIndex, size_t> inDegree;
  std::unordered_map<NodeIndex, size_t> outDegreeByLabel[4]; // 0='a', 1='-a', 2='d', 3='-d'

  for (const auto& edge : edges) {
    outDegree[edge.from]++;
    inDegree[edge.to]++;

    // Track by label type
    if (edge.label == labelAssign) {
      outDegreeByLabel[0][edge.from]++;
    } else if (edge.label == labelAssignInv) {
      outDegreeByLabel[1][edge.from]++;
    } else if (edge.label == labelDeref) {
      outDegreeByLabel[2][edge.from]++;
    } else if (edge.label == labelDerefInv) {
      outDegreeByLabel[3][edge.from]++;
    }
  }

  // Find nodes exceeding threshold
  std::vector<std::pair<NodeIndex, size_t>> highDegreeNodes;
  for (const auto& [node, degree] : outDegree) {
    if (degree > threshold) {
      highDegreeNodes.push_back({node, degree});
    }
  }

  // Sort by degree (descending)
  std::sort(highDegreeNodes.begin(), highDegreeNodes.end(),
    [](const auto& a, const auto& b) { return a.second > b.second; });

  EB_LOG("Found " << highDegreeNodes.size() << " nodes with out-degree > " << threshold << "\n");

  // Report top N nodes
  size_t numToReport = std::min(topN, highDegreeNodes.size());
  if (numToReport > 0) {
    EB_LOG("\nTop " << numToReport << " nodes by out-degree:\n");
    EB_LOG("NodeID\tOutDegree\tInDegree\t'a'\t'-a'\t'd'\t'-d'\n");
    EB_LOG("------\t---------\t--------\t---\t----\t---\t----\n");

    for (size_t i = 0; i < numToReport; ++i) {
      NodeIndex node = highDegreeNodes[i].first;
      size_t outDeg = highDegreeNodes[i].second;
      size_t inDeg = inDegree[node];

      EB_LOG(node << "\t" << outDeg << "\t\t" << inDeg << "\t\t"
             << outDegreeByLabel[0][node] << "\t"
             << outDegreeByLabel[1][node] << "\t"
             << outDegreeByLabel[2][node] << "\t"
             << outDegreeByLabel[3][node] << "\n");
    }

    // Populate output vector if provided
    if (outTopNodes) {
      outTopNodes->clear();
      for (size_t i = 0; i < numToReport; ++i) {
        outTopNodes->push_back(highDegreeNodes[i]);
      }
    }
  }

  // Overall statistics
  if (!outDegree.empty()) {
    size_t maxOutDegree = 0;
    size_t maxInDegree = 0;
    size_t totalOutDegree = 0;

    for (const auto& [node, degree] : outDegree) {
      maxOutDegree = std::max(maxOutDegree, degree);
      totalOutDegree += degree;
    }
    for (const auto& [node, degree] : inDegree) {
      maxInDegree = std::max(maxInDegree, degree);
    }

    size_t numNodes = outDegree.size();
    EB_LOG("\n=== Degree Statistics ===\n");
    EB_LOG("Total nodes: " << numNodes << "\n");
    EB_LOG("Max out-degree: " << maxOutDegree << "\n");
    EB_LOG("Max in-degree: " << maxInDegree << "\n");
    EB_LOG("Average out-degree: " << (totalOutDegree / numNodes) << "\n");

    // Distribution buckets
    size_t buckets[6] = {0}; // <10, 10-100, 100-1K, 1K-10K, 10K-100K, >100K
    for (const auto& [node, degree] : outDegree) {
      if (degree < 10) buckets[0]++;
      else if (degree < 100) buckets[1]++;
      else if (degree < 1000) buckets[2]++;
      else if (degree < 10000) buckets[3]++;
      else if (degree < 100000) buckets[4]++;
      else buckets[5]++;
    }

    EB_LOG("\nOut-degree distribution:\n");
    EB_LOG("  <10:        " << buckets[0] << " nodes\n");
    EB_LOG("  10-100:     " << buckets[1] << " nodes\n");
    EB_LOG("  100-1K:     " << buckets[2] << " nodes\n");
    EB_LOG("  1K-10K:     " << buckets[3] << " nodes\n");
    EB_LOG("  10K-100K:   " << buckets[4] << " nodes\n");
    EB_LOG("  >100K:      " << buckets[5] << " nodes\n");
  }

  // Report nodes with >100K outgoing 'a' edges
  std::vector<std::pair<NodeIndex, size_t>> highAEdgeNodes;
  for (const auto& [node, count] : outDegreeByLabel[0]) {
    if (count > 100000) {
      highAEdgeNodes.push_back({node, count});
    }
  }

  if (!highAEdgeNodes.empty()) {
    std::sort(highAEdgeNodes.begin(), highAEdgeNodes.end(),
      [](const auto& a, const auto& b) { return a.second > b.second; });

    EB_LOG("\n=== Nodes with >100K outgoing 'a' edges ===\n");
    EB_LOG("Found " << highAEdgeNodes.size() << " nodes\n");
    EB_LOG("NodeID\t'a' edges\tTotal out-degree\n");
    EB_LOG("------\t---------\t----------------\n");

    for (const auto& [node, aCount] : highAEdgeNodes) {
      EB_LOG(node << "\t" << aCount << "\t\t" << outDegree[node] << "\n");
    }
  }

  EB_LOG("=== Analysis complete ===\n");
}