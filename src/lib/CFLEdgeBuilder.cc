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