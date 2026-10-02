#include "CFLEdgeBuilder.h"

#include <cassert>
#include <fstream>

#include "Common.h"

#define EB_LOG(stmt) KA_LOG(2, "CFLEdgeBuilder: " << stmt)

void CFLEdgeBuilder::initialize(const ConstraintGraph &G,
                                const std::vector<std::string> &grammarLines) {
  graph = &G;
  grammar = std::make_unique<gracfl::Grammar>(grammarLines);
  initializeLabels();
}

void CFLEdgeBuilder::initialize(const ConstraintGraph &G,
                                const std::string &grammarFile) {
  graph = &G;
  grammar = std::make_unique<gracfl::Grammar>(grammarFile);
  initializeLabels();
}

void CFLEdgeBuilder::initializeLabels() {
  const auto &symbolMap = grammar->getSymbolToIDMap();
  auto findLabel = [&](const std::string &symbol) -> uint {
    auto it = symbolMap.find(symbol);
    if (it == symbolMap.end()) {
      errs() << "CFLEdgeBuilder: symbol '" << symbol
             << "' not found in grammar\n";
      exit(1);
    }
    return it->second;
  };
  labelAssign = findLabel("a");
  labelAssignInv = findLabel("-a");
  labelDeref = findLabel("d");
  labelDerefInv = findLabel("-d");
  labelM = findLabel("M");
  labelV = findLabel("V");

  // Field labels are present iff the grammar was built with
  // buildP2GrammarWithFields(K > 0). Buckets are contiguous from f0.
  labelField.clear();
  labelFieldInv.clear();
  if (symbolMap.count("fx")) {
    labelFieldAny = findLabel("fx");
    labelFieldAnyInv = findLabel("-fx");
    for (unsigned i = 0;; i++) {
      std::string fi = "f" + std::to_string(i);
      auto it = symbolMap.find(fi);
      if (it == symbolMap.end())
        break;
      labelField.push_back(it->second);
      labelFieldInv.push_back(findLabel("-" + fi));
    }
  }
  if (labelField.size() != graph->numFieldBuckets()) {
    errs() << "CFLEdgeBuilder: the grammar has " << labelField.size()
           << " field labels but the constraint graph has "
           << graph->numFieldBuckets() << " field buckets\n";
    exit(1);
  }
  EB_LOG("CFL Labels initialized: a=" << labelAssign << ", -a="
         << labelAssignInv << ", d=" << labelDeref << ", -d="
         << labelDerefInv << ", " << labelField.size()
         << " field buckets\n");
}

void CFLEdgeBuilder::sync() const {
  if (graph->removalCount() != syncedRemovals) {
    edges.clear();
    syncedTyped = 0;
    syncedRemovals = graph->removalCount();
  }
  const auto &typed = graph->edges();
  if (syncedTyped == typed.size())
    return;
  edges.reserve(2 * typed.size());
  for (size_t i = syncedTyped; i < typed.size(); i++) {
    const GraphEdge &E = typed[i];
    uint fwd = 0, inv = 0;
    switch (E.kind) {
    case EdgeKind::Copy:
      fwd = labelAssign;
      inv = labelAssignInv;
      break;
    case EdgeKind::Deref:
      fwd = labelDeref;
      inv = labelDerefInv;
      break;
    case EdgeKind::Field:
      fwd = labelField[E.bucket];
      inv = labelFieldInv[E.bucket];
      break;
    case EdgeKind::FieldAny:
      fwd = labelFieldAny;
      inv = labelFieldAnyInv;
      break;
    }
    edges.emplace_back(E.from, E.to, fwd);
    edges.emplace_back(E.to, E.from, inv);
  }
  syncedTyped = typed.size();
}

void CFLEdgeBuilder::outputEdgesToFile(const std::string &filename) const {
  std::ofstream outFile(filename);
  if (!outFile) {
    errs() << "CFLEdgeBuilder: cannot open output file " << filename << "\n";
    exit(1);
  }
  const auto &idToSymbolMap = grammar->getIDToSymbolMap();
  for (const auto &edge : getEdges()) {
    auto itr = idToSymbolMap.find(edge.label);
    assert(itr != idToSymbolMap.end() && "edge label not in grammar");
    outFile << edge.from << " " << edge.to << " " << itr->second << "\n";
  }
  EB_LOG("Output " << edges.size() << " edges to " << filename << "\n");
}
