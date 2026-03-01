#ifndef KANALYZER_COMPRESSEDGRAPH_H
#define KANALYZER_COMPRESSEDGRAPH_H

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include <llvm/ADT/StringRef.h>

#include "gracfl/include/utils/Edges.hpp"

struct BoundarySymbol {
  std::string symbol; // e.g. "func:malloc", "arg:foo:2", "ret:bar", "glob:errno"

  bool operator==(const BoundarySymbol &Other) const {
    return symbol == Other.symbol;
  }
};

struct BoundarySymbolHash {
  size_t operator()(const BoundarySymbol &S) const {
    return std::hash<std::string>()(S.symbol);
  }
};

struct CompressedGraphData {
  static constexpr uint32_t kVersion = 1;

  uint32_t numNodes = 0;
  std::vector<gracfl::Edge> edges;

  // boundary symbol -> compressed node ID
  std::unordered_map<BoundarySymbol, uint32_t, BoundarySymbolHash> symbolTable;

  // compressed node ID -> function names it contains
  std::unordered_map<uint32_t, std::vector<std::string>> funcNodes;

  std::string metadataJson;
};

bool saveCompressedGraph(llvm::StringRef Path, const CompressedGraphData &Data,
                         std::string *ErrMsg = nullptr);

bool loadCompressedGraph(llvm::StringRef Path, CompressedGraphData &Data,
                         std::string *ErrMsg = nullptr);

#endif
