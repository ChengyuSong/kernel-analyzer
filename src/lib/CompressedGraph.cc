#include "CompressedGraph.h"

#include <algorithm>
#include <array>
#include <limits>
#include <system_error>

#include <llvm/Support/FileSystem.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;

namespace {

constexpr std::array<char, 8> kMagic = {'K', 'A', 'C', 'F', 'L', 'C', 'G', '1'};

static void writeU32LE(raw_ostream &OS, uint32_t V) {
  for (unsigned I = 0; I < 4; I++)
    OS << static_cast<char>((V >> (I * 8)) & 0xffu);
}

static void writeVarUInt(raw_ostream &OS, uint64_t V) {
  while (V >= 0x80u) {
    OS << static_cast<char>((V & 0x7fu) | 0x80u);
    V >>= 7;
  }
  OS << static_cast<char>(V);
}

static bool readU32LE(const uint8_t *&P, const uint8_t *End, uint32_t &Out) {
  if (static_cast<size_t>(End - P) < 4)
    return false;
  Out = static_cast<uint32_t>(P[0]) |
        (static_cast<uint32_t>(P[1]) << 8) |
        (static_cast<uint32_t>(P[2]) << 16) |
        (static_cast<uint32_t>(P[3]) << 24);
  P += 4;
  return true;
}

static bool readVarUInt(const uint8_t *&P, const uint8_t *End, uint64_t &Out) {
  Out = 0;
  unsigned Shift = 0;
  while (P < End) {
    uint8_t Byte = *P++;
    Out |= (static_cast<uint64_t>(Byte & 0x7fu) << Shift);
    if ((Byte & 0x80u) == 0)
      return true;
    Shift += 7;
    if (Shift >= 64)
      return false;
  }
  return false;
}

static bool setError(std::string *ErrMsg, const Twine &Msg) {
  if (ErrMsg)
    *ErrMsg = Msg.str();
  return false;
}

} // namespace

bool saveCompressedGraph(StringRef Path, const CompressedGraphData &Data,
                         std::string *ErrMsg) {
  std::error_code EC;
  raw_fd_ostream OS(Path, EC, sys::fs::OF_None);
  if (EC)
    return setError(ErrMsg, Twine("failed to open output file: ") + EC.message());

  // Magic
  OS.write(kMagic.data(), kMagic.size());

  // Header
  writeU32LE(OS, CompressedGraphData::kVersion);
  writeU32LE(OS, Data.numNodes);
  writeU32LE(OS, static_cast<uint32_t>(Data.edges.size()));
  writeU32LE(OS, static_cast<uint32_t>(Data.symbolTable.size()));
  writeU32LE(OS, static_cast<uint32_t>(Data.funcNodes.size()));
  writeVarUInt(OS, static_cast<uint64_t>(Data.metadataJson.size()));
  OS.write(Data.metadataJson.data(), Data.metadataJson.size());

  // Edges section
  for (const auto &E : Data.edges) {
    writeVarUInt(OS, E.from);
    writeVarUInt(OS, E.to);
    writeVarUInt(OS, E.label);
  }

  // Symbol table section
  for (const auto &[sym, nodeId] : Data.symbolTable) {
    writeVarUInt(OS, nodeId);
    writeVarUInt(OS, static_cast<uint64_t>(sym.symbol.size()));
    OS.write(sym.symbol.data(), sym.symbol.size());
  }

  // Func nodes section
  for (const auto &[nodeId, funcNames] : Data.funcNodes) {
    writeVarUInt(OS, nodeId);
    writeVarUInt(OS, static_cast<uint64_t>(funcNames.size()));
    for (const auto &name : funcNames) {
      writeVarUInt(OS, static_cast<uint64_t>(name.size()));
      OS.write(name.data(), name.size());
    }
  }

  OS.flush();
  if (OS.has_error())
    return setError(ErrMsg, "I/O error while writing compressed graph");
  return true;
}

bool loadCompressedGraph(StringRef Path, CompressedGraphData &Data,
                         std::string *ErrMsg) {
  auto BufOrErr = MemoryBuffer::getFile(Path, /*IsText=*/false,
                                        /*RequiresNullTerminator=*/false);
  if (!BufOrErr)
    return setError(ErrMsg, Twine("failed to read compressed graph: ") +
                             std::error_code(BufOrErr.getError()).message());

  StringRef B = BufOrErr.get()->getBuffer();
  const uint8_t *P = reinterpret_cast<const uint8_t *>(B.data());
  const uint8_t *End = P + B.size();

  // Magic
  if (static_cast<size_t>(End - P) < kMagic.size())
    return setError(ErrMsg, "compressed graph file is too small");
  if (!std::equal(kMagic.begin(), kMagic.end(), reinterpret_cast<const char *>(P)))
    return setError(ErrMsg, "compressed graph magic mismatch");
  P += kMagic.size();

  // Header
  uint32_t version = 0, numNodes = 0, edgeCount = 0, symbolCount = 0, funcNodeCount = 0;
  if (!readU32LE(P, End, version) ||
      !readU32LE(P, End, numNodes) ||
      !readU32LE(P, End, edgeCount) ||
      !readU32LE(P, End, symbolCount) ||
      !readU32LE(P, End, funcNodeCount))
    return setError(ErrMsg, "compressed graph header is truncated");
  if (version != CompressedGraphData::kVersion)
    return setError(ErrMsg, "unsupported compressed graph version");

  uint64_t metadataSize = 0;
  if (!readVarUInt(P, End, metadataSize))
    return setError(ErrMsg, "failed to decode metadata size");
  if (metadataSize > static_cast<uint64_t>(End - P))
    return setError(ErrMsg, "metadata size exceeds file bounds");

  Data = CompressedGraphData();
  Data.numNodes = numNodes;
  Data.metadataJson.assign(reinterpret_cast<const char *>(P),
                           static_cast<size_t>(metadataSize));
  P += metadataSize;

  // Edges
  Data.edges.resize(edgeCount);
  for (uint32_t i = 0; i < edgeCount; i++) {
    uint64_t from = 0, to = 0, label = 0;
    if (!readVarUInt(P, End, from) ||
        !readVarUInt(P, End, to) ||
        !readVarUInt(P, End, label))
      return setError(ErrMsg, "failed to decode edge");
    Data.edges[i] = gracfl::Edge(static_cast<uint>(from),
                                 static_cast<uint>(to),
                                 static_cast<uint>(label));
  }

  // Symbol table
  Data.symbolTable.reserve(symbolCount);
  for (uint32_t i = 0; i < symbolCount; i++) {
    uint64_t nodeId = 0, nameLen = 0;
    if (!readVarUInt(P, End, nodeId))
      return setError(ErrMsg, "failed to decode symbol node id");
    if (!readVarUInt(P, End, nameLen))
      return setError(ErrMsg, "failed to decode symbol name length");
    if (nameLen > static_cast<uint64_t>(End - P))
      return setError(ErrMsg, "symbol name exceeds file bounds");

    BoundarySymbol sym;
    sym.symbol.assign(reinterpret_cast<const char *>(P),
                      static_cast<size_t>(nameLen));
    P += nameLen;
    auto it = Data.symbolTable.find(sym);
    if (it != Data.symbolTable.end()) {
      return setError(ErrMsg, Twine("duplicate boundary symbol in compressed graph: ") +
                               sym.symbol);
    }
    Data.symbolTable[sym] = static_cast<uint32_t>(nodeId);
  }

  // Func nodes
  Data.funcNodes.reserve(funcNodeCount);
  for (uint32_t i = 0; i < funcNodeCount; i++) {
    uint64_t nodeId = 0, count = 0;
    if (!readVarUInt(P, End, nodeId))
      return setError(ErrMsg, "failed to decode func node id");
    if (!readVarUInt(P, End, count))
      return setError(ErrMsg, "failed to decode func name count");

    auto &names = Data.funcNodes[static_cast<uint32_t>(nodeId)];
    names.reserve(static_cast<size_t>(count));
    for (uint64_t j = 0; j < count; j++) {
      uint64_t nameLen = 0;
      if (!readVarUInt(P, End, nameLen))
        return setError(ErrMsg, "failed to decode func name length");
      if (nameLen > static_cast<uint64_t>(End - P))
        return setError(ErrMsg, "func name exceeds file bounds");
      names.emplace_back(reinterpret_cast<const char *>(P),
                         static_cast<size_t>(nameLen));
      P += nameLen;
    }
  }

  if (P != End)
    return setError(ErrMsg, "trailing bytes found in compressed graph");
  return true;
}
