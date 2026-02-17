#include "VSnapshot.h"

#include <algorithm>
#include <array>
#include <limits>
#include <system_error>
#include <utility>

#include <llvm/Support/FileSystem.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;

namespace {

constexpr std::array<char, 8> kMagic = {'K', 'A', 'V', 'S', 'N', 'A', 'P', '1'};

static void writeU32LE(raw_ostream &OS, uint32_t V) {
  for (unsigned I = 0; I < 4; I++)
    OS << static_cast<char>((V >> (I * 8)) & 0xffu);
}

static void writeU64LE(raw_ostream &OS, uint64_t V) {
  for (unsigned I = 0; I < 8; I++)
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

static bool readU64LE(const uint8_t *&P, const uint8_t *End, uint64_t &Out) {
  if (static_cast<size_t>(End - P) < 8)
    return false;
  Out = static_cast<uint64_t>(P[0]) |
        (static_cast<uint64_t>(P[1]) << 8) |
        (static_cast<uint64_t>(P[2]) << 16) |
        (static_cast<uint64_t>(P[3]) << 24) |
        (static_cast<uint64_t>(P[4]) << 32) |
        (static_cast<uint64_t>(P[5]) << 40) |
        (static_cast<uint64_t>(P[6]) << 48) |
        (static_cast<uint64_t>(P[7]) << 56);
  P += 8;
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

bool saveVSnapshot(StringRef Path,
                   const VSnapshotData &Data,
                   std::string *ErrMsg) {
  if (Data.repRows.size() != Data.repToNode.size())
    return setError(ErrMsg, "repRows size mismatch with repToNode size");
  return saveVSnapshotWithRowProvider(
      Path,
      Data,
      [&Data](uint32_t rep, std::vector<uint32_t> &rowOut) { rowOut = Data.repRows.at(rep); },
      ErrMsg);
}

bool saveVSnapshotWithRowProvider(StringRef Path,
                                  const VSnapshotData &Data,
                                  const VSnapshotRowProvider &RowProvider,
                                  std::string *ErrMsg) {
  if (Data.nodeToRep.empty())
    return setError(ErrMsg, "nodeToRep must not be empty");
  if (!RowProvider)
    return setError(ErrMsg, "row provider is required");

  const uint32_t repCount = static_cast<uint32_t>(Data.repToNode.size());
  for (uint32_t rep : Data.nodeToRep) {
    if (rep >= repCount)
      return setError(ErrMsg, "nodeToRep contains out-of-range representative id");
  }

  std::error_code EC;
  raw_fd_ostream OS(Path, EC, sys::fs::OF_None);
  if (EC)
    return setError(ErrMsg, Twine("failed to open output file: ") + EC.message());

  const uint32_t flags = Data.flags | (Data.namedEntries.empty() ? 0u : 0x1u);
  OS.write(kMagic.data(), kMagic.size());
  writeU32LE(OS, VSnapshotData::kVersion);
  writeU32LE(OS, flags);
  writeU32LE(OS, Data.labelV);
  writeU32LE(OS, 0u); // reserved
  writeU64LE(OS, static_cast<uint64_t>(Data.nodeToRep.size()));
  writeU64LE(OS, static_cast<uint64_t>(Data.repToNode.size()));
  writeU64LE(OS, static_cast<uint64_t>(Data.metadataJson.size()));
  OS.write(Data.metadataJson.data(), Data.metadataJson.size());

  for (uint32_t rep : Data.nodeToRep)
    writeVarUInt(OS, rep);
  for (uint32_t node : Data.repToNode)
    writeVarUInt(OS, node);

  std::vector<uint32_t> row;
  for (uint32_t rep = 0; rep < repCount; rep++) {
    RowProvider(rep, row);
    std::sort(row.begin(), row.end());
    row.erase(std::unique(row.begin(), row.end()), row.end());

    writeVarUInt(OS, static_cast<uint64_t>(row.size()));
    uint64_t prev = 0;
    bool first = true;
    for (uint32_t dst : row) {
      if (dst >= repCount)
        return setError(ErrMsg, "rep row contains out-of-range representative id");
      uint64_t delta = first ? static_cast<uint64_t>(dst)
                             : (static_cast<uint64_t>(dst) - prev);
      writeVarUInt(OS, delta);
      prev = dst;
      first = false;
    }
  }

  writeVarUInt(OS, static_cast<uint64_t>(Data.namedEntries.size()));
  for (const auto &E : Data.namedEntries) {
    writeVarUInt(OS, E.node);
    OS << static_cast<char>(E.kind);
    writeVarUInt(OS, static_cast<uint64_t>(E.name.size()));
    OS.write(E.name.data(), E.name.size());
  }

  OS.flush();
  if (OS.has_error())
    return setError(ErrMsg, "I/O error while writing snapshot");
  return true;
}

bool loadVSnapshot(StringRef Path,
                   VSnapshotData &Data,
                   std::string *ErrMsg) {
  auto BufOrErr = MemoryBuffer::getFile(Path, /*IsText=*/false, /*RequiresNullTerminator=*/false);
  if (!BufOrErr)
    return setError(ErrMsg, Twine("failed to read snapshot: ") +
                             std::error_code(BufOrErr.getError()).message());

  StringRef B = BufOrErr.get()->getBuffer();
  const uint8_t *P = reinterpret_cast<const uint8_t *>(B.data());
  const uint8_t *End = P + B.size();

  if (static_cast<size_t>(End - P) < kMagic.size())
    return setError(ErrMsg, "snapshot is too small");
  if (!std::equal(kMagic.begin(), kMagic.end(), reinterpret_cast<const char *>(P)))
    return setError(ErrMsg, "snapshot magic mismatch");
  P += kMagic.size();

  uint32_t version = 0, flags = 0, labelV = 0, reserved = 0;
  uint64_t nodeCount = 0, repCount = 0, metadataSize = 0;
  if (!readU32LE(P, End, version) ||
      !readU32LE(P, End, flags) ||
      !readU32LE(P, End, labelV) ||
      !readU32LE(P, End, reserved) ||
      !readU64LE(P, End, nodeCount) ||
      !readU64LE(P, End, repCount) ||
      !readU64LE(P, End, metadataSize))
    return setError(ErrMsg, "snapshot header is truncated");
  if (version != VSnapshotData::kVersion)
    return setError(ErrMsg, "unsupported snapshot version");
  if (metadataSize > static_cast<uint64_t>(End - P))
    return setError(ErrMsg, "metadata size exceeds file bounds");

  Data = VSnapshotData();
  Data.flags = flags;
  Data.labelV = labelV;
  Data.metadataJson.assign(reinterpret_cast<const char *>(P), static_cast<size_t>(metadataSize));
  P += metadataSize;

  if (nodeCount > static_cast<uint64_t>(std::numeric_limits<size_t>::max()) ||
      repCount > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
    return setError(ErrMsg, "snapshot is too large for this build");

  Data.nodeToRep.resize(static_cast<size_t>(nodeCount));
  Data.repToNode.resize(static_cast<size_t>(repCount));
  Data.repRows.resize(static_cast<size_t>(repCount));

  uint64_t tmp = 0;
  for (size_t i = 0; i < Data.nodeToRep.size(); i++) {
    if (!readVarUInt(P, End, tmp))
      return setError(ErrMsg, "failed to decode nodeToRep");
    if (tmp >= repCount)
      return setError(ErrMsg, "nodeToRep contains out-of-range representative id");
    Data.nodeToRep[i] = static_cast<uint32_t>(tmp);
  }

  for (size_t i = 0; i < Data.repToNode.size(); i++) {
    if (!readVarUInt(P, End, tmp))
      return setError(ErrMsg, "failed to decode repToNode");
    if (tmp >= nodeCount)
      return setError(ErrMsg, "repToNode contains out-of-range node id");
    Data.repToNode[i] = static_cast<uint32_t>(tmp);
  }

  for (size_t r = 0; r < Data.repRows.size(); r++) {
    uint64_t degree = 0;
    if (!readVarUInt(P, End, degree))
      return setError(ErrMsg, "failed to decode row degree");
    if (degree > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
      return setError(ErrMsg, "row degree is too large");

    auto &row = Data.repRows[r];
    row.clear();
    row.reserve(static_cast<size_t>(degree));

    uint64_t prev = 0;
    for (uint64_t i = 0; i < degree; i++) {
      uint64_t delta = 0;
      if (!readVarUInt(P, End, delta))
        return setError(ErrMsg, "failed to decode row destination");
      uint64_t cur = (i == 0) ? delta : (prev + delta);
      if (cur >= repCount)
        return setError(ErrMsg, "row destination out of range");
      row.push_back(static_cast<uint32_t>(cur));
      prev = cur;
    }
  }

  if (P == End) {
    Data.namedEntries.clear();
    return true;
  }

  uint64_t namedCount = 0;
  if (!readVarUInt(P, End, namedCount))
    return setError(ErrMsg, "failed to decode named entry count");
  if (namedCount > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
    return setError(ErrMsg, "named entry count is too large");

  Data.namedEntries.clear();
  Data.namedEntries.reserve(static_cast<size_t>(namedCount));
  for (uint64_t i = 0; i < namedCount; i++) {
    uint64_t node = 0, len = 0;
    if (!readVarUInt(P, End, node))
      return setError(ErrMsg, "failed to decode named entry node");
    if (P >= End)
      return setError(ErrMsg, "failed to decode named entry kind");
    uint8_t kind = *P++;
    if (!readVarUInt(P, End, len))
      return setError(ErrMsg, "failed to decode named entry name length");
    if (len > static_cast<uint64_t>(End - P))
      return setError(ErrMsg, "named entry exceeds file bounds");

    VSnapshotNamedEntry E;
    E.node = static_cast<uint32_t>(node);
    E.kind = kind;
    E.name.assign(reinterpret_cast<const char *>(P), static_cast<size_t>(len));
    P += len;
    Data.namedEntries.push_back(std::move(E));
  }

  if (P != End)
    return setError(ErrMsg, "trailing bytes found in snapshot");
  return true;
}
