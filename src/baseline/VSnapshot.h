#ifndef KANALYZER_VSNAPSHOT_H
#define KANALYZER_VSNAPSHOT_H

#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include <llvm/ADT/StringRef.h>

struct VSnapshotNamedEntry {
  uint32_t node = 0;
  uint8_t kind = 0;
  std::string name;
};

struct VSnapshotData {
  static constexpr uint32_t kVersion = 1;

  uint32_t labelV = 0;
  uint32_t flags = 0;
  std::string metadataJson;

  // Maps original node id -> dense representative id [0, repToNode.size()).
  std::vector<uint32_t> nodeToRep;
  // Maps dense representative id -> original node id.
  std::vector<uint32_t> repToNode;
  // V-relation in representative space, sorted ascending per row.
  std::vector<std::vector<uint32_t>> repRows;
  std::vector<VSnapshotNamedEntry> namedEntries;
};

bool saveVSnapshot(llvm::StringRef Path,
                   const VSnapshotData &Data,
                   std::string *ErrMsg = nullptr);

using VSnapshotRowProvider = std::function<void(uint32_t rep, std::vector<uint32_t> &rowOut)>;

bool saveVSnapshotWithRowProvider(llvm::StringRef Path,
                                  const VSnapshotData &Data,
                                  const VSnapshotRowProvider &RowProvider,
                                  std::string *ErrMsg = nullptr);

bool loadVSnapshot(llvm::StringRef Path,
                   VSnapshotData &Data,
                   std::string *ErrMsg = nullptr);

#endif
