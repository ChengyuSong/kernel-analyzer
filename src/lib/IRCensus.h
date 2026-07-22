#ifndef IR_CENSUS_H
#define IR_CENSUS_H

#include "Global.h"

// --ir-census: enumerate every IR construct kind across the loaded
// modules and classify each against the edge builder's disposition
// table (handled / justified no-op / suspect / undispositioned).
// The encoder's soundness claim is "every construct that can move a
// pointer emits edges"; this pass makes that claim auditable — the
// default InstVisitor handler is a silent no-op, so an unlisted
// construct contributes nothing without a trace.
//
// jsonOut: if non-empty, the full census — dispositions, intrinsics,
// constexprs, all external callees, the classified inline-asm table,
// and the unsoundness ledger — is written there as JSON (the
// machine-readable per-corpus ledger artifact).
// printTables: emit the full per-kind CENSUS lines to stderr; the
// summary is always printed. Pass false when the census runs as a
// pre-analysis gate (--ir-census-strict without --ir-census).
// Shared with the edge builder (linker-array wiring): normalize a
// section name (strip kmod/LTO uniquification suffixes) and walk a
// module-level inline-asm blob, reporting every ".long/.quad SYM"
// entry with its target section via the callback.
std::string cflNormalizeSection(llvm::StringRef s);
void cflWalkModuleAsm(
    llvm::StringRef blob,
    llvm::function_ref<void(llvm::StringRef sec, llvm::StringRef sym)> cb);

struct IRCensusResult {
  uint64_t undispKinds = 0;
  uint64_t suspectPtrInsts = 0;
  std::vector<std::string> undispNames; // for the strict-mode report
};
IRCensusResult runIRCensus(GlobalContext *Ctx, const std::string &jsonOut,
                           bool printTables);

// Language-totality check: opcodes defined by Instruction.def that
// lack a disposition (empty = table is total over the LANGUAGE, not
// merely over observed corpora).
std::vector<std::string> opcodeTableGaps();

#endif
