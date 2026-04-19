#ifndef _IR_SIDECAR_H
#define _IR_SIDECAR_H

#include <llvm/ADT/StringRef.h>

#include "Global.h"

// Per-function IR fact exporter. Walks each loaded module's functions and
// emits one <bc>.facts.json sidecar per module into the given directory.
// See todo-kamain-ir-sidecar.md for the schema.
class IRSidecarExporter {
public:
  explicit IRSidecarExporter(GlobalContext *Ctx_) : Ctx(Ctx_) {}

  // Write one <bc-basename>.facts.json per loaded module under Dir.
  void dump(llvm::StringRef Dir);

private:
  GlobalContext *Ctx;
};

#endif
