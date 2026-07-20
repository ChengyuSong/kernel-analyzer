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
void runIRCensus(GlobalContext *Ctx);

#endif
