#pragma once
// Witness-taint propagation (rendezvous-keying design doc, v2
// consolidation): demand-driven population dataflow over IR with a
// strict lattice {Fn, Obj(root,off,stride)} + poison. Clamps an
// indirect callsite iff its fptr evaluates poison-free to a pure fn
// set. Subsumes the regfield walk's witness classes with flow
// composition (two-hop populations, stack copies) and needs no
// GEP-syntax site attribution.
#include "Global.h"

void runWitnessTaint(GlobalContext *Ctx);
