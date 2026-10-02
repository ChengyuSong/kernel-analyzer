#ifndef KA_DRIVER_H
#define KA_DRIVER_H

// Driver pieces shared by KAMain and KABaseline (src/lib/Driver.cc).

#include <llvm/ADT/ArrayRef.h>

#include "Global.h"

extern GlobalContext GlobalCtx;

// Process setup: log clock anchor, stack size, stack traces on signal.
void kaStartProcess(int argc, char **argv);

// A removed option and what to use instead. Passing it is an error
// (never a silent no-op), checked before option parsing.
struct RemovedFlag {
  const char *name;
  const char *replacement;
};
void kaRefuseRemovedFlags(int argc, char **argv,
                          llvm::ArrayRef<RemovedFlag> removed);

// Each returns nonzero (the process exit status) on error.
int kaReadInputList(const char *argv0); // positional inputs + --bc-list
int kaApplyMemLimit();                  // --mem-limit / --mem-limit-mode
int kaLoadModules(const char *argv0);   // parse, link symbols, node factory
// --cfl-field-buckets-auto: pick P from the loaded corpus.
void kaSelectFieldBuckets();
// --ir-census / --ir-census-strict / --ir-census-out; exitNow is set when
// the census is the whole job (--ir-census).
int kaIRCensusGate(bool &exitNow);

#endif
