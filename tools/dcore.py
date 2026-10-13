#!/usr/bin/env python3
"""Apply 29687ab's solver-order hunks to an older tree (the per-step census
re-cut, plan 3.53): the cells solve walks pointer sets in IR order.

Usage: tools/dcore.py ROOT, where ROOT is a checkout of an older commit.
29687ab does not cherry-pick onto commits before it: its gate files do not
exist there and the CellSolver / Slots contexts differ. This applies the
solver-order hunks only, and asserts that every anchor is found exactly
once:
- CellSolver.cc: the stable IR order, the function seeds, the receiver
  sites, callers[F] and the answer wiring;
- Names.cc: the two icall loops;
- Slots.cc and CallGraphInternal.h: icallsInIROrder.
Record the base hash, the resulting `git write-tree`, and 29687ab with any
number measured on the result."""
import sys
root = sys.argv[1]
def edit(rel, pairs):
    p = f"{root}/{rel}"; s = open(p).read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (rel, a[:60], n)
        s = s.replace(a, b)
    open(p, "w").write(s)

stable = '''  std::unordered_map<const Value *, uint64_t> stableOrd;
  {
    uint64_t k = 0;
    for (auto &[M, _] : Ctx->Modules)
      for (Function &F : *M) {
        stableOrd[&F] = k++;
        for (Instruction &I : instructions(F)) stableOrd[&I] = k++;
      }
  }
  auto stableKey = [&](const Value *V) {
    auto it = stableOrd.find(V);
    return it == stableOrd.end() ? UINT64_MAX : it->second;
  };
  std::vector<const Function *> addrTakenSorted(Ctx->AddressTakenFuncs.begin(),
                                                Ctx->AddressTakenFuncs.end());
  std::sort(addrTakenSorted.begin(), addrTakenSorted.end(), [&](const Function *a, const Function *b) {
    const uint64_t ka = stableKey(a), kb = stableKey(b);
    return ka != kb ? ka < kb : a->getName() < b->getName();
  });
  std::vector<const CallBase *> icallsSorted = icallsInIROrder(Ctx);

'''
cs = "src/lib/CellSolver.cc"
s = open(f"{root}/{cs}").read()
pairs = [('''  // ---- Seeds: functions and objects ----
  size_t funcSeeds = 0, objSeeds = 0;
  std::unordered_map<const Function *, uint32_t> funcFact;
  for (const Function *F : Ctx->AddressTakenFuncs) {''', stable + '''  // ---- Seeds: functions and objects ----
  size_t funcSeeds = 0, objSeeds = 0;
  std::unordered_map<const Function *, uint32_t> funcFact;
  for (const Function *F : addrTakenSorted) {''')]
if "for (const CallBase *CS : Ctx->IndirectCallInsts) {\n      const int k = dispatchReceiver(CS, &path);" in s:
    pairs.append(("for (const CallBase *CS : Ctx->IndirectCallInsts) {\n      const int k = dispatchReceiver(CS, &path);",
                  "for (const CallBase *CS : icallsSorted) {\n      const int k = dispatchReceiver(CS, &path);"))
if "      for (const Function *F : FS) callers[F].push_back(CS);\n" in s:
    pairs.append(("      for (const Function *F : FS) callers[F].push_back(CS);\n",
                  "      for (const Function *F : FS) callers[F].push_back(CS);\n"
                  "    for (auto &[F, cs] : callers)\n"
                  "      std::sort(cs.begin(), cs.end(), [&](const CallBase *a, const CallBase *b) { return stableKey(a) < stableKey(b); });\n"))
pairs.append(('''  const std::vector<const CallBase *> icallSnapshot(
      Ctx->IndirectCallInsts.begin(), Ctx->IndirectCallInsts.end());''',
              '''  const std::vector<const CallBase *> icallSnapshot = icallsSorted;'''))
pairs.append(('''    for (const Function *F : targets)
      if (wireResolvedCallee(CS, F)) newPairs++;''', '''    std::vector<const Function *> targetsSorted(targets.begin(), targets.end());
    std::sort(targetsSorted.begin(), targetsSorted.end(), [&](const Function *a, const Function *b) {
      const uint64_t ka = stableKey(a), kb = stableKey(b);
      return ka != kb ? ka < kb : a->getName() < b->getName();
    });
    for (const Function *F : targetsSorted)
      if (wireResolvedCallee(CS, F)) newPairs++;'''))
edit(cs, pairs)
nm = f"{root}/src/lib/Names.cc"; t = open(nm).read()
assert t.count("for (auto *CB : Ctx->IndirectCallInsts) {") == 2
open(nm, "w").write(t.replace("for (auto *CB : Ctx->IndirectCallInsts) {", "for (auto *CB : icallsInIROrder(Ctx)) {"))
edit("src/lib/CallGraphInternal.h", [('''bool tbaaReaches(const Instruction *I, StringRef SN, int64_t o);
''', '''bool tbaaReaches(const Instruction *I, StringRef SN, int64_t o);
std::vector<const CallBase *> icallsInIROrder(const GlobalContext *Ctx);
''')])
sl = f"{root}/src/lib/Slots.cc"; u = open(sl).read().rstrip("\n")
u += '''

std::vector<const CallBase *> icallsInIROrder(const GlobalContext *Ctx) {
  std::vector<const CallBase *> out;
  for (auto &[M, _] : Ctx->Modules)
    for (Function &F : *M)
      for (Instruction &I : instructions(F))
        if (const auto *CB = dyn_cast<CallBase>(&I); CB && Ctx->IndirectCallInsts.count(CB)) out.push_back(CB);
  return out;
}
'''
open(sl, "w").write(u)
print("applied:", len(pairs), "CellSolver hunks")
