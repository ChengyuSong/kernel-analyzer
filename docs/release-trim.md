# Release trim: fix-or-remove ledger (started 2026-09-04)

Policy (user): no tombstones, no parked code — fix it or remove it.
History lives in git; the tree ships what works. Every removal is a
pure deletion of default-off paths, gated by cfl-smoke + the
canonical pin.

REMOVED:
- witness-taint (2026-09-04): retired experiment, falsified by
  design review + GT. Files deleted; flag deleted.
- incremental cross-iteration solving (2026-09-04): divergent at
  kernel corpora (docs/incremental-518-divergence.md); the fix is
  a perpetual seed-enumeration tax on every future edge kind for a
  ~20% wall win that the PROVEN-EXACT lazymint+bidi pair largely
  recovers. wireIncremental + flag + envelope guards deleted.
  incr_exact (Staging.lean) retained as the specification for any
  future reimplementation.
- origin-bundles (2026-09-04): parked feature (Gate 2 wall fail),
  default-off. Removed: epoch machinery + remapBits/expandBits +
  mintRoot/blame bridging + 3 flags (--cfl-origin-bundles,
  --cfl-bundle-epoch-facts, --cfl-bundle-probe), plus leftover
  incremental-wiring debris found by the warning sweep (growTo,
  parkedRoots, newAllocNodes, edgesConsumed, protBlameName2,
  solverCapN headroom). Bundles.lean + design doc stay as the
  record/spec. Gates: cfl-smoke 4/4; libpng old-vs-new
  byte-identical; km all+ids mono + batched old-vs-new
  byte-identical (same-day binaries, same corpus).

QUEUED (each = its own gated pass):
1. Flag census for the wider trim — candidates by class:
   - superseded mechanisms: --cfl-ops-pairs, --cfl-rodata-copy,
     --cfl-join-cone (predecessors of regfield/obj; verify nothing
     canonical consumes the shared protection machinery first)
   - one-off measurement probes that produced their numbers and
     are recorded in docs: ablate-mints/ablate-funcs, probe-*,
     census-* (KEEP the ones the paper's instruments still use:
     probe-blob-formation/ClassHist, census-couplers, gt dumps)
   - legacy/task-specific listed in cli-reference "Other" section
2. cli-reference.md regeneration after each pass (remove dead
   entries).
3. The trimmed tree then IS the FSE artifact base (anonymized).
