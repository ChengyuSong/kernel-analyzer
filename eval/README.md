# Eval harness

Reproducible end-to-end evaluation: fetch + build corpora to LLVM
bitcode, run the analysis matrix, extract a results table. Designed
to run unattended on a fresh (big) machine.

## Quick start

```bash
git clone <this-repo> kanalyzer && cd kanalyzer
eval/run-all.sh                 # everything, default config
```

Requirements: LLVM/clang >= 18 with lld and llvm-ar (Ubuntu:
`llvm-18 clang-18 lld-18`), cmake >= 3.16, make, curl, bison, flex,
expat headers (`libexpat1-dev`), pcre2 (`libpcre2-dev`). ~15 GB disk
in `KA_WORK`; RAM per the table below.

## Configuration (env vars, see `env.sh`)

| var | default | meaning |
|---|---|---|
| `KA_WORK` | `~/ka-eval` | corpora + results workspace |
| `KA_JOBS` | `nproc` | build parallelism |
| `KA_LLVM_SUFFIX` | `-18` | toolchain suffix (`""` for unsuffixed) |
| `KA_MEM_LIMIT_GB` | `0` (=80% RAM watchdog) | analyzer memory cap |
| `KA_SAT_TIMEOUT` | `14400` | saturation wall cap (s) |
| `KA_EXTRA_FLAGS` | — | appended to flows-to runs |
| `KA_USER_BCLIST`/`KA_USER_NAME` | — | analyze an existing bclist too (e.g. a kernel) |

Big-machine note: the interesting saturation question is whether the
baseline COMPLETES given enough memory — raise `KA_MEM_LIMIT_GB`
(e.g. 700 on a 1 TB box) so the OOM bars become either completions
or higher-water OOMs. Flows-to runs need far less.

## What runs

Per corpus (httpd 2.4.68+apr static-all-modules; postgresql 18.4
backend objects only; optionally your bclist):

- **ft** — flows-to (the system config): `--cfl-compositional=false
  --cfl-flows-to --cfl-dump-icalls`. Produces the per-icall answer
  set; the sorted dump + sha256 is the portable pin — answers are
  deterministic, so hashes must match across machines for the same
  binary+corpus.
- **sat** — saturation baseline (GraCFL engine, same IR graph): no
  `--cfl-flows-to`. Expected outcome at library/app scale under
  ~50 GB caps: OOM (that is the measured result, not a harness
  failure).

## Ablations (optional: `KA_ABLATE=1` or run `35-ablate.sh` directly)

Two families with different success criteria, both diffed against
the default ft pin (so `30-run.sh` must run first):

- **exact** — perf machinery that must not change answers:
  `noshare` (#46 COW plane sharing), `nofastjoin` (#48 cluster-mark
  join skips), `scratch` (disable incremental), `lazymint`
  (demand-driven minting). The script asserts byte-identical pins;
  `MISMATCH` = soundness bug, reported loudly.
- **precision** — identity channels / relevance discipline:
  `notpkeys`, `noopstables`, `nocone`, `nosummaries` (kernel-only,
  auto-skipped without `--func-summaries` in `KA_EXTRA_FLAGS`).
  Channels only remove pairs, so the default pin must be a subset of
  the ablated run (the `-N/+0` certification); the delta is the
  channel's measured contribution.

`KA_ABLATE_LIST="nocone notpkeys"` selects a subset. Output:
`ablations.csv` / `ablations.md` + per-run logs and pins.
Note ablation runs cost roughly one ft run each — at kernel scale
pick your subset deliberately.

## Outputs (`$KA_RESULTS`)

- `<corpus>-<mode>.log` — full log incl. `/usr/bin/time -v` and
  `exitcode:` trailer.
- `<corpus>-ft-icalls.sort{,.sha256}` — answer pin.
- `results.csv` / `results.md` — one row per run: outcome
  (ok/oom/timeout/error), wall, peak RSS, type-based vs CFL pairs,
  sites, avg/max fanout, solve stats (classes/roots/facts/waves/
  pops/solve-ms), boundary ledgers (int-provenance modeled/ledgered,
  extern resolutions), pin sha256.

## Reference numbers (62 GB desktop, 2026-08-08, defaults)

| corpus | ft | sat (49 GB cap) |
|---|---|---|
| httpd | 42 s / 0.75 GB; 400,968 type → 108,282 CFL (1,191 sites) | OOM @ 11:41 |
| postgres | 5:16 / 5.9 GB; 2,382,359 type → 398,698 CFL (2,452 sites) | OOM @ 2:59 |

## Caveats

- These are fresh-IR corpora. Numbers are NOT comparable to
  engine-paper tables on the Graspan-suite fixed graphs (different
  graph construction, vintages, problems) — do not present them as
  such.
- Kernel corpora are built by their own flow (LLVM-IR kernel build →
  bclist); pass via `KA_USER_BCLIST`. Kernel runs want
  `KA_EXTRA_FLAGS="--func-summaries=$PWD/func_summaries.txt"` and a
  raised `KA_MEM_LIMIT_GB` (see the project docs for pinned kernel
  configs).
- `20-build-corpora.sh` encodes two non-obvious steps: postgres
  `objfiles.txt` lines are space-separated multi-path (tokenize!),
  and httpd libtool `.libs/` PIC twins are excluded (duplicate TUs
  would duplicate answers).
