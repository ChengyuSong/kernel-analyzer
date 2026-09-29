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
- **ftc** (opt-in: `KA_MODES="ft ftc sat"`) — ft + auto-certified
  identity channels (`--cfl-regfield-apply --cfl-regfield-audit`).
  The run script verifies ftc's pin is a STRICT SUBSET of ft's (a
  violation = certifier bug, reported loudly); the extraction adds
  chan_keys/chan_removed columns and the log carries the per-key
  provenance certificates (GREEN/YELLOW/ORANGE) + counted residual.
  Kernel 6.18 reference: 1,997 keys, -1,487,417/+0 (-30.6%), fanout
  p50 43->6, wall 1:46 (vs ft 2:07).

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

## FSE campaign scripts (60-series)

The paper's evaluation is driven by dedicated, resumable scripts —
one per campaign, all same-machine so timing columns are comparable
and all runnable from the repo (artifact):

- `60-kernel-fse.sh` — kernel 5.18 FI: frozen full stack, 14-arm
  precision/perf matrix, GT matching (`tools/gt-match.py`), quiet
  timed passes, one-sidedness + byte-identity gates, `summary.tsv`.
- `61-kernel-fs-endpoints.sh` — kernel field-sensitive endpoints
  (fsfull/fsbase, all+ids + batched + spill; big-machine).
- `62-sok-arm.sh` — ORCFL over the SoK-MLTA (WOOT'26) bitcode
  datasets, emitting their parsed_log JSON per program.
- `63-gracfl-graspan.sh` — GraCFL engine on the Graspan-suite fixed
  graphs (Q1 contrast: all-pairs points-to closure, NOT a callgraph
  competitor row).
- `64-usermode-fse.sh` — httpd + postgresql transfer RQ: FI
  full/base + fs endpoints per corpus, one-sidedness checks, quiet
  FI timed passes, `summary.tsv`. Memory-capped via RLIMIT_AS so a
  blow-up fails cleanly in-process.
- `65-sok-compare.sh` — merges 62's output into their harness
  layout (canonical program names, keys aligned to LLVM-CFI's
  exact strings) and runs THEIR `compare_approaches.py` in a
  network-less Docker sandbox against their pre-computed baselines
  (O0: LLVM-CFI + KallGraph; O3: LLVM-CFI + HPCFI).
- `66-sok-baselines.sh` + `sok-baselines.Dockerfile` — same-machine
  timing rows: MLTA/DeepType/TFA (+ TFA's MLTA-only variant) built
  from source at their pinned commits with their patches, run over
  their released bitcodes by their `run_experiment.py`, all inside
  a network-less container. Only the image build needs the network.
- `67-dataflow-baselines.sh` + `svf-baseline.Dockerfile` +
  `lotus-baseline.Dockerfile` — whole-program pointer-analysis
  baselines, which the SoK did not evaluate: SVF 3.2 Andersen and
  versioned flow-sensitive (LLVM 15 bitcode, same files as 62), and
  via Lotus (LLVM 14 only) AserPTA CI/1-CFA/2-CFA, DyckAA, SeaDsa.
  Per-site dumpers (`svf-baseline/svf-icalls.cpp`,
  `lotus-baseline/icall-sites.patch`, `lotus-baseline/seadsa-icalls.cpp`)
  write 62's JSON key space and change no analysis. Lotus rows pair
  with 62 run on the SAME LLVM 14 files (`KA_SOK_BC=<llvm14 dirs>`).
  Each tool's own resolution filter is recorded in the script header.
- `68-sok-httpd-apr.sh` — completes the artifact's httpd.bc (887
  undefined symbols, 423 of them APR/APR-util) by building APR 1.7.6 +
  APR-util 1.6.4 to bitcode with the artifact's compiler major (typed
  pointers for LLVM 15) and llvm-linking them in; httpd's own IR and
  call-site keys are unchanged.
- `69-sok-bigbox.sh` + `sok-toolchain.Dockerfile` — the whole SoK
  comparison for a big server, built entirely from pinned sources
  (SoK-MLTA, Lotus and SVF at pinned commits, APR tarballs sha256-checked,
  images built from the Dockerfiles). Only the SoK authors' dataset is a
  manual download (Google Drive link in the script). Runbook:
  ```
  export KA_SOK_ROOT=/path/to/sok-dataset KA_BIGBOX_WORK=/big/disk/sok \
         KA_BIGBOX_PAR=12 KA_DF_MEM=128g KA_DF_TIMEOUT=14400
  eval/69-sok-bigbox.sh setup     # once: clone + build (network)
  eval/69-sok-bigbox.sh all       # prepare + run + report
  ```
  Output: `$KA_BIGBOX_WORK/report.md` (per-site, no LLVM-CFI fallback),
  their tables in `merged-llvm15/`, `merged-llvm14/` (+ `pair-*/`).
  Timings from a parallel run share memory bandwidth; for timing rows
  rerun the chosen approaches with `KA_BIGBOX_PAR=1`.

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
