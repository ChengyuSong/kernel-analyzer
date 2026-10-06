# KAnalyzer

A whole-program call-graph analysis for C/C++ in LLVM IR, built for the
Linux kernel and large user-space programs. It began as a fork of
[KINT](https://github.com/CRYPTOlab/kint).

Indirect calls are resolved by a rooted flows-to analysis: the origins
that matter for a call graph (functions, globals, allocation sites) are
propagated through a constraint graph built from the IR, and memory
cells are named by what the program declares and tests (struct fields,
union members, discriminators, tags). The assumptions that make those
names sound are stated, checked, and reported per run rather than
assumed.

## Build

Requirements: LLVM 18 with clang, CMake 3.16+, a C++17 compiler,
jemalloc (built automatically if absent).

```bash
make BUILD_DIR=release LLVM_BUILD=/usr/lib/llvm-18      # clean build
cmake --build release                                   # incremental
```

Two binaries are produced:

- `release/lib/KAMain`: the analyzer.
- `release/baseline/KABaseline`: the CFL-reachability saturation
  baseline (GraCFL), kept for the scaling measurements. It carries the
  compositional per-translation-unit mode and the compressed-graph
  cache (`--cfl-compositional`, `--cfl-compressed-output/-input`,
  `--cfl-cache-*`); see `docs/compositional-cfl-analysis.md`.

## Quick start

```bash
# Analyze bitcode (files or a list); the default configuration is the
# one reported in the paper.
release/lib/KAMain tu1.bc tu2.bc --callgraph-json cg.json
release/lib/KAMain --bc-list files.txt --cfl-dump-icalls-json icalls.json

# Report the rules the call graph assumes and where the program breaks them
# (a whole program: code outside the bitcode is assumed to do nothing)
release/lib/KAMain --bc-list files.txt --cfl-whole-program \
  --cfl-named-planes --cfl-alloc-origins --cfl-rule-report=rules.txt
```

Outputs: `--callgraph-json` (functions with callers and callees),
`--cfl-dump-icalls-json` (per-callsite answers keyed by debug location),
`--ir-sidecar-dir` (per-module IR facts). Options removed from the
analyzer are rejected with a message naming the replacement.

The full option list with descriptions is in `docs/cli-reference.md`.

## Evaluation

`eval/` rebuilds every corpus and baseline from pinned sources and runs
the comparison; see `eval/README.md`. Gates for changes:
`test/cfl-smoke.sh` (pinned answers), `test/consumer-gate.sh` with
`test/consumer-diff.sh` (every consumer output, old binary against new).

## Documentation

- Design of named cells and the rule report: `docs/named-cells-design.md`
- Transfer summaries (`func_summaries.txt`) and their scopes: header of
  that file
- Lean models and open obligations: `proof/lean/README.md`,
  `proof/lean/GAPS.md`
- Compositional CFL baseline: `docs/compositional-cfl-analysis.md`,
  `docs/cfl-reachability-vsnapshot.md`
- Known limitations: `docs/call-graph-limitations.md`
- Command-line reference: `docs/cli-reference.md`

## Reference

If you use this code, please cite:

```
Enforcing Kernel Security Invariants with Data Flow Integrity
Chengyu Song, Byoungyoung Lee, Kangjie Lu, William R. Harris, Taesoo Kim, and Wenke Lee
NDSS 2016

@inproceedings{song:kenali,
  title        = {{Enforcing Kernel Security Invariants with Data Flow Integrity}},
  author       = {Chengyu Song and Byoungyoung Lee and Kangjie Lu and William R. Harris and Taesoo Kim and Wenke Lee},
  booktitle    = {Proceedings of the 2016 Annual Network and Distributed System Security Symposium (NDSS)},
  month        = feb,
  year         = 2016,
  address      = {San Diego, CA},
}
```

## Papers and tools that use this framework

```
Principled Unearthing of TCP Side Channel Vulnerabilities
Yue Cao, Zhongjie Wang, Zhiyun Qian, Chengyu Song, Srikanth Krishnamurthy, and Paul Yu
CCS 2019
```
```
Detecting Missing-Check Bugs via Semantic- and Context-Aware Criticalness and Constraints Inferences
Kangjie Lu, Aditya Pakki, and Qiushi Wu
USENIX Security 2019
```
```
Automatically Identifying Security Checks for Detecting Kernel Semantic Bugs
Kangjie Lu, Aditya Pakki, and Qiushi Wu
ESORICS 2019
```
```
Check it Again: Detecting Lacking-Recheck Bugs in OS Kernels
Wenwen Wang, Kangjie Lu, and Pen-Chung Yew
CCS 2018
```
```
UniSan: Proactive Kernel Memory Initialization to Eliminate Data Leakages
Kangjie Lu, Chengyu Song, Taesoo Kim, and Wenke Lee
CCS 2016
```
