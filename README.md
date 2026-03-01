# Linux Kernel Analyzer

This is a static kernel analyzer forked from [KINT](https://github.com/CRYPTOlab/kint).

## Compositional CFL Analysis

The `--cfl-compositional` flag enables per-TU CFL solving with V-SCC
compression and whole-program composition. This avoids building a single
monolithic constraint graph and allows caching per-library results.

### Quick start

```bash
# All-in-one: per-TU solve + compose (no intermediate files)
kanalyzer tu1.o tu2.o tu3.o --cfl-compositional --callgraph-json cg.json

# Two-phase with cached compressed graphs:
kanalyzer lib_tu1.o lib_tu2.o --cfl-compressed-output lib.cflcg
kanalyzer app.o               --cfl-compressed-output app.cflcg

kanalyzer lib_tu1.o lib_tu2.o app.o \
  --cfl-compositional \
  --cfl-compressed-input lib.cflcg \
  --cfl-compressed-input app.cflcg \
  --callgraph-json cg.json
```

### Flags

| Flag | Description |
|------|-------------|
| `--cfl-compositional` | Enable per-TU CFL solving and whole-program composition |
| `--cfl-compressed-output <path>` | Export compressed constraint graph to a `.cflcg` file |
| `--cfl-compressed-input <path>` | Load a pre-built `.cflcg` file (repeatable) |
| `--cfl-cache-strict=<true\|false>` | Strict cache validation for `.cflcg` inputs (default: `true`) |
| `--cfl-cache-repair` | Recompute missing/stale/incompatible modules from current IR, then compose |
| `--cfl-cache-allow-duplicate-coverage` | Allow multiple input `.cflcg` files to claim the same covered module |

### Cache validation policy

Compositional mode now validates `.cflcg` cache inputs against current bitcode
inputs in strict mode (`--cfl-cache-strict=true`, default).

Strict mode checks:

- coverage: union of `covered_modules` equals current input module set
- freshness: per-module SHA256 in `module_hashes` matches current bitcode
- compatibility: `analysis_key` (grammar/labels/flags/schema) matches current run
- duplicates: same module cannot be covered by multiple `.cflcg` inputs unless
  `--cfl-cache-allow-duplicate-coverage` is set
- boundary sanity: required boundary classes
  (`func/arg/ret/vararg/glob/icall`) are present when expected from current IR

On mismatch, diagnostics list `missing`, `stale`, `duplicate`, and
`incompatible` entries, and the run fails closed.

Use `--cfl-cache-repair` to rebuild invalid/missing modules from current IR and
continue composition automatically.

For legacy or handcrafted `.cflcg` fixtures without metadata, use
`--cfl-cache-strict=false`.

See `docs/compositional-cfl-analysis.md` for the full design.

## Documentation

- CFL-reachability architecture, optimizations, and VSnapshot serialization:
  `docs/cfl-reachability-vsnapshot.md`
- Compositional CFL analysis design:
  `docs/compositional-cfl-analysis.md`
- Lean proof scaffold for compositional soundness:
  `proof/lean/README.md`
  (gap tracker: `proof/lean/GAPS.md`)
- Known call graph limitations:
  `docs/call-graph-limitations.md`

### Referece

If you like our code, please kindly acknowledge the usage of our tool by citing the following paper:
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

### Papers/Tools use this tool/framework

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
