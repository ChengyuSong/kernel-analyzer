#!/usr/bin/env python3
"""Regenerate docs/cli-reference.md from the cl::opt definitions.

    tools/gen-cli-reference.py > docs/cli-reference.md

Options are read from src/lib/Flags.cc (shared), src/lib/KAMain.cc and
src/baseline/BaselineMain.cc; descriptions and defaults come from the
code. The grouping below is the flag census of docs/release-trim.md;
an option missing from it is an error, so a new option has to be
classified here.
"""
import os
import re
import sys
from datetime import date

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')

GROUPS = [
    ('Inputs, outputs, driver', '''bc-list verbose log-timestamps mem-limit mem-limit-mode
        callgraph-json cfl-dump-icalls cfl-dump-icalls-json ir-sidecar-dir ir-census
        ir-census-strict ir-census-out cfl-clone-per-caller'''),
    ('Solver and graph build', '''cfl-global-dedup cfl-local-alloca-summary
        cfl-ext-globals-own-identity cfl-linker-arrays cfl-static-call cfl-printf-vararg-sink
        cfl-tracepoint-keys cfl-static-ops-tables cfl-presolve-cone cfl-presolve-exact
        cfl-presolve-once cfl-flows-to-max-iters cfl-iter-cap-ok cfl-verify-closure
        cfl-varargs-strict cfl-reachable cfl-entry-list cfl-bidi-prune cfl-lazy-mint
        cfl-intern-planes cfl-intern-sweep cfl-join-fastpath cfl-witness-answers
        cfl-flows-to-slice cfl-residue-copies'''),
    ('Threading and batching', '''cfl-solver-threads cfl-solver-block cfl-batch-roots
        cfl-batch-workers cfl-batch-spill'''),
    ('Summaries, provers, confirmers', '''func-summaries cfl-propose-chain-summaries
        cfl-propose-solved-summaries cfl-adopt-proposed-summaries cfl-propose-noop-summaries
        cfl-propose-atom-summaries cfl-atoms-global-stores cfl-adopt-skip cfl-confirm-fresh cfl-pool-carves
        cfl-confirm-invoke cfl-census-invoke cfl-census-extern-bound'''),
    ('Names: field and object tables', '''cfl-regfield-apply cfl-regfield-obj
        cfl-regfield-report cfl-regfield-audit cfl-regfield-watch cfl-filter-ledger'''),
    ('Certificates and contract gates', '''cfl-cert-usercopy cfl-confirm-sinks
        cfl-sink-instr'''),
    ('Field sensitivity and cell models (decided in Part B)', '''cfl-field-buckets
        cfl-field-buckets-auto cfl-auto-buckets-residual-bp cfl-auto-buckets-max
        cfl-nexus-fields cfl-channel-cells cfl-channel-cone cfl-channel-demand cfl-demand-site
        cfl-key-identity cfl-holder-identity cfl-lazy-address cfl-lazy-cap
        cfl-lazy-trace-object cfl-lazy-typed-access cfl-lazy-type-identity'''),
    ('Named cells and the cell solver (plan 3.9-3.31)', '''cfl-alloc-origins cfl-whole-program
        cfl-outside cfl-env-depth cfl-named-planes cfl-named-untyped cfl-name-by-target
        cfl-key-cells cfl-key-hubs cfl-key-partition cfl-union-keys cfl-union-path-stable
        cfl-rule-report cfl-cells cfl-cell-cap cfl-cell-unify cfl-cell-merge-ptrs cfl-cell-receivers
        cfl-cell-one-label cfl-cell-one-label-max cfl-cell-census-at cfl-cell-stop-answers cfl-cell-census-formal
        cfl-cell-trace-obj cfl-cell-why cfl-cell-why-at cfl-cell-collapse cfl-cell-soup-profile cfl-cell-leak-census cfl-cell-weld-census cfl-cell-soup-cap cfl-cell-soup-time
        cfl-construct-census cfl-census-names cfl-census-type-labels cfl-census-unions
        cfl-census-unions-detail cfl-weld-watch'''),
    ('Measurement instruments', '''cfl-probe-blob-formation cfl-census-couplers
        cfl-census-nexus cfl-census-type-rej cfl-gt-type-census cfl-dump-gt-aux
        cfl-ablate-mints cfl-ablate-funcs cfl-conflation-report cfl-root-relevance
        cfl-cotravel-stats cfl-solver-profile'''),
    ('Trace and dump', '''cfl-trace-func cfl-trace-first cfl-trace-fptr cfl-trace-meet
        cfl-trace-value cfl-dump-class cfl-dump-scc cfl-dump-merges cfl-dump-agraph
        cfl-dump-type-json cfl-dump-callee-mismatch cfl-dump-fnptr-offsets'''),
]
BASELINE_GROUP = 'KABaseline only'

OPT = re.compile(r'cl::(opt|list)<([^>]*)>\s+(\w+)\(\s*(?:cl::Positional,\s*)?'
                 r'(?:"([^"]*)")?(.*?)\);\n', re.S)


def read(path):
    s = open(os.path.join(ROOT, path)).read()
    out = {}
    for m in OPT.finditer(s):
        name, body = m.group(4), m.group(5)
        if not name:
            continue
        init = re.search(r'cl::init\(([^)]*)\)', body)
        desc = ''.join(re.findall(r'"((?:[^"\\]|\\.)*)"', body.split('cl::init')[0]))
        desc = desc.replace('\\"', '"').replace('\\n', ' ')
        out[name] = (init.group(1) if init else '', desc)
    return out


shared = read('src/lib/Flags.cc')
kamain = read('src/lib/KAMain.cc')
base = read('src/baseline/BaselineMain.cc')
opts = {**shared, **kamain}
grouped = {}
for title, names in GROUPS:
    for n in names.split():
        assert n in opts, f'{n} is in GROUPS but not defined'
        grouped[n] = title
missing = sorted(set(opts) - set(grouped))
if missing:
    sys.exit(f'unclassified options (add them to GROUPS): {missing}')

defaults_note = {'KA_DEFAULT_SUMMARIES': 'the repository\'s func_summaries.txt'}
print(f'''# KAMain and KABaseline command-line reference

Generated {date.today().isoformat()} by `tools/gen-cli-reference.py` from the
`cl::opt` definitions (`src/lib/Flags.cc` for options both binaries share,
`src/baseline/BaselineMain.cc` for the baseline's own). The descriptions in
the code are the source of truth; the grouping is the flag census of
`docs/release-trim.md`. `KAMain --help` prints the flat list.

## The binaries

- `release/lib/KAMain` resolves indirect calls with the rooted flows-to
  solver, its only mode. With no options it runs the reported
  configuration: the five channel and adoption mechanisms on
  (`--cfl-propose-chain-summaries`, `--cfl-propose-solved-summaries`,
  `--cfl-adopt-proposed-summaries`, `--cfl-regfield-apply`,
  `--cfl-regfield-obj`) and the repository's `func_summaries.txt` loaded.
- `release/baseline/KABaseline` is the CFL-reachability baseline: the same
  IR front end and constraint graph, saturated by GraCFL with the points-to
  grammar, per translation unit with composition (default) or monolithic
  (`--cfl-compositional=false`). It keeps the old saturation defaults (the
  five mechanisms off, no summary file) and refuses options only the
  flows-to solver honors.

## Common configurations

Kernel, field-insensitive:
```
KAMain --verbose=2 --cfl-dump-icalls --log-timestamps @filelist
```

Kernel, field-sensitive (all+ids instrument, big machine): add
```
--cfl-bidi-prune --cfl-nexus-fields=all+ids --mem-limit-mode=rss --mem-limit=90
--cfl-batch-roots=4000 --cfl-batch-workers=32 --cfl-batch-spill=<fresh-dir>
--cfl-presolve-once
```

Base (summaries, no channel mechanisms): add `--cfl-propose-chain-summaries=false
--cfl-regfield-apply=false --cfl-regfield-obj=false
--cfl-propose-solved-summaries=false --cfl-adopt-proposed-summaries=false`;
`eval/env.sh` provides `ka_config` for this.

Gate protocol for an answer-affecting change: pairs removal-only against the
pinned baseline (`^ICALL`/`^REGCALL` union, `LC_ALL=C`), ground-truth FN
lists unchanged (`tools/gt-match.py`); for a refactor, `test/consumer-gate.sh`
plus `test/consumer-diff.sh` old binary against new.

Removed options are errors that name their replacement; the list is in
`docs/release-trim.md`.
''')


def emit(title, names, table):
    print(f'## {title}\n')
    for n in names:
        init, desc = table[n]
        init = defaults_note.get(init, init)
        dflt = f' (default `{init}`)' if init else ''
        print(f'- **`--{n}`**{dflt}: {desc}')
    print()


for title, names in GROUPS:
    emit(title, names.split(), opts)
emit(BASELINE_GROUP, sorted(base), base)
