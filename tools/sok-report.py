#!/usr/bin/env python3
"""One-pass SoK report over eval/65 merged directories, per call site,
with NO LLVM-CFI fallback (see tools/sok-persite.py for why).

Tables (markdown on stdout):
  1. fuzz-GT targets missed, per program x approach (* = some GT sites
     have no answer key at all);
  2. mean targets per site and empty sites, per program x approach;
  3. per-site comparison against the reference (default ORCFL), summed
     over programs: sites where ref is tighter / wider / equal /
     incomparable, and targets only one side has;
  4. wall time and max RSS, when --times is given (eval/67 summary.tsv
     files and eval/62 <prog>.log.time files).
Names are compared the way sok-persite does: one numeric clone suffix
dropped, C++ demangled, libc alias spellings unified.

usage: sok-report.py --merged DIR[,DIR...] [--ref ORCFL]
         [--times SOKOUT[,SOKOUT...]] > report.md
(--times dirs pair with --merged dirs by position.)
"""
import argparse, collections, importlib.util, json, re, sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    'ps', Path(__file__).with_name('sok-persite.py'))
ps = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ps)

ORDER = ['ORCFL', 'ORCFL-base', 'LLVM-CFI', 'KallGraph', 'HPCFI', 'MLTA_Orig',
         'MLTA', 'TFA', 'DeepType', 'SVF-Andersen', 'SVF-VFS']


def programs(merged, opt):
    d = Path(merged) / opt / 'ORCFL-full' / 'parsed_log'
    return sorted(p.stem for p in d.glob('*.json')) if d.is_dir() else []


def order(names):
    first = [n for n in ORDER if n in names]
    return first + sorted(n for n in names if n not in first)


def table(title, cols, rows):
    out = [f'\n### {title}\n', '| opt | program | ' + ' | '.join(cols) + ' |',
           '|---|---|' + '---|' * len(cols)]
    out += ['| ' + ' | '.join(r) + ' |' for r in rows]
    return '\n'.join(out)


def times(sokouts):
    t = {}   # (approach, opt, prog) -> (wall, rss_kb)
    for so in sokouts:
        so = Path(so)
        for s in so.glob('baselines/summary.tsv'):
            for ln in open(s):
                f = ln.rstrip('\n').split('\t')
                if len(f) == 6 and f[3] == 'ok':
                    opt = 'O0' if f[1].endswith('O0') else 'O3'
                    t[(f[0], opt, f[2])] = (f[4], f[5])   # last row wins
        for cfg, name in (('full', 'ORCFL'), ('base', 'ORCFL-base')):
            for tf in so.glob(f'{cfg}/*/*.log.time'):
                opt = 'O0' if 'O0' in tf.parent.name else 'O3'
                txt = tf.read_text()
                w = re.search(r'Elapsed \(wall clock\).*: (\S+)', txt)
                r = re.search(r'Maximum resident set size \(kbytes\): (\d+)', txt)
                prog = tf.name[:-len('.log.time')]
                if w and r:
                    t[(name, opt, prog)] = (w.group(1), r.group(1))
    return t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--merged', required=True)
    ap.add_argument('--ref', default='ORCFL')
    ap.add_argument('--times')
    a = ap.parse_args()

    miss_rows, width_rows = {}, {}
    cmp = collections.defaultdict(collections.Counter)
    allappr = set()
    per = []   # (merged, opt, prog, A, gt, index of the merged dir)
    for mi, merged in enumerate(a.merged.split(',')):
        for opt in ('O0', 'O3'):
            for prog in programs(merged, opt):
                A = ps.load_approaches(merged, opt, prog)
                if a.ref not in A:
                    continue
                gt = ps.load_gt(prog, A[a.ref].keys())
                per.append((Path(merged).name, opt, prog, A, gt, mi))
                allappr |= set(A)
    cols = order(allappr)
    for mname, opt, prog, A, gt, _ in per:
        key = (mname, opt, prog)
        mr, wr = [], []
        for n in cols:
            ans = A.get(n)
            if ans is None:
                mr.append('–'); wr.append('–'); continue
            miss = sum(1 for k, ts in gt.items() for t in ts
                       if k in ans and t not in ans[k])
            absent = any(k not in ans for k in gt)
            mr.append(f'{miss}{"*" if absent else ""}' if gt else '')
            tot = sum(len(v) for v in ans.values())
            empty = sum(1 for v in ans.values() if not v)
            wr.append(f'{tot / max(len(ans), 1):.1f} ({empty})')
            if n != a.ref:
                ref = A[a.ref]
                for k in ref.keys() & ans.keys():
                    r, o = ref[k], ans[k]
                    c = cmp[n]
                    c['common'] += 1
                    c['equal' if r == o else 'ref-tighter' if r < o else
                      'ref-wider' if r > o else 'incomparable'] += 1
                    c['ref-only'] += len(r - o)
                    c['other-only'] += len(o - r)
        if gt:
            miss_rows[key] = [opt, f'{prog} ({mname}, {sum(len(v) for v in gt.values())} GT)'] + mr
        width_rows[key] = [opt, f'{prog} ({mname})'] + wr

    print(f'# SoK per-site report (reference {a.ref}; no LLVM-CFI fallback)')
    print(table('Fuzz-observed targets missed (* = GT sites with no answer key)',
                cols, [miss_rows[k] for k in sorted(miss_rows)]))
    print(table('Mean targets per site (empty sites)', cols,
                [width_rows[k] for k in sorted(width_rows)]))
    print(f'\n### Per-site comparison against {a.ref}, summed over programs\n')
    print(f'| approach | common sites | {a.ref} tighter | {a.ref} wider | equal | '
          f'incomparable | {a.ref}-only targets | other-only targets |')
    print('|---|---|---|---|---|---|---|---|')
    for n in cols:
        if n == a.ref or n not in cmp:
            continue
        c = cmp[n]
        print(f'| {n} | {c["common"]} | {c["ref-tighter"]} | {c["ref-wider"]} | '
              f'{c["equal"]} | {c["incomparable"]} | {c["ref-only"]} | {c["other-only"]} |')
    if a.times:
        # --times dirs pair with --merged dirs by position
        T = [times([so]) for so in a.times.split(',')]
        tcols = [n for n in cols if any(k[0] == n for t in T for k in t)]
        rows = []
        for mname, opt, prog, A, gt, mi in per:
            t = T[mi] if mi < len(T) else {}
            base = prog.split('__')[-1]
            rows.append([opt, f'{prog} ({mname})'] + [
                '/'.join(x for x in (t.get((n, opt, base)) or t.get((n, opt, prog)) or ('–',)))
                for n in tcols])
        print(table('Wall time / max RSS KB (runs on disjoint cpusets; not '
                    'solo-timed unless run with KA_BIGBOX_PAR=1)', tcols, rows))


if __name__ == '__main__':
    main()
