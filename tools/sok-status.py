#!/usr/bin/env python3
"""Completion status of every SoK run, per analysis: how many program
builds finished, timed out, ran out of memory, crashed, or were not
reached (the run was stopped first).

Sources:
  --summary  eval/67 summary.tsv (approach, set, prog, status, wall, rss);
             statuses ok | timeout | killed-oom-or-signal | exit-N.
             Kills are counted as out of memory: check the kernel log
             ("Memory cgroup out of memory" = the container's own cap;
             "kernel: Out of memory" = host contention, not a fair kill).
  --orcfl    eval/62 output dir (KA_SOK_OUT): <cfg>/<tag>/<prog>.log,
             <prog>.log.time and parsed_log/<prog>.json; only cfg "full"
             (the configuration the paper reports) is counted.
  --expected number of program builds per analysis (default: the largest
             count any analysis attempted).

usage: sok-status.py --summary SUMMARY.tsv [--orcfl SOKOUT]
         [--expected 60] [--format md|tex|tex2] > table
(tex = LaTeX rows, zeros blank; tex2 = the same rows in two side-by-side
panels, for a 12-column tabular)
"""
import argparse, collections, re
from pathlib import Path

# paper order: ours, whole-program pointer analyses, shape-check variants,
# type-based reference rows
ORDER = ['ORCFL',
         'SVF-Andersen', 'SVF-VFS', 'SeaDsa', 'DyckAA',
         'AserPTA-CI', 'AserPTA-Origin', 'AserPTA-1CFA', 'AserPTA-2CFA',
         'TPA-K0', 'TPA-K1', 'LotusAA', 'SparrowAA', 'BootstrapAA',
         'DDA-Flow', 'FSPTA', 'VFSPTA', 'VFPTA',
         'GPG-FICI', 'GPG-FICS', 'GPG-FSCS',
         'AserPTA-CI-shape', 'DyckAA-shape',
         'CHA', 'RTA', 'VTA', 'OTF']
COLS = ['ok', 'timeout', 'oom', 'crash']


def kind(status):
    if status == 'ok':
        return 'ok'
    if status == 'timeout':
        return 'timeout'
    if status.startswith('killed'):
        return 'oom'
    return 'crash'


def from_summary(path):
    last = {}   # (approach, set, prog) -> status; a rerun's row wins
    for ln in open(path):
        f = ln.rstrip('\n').split('\t')
        if len(f) == 6:
            last[(f[0], f[1], f[2])] = f[3]
    c = collections.defaultdict(collections.Counter)
    for (appr, _, _), st in last.items():
        c[appr][kind(st)] += 1
    return c


def from_orcfl(sokout):
    c = collections.Counter()
    for log in Path(sokout, 'full').glob('*/*.log'):
        prog = log.name[:-len('.log')]
        js = log.parent / 'parsed_log' / f'{prog}.json'
        if js.is_file() and js.stat().st_size > 0:
            c['ok'] += 1
            continue
        t = log.with_name(log.name + '.time')
        txt = t.read_text() if t.is_file() else ''
        if 'signal 9' in txt:
            c['oom'] += 1
        elif re.search(r'non-zero status|terminated by signal', txt):
            c['crash'] += 1
        else:            # timeout(1) kills /usr/bin/time before it reports
            c['timeout'] += 1
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', required=True)
    ap.add_argument('--orcfl')
    ap.add_argument('--expected', type=int)
    ap.add_argument('--format', choices=['md', 'tex', 'tex2'], default='md')
    a = ap.parse_args()
    C = from_summary(a.summary)
    if a.orcfl:
        C['ORCFL'] = from_orcfl(a.orcfl)
    exp = a.expected or max(sum(c.values()) for c in C.values())
    names = [n for n in ORDER if n in C] + sorted(n for n in C if n not in ORDER)
    rows = []
    for n in names:
        c = C[n]
        rows.append([n] + [str(c[k]) for k in COLS]
                    + [str(exp - sum(c.values()))])
    head = ['analysis', 'finished', 'timeout', 'out of memory', 'crashed',
            'not reached']
    if a.format == 'md':
        print('| ' + ' | '.join(head) + ' |')
        print('|---' * len(head) + '|')
        for r in rows:
            print('| ' + ' | '.join(r) + ' |')
    else:
        tex = [[r[0]] + [v if v != '0' else '' for v in r[1:]] for r in rows]
        if a.format == 'tex':
            for t in tex:
                print(' & '.join(t) + r' \\')
        else:
            h = (len(tex) + 1) // 2
            for i in range(h):
                right = tex[h + i] if h + i < len(tex) else [''] * len(head)
                print(' & '.join(tex[i] + right) + r' \\')


if __name__ == '__main__':
    main()
