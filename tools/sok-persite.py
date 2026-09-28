#!/usr/bin/env python3
"""Per-call-site comparison of indirect-call answers on one SoK program.

Averages hide the shape of an answer. This reports, per approach:
  * the width histogram and the widest sites;
  * POOLED SETS: groups of sites that share one identical large target
    set -- the signature of a single pooled (universal) pointer class;
  * per-site comparison against a reference approach (default ORCFL):
    where the other approach is tighter, looser, equal, incomparable;
  * fuzz ground-truth misses, listed per site (not a percentage).
With --bc it also maps each site of the largest pooled sets back to the
IR: what the callee operand is (a load from struct field / global /
argument / phi ...), so a pooled set can be named by its pointer.

No LLVM-CFI fallback: their compare_approaches.py (hard-coded
ENABLE_FALLBACK_TO_LLVM_CFI) replaces every EMPTY site answer of every
approach with LLVM-CFI's answer, for AICT and recall alike, so a tool
that resolves nothing scores as LLVM-CFI. Here an empty site is empty.

Inputs are eval/65's merged layout (keys already aligned to LLVM-CFI's
strings) plus the artifact's pre-computed LLVM-CFI/KG/HPCFI logs.

usage: sok-persite.py --merged DIR --opt O0 --prog httpd__httpd
         [--ref ORCFL] [--bc file.bc] [--top 8] [--json out.json]
"""
import argparse, collections, json, os, re, subprocess, sys, tempfile
from pathlib import Path

ART = Path(os.environ.get('KA_SOK_ROOT', Path.home() / 'fast/ka-scratch/sok-mlta'))


def norm(t):
    """Their compare_approaches.py rule: drop ONE numeric clone suffix
    (LTO-internalized names differ between builds: register_hook.22985)."""
    head, _, tail = t.rpartition('.')
    return head if head and tail.isnumeric() else t


_DEMANGLED = {}


def demangle_all(names):
    """Batch-demangle Itanium names (the fuzz GT records demangled C++
    names; the tools emit mangled symbols)."""
    todo = sorted({n for n in names if n.startswith('_Z') and n not in _DEMANGLED})
    if not todo:
        return
    out = subprocess.run(['llvm-cxxfilt-18'], input='\n'.join(todo), text=True,
                         capture_output=True, check=True).stdout.split('\n')
    for n, d in zip(todo, out):
        _DEMANGLED[n] = d


def canon(t):
    """Name used for comparison: clone suffix dropped (their rule), C++
    demangled, and libc alias spellings unified -- the GT symbolizer
    records whichever alias the address resolved to (read/__read,
    fstat/fstat64, mmap/mmap64), so those are one function."""
    t = norm(_DEMANGLED.get(t, t))
    if t.startswith('__') and not t.startswith('___') and '::' not in t:
        t = t[2:]
    if t.endswith('64') and t[:-2] in LIBC64:
        t = t[:-2]
    return t


LIBC64 = {'fstat', 'stat', 'lstat', 'mmap', 'lseek', 'open', 'pread', 'pwrite',
          'ftruncate', 'truncate', 'fopen', 'fseeko', 'ftello', 'readdir',
          'fstatat', 'openat', 'statfs', 'fstatfs', 'getrlimit', 'setrlimit',
          'fcntl', 'creat', 'sendfile'}


def nset(v):
    return frozenset(canon(t) for t in v)


def load_approaches(merged, opt, prog):
    out = {}
    raw = []
    base0 = Path(merged) / opt
    for d in base0.iterdir():
        f = d / 'parsed_log' / f'{prog}.json'
        if d.is_dir() and f.exists():
            raw += [t for v in json.load(open(f)).values() for t in v]
    demangle_all(raw)
    base = Path(merged) / opt
    for d in sorted(base.iterdir()):
        if not d.is_dir() or d.name in ('common',) or d.name.startswith('pair-'):
            continue
        f = d / 'parsed_log' / f'{prog}.json'
        if f.exists():
            name = {'ORCFL-full': 'ORCFL'}.get(d.name, d.name)
            out[name] = {k: nset(v) for k, v in json.load(open(f)).items()}
    pre = ART / 'pre-computed/soundness' / opt
    for tool, name in (('LLVM-CFI', 'LLVM-CFI'), ('KG', 'KallGraph'), ('HPCFI', 'HPCFI')):
        f = pre / tool / 'parsed_log' / f'{prog}.json'
        if f.exists():
            out[name] = {k: nset(v) for k, v in json.load(open(f)).items()}
    return out


def boundary_suffix(a, b):
    return a == b or a.endswith('/' + b) or b.endswith('/' + a)


def load_gt(prog, keys):
    f = ART / 'fuzz_groundtruth' / f'{prog}.json'
    if not f.exists():
        return {}
    gt = {}
    for gk, targets in json.load(open(f)).items():
        m = [k for k in keys if boundary_suffix(gk, k)]
        if m:
            gt.setdefault(max(m, key=len), set()).update(canon(t) for t in targets)
    return gt


BUCKETS = ((0, 0), (1, 1), (2, 5), (6, 20), (21, 100), (101, 10**9))


def hist(ans):
    h = collections.Counter()
    for v in ans.values():
        for lo, hi in BUCKETS:
            if lo <= len(v) <= hi:
                h[(lo, hi)] += 1
    return ' '.join(f"{lo if lo == hi else f'{lo}-{hi if hi < 10**9 else ''}'}:{h[(lo, hi)]}"
                    for lo, hi in BUCKETS)


def pooled_sets(ans, min_sites=3, min_width=10):
    g = collections.defaultdict(list)
    for k, v in ans.items():
        if len(v) >= min_width:
            g[v].append(k)
    groups = [(s, ks) for s, ks in g.items() if len(ks) >= min_sites]
    groups.sort(key=lambda x: -(len(x[0]) * len(x[1])))
    return groups


# ---- IR mapping (--bc): site key -> callee-operand description ---------
def ir_callee_origins(bc):
    """Map 'file:line' -> list of callee-operand descriptions."""
    with tempfile.NamedTemporaryFile(suffix='.ll') as t:
        subprocess.run(['llvm-dis-18', bc, '-o', t.name], check=True)
        text = open(t.name, encoding='utf-8', errors='replace').read().split('\n')
    files, scopes, locs = {}, {}, {}
    for ln in text:
        m = re.match(r'!(\d+) = (?:distinct )?!(\w+)\((.*)\)$', ln)
        if not m:
            continue
        nid, kind, body = m.groups()
        if kind == 'DIFile':
            fm = re.search(r'filename: "([^"]*)"', body)
            files[nid] = fm.group(1) if fm else '?'
        elif kind in ('DISubprogram', 'DILexicalBlock', 'DILexicalBlockFile'):
            fm = re.search(r'\bfile: !(\d+)', body)
            if fm:
                scopes[nid] = fm.group(1)
        elif kind == 'DILocation':
            lm = re.search(r'line: (\d+)', body)
            sm = re.search(r'scope: !(\d+)', body)
            if lm and sm:
                locs[nid] = (lm.group(1), sm.group(1))
    out = collections.defaultdict(list)
    defs = {}
    fn = None
    for ln in text:
        if ln.startswith('define '):
            fm = re.search(r'@("?[^"(]+"?)\(', ln)
            fn = fm.group(1) if fm else '?'
            defs = {}
            continue
        dm = re.match(r'\s*(%[\w.$-]+) = (.*)$', ln)
        if dm:
            defs[dm.group(1)] = dm.group(2)
        cm = re.search(r'(?:call|invoke) [^@%]*?(%[\w.$-]+)\(', ln)
        if not cm or 'asm ' in ln:
            continue
        dbg = re.search(r'!dbg !(\d+)', ln)
        if not dbg or dbg.group(1) not in locs:
            continue
        line, scope = locs[dbg.group(1)]
        fname = files.get(scopes.get(scope, ''), '?')
        out[f'{fname}:{line}'].append(f'{fn}: ' + describe(cm.group(1), defs))
    return out


def describe(v, defs, depth=0):
    d = defs.get(v)
    if d is None:
        return f'{v} (argument)' if depth == 0 else v
    if d.startswith('load '):
        p = re.search(r', ptr (%[\w.$-]+|@[\w.$"-]+)', d)
        src = p.group(1) if p else '?'
        if src.startswith('@'):
            return f'load global {src}'
        g = defs.get(src, '')
        gm = re.match(r'getelementptr (?:inbounds )?(%[\w.$"]+|\[[^\]]+\]|i8), ptr (%[\w.$-]+|@[\w.$"-]+)(.*)', g)
        if gm:
            idx = re.findall(r'i(?:32|64) (-?\d+|%[\w.$-]+)', gm.group(3))
            return f'load {gm.group(1)}{idx} of {gm.group(2)}'
        if depth < 2 and src in defs:
            return 'load *(' + describe(src, defs, depth + 1) + ')'
        return f'load *{src}'
    op = d.split(' ')[0]
    return f'{op} ...'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--merged', required=True)
    ap.add_argument('--opt', required=True)
    ap.add_argument('--prog', required=True)
    ap.add_argument('--ref', default='ORCFL')
    ap.add_argument('--bc')
    ap.add_argument('--top', type=int, default=6)
    ap.add_argument('--json')
    a = ap.parse_args()

    A = load_approaches(a.merged, a.opt, a.prog)
    if a.ref not in A:
        sys.exit(f'!! reference {a.ref} has no answer for {a.prog}: {sorted(A)}')
    ref = A[a.ref]
    gt = load_gt(a.prog, ref.keys())
    report = {'prog': a.prog, 'opt': a.opt, 'approaches': {}}

    print(f'# {a.prog} {a.opt}: {len(A)} approaches, reference {a.ref}, '
          f'{len(gt)} GT sites')
    print('\n## Width histogram (sites by #targets) and GT misses')
    for n, ans in sorted(A.items()):
        miss = [(k, t) for k, ts in gt.items() for t in sorted(ts)
                if k in ans and t not in ans[k]]
        absent = [k for k in gt if k not in ans]
        tot = sum(len(v) for v in ans.values())
        print(f'{n:18} sites={len(ans):5} mean={tot / max(len(ans), 1):7.2f} '
              f'max={max((len(v) for v in ans.values()), default=0):5} | {hist(ans)} '
              f'| GT-miss={len(miss)} GT-site-absent={len(absent)}')
        report['approaches'][n] = {'sites': len(ans), 'targets': tot,
                                   'gt_miss': miss, 'gt_absent': absent}

    print(f'\n## GT misses per site (approach: site -> missed targets)')
    for n in sorted(A):
        miss = report['approaches'][n]['gt_miss']
        if not miss:
            continue
        by = collections.defaultdict(list)
        for k, t in miss:
            by[k].append(t)
        items = list(by.items())
        print(f'{n}: {len(miss)} missed at {len(by)} sites')
        for k, ts in items[:a.top]:
            print(f'   {k} -> {ts[:4]}{" ..." if len(ts) > 4 else ""}')
        if len(items) > a.top:
            print(f'   ... {len(items) - a.top} more sites')

    print(f'\n## Pooled sets (>=3 sites sharing one identical set of >=10 targets)')
    pooled_ref = pooled_sets(ref)
    for n in sorted(A):
        g = pooled_sets(A[n])
        cov = sum(len(ks) for _, ks in g)
        print(f'{n:18} groups={len(g):4} sites-in-groups={cov:5} '
              + ' '.join(f'[{len(s)}x{len(ks)}]' for s, ks in g[:6]))

    print(f'\n## Per-site vs {a.ref} on common sites')
    for n in sorted(A):
        if n == a.ref:
            continue
        c = collections.Counter()
        extra = []
        for k in ref.keys() & A[n].keys():
            r, o = ref[k], A[n][k]
            c['equal' if r == o else 'ref-wider' if r > o else
              'ref-tighter' if r < o else 'incomparable'] += 1
            extra.append((len(r - o), len(o - r), k))
        extra.sort(reverse=True)
        print(f'{n:18} common={sum(c.values()):5} equal={c["equal"]:5} '
              f'{a.ref}-wider={c["ref-wider"]:5} {a.ref}-tighter={c["ref-tighter"]:5} '
              f'incomparable={c["incomparable"]:5} | '
              f'{a.ref}-only targets={sum(x for x, _, _ in extra)} '
              f'{n}-only targets={sum(y for _, y, _ in extra)}')

    if a.bc and pooled_ref:
        print(f'\n## {a.ref} pooled sets mapped to callee operands ({a.bc})')
        orig = ir_callee_origins(a.bc)
        for s, ks in pooled_ref[:a.top]:
            print(f'\n[{len(s)} targets x {len(ks)} sites] e.g. {sorted(s)[:5]}')
            kinds = collections.Counter()
            for k in ks:
                m = [o for ok, os_ in orig.items() if boundary_suffix(k, ok) for o in os_]
                for o in m:
                    kinds[o.split(': ', 1)[1]] += 1
            for kd, cnt in kinds.most_common(8):
                print(f'   {cnt:4}  {kd}')
            others = {n: sum(len(A[n][k]) for k in ks if k in A[n]) /
                      max(1, sum(1 for k in ks if k in A[n]))
                      for n in sorted(A) if n != a.ref}
            print('   same sites, mean width elsewhere: ' +
                  ' '.join(f'{n}={w:.1f}' for n, w in others.items()))

    if a.json:
        json.dump(report, open(a.json, 'w'), indent=1, default=list)


if __name__ == '__main__':
    main()
