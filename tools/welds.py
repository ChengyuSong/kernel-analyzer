#!/usr/bin/env python3
"""Replay a --cfl-dump-merges log and tell how the largest cluster formed.

A cluster class anchors the origins whose cells it holds (K lines: first
key inserts; M lines: unions in solve order, a join naming its key and the
pointer whose sweep issued it). Origins carry labels (R lines: what the
program made them as). The replay follows the class that ends with the
most origins and reports, in order, the unions that grew it: which pointer
caused each, and which labels each brought in for the first time.

usage: welds.py LOG [--top N] [--story N]
"""
import argparse, collections, re

ap = argparse.ArgumentParser()
ap.add_argument('log')
ap.add_argument('--top', type=int, default=25)
ap.add_argument('--story', type=int, default=40)
ap.add_argument('--pairs', action='store_true',
                help='print one (pointer class, key origin) per top '
                     'incompatible group, for --cfl-trace-func and welds-why.py')
args = ap.parse_args()

names, rkind, rlabel, rname, ctype = {}, {}, {}, {}, {}
ev = []
for line in open(args.log, errors='replace'):
    t = line.rstrip('\n').split('\t')
    if t[0] == 'N':
        names[int(t[1])] = t[2]
    elif t[0] == 'R':
        r = int(t[1]); rkind[r] = t[2]; rlabel[r] = t[3]; rname[r] = t[4]
    elif t[0] == 'T':
        ctype[int(t[1])] = t[2]
    elif t[0] == 'K':
        ev.append(('K', int(t[1]), int(t[2]), int(t[3]), int(t[4]), int(t[5])))
    elif t[0] == 'M':
        ptr = int(t[7]) if t[7] != '-' else None
        ko = int(t[4]) if t[4] != '-' else None
        cell = int(t[8]) if len(t) > 8 and t[8] not in ('-', '4294967295') else None
        ev.append(('M', int(t[1]), int(t[2]), t[3], ko, ptr, cell))


def family(r):
    """Coarse label: what kind of thing the program made this origin as."""
    k, l = rkind.get(r, '?'), rlabel.get(r, '?')
    base = k.split('+')[0]
    if base == 'fn':
        return 'fn'
    if base == 'heap':
        return 'heap'
    m = re.search(r'%(struct|union)\.([A-Za-z0-9_]+)', l)
    if m:
        s = m.group(2)
        return ('id:' if base in ('cell-id', 'val-id') else '') + 'S:' + s
    if re.search(r'x i8\]|^i8\b|x i16\]', l):
        return ('id:' if base in ('cell-id', 'val-id') else '') + 'chardata'
    if 'ptr' in l or '*' in l:
        return ('id:' if base in ('cell-id', 'val-id') else '') + 'ptr'
    if re.search(r'\bi(32|64|16)\b', l):
        return ('id:' if base in ('cell-id', 'val-id') else '') + 'int'
    return base + ':?'


def access(cell):
    m = re.match(r'%(struct|union)\.([A-Za-z0-9_]+)', ctype.get(cell, ''))
    return m.group(2) if m else None


def rule(ko, cell):
    """The strict rule at a join: the dereference accesses struct A; the
    key's origin was made as struct X. Compatible iff X == A."""
    A = access(cell)
    f = family(ko) if ko is not None else '?'
    m = re.match(r'(id:)?S:(.*)', f)
    if A is None or not m:
        return 'unknown'
    return 'compatible' if m.group(2) == A else 'incompatible'


rulecount = collections.Counter()
example = {}
incompat = collections.Counter()
par = {}
def find(u):
    root = u
    while par.get(root, root) != root:
        root = par[root]
    while par.get(u, u) != root:
        nxt = par[u]; par[u] = root; u = nxt
    return root

origins = collections.defaultdict(set)   # class rep -> anchored origins
# Pass 1: final class membership of origins, to pick the target.
for e in ev:
    if e[0] == 'K':
        _, c, o, s, p, cl = e
        origins[find(c)].add(o)
    else:
        _, a, b = e[:3]
        ra, rb = find(a), find(b)
        if ra != rb:
            par[rb] = ra
            if origins.get(rb):
                origins[ra] |= origins.pop(rb)
final = max(origins, key=lambda c: len(origins[c]))
target_members = {u for u in set(par) | set(origins) if find(u) == final}
print(f"largest cluster: c{final} with {len(origins[final])} origins "
      f"({len(target_members)} dense nodes)  {names.get(final, '')[:70]}")
fam = collections.Counter(family(r) for r in origins[final])
print("families in it:", ', '.join(f"{f} {n}" for f, n in fam.most_common(14)))

# Pass 2: replay again, following every class that ends in the target.
par.clear()
origins = collections.defaultdict(set)
fams = collections.defaultdict(collections.Counter)
def nm(d):
    return names.get(d, '?')[:60] if d is not None else '-'
story = []
byptr = collections.Counter()
byptrNew = collections.defaultdict(set)
for i, e in enumerate(ev):
    if e[0] == 'K':
        _, c, o, s, p, cl = e
        rc = find(c)
        origins[rc].add(o)
        fams[rc][family(o)] += 1
        continue
    _, a, b, why, ko, ptr, cell = e
    ra, rb = find(a), find(b)
    if ra == rb:
        continue
    if why == 'join' and (a in target_members or b in target_members):
        verdict = rule(ko, cell)
        rulecount[verdict] += 1
        if verdict == 'incompatible':
            g = (nm(ptr), access(cell), family(ko))
            incompat[g] += 1
            example.setdefault(g, (ptr, ko))
    inTarget = a in target_members or b in target_members
    if inTarget and origins.get(ra) and origins.get(rb):
        fa, fb = set(fams[ra]), set(fams[rb])
        # The union welds two non-empty clusters: what each side was.
        newfam = (fa ^ fb)
        small, big = (ra, rb) if len(origins[ra]) < len(origins[rb]) else (rb, ra)
        story.append((i, why, ko, ptr, len(origins[ra]), len(origins[rb]),
                      sorted(fams[small].items(), key=lambda x: -x[1])[:4],
                      sorted(fams[big].items(), key=lambda x: -x[1])[:4]))
        key = nm(ptr) if why == 'join' else why
        byptr[key] += 1
        byptrNew[key] |= newfam
    par[rb] = ra
    if origins.get(rb):
        origins[ra] |= origins.pop(rb)
    if fams.get(rb):
        fams[ra].update(fams.pop(rb))

print(f"\n{len(story)} unions of two non-empty clusters built it; the first "
      f"{min(args.story, len(story))}:")
for (i, why, ko, ptr, na, nb, sf, bf) in story[:args.story]:
    k = f"key r{ko} {rname.get(ko, '')[:40]} [{family(ko)}]" if ko is not None else ''
    print(f"  #{i} {why} {na}+{nb} {k} by {nm(ptr)}")
    print(f"       small side: {', '.join(f'{f} {n}' for f, n in sf)}")
    print(f"       big side:   {', '.join(f'{f} {n}' for f, n in bf)}")
print(f"\njoins into it by the strict rule (access struct vs key origin's label): "
      + ', '.join(f'{k} {v}' for k, v in rulecount.most_common()))
print("top incompatible (pointer, access struct, key label):")
for (p_, a_, f_), n in incompat.most_common(args.top):
    print(f"  {n:6d}  {p_}  as {a_}  key {f_}")
if args.pairs:
    print("PAIRS " + ' '.join(f"{example[g][0]}:r{example[g][1]}"
                              for g, _ in incompat.most_common(args.top)))
print(f"\npointers whose joins welded non-empty clusters into it (top {args.top}):")
for k, n in byptr.most_common(args.top):
    print(f"  {n:6d}  {k}")
