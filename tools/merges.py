#!/usr/bin/env python3
"""Replay a --cfl-dump-merges log: which union first put X and Y in one class, and why.
usage: merges.py LOG NAME-X NAME-Y        (names are substrings; first dense id whose name/alias matches)
       merges.py LOG cN cM                (dense ids)
Prints the decisive union (cause: join key + issuing pointer, or scc), then the union-count context."""
import re, sys
log, X, Y = sys.argv[1:4]
names = {}; alias = {}
ev = []
for line in open(log, errors='replace'):
    t = line.rstrip('\n').split('\t')
    if t[0] == 'N': names[int(t[1])] = t[2]
    elif t[0] == 'A': alias.setdefault(int(t[1]), []).append(t[2])
    elif t[0] == 'M': ev.append((int(t[1]), int(t[2]), t[3], t[4], t[5], t[6], t[7]))  # a b why keyO keyName keyS ptr
def resolve(q):
    if re.fullmatch(r'c\d+', q): return int(q[1:])
    for d, nm in names.items():
        if q in nm: return d
    for d, al in alias.items():
        if any(q in a for a in al): return d
    sys.exit(f"no node named like {q!r}")
x, y = resolve(X), resolve(Y)
print(f"X = c{x} {names.get(x,'?')}\nY = c{y} {names.get(y,'?')}")
par = {}
def find(u):
    while par.get(u, u) != u:
        par[u] = par.get(par[u], par[u]); u = par[u]
    return u
def nm(d): return names.get(d, '?')
for i, (a, b, why, ko, kn, ks, p) in enumerate(ev):
    ra, rb = find(a), find(b)
    if ra != rb: par[rb] = ra
    if find(x) == find(y):
        print(f"joined at union #{i} of {len(ev)}: c{a} [{nm(a)}] + c{b} [{nm(b)}]  why={why}", end='')
        if why == 'join': print(f"  key=(r{ko} {kn},s{ks}) by-ptr=c{p} [{nm(int(p))}]")
        else: print()
        break
else:
    print("never joined")
