#!/usr/bin/env python3
"""Offline attribution of the flows-to value-flow graph's giant component.

usage: agraph_scc.py <prefix> <target-name-substring>
reads <prefix>.nodes / .edges / .members written by --cfl-dump-agraph;
removes one edge kind at a time to see which kind closes the cycles
of the component containing the target.
"""
import sys, collections
pfx, target = sys.argv[1], sys.argv[2]
nodes = {}
for ln in open(pfx + ".nodes"):
    p = ln.rstrip("\n").split(" ", 3)
    nid, kind, mem = int(p[0]), p[1], int(p[2])
    name = p[3] if len(p) > 3 else ""
    ptr = None
    if kind == "deref":
        q = name.rsplit(" ", 1)
        if len(q) == 2 and q[1].isdigit():
            name, ptr = q[0], int(q[1])
    nodes[nid] = (kind, mem, name, ptr)
N = max(nodes) + 1
edges = []
for ln in open(pfx + ".edges"):
    s, t, k = ln.split()
    edges.append((int(s), int(t), k))
members = collections.defaultdict(list)
try:
    for ln in open(pfx + ".members"):
        c, kind, name = ln.rstrip("\n").split(" ", 2)
        members[int(c)].append((kind, name))
except FileNotFoundError:
    pass
tgt = [n for n, v in nodes.items() if target in v[2] and v[0] != "deref"]
if not tgt:
    tgt = [c for c, ms in members.items() if any(target in nm for k, nm in ms)]
if not tgt:
    sys.exit(f"no node matches {target}")
tgt = tgt[0]
if members.get(tgt):
    print(f"(target sits in a presolve class of {len(members[tgt])} members)")
print(f"target node {tgt} = {nodes[tgt][2]} kind={nodes[tgt][0]} members={nodes[tgt][1]}")


def scc(keep):
    out = [[] for _ in range(N)]
    for s, t, k in edges:
        if keep(k) and s != t:
            out[s].append(t)
    idx = [0] * N; low = [0] * N; on = [False] * N; comp = [-1] * N
    stack = []; counter = 1; ncomp = 0
    for root in range(N):
        if idx[root]:
            continue
        work = [(root, 0)]
        idx[root] = low[root] = counter; counter += 1
        stack.append(root); on[root] = True
        while work:
            v, i = work[-1]
            if i < len(out[v]):
                work[-1] = (v, i + 1)
                w = out[v][i]
                if not idx[w]:
                    idx[w] = low[w] = counter; counter += 1
                    stack.append(w); on[w] = True
                    work.append((w, 0))
                elif on[w]:
                    low[v] = min(low[v], idx[w])
            else:
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == idx[v]:
                    while True:
                        w = stack.pop(); on[w] = False; comp[w] = ncomp
                        if w == v:
                            break
                    ncomp += 1
    sizes = collections.Counter(comp)
    return comp, sizes, out


def is_mem(k): return k in ("store", "load", "memcpy")
variants = [
    ("all", lambda k: True),
    ("-icall", lambda k: k != "icall"),
    ("-call", lambda k: k != "call"),
    ("-call-icall", lambda k: k not in ("call", "icall")),
    ("-ret", lambda k: k != "ret"),
    ("-mem", lambda k: not is_mem(k)),
    ("-icall-ret", lambda k: k not in ("icall", "ret")),
    ("-call-icall-ret", lambda k: k not in ("call", "icall", "ret")),
    ("-icall-mem", lambda k: k != "icall" and not is_mem(k)),
    ("-call-icall-mem", lambda k: k not in ("call", "icall") and not is_mem(k)),
    ("-f", lambda k: not k.startswith("f")),
]
print(f"\n{'variant':>18} {'largest':>8} {'#>100':>6} {'target-SCC':>10}")
results = {}
for name, keep in variants:
    comp, sizes, out = scc(keep)
    big = sizes.most_common(1)[0][1]
    n100 = sum(1 for c, s in sizes.items() if s > 100)
    tsz = sizes[comp[tgt]]
    results[name] = (comp, sizes, out)
    print(f"{name:>18} {big:>8} {n100:>6} {tsz:>10}")

comp, sizes, out = results["all"]
tc = comp[tgt]
members = [n for n in range(N) if comp[n] == tc]
print(f"\ntarget SCC (all edges): {len(members)} classes")
kinds = collections.Counter(nodes[n][0] for n in members)
print("  node kinds:", ", ".join(f"{k}={v}" for k, v in kinds.most_common(12)))
funcs = collections.Counter()
for n in members:
    nm = nodes[n][2]
    if "::" in nm:
        funcs[nm.split("::")[0].lstrip("*")] += 1
print(f"  functions: {len(funcs)}; top:", ", ".join(f"{f}({c})" for f, c in funcs.most_common(12)))
ek = collections.Counter(k for s, t, k in edges if comp[s] == tc and comp[t] == tc and s != t)
print("  intra-SCC edge kinds:", ", ".join(f"{k}={v}" for k, v in ek.most_common(14)))
ink = collections.Counter(k for s, t, k in edges if t == tgt)
print(f"  target in-edges by kind: {dict(ink)}")
for s, t, k in edges:
    if t == tgt:
        print(f"    {k:6} <- n{s} {nodes[s][0]} {nodes[s][2][:70]}")

# shortest cycle through the target within its SCC
inside = set(members)
adj = collections.defaultdict(list)
for s, t, k in edges:
    if s in inside and t in inside and s != t:
        adj[s].append((t, k))
par = {tgt: None}
q = [tgt]; closer = None; qi = 0
while qi < len(q) and closer is None:
    u = q[qi]; qi += 1
    for v, k in adj[u]:
        if v == tgt:
            closer = (u, k); break
        if v not in par:
            par[v] = (u, k); q.append(v)
if closer:
    path = []
    u, k = closer
    path.append((u, k))
    while par[u] is not None:
        pu, pk = par[u]
        path.append((pu, pk))
        u = pu
    path.reverse()
    print(f"\nshortest cycle through target: {len(path)} hops")
    prev = tgt
    for n, k in path:
        pass
    # print as target -k-> n1 -k-> n2 ... -k-> target
    seq = [(tgt, None)] + [(n, k) for n, k in path[1:]] if False else None
    # rebuild ordered: par chain gives nodes from tgt outward
    chain = []
    u = closer[0]
    while u is not None:
        chain.append(u)
        u = par[u][0] if par[u] else None
    chain.reverse()  # tgt ... closer
    for i, n in enumerate(chain):
        kind = "" if i == 0 else par[n][1]
        print(f"  {'-'+kind+'->' if kind else 'START':>12} n{n} {nodes[n][0]:14} {nodes[n][2][:80]}")
    print(f"  {'-'+closer[1]+'->':>12} back to target")
