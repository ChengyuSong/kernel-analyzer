#!/usr/bin/env python3
"""Reference field-insensitive, context-insensitive inclusion-based
(Andersen) points-to over a --cfl-dump-agraph dump, with EXACT
per-object cells: no cluster welding, no identity roots. Used to test
whether a wide answer in the flows-to solver comes from the solver's
own quotients (welds, identity roots) or from the graph itself
(field-insensitivity + context-insensitive call/return wiring).

usage: andersen_ref.py <prefix> <target-name-substring> [<target2> ...]
reads <prefix>.nodes / .edges / .members written by --cfl-dump-agraph.
Approximations: origins are globals, functions, allocas, object nodes
and FRESH sub-objects (allocation-call results that the solver encodes
otherwise are not origins here); memcpy cell->cell edges are ignored.
"""
import sys, collections, time

pfx = sys.argv[1]
targets = sys.argv[2:]
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
members = collections.defaultdict(list)
try:
    for ln in open(pfx + ".members"):
        c, kind, name = ln.rstrip("\n").split(" ", 2)
        members[int(c)].append((kind, name))
except FileNotFoundError:
    pass


def locate(sub):
    hits = [n for n, v in nodes.items() if sub in v[2] and v[0] != "deref"]
    if not hits:
        hits = [c for c, ms in members.items() if any(sub in nm for _, nm in ms)]
    return hits[0] if hits else None


copies = collections.defaultdict(list)  # s -> [t]
stores = collections.defaultdict(list)  # cell -> [value]
loads = collections.defaultdict(list)   # cell -> [result]
kinds = collections.Counter()
for ln in open(pfx + ".edges"):
    s, t, k = ln.split()
    s, t = int(s), int(t)
    if s == t:
        continue
    kinds[k] += 1
    sd, td = nodes[s][0] == "deref", nodes[t][0] == "deref"
    if td and not sd:
        stores[t].append(s)
    elif sd and not td:
        loads[s].append(t)
    elif not sd and not td:
        copies[s].append(t)

ORIGIN_KINDS = {"global", "fn", "obj", "inst:alloca"}
origin_id = {}
for n, v in nodes.items():
    if v[0] in ORIGIN_KINDS or (v[0] == "syn" and "freshsub" in v[2]) or \
       any(k in ORIGIN_KINDS for k, _ in members.get(n, ())):
        origin_id[n] = len(origin_id)
print(f"nodes {N}, origins {len(origin_id)}, edges {dict(kinds)}")

pts = [0] * N                             # bitset over origin ids
content = collections.defaultdict(int)    # origin id -> bitset
for n, o in origin_id.items():
    pts[n] |= 1 << o
cells_of_ptr = collections.defaultdict(list)
for c in set(stores) | set(loads):
    if nodes[c][3] is not None:
        cells_of_ptr[nodes[c][3]].append(c)
stored_through = collections.defaultdict(list)  # value -> [cells]
for c, vs in stores.items():
    for v in vs:
        stored_through[v].append(c)
readers_of_obj = collections.defaultdict(set)   # origin -> cells reading it
known_objs = [0] * N                            # cell -> objects wired


def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


t0 = time.time()
rounds = 0
changed = True
while changed:
    changed = False
    rounds += 1
    # stored values -> object contents
    for v, cs in stored_through.items():
        pv = pts[v]
        if not pv:
            continue
        for c in cs:
            for o in bits(known_objs[c]):
                if pv & ~content[o]:
                    content[o] |= pv
                    changed = True
    # object contents -> load results
    for o, cs in readers_of_obj.items():
        co = content[o]
        for c in cs:
            for x in loads[c]:
                if co & ~pts[x]:
                    pts[x] |= co
                    changed = True
    # copies + cell wiring, to a local fixpoint
    work = collections.deque(n for n in range(N) if pts[n])
    inwork = [False] * N
    for n in work:
        inwork[n] = True
    while work:
        n = work.popleft()
        inwork[n] = False
        pn = pts[n]
        for t in copies[n]:
            if pn & ~pts[t]:
                pts[t] |= pn
                changed = True
                if not inwork[t]:
                    work.append(t)
                    inwork[t] = True
        for c in cells_of_ptr.get(n, ()):
            new = pn & ~known_objs[c]
            if not new:
                continue
            known_objs[c] |= new
            changed = True
            for o in bits(new):
                for v in stores.get(c, ()):
                    if pts[v] & ~content[o]:
                        content[o] |= pts[v]
                if loads.get(c):
                    readers_of_obj[o].add(c)
                    for x in loads[c]:
                        if content[o] & ~pts[x]:
                            pts[x] |= content[o]
                            if not inwork[x]:
                                work.append(x)
                                inwork[x] = True
print(f"fixpoint after {rounds} rounds, {time.time() - t0:.1f}s")
inv = {o: n for n, o in origin_id.items()}
sizes = sorted((bin(p).count("1") for p in pts), reverse=True)
print(f"pts size: max {sizes[0]}, #nodes >1000: {sum(1 for s in sizes if s > 1000)}, "
      f">100: {sum(1 for s in sizes if s > 100)}, median {sizes[len(sizes) // 2]}")
for tg in targets:
    n = locate(tg)
    if n is None:
        print(f"{tg}: not found")
        continue
    p = pts[n]
    ks = collections.Counter(nodes[inv[o]][0] for o in bits(p))
    print(f"{tg}: node {n} ({nodes[n][2][:60]}) |pts|={bin(p).count('1')} kinds={dict(ks)}")
    print("   sample:", [nodes[inv[o]][2][:40] for o in list(bits(p))[:12]])
