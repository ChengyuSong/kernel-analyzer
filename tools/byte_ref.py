#!/usr/bin/env python3
"""Byte-exact reference flows-to solver over a --cfl-dump-agraph RAW dump.

Semantics (the lazily materialized address model):
  * an address is (object, byte offset); addresses are materialized on
    first use; a variable-index GEP yields (object, X) = any offset;
  * pts(v) = set of addresses; a GEP by +k maps every (o, off) to
    (o, off+k) and (o, X) to (o, X);
  * cells are addresses: `*p = v` writes pts(v) into every address in
    pts(p); `x = *p` reads them back; (o, X) reads/writes every cell of o;
  * objects = allocation sites (each alloca / global / function /
    object node is one object); NO cluster welding, NO identity roots,
    context-insensitive: actual->formal and return->callsite copies;
  * indirect calls are resolved by the reference itself: callee =
    functions in pts(callee expression) that pass the solver's own
    type-compatibility filter (the C list in .raw.icalls), wired
    iteratively until no new pair appears.
Integer arithmetic on pointers (copy:add/sub/...) is treated as a
copy that keeps the offset (optimistic) unless --arith-x is given
(then it smears to (o, X)).

usage: byte_ref.py <prefix> [--arith-x] [--no-canon] <target-substring>...
"""
import sys, collections, time

args = [a for a in sys.argv[1:] if not a.startswith("--")]
opts = {a for a in sys.argv[1:] if a.startswith("--")}
pfx = args[0] + ".raw"
targets = args[1:]
ARITH_X = "--arith-x" in opts
USE_CANON = "--no-canon" not in opts

nodes = {}
sizes_of = {}    # node -> object extent in bytes when the IR states it
alloc_sites = set()  # allocation-call value nodes: their own address
for ln in open(pfx + ".nodes"):
    p = ln.rstrip("\n").split(" ", 2)
    nid, kind = int(p[0]), p[1]
    rest = p[2] if len(p) > 2 else ""
    ptr = None
    if rest.endswith(" alloc"):
        rest = rest[:-6]
        alloc_sites.add(nid)
    if " size=" in rest:
        rest, sv = rest.rsplit(" size=", 1)
        sizes_of[nid] = int(sv)
    if kind == "deref" and " ptr=" in rest:
        rest, pv = rest.rsplit(" ptr=", 1)
        ptr = int(pv)
        if ptr < 0:
            ptr = None
    nodes[nid] = (kind, rest, ptr)
# Offsets are bounded: past a known extent the address is infeasible
# (dropped); for objects of unknown extent, past HEAP_CAP bytes or more
# than OFFS_CAP distinct offsets the object degrades to (o, X).
HEAP_CAP = 4096
OFFS_CAP = 256
canon = {}
if USE_CANON:
    for ln in open(pfx + ".canon"):
        a, b = ln.split()
        canon[int(a)] = int(b)


def find(n):
    while n in canon:
        n = canon[n]
    return n


raw_edges = []
for ln in open(pfx + ".edges"):
    s, t, k = ln.split()
    raw_edges.append((find(int(s)), find(int(t)), k))
funcs = {}       # name -> dict(fn, ret, vararg, nparams, params{i: node})
for ln in open(pfx + ".funcs"):
    p = ln.split()
    if p[0] == "F":
        funcs[p[1]] = dict(fn=find(int(p[2])), ret=(find(int(p[3])) if int(p[3]) >= 0 else None),
                           vararg=p[4] == "1", nparams=int(p[5]), params={})
    else:
        funcs[p[1]]["params"][int(p[2])] = find(int(p[3]))
sites = {}       # id -> dict(callee, res, loc, fn, actuals{i: node}, cands[])
for ln in open(pfx + ".icalls"):
    p = ln.rstrip("\n").split(" ")
    if p[0] == "I":
        sites[int(p[1])] = dict(callee=find(int(p[2])), res=(find(int(p[3])) if int(p[3]) >= 0 else None),
                                loc=p[4], fn=p[5], actuals={}, cands=[])
    elif p[0] == "A":
        sites[int(p[1])]["actuals"][int(p[2])] = find(int(p[3]))
    else:
        sites[int(p[1])]["cands"].append(p[2])
fn_of_node = {}  # function OBJECT node -> name (filled after addrof is read)

# ---- graph in solver form -------------------------------------------------
addrof = collections.defaultdict(set)      # value node -> object nodes it addresses
copies = collections.defaultdict(list)     # s -> [(t, shift)] shift: int or 'X'
stores = collections.defaultdict(list)     # cell -> [value]
loads = collections.defaultdict(list)      # cell -> [result]
cell_ptr = {}                              # cell -> ptr (from d edges / nodes)
for n, (k, _, ptr) in nodes.items():
    if k == "deref" and ptr is not None:
        cell_ptr[find(n)] = find(ptr)
edge_kinds = collections.Counter()
for s, t, k in raw_edges:
    if s == t and k != "d":
        continue
    edge_kinds[k] += 1
    if k == "d":
        # value -> object node: address-of; pointer -> deref node: cell
        if nodes.get(t, ("?",))[0].startswith("obj"):
            addrof[s].add(t)
        else:
            cell_ptr[t] = s
        continue
    sd, td = nodes.get(s, ("?",))[0] == "deref", nodes.get(t, ("?",))[0] == "deref"
    if k == "store" or (td and not sd):
        stores[t].append(s)
    elif k == "load" or (sd and not td):
        loads[s].append(t)
    elif k == "memcpy":
        continue  # cell->cell bulk copy: not modeled (counted)
    elif k.startswith("gep:"):
        copies[s].append((t, int(k[4:])))
    elif k == "gepX":
        copies[s].append((t, "X"))
    elif k.startswith("copy:") and k[5:] in ("add", "sub", "mul", "and", "or", "xor",
                                             "lshr", "shl", "ashr", "ptrtoint", "inttoptr"):
        copies[s].append((t, "X" if ARITH_X else 0))
    else:
        copies[s].append((t, 0))
print(f"nodes {len(nodes)}, edges {dict(edge_kinds)}, sites {len(sites)}, funcs {len(funcs)}")

# ---- objects and addresses ------------------------------------------------
# Objects: in this solver a global, function, alloca or allocation-call
# VALUE node is itself the address of the object it creates (origin);
# the factory's object nodes appear only behind explicit address-of
# edges (opaque/fresh heap objects).
ORIGIN_KINDS = {"global", "fn", "inst:alloca"}
obj_of_node = {}
self_addr = set()
for n, (k, name, _) in nodes.items():
    n2 = find(n)
    if k in ORIGIN_KINDS or n in alloc_sites:
        obj_of_node[n2] = n2
        self_addr.add(n2)
for s, objs in addrof.items():
    for o in objs:
        obj_of_node[o] = o
print(f"objects: {len(obj_of_node)} ({len(self_addr)} self-addressed value origins, "
      f"{sum(len(v) for v in addrof.values())} address-of edges); kinds "
      f"{dict(collections.Counter(nodes[o][0] for o in obj_of_node))}")
for name, f in funcs.items():
    fn_of_node.setdefault(f["fn"], name)
    for o in addrof.get(f["fn"], ()):
        fn_of_node.setdefault(o, name)
print(f"function objects: {len(fn_of_node)} of {len(funcs)} address-taken functions")
addr_id = {}     # (obj, off) -> id
addr_key = []    # id -> (obj, off)
addrs_of_obj = collections.defaultdict(list)


def addr(o, off):
    key = (o, off)
    i = addr_id.get(key)
    if i is None:
        i = len(addr_key)
        addr_id[key] = i
        addr_key.append(key)
        addrs_of_obj[o].append(i)
    return i


pts = collections.defaultdict(int)      # node -> bitset over address ids
content = collections.defaultdict(int)  # address id -> bitset
for n in self_addr:
    pts[n] |= 1 << addr(n, 0)
for s, objs in addrof.items():
    for o in objs:
        pts[s] |= 1 << addr(o, 0)


def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


obj_size = {n: sizes_of[n] for n in obj_of_node if n in sizes_of}


def shift(bs, k):
    if k == 0:
        return bs
    out = 0
    for a in bits(bs):
        o, off = addr_key[a]
        if k == "X" or off == "X":
            out |= 1 << addr(o, "X")
            continue
        noff = off + k
        S = obj_size.get(o)
        if S is not None:
            if noff < 0 or noff >= S:
                continue  # outside the object: infeasible address
        elif abs(noff) > HEAP_CAP or len(addrs_of_obj[o]) > OFFS_CAP:
            out |= 1 << addr(o, "X")  # unknown extent: degrade to range
            continue
        out |= 1 << addr(o, noff)
    return out


def cells_read(a):
    """addresses whose content a read at address a sees"""
    o, off = addr_key[a]
    if off == "X":
        return addrs_of_obj[o]
    xi = addr_id.get((o, "X"))
    return [a] if xi is None else [a, xi]


def cells_written(a):
    o, off = addr_key[a]
    if off == "X":
        return addrs_of_obj[o]  # writes through (o,X) may hit any cell
    return [a]


cells_of_ptr = collections.defaultdict(list)
for c, p in cell_ptr.items():
    if c in stores or c in loads:
        cells_of_ptr[p].append(c)
stored_through = collections.defaultdict(list)
for c, vs in stores.items():
    for v in vs:
        stored_through[v].append(c)
readers_of_addr = collections.defaultdict(set)  # address -> cells reading it
known = collections.defaultdict(int)            # cell -> addresses wired
wired = set()                                   # (site, fname)


def solve():
    changed = True
    rounds = 0
    while changed:
        changed = False
        rounds += 1
        print(f"  round {rounds}: {len(addr_key)} addresses, "
              f"{sum(1 for p in pts.values() if p)} pointed nodes, {time.time()-t0:.0f}s",
              flush=True)
        for v, cs in stored_through.items():
            pv = pts[v]
            if not pv:
                continue
            for c in cs:
                for a in bits(known[c]):
                    for w in cells_written(a):
                        if pv & ~content[w]:
                            content[w] |= pv
                            changed = True
        for a, cs in list(readers_of_addr.items()):
            ca = content[a]
            if not ca:
                continue
            for c in cs:
                for x in loads[c]:
                    if ca & ~pts[x]:
                        pts[x] |= ca
                        changed = True
        work = collections.deque(n for n, p in pts.items() if p)
        inwork = set(work)
        pops = 0
        maxpop = 0
        while work:
            n = work.popleft()
            inwork.discard(n)
            pn = pts[n]
            pops += 1
            if pops % 5000 == 0:
                print(f"    pops {pops}: queue {len(work)}, {len(addr_key)} addresses, "
                      f"max |pts| seen {maxpop}, {time.time()-t0:.0f}s", flush=True)
            if pops % 50000 == 0:
                top = sorted(((bin(p).count("1"), m) for m, p in pts.items()), reverse=True)[:8]
                for cnt2, m in top:
                    objset = {addr_key[a][0] for a in bits(pts[m])}
                    okinds = collections.Counter(nodes[o][0] for o in objset)
                    sample = [nodes[o][1][:28] for o in list(objset)[:6]]
                    print(f"      top: n{m} {nodes[m][0]:10} {nodes[m][1][:55]} |pts|={cnt2} "
                          f"objects={len(objset)} kinds={dict(okinds)} e.g. {sample}", flush=True)
            # Name the pointers that first cross each size threshold: the
            # widest sets identify the confluence points of the graph.
            cnt = bin(pn).count("1")
            if cnt > maxpop and cnt >= 64 and (cnt >= 2 * maxpop or maxpop < 64):
                objs = len({addr_key[a][0] for a in bits(pn)})
                print(f"    widest so far: n{n} {nodes[n][1][:60]} |pts|={cnt} "
                      f"over {objs} objects", flush=True)
            maxpop = max(maxpop, cnt)
            for t, k in copies[n]:
                nv = shift(pn, k)
                if nv & ~pts[t]:
                    pts[t] |= nv
                    changed = True
                    if t not in inwork:
                        work.append(t)
                        inwork.add(t)
            for c in cells_of_ptr.get(n, ()):
                new = pn & ~known[c]
                if not new:
                    continue
                known[c] |= new
                changed = True
                for a in bits(new):
                    for v in stores.get(c, ()):
                        for w in cells_written(a):
                            if pts[v] & ~content[w]:
                                content[w] |= pts[v]
                    if loads.get(c):
                        for r in cells_read(a):
                            readers_of_addr[r].add(c)
                            if content[r] & ~pts[loads[c][0]]:
                                for x in loads[c]:
                                    if content[r] & ~pts[x]:
                                        pts[x] |= content[r]
                                        if x not in inwork:
                                            work.append(x)
                                            inwork.add(x)
    return rounds


def resolve_and_wire():
    new = 0
    for sid, S in sites.items():
        p = pts[S["callee"]]
        if not p:
            continue
        fns = set()
        for a in bits(p):
            o, off = addr_key[a]
            if off == 0 and o in fn_of_node:
                fns.add(fn_of_node[o])
        for name in fns & set(S["cands"]):
            if (sid, name) in wired:
                continue
            wired.add((sid, name))
            new += 1
            f = funcs[name]
            for i, an in S["actuals"].items():
                if i in f["params"]:
                    copies[an].append((f["params"][i], 0))
            if f["ret"] is not None and S["res"] is not None:
                copies[f["ret"]].append((S["res"], 0))
    return new


t0 = time.time()
it = 0
while True:
    rounds = solve()
    new = resolve_and_wire()
    it += 1
    print(f"iteration {it}: {rounds} rounds, {len(addr_key)} addresses, "
          f"{len(wired)} pairs wired (+{new}), {time.time()-t0:.0f}s")
    if new == 0 or it > 12:
        break

# ---- report ------------------------------------------------------------
sizes = sorted((bin(p).count("1") for p in pts.values()), reverse=True)
print(f"pts size: max {sizes[0]}, #>1000: {sum(1 for s in sizes if s > 1000)}, "
      f"#>100: {sum(1 for s in sizes if s > 100)}, median {sizes[len(sizes)//2]}")
per_site = {}
for sid, S in sites.items():
    per_site[S["loc"]] = sorted(n for (s2, n) in wired if s2 == sid)
fan = [len(v) for v in per_site.values() if v]
print(f"icall sites resolved {len(fan)}/{len(sites)}, mean fanout {sum(fan)/max(1,len(fan)):.1f}, "
      f"median {sorted(fan)[len(fan)//2] if fan else 0}")
for tg in targets:
    hits = [S for S in sites.values() if tg in S["loc"]]
    for S in hits:
        print(f"site {S['loc']} in {S['fn']}: {len(per_site[S['loc']])} targets: {per_site[S['loc']][:12]}")
    ns = [n for n, v in nodes.items() if tg in v[1] and v[0] != "deref"]
    for n in ns[:3]:
        p = pts[find(n)]
        objs = collections.Counter(nodes[addr_key[a][0]][0] for a in bits(p))
        offs = collections.Counter(addr_key[a][1] for a in bits(p))
        print(f"value {nodes[n][1][:60]}: |pts|={bin(p).count('1')} objects-by-kind={dict(objs)} "
              f"offsets={sorted(offs.items(), key=lambda kv: -kv[1])[:8]}")
        print("   sample:", [f"{nodes[addr_key[a][0]][1][:30]}+{addr_key[a][1]}" for a in list(bits(p))[:10]])
