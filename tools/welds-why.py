#!/usr/bin/env python3
"""Why does a welding pointer hold an origin? Walk first arrivals back.

Input: a --cfl-trace-func=r<id>,... --cfl-trace-first log (stderr of
KAMain) and pairs PTR:rRID (welds.py --pairs). For each pair, start at the
first arrival of the origin at the pointer's class in the LAST solve, and
follow each arrival's source class back to the origin's seed. Every step
prints how the origin arrived (a-edge kind, merge with its join key and
pointer, bridge) and the class it arrived at.

usage: welds-why.py TRACELOG PTR:rRID [PTR:rRID ...]
"""
import re, sys

log, pairs = sys.argv[1], sys.argv[2:]
lines = open(log, errors='replace').read().split('\n')
# The last solve: after the last block of "TRACE root" lines.
starts = [i for i, l in enumerate(lines) if l.startswith('TRACE root')]
nroots = len(set(l.split(' = ')[0] for l in lines if l.startswith('TRACE root'))) or 1
last = starts[-1] if starts else 0
# Find the first line of the final block of root lines.
while last > 0 and lines[last - 1].startswith('TRACE root'):
    last -= 1
arr = {}   # (rid, cls) -> (how, from, rest)
pat = re.compile(r'^TRACE \+ c(\d+) s(\d+)(?: \[br\])? via (\S+) from c(\d+|\?)(.*)$')
for l in lines[last:]:
    m = pat.match(l)
    if not m:
        continue
    cls, how, frm, rest = int(m.group(1)), m.group(3), m.group(4), m.group(5)
    r = re.search(r'root=r(\d+)', rest)
    rid = int(r.group(1)) if r else None
    arr.setdefault((rid, cls), (how, None if frm == '?' else int(frm), rest.strip()))
rids = {k[0] for k in arr}
single = len(rids) == 1
for p in pairs:
    ptr, rid = p.split(':')
    ptr, rid = int(ptr), int(rid.lstrip('r'))
    key = (None if single else rid)
    print(f"== origin r{rid} at pointer class c{ptr}")
    cur, seen = ptr, set()
    if (key, cur) not in arr:
        print("   no arrival recorded at this class (it reached a class later merged into it)")
        continue
    for _ in range(60):
        if (key, cur) not in arr or cur in seen:
            break
        seen.add(cur)
        how, frm, rest = arr[(key, cur)]
        rest = re.sub(r'root=r\d+\s*', '', rest)
        print(f"   c{cur} via {how} from c{frm}: {rest[:200]}")
        if frm is None:
            break
        cur = frm
