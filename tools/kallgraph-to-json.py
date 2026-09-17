#!/usr/bin/env python3
"""KallGraph 'callgraph' output (file:line / count / callee names, blank-separated) -> {"file:line": [...]}"""
import sys, json
d={}; lines=[l.rstrip('\n') for l in open(sys.argv[1])]
i=0
while i < len(lines):
    if not lines[i].strip(): i+=1; continue
    key=lines[i]; n=int(lines[i+1]); d.setdefault(key,set()).update(lines[i+2:i+2+n]); i+=2+n
json.dump({k:sorted(v) for k,v in sorted(d.items())}, open(sys.argv[2],'w'), indent=1)
print(len(d),'sites',sum(len(v) for v in d.values()),'pairs')
