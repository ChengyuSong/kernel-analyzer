#!/usr/bin/env python3
"""Coupler census.
  census.py select MERGES.tsv N        -> prints the first N cross-object coupler unions inside the universal
                                          cluster and writes roots.txt (comma list of key origins to trace)
  census.py attribute MERGES.tsv TRACE.log N -> for each coupler: the issuing pointer, its node kind, and the
                                          edge kind that delivered the key origin to that pointer's class
"""
import sys, re, collections
mode, mlog = sys.argv[1], sys.argv[2]
names={}; ev=[]
for line in open(mlog, errors='replace'):
    t=line.rstrip('\n').split('\t')
    if t[0]=='N': names[int(t[1])]=t[2]
    elif t[0]=='M': ev.append((int(t[1]),int(t[2]),t[3],t[4],t[5],t[6],t[7]))
def nm(d): return names.get(d,'?')
def couplers(N):
    par={}
    def find(u):
        while par.get(u,u)!=u: par[u]=par.get(par[u],par[u]); u=par[u]
        return u
    for a,b,*_ in ev:
        ra,rb=find(a),find(b)
        if ra!=rb: par[rb]=ra
    # the universal cluster = the largest final component
    comp=collections.Counter(find(d) for d in names); R=comp.most_common(1)[0][0]
    inU=set(d for d in names if find(d)==R)
    par={}; origins=collections.defaultdict(set); out=[]
    for i,(a,b,why,ko,kn,ks,p) in enumerate(ev):
        ra,rb=find(a),find(b)
        if ra==rb: continue
        oa,ob=set(origins[ra]),set(origins[rb])
        coal = why=='join' and oa and ob and not (oa&ob)
        par[rb]=ra; origins[ra]|=ob
        if why=='join': origins[ra].add(kn)
        if coal and a in inU and b in inU:
            pr=find(int(p)); members=[d for d in names if find(d)==pr]
            out.append((i,kn,ks,int(p),len(oa),len(ob),sorted(oa)[0],sorted(ob)[0],members))
            if len(out)>=N: break
    return out
N=int(sys.argv[-1])
if mode=='select':
    cs=couplers(N); roots=[]
    for i,kn,ks,p,la,lb,oa,ob,_m in cs:
        print(f"#{i} key=({kn},s{ks}) by-ptr=c{p}:{nm(p)[:50]} | {la} origins ({oa[:30]}) + {lb} origins ({ob[:30]})")
        if kn not in roots: roots.append(kn)
    open('roots.txt','w').write(','.join(roots)); print(len(roots),'roots ->', 'roots.txt')
else:
    tlog=sys.argv[3]
    rid={}  # filled from the FINAL iteration's root table (ids are re-minted per iteration)
    # last-iteration arrivals per root: first arrival per (root, class). Streamed: the
    # multi-root log is several GB; only the part after the last presolve line matters.
    last_off=0; off=0
    with open(tlog,'rb') as f:
        for raw in f:
            if raw.startswith(b'CallGraph: Pre-solve merge'): last_off=off
            off+=len(raw)
    pat=re.compile(r'^TRACE \+ c(\d+) s(\d+)(?: \[br\])? via ([a-z>-]+)(\[[^\]]*\])? from c(\d+|\?)(?: root=r(\d+))?\s+(.*)$')
    first={}
    with open(tlog,'rb') as f:
        f.seek(last_off)
        for raw in f:
            if raw.startswith(b'TRACE root '):
                m=re.match(r'TRACE root (\d+) = (?:origin )?(.*?)(?: \((?:by id|substring)\))?$', raw.decode('utf-8','replace').rstrip('\n'))
                if m: rid.setdefault(m.group(2), int(m.group(1)))
                continue
            if not raw.startswith(b'TRACE + '): continue
            m=pat.match(raw.decode('utf-8','replace').rstrip('\n'))
            if not m: continue
            c,s,how,kind,frm,r,name=m.groups()
            key=(int(r) if r else -1, int(c))
            if key not in first: first[key]=(how,kind or '',frm,name.strip())
    kinds=collections.Counter()
    for i,kn,ks,p,la,lb,oa,ob,members in couplers(N):
        r=rid.get(kn)
        if r is None:
            cand=[v for k,v in rid.items() if k.startswith(kn)]
            r=cand[0] if cand else None
        if r is None: print(f"#{i} key={kn}: root not traced"); continue
        # the fact arrived at whichever rep the pointer's class had then: try every member
        hits=[(m,first[(r,m)]) for m in members if (r,m) in first]
        chain=[]; seen=set()
        if hits:
            c=hits[0][0]
        else:
            c=p
        for _ in range(12):
            e=first.get((r,c)) or first.get((-1,c))
            if not e: break
            how,kind,frm,name=e; chain.append((c,how,kind,name)); 
            if frm=='?' or int(frm)==c or c in seen: break
            seen.add(c); c=int(frm)
        if not chain: print(f"#{i} key=({kn},s{ks}) by-ptr=c{p}:{nm(p)[:44]} -> no arrival recorded at the pointer class"); continue
        c0,how0,kind0,name0=chain[0]
        lab=f"{how0}{kind0}"; kinds[lab]+=1
        print(f"#{i} key=({kn[:40]},s{ks}) by-ptr=c{p}:{nm(p)[:44]} <- {lab}  chain: " + ' <- '.join(f"{h}{k} {n[:28]}" for _,h,k,n in chain[1:4]))
    print("delivering-edge kinds:", kinds.most_common())
