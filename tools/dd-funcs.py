#!/usr/bin/env python3
"""Delta debugging over function bodies (ddmin): find a 1-minimal set of functions
to KEEP (all others ablated with --cfl-ablate-funcs, MEASUREMENT-ONLY but monotone:
an ablated body emits no flows, callers still wire its formals) such that one
indirect-call site still has a target outside a given legitimate set.

usage: dd-funcs.py WORKDIR FUNCS.txt LEGIT.txt SITE 'KAMain command up to the .bc'
  WORKDIR   scratch dir for per-test json/log/ablate files and cache.tsv (resumable)
  FUNCS.txt one function name per line (the universe; e.g. all `define`s of the IR)
  LEGIT.txt targets that may arrive legitimately (property = any target outside it)
  SITE      suffix of the site key in the icall JSON, e.g. elf64-x86-64.c:4688
  command   the analysis command WITHOUT --cfl-dump-icalls-json/--cfl-dump-merges;
            run from the repo root; DD_PAR sets parallelism (default 6)
Writes WORKDIR/current.txt after every shrink and WORKDIR/minimal.txt at the end.
"""
import subprocess, os, sys, json, hashlib, re, time, concurrent.futures as cf
if len(sys.argv) != 6: sys.exit(__doc__)
S, FUNCS, LEGIT, SITE, cmd = sys.argv[1:6]
REPO = os.getcwd()
PAR = int(os.environ.get('DD_PAR', '6'))
os.makedirs(S, exist_ok=True)
U = [l.strip() for l in open(FUNCS) if l.strip()]
legit = set(l.strip() for l in open(LEGIT) if l.strip())
cache={}
CACHE=S+'/cache.tsv'
if os.path.exists(CACHE):
    for l in open(CACHE):
        h,n,res,ntg=l.rstrip('\n').split('\t'); cache[h]=(res=='1',int(ntg))
def key(keep): return hashlib.sha1('\n'.join(sorted(keep)).encode()).hexdigest()[:16]
def test(keep):
    keep=set(keep); h=key(keep)
    if h in cache: return cache[h][0]
    abl=[f for f in U if f not in keep]
    tid=h; d=S
    jsn=f'{d}/{tid}.json'; log=f'{d}/{tid}.log'; ablf=f'{d}/{tid}.ablate'
    open(ablf,'w').write(','.join(abl))
    full=cmd+f' --cfl-dump-icalls-json={jsn}'+(f' --cfl-ablate-funcs=$(cat {ablf})' if abl else '')
    env=dict(os.environ, MALLOC_ARENA_MAX='2')
    t0=time.time()
    r=subprocess.run(['bash','-c',f'cd {REPO} && timeout 3600 {full} > {log} 2>&1'], env=env)
    ntg=-1; res=False
    try:
        a=json.load(open(jsn)); k=[x for x in a if x.endswith(SITE)]
        tg=set(a[k[0]]) if k else set(); ntg=len(tg); res=bool(tg-legit)
    except Exception as e:
        print(f"  test {tid}: no answer ({e}); rc={r.returncode}", flush=True)
    cache[h]=(res,ntg)
    open(CACHE,'a').write(f'{h}\t{len(keep)}\t{int(res)}\t{ntg}\n')
    print(f"  test keep={len(keep):5d} -> targets={ntg:3d} soup={int(res)} ({time.time()-t0:.0f}s)", flush=True)
    return res
def ptest(sets):
    with cf.ThreadPoolExecutor(max_workers=PAR) as ex:
        return list(ex.map(lambda s: test(s), sets))
def ddmin(keep):
    keep=list(keep); n=2
    while len(keep)>=2:
        chunk=(len(keep)+n-1)//n
        subsets=[keep[i:i+chunk] for i in range(0,len(keep),chunk)]
        print(f"round: keep={len(keep)} n={n} subsets={len(subsets)}", flush=True)
        res=ptest(subsets)
        hit=[s for s,r in zip(subsets,res) if r]
        if hit: keep=min(hit,key=len); n=2; open(S+'/current.txt','w').write('\n'.join(keep)+'\n'); continue
        comps=[[f for f in keep if f not in set(s)] for s in subsets]
        res=ptest(comps)
        hit=[c for c,r in zip(comps,res) if r]
        if hit: keep=min(hit,key=len); n=max(n-1,2); open(S+'/current.txt','w').write('\n'.join(keep)+'\n'); continue
        if n>=len(keep): break
        n=min(n*2,len(keep))
    return keep
if __name__=='__main__':
    start=[l.strip() for l in open(S+'/current.txt')] if os.path.exists(S+'/current.txt') else U
    print("universe", len(U), "start", len(start), "legit", len(legit), flush=True)
    assert test(start), "property does not hold on the start set"
    m=ddmin(start)
    open(S+'/minimal.txt','w').write('\n'.join(m)+'\n')
    print("MINIMAL keep set:", len(m), flush=True)
    for f in m: print("  ", f, flush=True)
