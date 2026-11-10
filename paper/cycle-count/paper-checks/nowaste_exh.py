import itertools, sys
from lib import *
def run(n, Wedges):
    VW=set(v for e in Wedges for v in e)
    pairs=[(a,b) for a in range(n) for b in range(a+1,n) if (a,b) not in Wedges]
    best={}; ex={}
    tW=len(Wedges)-len(VW)+1
    maxextra=n+3   # |E(G')| <= n+3 necessary
    cnt=0
    for k in range(0,maxextra+1):
        for extra in itertools.combinations(pairs,k):
            E=list(Wedges)+list(extra)
            if comps(n,E)!=1: continue
            basis=cyc_basis(n,E); r=len(basis)
            Z=span(basis)
            W=(1<<len(Wedges))-1
            words={}
            for z in Z: words.setdefault(z & ~W, []).append(z)
            ok=True
            for cls in words.values():
                if not any(is_cycle(n,E,z) for z in cls): ok=False; break
            if ok:
                cnt+=1
                d=(r-tW)-len(VW)
                best[d]=best.get(d,0)+1
                if d not in ex: ex[d]=extra
    print("n",n,"W",Wedges,"nowaste graphs",cnt,"dist",dict(sorted(best.items())))
    for d in sorted(ex)[-2:]: print("   d=",d,"extra edges",ex[d])
tri=[(0,1),(0,2),(1,2)]
run(5,tri); run(6,tri)
c4=[(0,1),(1,2),(2,3),(0,3)]
run(6,c4)
