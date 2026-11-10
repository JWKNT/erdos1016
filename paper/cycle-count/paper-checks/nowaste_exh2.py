import itertools, sys
from lib import *
def run(n, Wedges, kmin):
    VW=set(v for e in Wedges for v in e)
    pairs=[(a,b) for a in range(n) for b in range(a+1,n) if (a,b) not in Wedges]
    best={}; ex={}
    tW=len(Wedges)-len(VW)+1
    cnt=0; tot=0
    W=(1<<len(Wedges))-1
    for k in range(kmin,n+3+1):
        for extra in itertools.combinations(pairs,k):
            E=list(Wedges)+list(extra)
            if comps(n,E)!=1: continue
            tot+=1
            basis=cyc_basis(n,E); r=len(basis)
            Z=span(basis)
            # quick filter: every nonzero even subgraph avoiding W must be a cycle
            ok=True
            for z in Z:
                if z and not (z&W) and not is_cycle(n,E,z): ok=False; break
            if not ok: continue
            words={}
            for z in Z: words.setdefault(z & ~W, []).append(z)
            for cls in words.values():
                if not any(is_cycle(n,E,z) for z in cls): ok=False; break
            if ok:
                cnt+=1
                d=(r-tW)-len(VW)
                best[d]=best.get(d,0)+1
                if d not in ex: ex[d]=extra
    print("n",n,"W",Wedges,"kmin",kmin,"connected graphs",tot,"nowaste",cnt,"dist of (r-t)-|V(W)|",dict(sorted(best.items())),flush=True)
    for d in sorted(ex)[-1:]: print("   d=",d,"extra edges",ex[d],flush=True)
tri=[(0,1),(0,2),(1,2)]
c4=[(0,1),(1,2),(2,3),(0,3)]
# d>=1 needs |E(G')| >= n+1
run(7,tri,8)
run(7,c4,8)
run(8,tri,10)
