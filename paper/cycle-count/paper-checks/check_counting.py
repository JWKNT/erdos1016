import random, sys
from lib import *
rng=random.Random(7)
tests=0; nowaste=0; maxdiff={} ; viol=0
examples={}
for trial in range(4000):
    n=rng.randint(4,8)
    r=rng.randint(1,8)
    m=min(n-1+r, n*(n-1)//2)
    E=rand_connected(n,m,rng)
    basis=cyc_basis(n,E); r=len(basis)
    if r==0: continue
    Z=span(basis)
    # choose W: union of k random cycles, or random edge subset
    cycles=[z for z in Z if is_cycle(n,E,z)]
    lens={bin(z).count('1') for z in cycles}
    mode=rng.random()
    if mode<0.6 and cycles:
        k=rng.randint(1,min(3,len(cycles)))
        W=0
        for c in rng.sample(cycles,k): W|=c
    else:
        W=0
        for i in range(len(E)):
            if rng.random()<0.4: W|=1<<i
    mW=bin(W).count('1')
    VW=set()
    for i in bits(W): VW|=set(E[i])
    # rank of W as subgraph on its own vertices
    idx={v:j for j,v in enumerate(sorted(VW))}
    EW=[(idx[E[i][0]],idx[E[i][1]]) for i in bits(W)]
    t=len(EW)-len(VW)+ (comps(len(VW),EW) if VW else 0)
    words={}
    for z in Z:
        words.setdefault(z & ~W, []).append(z)
    assert len(words)==2**(r-t), (len(words), r, t)
    nf=sum(1 for x in words if is_forest(n,E,x))
    p_num=nf; tot=len(words)
    # (b) #cycles <= 2^t * nf + (tot - nf)
    if not (len(cycles) <= (2**t)*nf + (tot-nf)): viol+=1; print("VIOL b", n,E,W)
    # (c) #lengths <= mW*nf + (tot-nf)
    if not (len(lens) <= mW*nf + (tot-nf)): viol+=1; print("VIOL c", n,E,W)
    tests+=1
    # no waste?
    if mW>=1 and all(any(is_cycle(n,E,z) for z in cls) for cls in words.values()):
        nowaste+=1
        # every nonzero even subgraph of G-E(W) is a cycle
        for z in Z:
            if z and (z & W)==0 and not is_cycle(n,E,z):
                viol+=1; print("VIOL nowaste-evensub", n,E,W)
        d=(r-t)-len(VW)
        maxdiff[d]=maxdiff.get(d,0)+1
        if d not in examples: examples[d]=(n,E,[E[i] for i in bits(W)])
        if d>3: viol+=1; print("VIOL X", n,E,W)
print("tests",tests,"nowaste",nowaste,"viol",viol)
print("distribution of (r-t)-|V(W)| in no-waste cases:", dict(sorted(maxdiff.items())))
for d in sorted(examples)[-2:]:
    print("example d=",d, examples[d])
