import random, math
rng=random.Random(4)
def girth_multi(n,E):
    # E list of (u,v) possibly loops / parallel; returns shortest cycle length or None
    best=None
    seen={}
    for (u,v) in E:
        if u==v: return 1
        k=(min(u,v),max(u,v)); seen[k]=seen.get(k,0)+1
    if any(c>=2 for c in seen.values()): best=2
    adj=[set() for _ in range(n)]
    for (u,v) in seen: adj[u].add(v); adj[v].add(u)
    g=10**9
    for s in range(n):
        dist={s:0}; par={s:-1}; q=[s]
        for x in q:
            for y in adj[x]:
                if y not in dist: dist[y]=dist[x]+1; par[y]=x; q.append(y)
                elif par[x]!=y: g=min(g,dist[x]+dist[y]+1)
    if g<10**9: best=g if best is None else min(best,g)
    return best
viol=0; tests=0; worst=0
for trial in range(20000):
    nv=rng.choice([2,4,6,8,10,14,20,30,40])
    # random multigraph with min degree >=3: configuration model with degrees 3 or 4
    degs=[rng.choice([3,3,3,4]) for _ in range(nv)]
    if sum(degs)%2: degs[0]+=1
    stubs=[i for i,d in enumerate(degs) for _ in range(d)]
    rng.shuffle(stubs)
    E=list(zip(stubs[::2],stubs[1::2]))
    # connected?
    par=list(range(nv))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for u,v in E: par[f(u)]=f(v)
    if len({f(x) for x in range(nv)})!=1: continue
    r=len(E)-nv+1
    j=rng.randint(0,min(6,r-1))
    E2=E[:]; rng.shuffle(E2); E2=E2[j:]
    g=girth_multi(nv,E2)
    if g is None: continue
    bound=2*math.log2(r)+2*j+4
    tests+=1
    if g>bound: viol+=1; print("VIOL",nv,r,j,g,bound)
    worst=max(worst,g/bound)
print("tests",tests,"violations",viol,"max girth/bound",round(worst,3))
