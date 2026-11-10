import random, itertools
def comps(n, edges, mask=None):
    par=list(range(n))
    def f(x):
        while par[x]!=x:
            par[x]=par[par[x]]; x=par[x]
        return x
    for i,(u,v) in enumerate(edges):
        if mask is None or (mask>>i)&1:
            a,b=f(u),f(v)
            if a!=b: par[a]=b
    return len({f(x) for x in range(n)})
def cyc_basis(n, edges):
    par=list(range(n))
    def f(x):
        while par[x]!=x:
            par[x]=par[par[x]]; x=par[x]
        return x
    adj=[[] for _ in range(n)]; non=[]
    for i,(u,v) in enumerate(edges):
        a,b=f(u),f(v)
        if a!=b:
            par[a]=b; adj[u].append((v,i)); adj[v].append((u,i))
        else: non.append(i)
    basis=[]
    for i in non:
        u,v=edges[i]
        if u==v: basis.append(1<<i); continue
        # path u->v in tree
        prev={u:(None,None)}; st=[u]
        while st:
            x=st.pop()
            if x==v: break
            for (y,j) in adj[x]:
                if y not in prev:
                    prev[y]=(x,j); st.append(y)
        m=1<<i; x=v
        while prev[x][0] is not None:
            m^=1<<prev[x][1]; x=prev[x][0]
        basis.append(m)
    return basis
def span(basis):
    out=[0]
    for b in basis:
        out+= [x^b for x in out]
    return out
def bits(m):
    i=0
    while m:
        if m&1: yield i
        m>>=1; i+=1
def is_cycle(n, edges, m):
    if m==0: return False
    deg={}
    for i in bits(m):
        u,v=edges[i]
        if u==v: return m==(1<<i)
        deg[u]=deg.get(u,0)+1; deg[v]=deg.get(v,0)+1
    if any(d!=2 for d in deg.values()): return False
    # connected?
    es=[edges[i] for i in bits(m)]
    start=es[0][0]; seen={start}; ch=True
    nb={}
    for u,v in es:
        nb.setdefault(u,[]).append(v); nb.setdefault(v,[]).append(u)
    st=[start]
    while st:
        x=st.pop()
        for y in nb[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen)==len(deg)
def is_forest(n, edges, m):
    par=list(range(n))
    def f(x):
        while par[x]!=x:
            par[x]=par[par[x]]; x=par[x]
        return x
    for i in bits(m):
        u,v=edges[i]
        a,b=f(u),f(v)
        if a==b: return False
        par[a]=b
    return True
def rank(n, edges, mask=None):
    e = len(edges) if mask is None else bin(mask).count('1')
    # count only vertices? use all n vertices: beta = e - n + comps
    return e - n + comps(n, edges, mask)
def rand_connected(n, m, rng):
    # random connected simple graph with n vertices and m>=n-1 edges
    while True:
        perm=list(range(n)); rng.shuffle(perm)
        E=set()
        for i in range(1,n):
            j=rng.randrange(i); a,b=perm[i],perm[j]; E.add((min(a,b),max(a,b)))
        allp=[(a,b) for a in range(n) for b in range(a+1,n) if (a,b) not in E]
        rng.shuffle(allp)
        need=m-len(E)
        if need>len(allp): m=len(E)+len(allp); need=len(allp)
        E|=set(allp[:need])
        return sorted(E)
