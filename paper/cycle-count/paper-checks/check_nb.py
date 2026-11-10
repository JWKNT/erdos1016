import numpy as np, random, math
rng=random.Random(3)
def rand_subcubic(v, deficit_frac):
    # random simple graph with max degree 3: start from random cubic-ish via pairing, drop loops/multi, then delete some edges
    while True:
        stubs=[i for i in range(v) for _ in range(3)]
        rng.shuffle(stubs)
        E=set()
        for a,b in zip(stubs[::2],stubs[1::2]):
            if a!=b: E.add((min(a,b),max(a,b)))
        E=list(E)
        E=[e for e in E if rng.random()>deficit_frac]
        if E: return E
def girth(v,E):
    adj=[[] for _ in range(v)]
    for a,b in E: adj[a].append(b); adj[b].append(a)
    g=10**9
    for s in range(v):
        dist={s:0}; par={s:-1}; q=[s]
        for x in q:
            for y in adj[x]:
                if y not in dist: dist[y]=dist[x]+1; par[y]=x; q.append(y)
                elif par[x]!=y: g=min(g,dist[x]+dist[y]+1)
    return g
viol=0; n_tests=0; minmargin=1e9
for trial in range(300):
    v=rng.choice([10,14,20,30,40])
    E=rand_subcubic(v, rng.choice([0,0.02,0.05,0.1]))
    deg=[0]*v
    for a,b in E: deg[a]+=1; deg[b]+=1
    dJ=sum(3-d for d in deg)
    if dJ>=v: continue
    de=[(a,b) for a,b in E]+[(b,a) for a,b in E]
    idx={e:i for i,e in enumerate(de)}
    m=len(de)
    B=np.zeros((m,m))
    for (i,j) in de:
        for (j2,k) in de:
            if j2==j and k!=i: B[idx[(i,j)],idx[(j,k)]]=1
    ev=np.linalg.eigvals(B)
    real=[z.real for z in ev if abs(z.imag)<1e-7]
    nonreal=[z for z in ev if abs(z.imag)>=1e-7]
    lam=2-dJ/v
    # (i) a real eigenvalue >= 2 - dJ/v
    if not (max(real)>=lam-1e-6): viol+=1; print("VIOL real eig", v, dJ, max(real), lam)
    # (ii) nonreal eigenvalues have modulus <= sqrt2
    if nonreal and max(abs(z) for z in nonreal)>math.sqrt(2)+1e-6: viol+=1; print("VIOL modulus", max(abs(z) for z in nonreal))
    # (iii) trace inequality for even l
    Bp=np.eye(m)
    for l in range(1,25):
        Bp=Bp@B
        if l%2==0:
            tr=np.trace(Bp)
            rhs=lam**l-3*v*2**(l/2)
            if tr < rhs-1e-6*abs(rhs)-1e-6: viol+=1; print("VIOL trace",v,l,tr,rhs)
            if rhs>0: minmargin=min(minmargin, tr/rhs)
    # (iv) NB walk bound: N_t(u,w) <= (3/2) 2^(t-s), s=floor((D-1)/2) for girth > D
    g=girth(v,E)
    if g<10**9:
        D=g-1; s=(D-1)//2
        if s>=1:
            # count NB walks of length t from u to w via B: N_t(u,w)= sum over first directed edge from u, last into w of (B^(t-1))
            out=[[idx[(a,b)] for (a,b) in de if a==u] for u in range(v)]
            inn=[[idx[(a,b)] for (a,b) in de if b==w] for w in range(v)]
            Bp=np.eye(m)
            for t in range(1,s+6):
                if t>1: Bp=Bp@B
                if t>s:
                    for u in range(v):
                        for w in range(v):
                            N=sum(Bp[i,j] for i in out[u] for j in inn[w])
                            if N>1.5*2**(t-s)+1e-9: viol+=1; print("VIOL walk",v,g,t,s,N)
    n_tests+=1
print("graphs tested",n_tests,"violations",viol,"min tr/rhs when rhs>0:",minmargin)
