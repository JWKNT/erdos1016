import random, itertools
from fractions import Fraction
from lib import *
rng=random.Random(11)
def rand_multi(n, m):
    # connected multigraph, no loops (loops are irrelevant for cuts), parallel edges allowed
    E=[]
    perm=list(range(n)); rng.shuffle(perm)
    for i in range(1,n):
        E.append((perm[i],perm[rng.randrange(i)]))
    while len(E)<m:
        a,b=rng.randrange(n),rng.randrange(n)
        if a!=b: E.append((a,b))
    return E
def connected_subsets(n,E,maxsize):
    adj=[set() for _ in range(n)]
    for a,b in E: adj[a].add(b); adj[b].add(a)
    out=set()
    def grow(S):
        if S in out: return
        out.add(S)
        if len(S)>=maxsize: return
        for x in S:
            for y in adj[x]:
                if y not in S: grow(S|frozenset([y]))
    for v in range(n): grow(frozenset([v]))
    return out
def links(n,E,A,B):
    e=sum(1 for a,b in E if (a in A and b in B) or (a in B and b in A))
    rest=[x for x in range(n) if x not in A and x not in B]
    # components of G-A-B
    idx={x:i for i,x in enumerate(rest)}
    par=list(range(len(rest)))
    def f(x):
        while par[x]!=x:
            par[x]=par[par[x]]; x=par[x]
        return x
    for a,b in E:
        if a in idx and b in idx:
            pa,pb=f(idx[a]),f(idx[b])
            if pa!=pb: par[pa]=pb
    toA=set(); toB=set()
    for a,b in E:
        for x,y in ((a,b),(b,a)):
            if x in idx:
                if y in A: toA.add(f(idx[x]))
                if y in B: toB.add(f(idx[x]))
    return e+len(toA&toB)
viol=0; tested=0; maxratio=0; worst63=-10
for trial in range(400):
    n=rng.randint(5,9); m=rng.randint(n,n+7)
    E=rand_multi(n,m)
    basis=cyc_basis(n,E); Z=span(basis); tot=len(Z)
    def cutmask(A):
        mk=0
        for i,(a,b) in enumerate(E):
            if (a in A)!=(b in A): mk|=1<<i
        return mk
    subs=[S for S in connected_subsets(n,E,3)]
    A=rng.choice(subs)
    cA=cutmask(A); pA=Fraction(sum(1 for z in Z if not z&cA),tot)
    d=bin(cA).count('1')
    exc=[]
    for B in subs:
        if B & A: continue
        cB=cutmask(B); pB=Fraction(sum(1 for z in Z if not z&cB),tot)
        pAB=Fraction(sum(1 for z in Z if not z&(cA|cB)),tot)
        l=links(n,E,A,B)
        tested+=1
        if pAB!=Fraction(2)**(l-1)*pA*pB:
            viol+=1; print("VIOL link formula",n,E,sorted(A),sorted(B),l,pA,pB,pAB)
        if l>=3: exc.append(B)
    # max disjoint family among exc (exhaustive by size, small)
    best=0
    def rec(i,used,k):
        global best
        best=max(best,k)
        for j in range(i,len(exc)):
            if not (exc[j]&used): rec(j+1,used|exc[j],k+1)
    rec(0,frozenset(),0)
    if best> max(d-2,0): viol+=1; print("VIOL exceptional count",n,E,sorted(A),d,best)
    worst63=max(worst63,best-(d-2))
print("pairs tested",tested,"violations",viol,"max of (disjoint exceptional partners) - (d-2):",worst63)
