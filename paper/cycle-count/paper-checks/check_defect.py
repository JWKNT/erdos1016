import math, random
from lib import *
from check_construction import build
def greedy(n,E):
    basis=cyc_basis(n,E); Z=span(basis); r=len(basis)
    cyc=[z for z in Z if is_cycle(n,E,z)]
    bylen={}
    for z in cyc: bylen.setdefault(bin(z).count('1'),[]).append(z)
    lens=set(bylen)
    L=2
    while L+1 in lens: L+=1
    if L<3: return None
    Evalue=(L-2)/2**r
    W=0; rows=[]
    def stats(W):
        m=bin(W).count('1')
        VW=set()
        for i in bits(W): VW|=set(E[i])
        idx={v:j for j,v in enumerate(sorted(VW))}
        EW=[(idx[E[i][0]],idx[E[i][1]]) for i in bits(W)]
        t=len(EW)-len(VW)+(comps(len(VW),EW) if VW else 0)
        wl={bin(z).count('1') for z in cyc if z & ~W==0}
        return m,t,wl
    # start with a triangle
    W=bylen[3][0]
    seq=[]
    while True:
        m,t,wl=stats(W)
        l=3
        while l in wl: l+=1
        seq.append((m,t,len(wl),l))
        if l>L: break
        # choose a cycle of length l (random choice among them)
        C=random.choice(bylen[l])
        W|=C
    return Evalue,r,L,seq
random.seed(5)
viol=0; cases=0
def run(n,E,name):
    global viol,cases
    g=greedy(n,E)
    if g is None: return
    Ev,r,L,seq=g
    rho=[(m+2)/2**t for (m,t,N,l) in seq]
    tot=0.0
    for q in range(len(seq)-1):
        m,t,N,l=seq[q]; m2,t2,N2,l2=seq[q+1]
        P=m2-m; kappa=1-P/(m+2); j=t2-t-1
        assert j>=0 and 0<kappa<=1, (name,q,kappa,j)
        assert abs(rho[q+1]-rho[q]*(1-kappa/2)*2**(-j))<1e-12
        # perfect-step consequences
        assert l<=N+3 and N<=m-2 and P<=l
        tot+=kappa/2+j*math.log(2)
    for q in range(len(seq)):
        if not Ev<rho[q]: viol+=1; print("VIOL E<rho",name,q,Ev,rho[q])
    if not tot<math.log(rho[0]/Ev)+1e-12: viol+=1; print("VIOL budget",name,tot,math.log(rho[0]/Ev))
    cases+=1
    return Ev,r,L,len(seq),tot,math.log(rho[0]/Ev)
for n in [7,12,20,40,75,140]:
    E,ch,k=build(n); es=E+[tuple(sorted(c)) for c in ch]
    print("construction n=%d:"%n, "E=%.4f r=%d L=%d steps=%d  defect sum=%.3f  ln(rho_1/E)=%.3f"%run(n,es,"bondy%d"%n))
rng=random.Random(9)
for trial in range(1500):
    n=rng.randint(5,9); r=rng.randint(2,9)
    E=rand_connected(n,min(n-1+r,n*(n-1)//2),rng)
    run(n,E,"rand")
print("cases",cases,"violations",viol)
