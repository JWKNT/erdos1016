import math, sys
from lib import *
def logstar(x):
    j=0
    while x>1: x=math.log2(x); j+=1
    return j
def build(n):
    E=[(i,(i+1)%n) for i in range(n)]
    chords=[]
    if n<=6:
        if n>=4: chords.append((0,2))
        if n==6: chords.append((0,3))
        return E,chords,None
    k=0
    while 2**(k+1)+(k+1)+1<=n: k+=1
    assert 2**k+k+1<=n<=2**(k+1)+k+1 and k>=2
    v=[0]
    for i in range(k): v.append(v[-1]+2**i+1)
    assert v[k]==2**k+k-1<=n-2
    for i in range(k): chords.append((v[i],v[i+1]))
    chords.append((v[0],v[k]))
    t=k; extra=0
    while t>2:
        j=math.ceil(math.log2(t)); assert 2<=j<t
        chords.append((v[0],v[j])); extra+=1; t=j
    assert extra==logstar(k)-1, (k,extra,logstar(k))
    if n==2**(k+1)+k+1:
        # missing length 2^k+k+1: chord of H at distance 2^k+k
        a=n-1; b=(a+2**k+k)%n
        chords.append((min(a,b),max(a,b)))
    return E,chords,k
def cycle_lengths(n,E):
    basis=cyc_basis(n,E)
    Z=span(basis)
    return {bin(z).count('1') for z in Z if is_cycle(n,E,z)}
bad=0
Ns=list(range(3,140))+[2**k+k+1 for k in range(7,10)]+[2**(k+1)+k+1 for k in range(6,9)]+[2**(k+1)+k for k in range(6,9)]+[300,500]
worst=0
for n in Ns:
    E,ch,k=build(n)
    es=E+[tuple(sorted(c)) for c in ch]
    assert len(set(tuple(sorted(e)) for e in es))==len(es), ("multi-edge",n)
    L=cycle_lengths(n,es)
    ok = all(l in L for l in range(3,n+1))
    bound = math.floor(math.log2(n))+logstar(n)+1
    if not ok or len(ch)>bound:
        bad+=1; print("FAIL",n,k,len(ch),bound,sorted(set(range(3,n+1))-L)[:5])
    worst=max(worst,len(ch)-bound)
print("checked",len(Ns),"values of n; failures",bad,"; max (chords - bound) =",worst)
