import numpy as np
def test(name,v,E,g):
    de=[(a,b) for a,b in E]+[(b,a) for a,b in E]
    idx={e:i for i,e in enumerate(de)}; m=len(de)
    B=np.zeros((m,m))
    for (i,j) in de:
        for (j2,k) in de:
            if j2==j and k!=i: B[idx[(i,j)],idx[(j,k)]]=1
    D=g-1; s=(D-1)//2
    out=[[idx[(a,b)] for (a,b) in de if a==u] for u in range(v)]
    inn=[[idx[(a,b)] for (a,b) in de if b==w] for w in range(v)]
    Bp=np.eye(m); worst=0
    for t in range(1,s+8):
        if t>1: Bp=Bp@B
        if t>s:
            for u in range(v):
                for w in range(v):
                    N=sum(Bp[i,j] for i in out[u] for j in inn[w])
                    worst=max(worst, N/(1.5*2**(t-s)))
    print(name,"girth",g,"s",s,"max N_t/(1.5*2^(t-s)) =",round(worst,4))
pet=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
test("Petersen",10,pet,5)
hea=[(i,(i+1)%14) for i in range(14)]+[(i,(i+5)%14) for i in range(0,14,2)]
test("Heawood",14,hea,6)
# Tutte-Coxeter (LCF [-13,-9,7,-7,9,13]^5), 30 vertices, girth 8
lcf=[-13,-9,7,-7,9,13]*5
tc=set()
for i in range(30):
    tc.add((min(i,(i+1)%30),max(i,(i+1)%30)))
    j=(i+lcf[i])%30; tc.add((min(i,j),max(i,j)))
test("Tutte-Coxeter",30,sorted(tc),8)
