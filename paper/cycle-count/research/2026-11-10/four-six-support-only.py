#!/usr/bin/env python3
"""Support-only necessary conditions; no forest amplitudes or graph realization."""
import itertools
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import coo_matrix
from random_seven_cycle_dual import matchings


def main():
    V=tuple(range(6));fours=tuple(itertools.combinations(V,4));M4={S:tuple(matchings(S)) for S in fours}
    M6=tuple(matchings(V));states=tuple((S,a) for S in fours for a in M4[S]);ix={s:i for i,s in enumerate(states)}
    z={S:90+i for i,S in enumerate(fours)};N=105
    beta=M6[0];gamma=next(a for a in M6 if set(a).isdisjoint(beta))
    ii=[];jj=[];vv=[];lo=[];hi=[]
    def add(row,l=-np.inf,h=np.inf):
        r=len(lo)
        for j,v in row.items():
            if v:ii.append(r);jj.append(j);vv.append(v)
        lo.append(l);hi.append(h)
    for S in fours:
        for a in M4[S]:add({ix[S,a]:1,45+ix[S,a]:1,z[S]:-1},h=0)
        for offset in (0,45):
            row={offset+ix[S,a]:1 for a in M4[S]};row[z[S]]=-1;add(row,l=0)
    for offset,witness in [(0,beta),(45,gamma)]:
        for alpha in M6:
            positive=int(set(alpha).isdisjoint(witness))
            for e in alpha:
                others=[f for f in alpha if f!=e];row={}
                for f in others:
                    S=tuple(sorted(e+f));a=tuple(sorted((e,f)))
                    row[offset+ix[S,a]]=1;row[z[S]]=-1
                add(row,l=positive-2)
        for Q in itertools.combinations(V,3):
            rest=tuple(v for v in V if v not in Q)
            for e in itertools.combinations(rest,2):
                row={}
                for f in itertools.combinations(Q,2):
                    S=tuple(sorted(e+f));a=tuple(sorted((e,f)))
                    row[offset+ix[S,a]]=1;row[z[S]]=-1
                add(row,l=-2)
    add({j:1 for j in z.values()},h=12)
    matrix=coo_matrix((vv,(ii,jj)),shape=(len(lo),N)).tocsc();c=np.zeros(N)
    for j in z.values():c[j]=-1
    start=time.time()
    result=milp(c,integrality=np.ones(N),bounds=Bounds(np.zeros(N),np.ones(N)),
                constraints=LinearConstraint(matrix,lo,hi),
                options={'time_limit':60,'mip_rel_gap':0,'disp':True})
    payload=dict(status=int(result.status),message=result.message,seconds=time.time()-start,
                 beta=beta,gamma=gamma,variables=N,constraints=len(lo),
                 scope='Finite support relaxation; numerical upper bound is not an exact certificate')
    for key in ('fun','mip_dual_bound','mip_gap','mip_node_count'):
        val=getattr(result,key,None)
        if val is not None:payload[key]=float(val)
    if result.x is not None:
        x=[int(round(v)) for v in result.x]
        assert all(abs(a-b)<1e-7 for a,b in zip(x,result.x))
        for i,(lower,upper) in enumerate(zip(lo,hi)):
            value=sum(v*x[j] for r,j,v in zip(ii,jj,vv) if r==i)
            assert lower<=value<=upper
        payload['active_fours']=[S for S,j in z.items() if x[j]]
        payload['support_x']=[s for s,i in ix.items() if x[i]]
        payload['support_y']=[s for s,i in ix.items() if x[45+i]]
    Path(__file__).with_name('four-six-support-only.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ('active_fours','support_x','support_y')}))


if __name__=='__main__':main()
