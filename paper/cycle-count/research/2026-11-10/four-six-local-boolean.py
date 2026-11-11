#!/usr/bin/env python3
"""Exploratory Boolean four-sectors inside one active six-sector."""
import itertools
import json
import time
import argparse
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
from random_seven_cycle_dual import matchings


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--caps',choices=('all','matching','star','binary'),default='all')
    parser.add_argument('--seconds',type=int,default=180)
    parser.add_argument('--four-relax',action='store_true')
    parser.add_argument('--six-zero',action='store_true')
    args=parser.parse_args()
    V=tuple(range(6));pairs=tuple(itertools.combinations(V,2))
    fours=tuple(itertools.combinations(V,4));M4={S:tuple(matchings(S)) for S in fours}
    M6=tuple(matchings(V))
    states=tuple(('f',S,a) for S in fours for a in M4[S])+tuple(('w',a) for a in M6)
    ix={s:i for i,s in enumerate(states)};n=len(states)
    z={S:2*n+i for i,S in enumerate(fours)}
    flag={s:2*n+15+i for i,s in enumerate(states[:45])}
    wx={a:2*n+60+i for i,a in enumerate(M6)}
    wy={a:2*n+75+i for i,a in enumerate(M6)}
    N=2*n+90;ii=[];jj=[];vv=[];lo=[];hi=[]
    def add(row,l=-np.inf,h=np.inf):
        r=len(lo)
        for j,v in row.items():
            if v:ii.append(r);jj.append(j);vv.append(v)
        lo.append(l);hi.append(h)
    def rho(a):
        if len(a)==1:return {}
        if len(a)==2:
            S=tuple(sorted(v for e in a for v in e))
            return {ix['f',S,b]:1 for b in M4[S] if b!=a}
        return {ix['w',b]:1 for b in M6 if set(a).isdisjoint(b)}
    caps=[]
    def cap(parts,bound):
        row={}
        for a in parts:
            for j,v in rho(tuple(sorted(a))).items():row[j]=row.get(j,0)+v
        caps.append((row,bound))
    for S in fours:
        for a in M4[S]:
            for e in a:cap([a],1)
    for a in M6:
        for e in a:
            others=[f for f in a if f!=e]
            cap([(e,others[0]),(e,others[1]),a],2)
    if args.caps in ('all','star'):
        for Q in itertools.combinations(V,3):
            others=tuple(v for v in V if v not in Q)
            for e in itertools.combinations(others,2):
                cap([(e,f) for f in itertools.combinations(Q,2)],2)
    if args.caps in ('all','binary'):
        for e in pairs:
            Q=tuple(v for v in V if v not in e)
            for a in matchings(Q):
                cap([(e,f) for f in itertools.combinations(Q,2)]+[(e,)+a],4)
    for offset in (0,n):
        for row,bound in caps:add({offset+j:v for j,v in row.items()},h=bound)
        for S in fours:
            row={offset+ix['f',S,a]:1 for a in M4[S]};row[z[S]]=-1;add(row,0,0)
        value=0 if args.six_zero else 1
        add({offset+ix['w',a]:1 for a in M6},value,value)
    for s,j in flag.items():
        add({ix[s]:1,j:-1},h=0);add({n+ix[s]:1,j:1},h=1)
    for a in M6:
        add({ix['w',a]:1,wx[a]:-1},h=0)
        add({n+ix['w',a]:1,wy[a]:-1},h=0)
        for b in M6:
            if not set(a).isdisjoint(b):add({wx[a]:1,wy[b]:1},h=1)
    beta=M6[0];gamma=next(a for a in M6 if set(a).isdisjoint(beta))
    if not args.six_zero:
        add({ix['w',beta]:1},l=1/15);add({n+ix['w',gamma]:1},l=1/15)
        add({j:1 for j in z.values()},h=12)
    # A selected support pair forces every common compatible matching to
    # contain a pair complementary to an inactive four-sector.
    for a in M6:
        for b in M6:
            if not set(a).isdisjoint(b):continue
            for alpha in M6:
                if not set(alpha).isdisjoint(a) or not set(alpha).isdisjoint(b):continue
                row={z[tuple(v for v in V if v not in e)]:1 for e in alpha}
                row[wx[a]]=1;row[wy[b]]=1;add(row,h=4)
    matrix=coo_matrix((vv,(ii,jj)),shape=(len(lo),N)).tocsc()
    objective=np.zeros(N)
    for j in z.values():objective[j]=-1
    integ=np.zeros(N);integ[2*n:]=1
    if args.four_relax:
        for j in flag.values():integ[j]=0
    start=time.time()
    result=milp(objective,integrality=integ,bounds=Bounds(np.zeros(N),np.ones(N)),
                constraints=LinearConstraint(matrix,lo,hi),
                options={'time_limit':args.seconds,'mip_rel_gap':0,'disp':True})
    payload=dict(status=int(result.status),message=result.message,seconds=time.time()-start,
                 variables=N,constraints=len(lo),caps=args.caps,four_relax=args.four_relax,
                 six_zero=args.six_zero,
                 scope='Abstract limiting relaxation; no graph realization')
    for name in ('fun','mip_gap','mip_node_count','mip_dual_bound'):
        value=getattr(result,name,None)
        if value is not None:payload[name]=float(value)
    if result.x is not None:
        payload['active_four_count']=int(round(-result.fun))
        payload['active_fours']=[S for S,j in z.items() if result.x[j]>.5]
        payload['state_order']=states
        payload['x']=list(map(float,result.x[:n]));payload['y']=list(map(float,result.x[n:2*n]))
        ax=matrix@result.x
        payload['maximum_constraint_violation']=float(max(np.max(np.array(lo)-ax),np.max(ax-np.array(hi)),0))
    suffix='' if args.caps=='all' else '-'+args.caps
    if args.four_relax:suffix+='-four-relax'
    if args.six_zero:suffix+='-six-zero'
    Path(__file__).with_name('four-six-local-boolean'+suffix+'.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ('x','y','state_order','active_fours')}))


if __name__=='__main__':main()
