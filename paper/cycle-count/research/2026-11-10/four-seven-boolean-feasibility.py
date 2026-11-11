#!/usr/bin/env python3
"""Exploratory critical two-shore feasibility. A solver result is not a proof."""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix
import random_seven_cycle_dual as model


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--output', default='four-seven-boolean-feasibility.json')
    parser.add_argument('--six-active',type=int,default=None)
    args=parser.parse_args()
    forest_states=tuple(s for s in model.STATES if s[0]!='p')
    ix={s:i for i,s in enumerate(forest_states)}
    n=len(ix)
    sectors=tuple(('f4',S) for S in model.FOURS)+tuple(('f6',S) for S in model.SIXES)
    zi={s:2*n+i for i,s in enumerate(sectors)}
    f4states=tuple(s for s in forest_states if s[0]=='f4')
    f6states=tuple(s for s in forest_states if s[0]=='f6')
    fi={s:2*n+len(sectors)+i for i,s in enumerate(f4states)}
    wx={s:2*n+len(sectors)+len(fi)+i for i,s in enumerate(f6states)}
    wy={s:2*n+len(sectors)+len(fi)+len(wx)+i for i,s in enumerate(f6states)}
    variables=2*n+len(sectors)+len(fi)+len(wx)+len(wy)
    ii=[]; jj=[]; vv=[]; lows=[]; highs=[]; labels=[]
    def add(row,lo=-np.inf,hi=np.inf,label=None):
        r=len(lows)
        for j,v in row.items():
            if v: ii.append(r);jj.append(j);vv.append(v)
        lows.append(lo);highs.append(hi);labels.append(label)
    rows,rhs,rlab,_=model.system(extra_caps=True)
    for shore in range(2):
        offset=shore*n
        for row,bound,label in zip(rows,rhs,rlab):
            projected={offset+ix[state]:row[j] for j,state in enumerate(model.STATES)
                       if state in ix and row[j]}
            if projected:
                add(projected,hi=float(bound),label=dict(shore=shore,cap=label))
        for kind,S in sectors:
            row={offset+ix[state]:1 for state in forest_states if state[:2]==(kind,S)}
            row[zi[kind,S]]=-1
            add(row,lo=0,hi=0,label=dict(kind='common_sector',shore=shore,ports=S))
    add({j:1 for j in zi.values()},lo=32,hi=32,label=dict(kind='critical_sector_count'))
    # An active six-sector needs three missing four-sectors. The proof uses
    # the four perfect matchings of the complement of a six-cycle.
    for S in model.SIXES:
        row={zi['f4',Q]:1 for Q in model.FOURS if set(Q)<=set(S)}
        row[zi['f6',S]]=3
        add(row,hi=15,label=dict(kind='six_compatibility_three_missing',ports=S))
    if args.six_active is not None:
        assert 0<=args.six_active<=7
        # The seven six-sectors are indexed by their omitted port.
        # Every subset of a given size is equivalent under a port permutation.
        for i,S in enumerate(model.SIXES):
            value=int(i<args.six_active)
            add({zi['f6',S]:1},lo=value,hi=value)
    for state in f4states:
        add({ix[state]:1,fi[state]:-1},hi=0)
        add({n+ix[state]:1,fi[state]:1},hi=1)
    for state in f6states:
        add({ix[state]:1,wx[state]:-1},hi=0)
        add({n+ix[state]:1,wy[state]:-1},hi=0)
    for S in model.SIXES:
        for beta in model.M6[S]:
            for gamma in model.M6[S]:
                if not set(beta).isdisjoint(gamma):
                    add({wx['f6',S,beta]:1,wy['f6',S,gamma]:1},hi=1)
    # Any active four-sector can be moved here by a port permutation.
    if args.six_active is None:
        first=('f4',model.FOURS[0])
        add({zi[first]:1},lo=1,hi=1,label=dict(kind='symmetry_active_four_sector'))
        # Within it, one X pairing has mass at least one third.
        add({ix['f4',model.FOURS[0],model.M4[model.FOURS[0]][0]]:1},lo=1/3)
    matrix=coo_matrix((vv,(ii,jj)),shape=(len(lows),variables)).tocsc()
    integrality=np.zeros(variables)
    integrality[2*n:]=1
    started=time.time()
    result=milp(np.zeros(variables), integrality=integrality,
                bounds=Bounds(np.zeros(variables),np.ones(variables)),
                constraints=LinearConstraint(matrix,lows,highs),
                options={'time_limit':args.seconds,'mip_rel_gap':0,'disp':True})
    payload=dict(status=int(result.status),message=result.message,seconds=time.time()-started,
                 variables=variables,binary_variables=int(integrality.sum()),
                 constraints=len(lows),six_active=args.six_active,
                 scope='Abstract limiting-state relaxation; not a graph realization')
    for key in ('mip_gap','mip_node_count','mip_dual_bound','fun'):
        value=getattr(result,key,None)
        if value is not None:payload[key]=float(value)
    if result.x is not None:
        x=result.x
        payload['nonzero_variables']=[dict(index=j,value=float(value)) for j,value in enumerate(x) if value>1e-8]
        payload['state_order']=forest_states
        payload['active_sectors']=[s for s,j in zi.items() if x[j]>.5]
        ax=matrix@x
        payload['maximum_constraint_violation']=float(max(np.max(np.array(lows)-ax),np.max(ax-np.array(highs)),0))
    path=Path(__file__).with_name(args.output)
    path.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ('nonzero_variables','state_order','active_sectors')}))


if __name__=='__main__':main()
