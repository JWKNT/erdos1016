#!/usr/bin/env python3
"""Exact rational primal checks. This does not certify optimization upper bounds."""
import itertools
import json
from fractions import Fraction
from pathlib import Path
from random_seven_cycle_dual import matchings


def freeze(value):
    return tuple(map(freeze,value)) if isinstance(value,list) else value


def main():
    folder=Path(__file__).resolve().parent
    V=tuple(range(6));fours=tuple(itertools.combinations(V,4));M6=tuple(matchings(V))
    checked=[]
    for path in sorted(folder.glob('four-six-local-boolean*.json')):
        payload=json.loads(path.read_text())
        if 'x' not in payload:continue
        states=list(map(freeze,payload['state_order']))
        shores=[dict(zip(states,[Fraction(v).limit_denominator(10**6) for v in payload[side]]))
                for side in ('x','y')]
        assert all(0<=v<=1 for shore in shores for v in shore.values())
        totals=[{S:sum(shore['f',S,a] for a in matchings(S)) for S in fours} for shore in shores]
        assert totals[0]==totals[1]
        assert all(v in (0,1) for v in totals[0].values())
        assert sum(totals[0].values())==payload['active_four_count']
        def rho(shore,a):
            if len(a)==2:
                S=tuple(sorted(v for e in a for v in e))
                return totals[0][S]-shore['f',S,a]
            return sum(shore['w',b] for b in M6 if set(a).isdisjoint(b))
        for shore in shores:
            assert sum(shore['w',a] for a in M6)==(0 if payload.get('six_zero') else 1)
            for alpha in M6:
                for e in alpha:
                    others=[f for f in alpha if f!=e]
                    assert rho(shore,tuple(sorted((e,others[0]))))+rho(shore,tuple(sorted((e,others[1]))))+rho(shore,alpha)<=2
            if payload.get('caps','all') in ('all','star'):
                for Q in itertools.combinations(V,3):
                    rest=tuple(v for v in V if v not in Q)
                    for e in itertools.combinations(rest,2):
                        assert sum(rho(shore,tuple(sorted((e,f)))) for f in itertools.combinations(Q,2))<=2
            if payload.get('caps','all') in ('all','binary'):
                for e in itertools.combinations(V,2):
                    Q=tuple(v for v in V if v not in e)
                    for a in matchings(Q):
                        assert sum(rho(shore,tuple(sorted((e,f)))) for f in itertools.combinations(Q,2))+rho(shore,tuple(sorted((e,)+a)))<=4
        x,y=shores
        for S in fours:
            for a in matchings(S):
                assert x['f',S,a]+y['f',S,a]<=1
                if not payload.get('four_relax'):assert x['f',S,a]*y['f',S,a]==0
        for a in M6:
            for b in M6:
                if x['w',a]*y['w',b]:
                    assert set(a).isdisjoint(b)
                    for alpha in M6:
                        if set(alpha).isdisjoint(a) and set(alpha).isdisjoint(b):
                            assert sum(totals[0][tuple(v for v in V if v not in e)] for e in alpha)<=2
        checked.append(dict(file=path.name,active_four_count=payload['active_four_count'],
                            caps=payload.get('caps','all'),four_relax=payload.get('four_relax',False),
                            six_zero=payload.get('six_zero',False)))
    result=dict(status='All rational primal checks passed',checks=checked,
                scope='Feasible witnesses only. Numerical optimization upper bounds remain uncertified.')
    (folder/'four-six-local-witness-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],witnesses=len(checked))))


if __name__=='__main__':main()
