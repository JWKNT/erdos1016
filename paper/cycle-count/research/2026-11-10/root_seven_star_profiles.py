#!/usr/bin/env python3
"""Exact necessary local-star/prism conditions for seven-port Boolean profiles."""
from itertools import combinations
from pathlib import Path
import json

P=tuple(combinations(range(7),2));F=tuple(combinations(range(7),4));SIX=tuple(combinations(range(7),6))
TABLE=json.loads(Path(__file__).with_name('root-exact-star-cover-table.json').read_text())['minimum_mass_times_two']
local=[]
for Q in F:
    slots=[]
    for e in combinations(Q,2):
        remain=tuple(v for v in range(7) if v not in e);f=tuple(v for v in Q if v not in e)
        slots.append((P.index(e),tuple(combinations(remain,2)).index(f)))
    local.append(slots)

def matchings(V):
    if not V:yield ();return
    a=V[0]
    for b in V[1:]:
        for tail in matchings(tuple(v for v in V if v not in (a,b))):yield ((a,b),)+tail
M=tuple(matchings(tuple(range(6))));pairs6=tuple(combinations(range(6),2))
compat=[{i for i,b in enumerate(M) if set(a).isdisjoint(b)} for a in M]
prism_families=[]
for i,j in combinations(range(15),2):
    if j in compat[i]:
        common=compat[i]&compat[j];assert len(common)==4
        prism_families.append(tuple(sum(1<<pairs6.index(e) for e in M[k]) for k in common))

def prism_possible(mask):return any(all(mask&m for m in family) for family in prism_families)

inside=[]
for T in SIX:
    mapping={v:i for i,v in enumerate(T)};row={}
    for i,Q in enumerate(F):
        if set(Q)<=set(T):
            missing=tuple(mapping[v] for v in T if v not in Q);row[i]=1<<pairs6.index(missing)
    inside.append(row)


def main():
    rows=[]
    for z in (3,4,5,6):
        m=z-3;active=range(m);valid=0;best=10000;witness=None
        for family in combinations(range(35),z):
            masks=[]
            for t in active:
                mask=sum(inside[t].get(i,0) for i in family)
                if not prism_possible(mask):break
                masks.append(mask)
            else:
                valid+=1;H=[1023]*21
                for i in family:
                    for pair,edge in local[i]:H[pair]^=1<<edge
                score=sum(TABLE[mask] for mask in H)
                if score<best:best=score;witness=family
        row=dict(active_six=m,missing_four=z,admissible_families=valid,
                 exact_local_minimum_times_two=best,available_mass_times_two=8*(35-z),
                 witness=None if witness is None else [F[i] for i in witness])
        rows.append(row);print(json.dumps(row),flush=True)
    Path(__file__).with_name('root-seven-star-profile-checks.json').write_text(json.dumps(dict(status='exact finite necessary-condition exploration; not a complete critical-profile classification',rows=rows),indent=2)+'\n')

if __name__=='__main__':main()
