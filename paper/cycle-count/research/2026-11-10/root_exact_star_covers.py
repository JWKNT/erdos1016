#!/usr/bin/env python3
"""Exact half-integral triangle-cover minima on all five-vertex graphs."""
from itertools import combinations
from functools import lru_cache
from pathlib import Path
import json

EDGES=tuple(combinations(range(5),2))
TRIANGLES=tuple(sum(1<<EDGES.index(e) for e in combinations(T,2)) for T in combinations(range(5),3))

@lru_cache(None)
def fractional_cover_twice(edges):
    """Min half-integral vertex cover, in doubled units; isolated vertices omitted."""
    vertices=sorted({v for e in edges for v in e});n=len(vertices)
    if not n:return 0
    remap={v:i for i,v in enumerate(vertices)};adj=[0]*n
    for u,v in edges:adj[remap[u]]|=1<<remap[v];adj[remap[v]]|=1<<remap[u]
    best=n
    for zeros in range(1<<n):
        neighbors=0
        for i in range(n):
            if zeros>>i&1:neighbors|=adj[i]
        if neighbors&zeros:continue
        best=min(best,n-zeros.bit_count()+neighbors.bit_count())
    return best


def minimum_twice(mask):
    triangles=[T for T in TRIANGLES if T&mask==T]
    best=1000;red=mask
    while True:
        blue=mask^red;forced=[0,0];pairrows=[[],[]];valid=True
        for T in triangles:
            r=T&red;b=T&blue
            if not r or not b:valid=False;break
            for color,sub in enumerate((r,b)):
                if sub.bit_count()==1:forced[color]|=sub
                else:pairrows[color].append(tuple(i for i in range(10) if sub>>i&1))
        if valid:
            score=2*sum(f.bit_count() for f in forced)
            for color in range(2):
                rows=tuple(sorted(set(e for e in pairrows[color] if all(not(forced[color]>>v&1) for v in e))))
                score+=fractional_cover_twice(rows)
            best=min(best,score)
        if red==0:break
        red=(red-1)&mask
    assert best<1000
    return best


def main():
    vals=[minimum_twice(mask) for mask in range(1024)]
    assert vals[-1]==20
    from collections import defaultdict
    hist=defaultdict(set)
    for mask,value in enumerate(vals):hist[10-mask.bit_count()].add(value)
    out=dict(status='exact combinatorial computation',graphs=1024,
             edge_order=EDGES,minimum_mass_times_two=vals,
             values_by_missing_edges={str(k):sorted(v) for k,v in sorted(hist.items())},
             method='Color supports; singleton constraints force weight one; remaining constraints form fractional vertex cover, whose half-integral minimum is enumerated exactly.')
    Path(__file__).with_name('root-exact-star-cover-table.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out['values_by_missing_edges']))
if __name__=='__main__':main()
