#!/usr/bin/env python3
"""Independent exact checks of saturated-tripole product and distance bounds."""
import itertools
import json
from collections import deque
from check_second_order_path_gap import compositions, capped_ladder
from check_second_order_saturated_blocks import paths


def distance(n,edges,s,t):
    adj=[[] for _ in range(n)]
    for u,v in edges:
        adj[u].append(v);adj[v].append(u)
    todo=deque([s]);seen={s:0}
    while todo:
        u=todo.popleft()
        if u==t:return seen[u]
        for v in adj[u]:
            if v not in seen:seen[v]=seen[u]+1;todo.append(v)
    raise AssertionError('Disconnected terminals')


def check(n,edges,a,c):
    h=len(edges)-n+1
    assert paths(n,edges,a,c)==2**h
    for i,(u,v) in enumerate(edges):
        new=edges[:i]+edges[i+1:]+[(u,n),(n,v)]
        left=paths(n+1,new,a,n);right=paths(n+1,new,n,c)
        assert (left*right)**2 <= 49*2**(3*h)
        assert left**2 * 2**distance(n+1,new,n,c) <= 18*2**(2*h)
        assert right**2 * 2**distance(n+1,new,n,a) <= 18*2**(2*h)
    return len(edges)


def main():
    single=series=0
    for k in range(1,11):
        for blocks in compositions(k):
            n,e,a,c,_,_=capped_ladder(blocks)
            single+=check(n,e,a,c)
    small=[(2,[(0,1),(0,1)],0,1)]
    for k in range(1,4):
        for blocks in compositions(k):
            n,e,a,c,_,_=capped_ladder(blocks)
            small.append((n,e,a,c))
    for (n,e,a,c),(m,f,s,t) in itertools.product(small,repeat=2):
        series+=check(n+m,e+[(u+n,v+n) for u,v in f]+[(c,n+s)],a,n+t)
    print(json.dumps(dict(status='pass',single_piece_subdivisions=single,
                         series_subdivisions=series,
                         checks_per_subdivision=['squared_product_bound','left_density_distance','right_density_distance']),indent=2))

if __name__=='__main__':main()
