#!/usr/bin/env python3
"""Exhaustive finite cut checks and independent cycle/path identities."""
from pathlib import Path
import json
from check_root_shortest_cycle_prefix import components, rank, paths, cycle_space_count


def minimum_cuts(V, E):
    vertices=sorted(V); root=vertices[0]; cuts=[]; best=len(E)+1
    for mask in range(1,1<<(len(vertices)-1)):
        A={vertices[i+1] for i in range(len(vertices)-1) if mask>>i&1}
        B=V-A; cross=[i for i,(u,v) in enumerate(E) if (u in A)!=(v in A)]
        if len(cross)>best: continue
        if rank(A,[e for e in E if set(e)<=A])<1: continue
        if rank(B,[e for e in E if set(e)<=B])<1: continue
        if len(cross)<best: best=len(cross); cuts=[]
        cuts.append((A,cross))
    return best,cuts


def check(name,V,E):
    k,cuts=minimum_cuts(V,E); total=cycle_space_count(V,E); checks=0
    cached={}
    for A,cut in cuts:
        B=V-A
        assert len(components(A,[e for e in E if set(e)<=A]))==1
        assert len(components(B,[e for e in E if set(e)<=B]))==1
        assert len({u for i in cut for u in E[i]})==2*k
        for eid in cut:
            u,v=E[eid]; N=E[:eid]+E[eid+1:]
            W=V-{u,v}; F=list(N)
            for terminal in (u,v):
                touched=[e for e in F if terminal in e]
                assert len(touched)==2
                other=[b if a==terminal else a for a,b in touched]
                F=[e for e in F if terminal not in e]+[tuple(other)]
            assert rank(W,F)==rank(V,E)-1
            assert all(a!=b for a,b in F)
            if eid not in cached:
                newk,_=minimum_cuts(W,F)
                p=paths(V,N,u,v); count=cycle_space_count(W,F)
                assert newk==k-1 and total==count+p
                cached[eid]=(newk,count,p)
            for shore in (A,B):
                before=rank(shore,[e for e in E if set(e)<=shore])
                after=rank(shore&W,[e for e in F if set(e)<=shore&W])
                assert before==after
            checks+=1
    return dict(name=name,rank=rank(V,E),minimum_cyclic_cut=k,
                minimum_cuts=len(cuts),cut_edge_checks=checks,
                independently_enumerated_deletions=len(cached),cycles=total,
                path_counts=sorted(set(v[2] for v in cached.values())))


def main():
    E=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]
    E += [(i+5,(i+2)%5+5) for i in range(5)]
    rows=[check('Petersen',set(range(10)),E)]
    E=[(i,(i+1)%14) for i in range(14)]
    E += [(i,(i+5)%14) for i in range(0,14,2)]
    rows.append(check('Heawood',set(range(14)),E))
    out=dict(status='PASS',graphs=rows,
             scope='All cyclic vertex cuts in these graphs; every minimum-cut smoothing; exact cycle-space and path-DFS identities.')
    Path(__file__).with_name('root-cut-smoothing-checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
