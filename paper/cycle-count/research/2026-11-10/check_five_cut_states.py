#!/usr/bin/env python3
"""Exact five-cut gluing and three-port capping checks.

Independent cycle-space enumeration checks the whole glued graph. Local
path counts use DFS; four-terminal forests use affine cycle-space classes.
This checks identities, not the unfinished asymptotic five-cut theorem.
"""
import itertools
import json
from check_second_order_saturated_blocks import paths, cycles
from check_second_order_four_cut_states import forest_states, PAIRINGS

PAIRS=list(itertools.combinations(range(5),2))
QUADS=list(itertools.combinations(range(5),4))

def state(graph,order):
    n,edges,ports=graph
    v=[ports[i] for i in order]
    return ({pair:paths(n,edges,v[pair[0]],v[pair[1]]) for pair in PAIRS},
            {quad:forest_states(n,edges,[v[i] for i in quad]) for quad in QUADS})

def cap_path_prediction(p,f,cap):
    left=tuple(i for i in range(5) if i not in cap)
    total=p[left]
    for pair in itertools.combinations(cap,2):
        quad=tuple(sorted(left+pair))
        positions={v:i for i,v in enumerate(quad)}
        target={frozenset(positions[v] for v in left),frozenset(positions[v] for v in pair)}
        index=next(i for i,pairing in enumerate(PAIRINGS)
                   if {frozenset(x) for x in pairing}==target)
        total+=sum(f[quad])-f[quad][index]
    return total

def main():
    graphs=[
        (5,[(i,(i+1)%5) for i in range(5)],list(range(5))),
        (7,[(i,(i+1)%7) for i in range(7)]+[(0,3)],[1,2,4,5,6]),
        (9,[(i,(i+1)%9) for i in range(9)]+[(0,3),(5,8)],[1,2,4,6,7]),
        (7,[(0,1),(1,2),(2,0),(3,4),(4,5),(5,6),(6,3),(2,3)],[0,1,4,5,6]),
    ]
    perms=list(itertools.permutations(range(5)))
    states={(i,o):state(g,o) for i,g in enumerate(graphs) for o in perms}
    internal=[cycles(n,e) for n,e,_ in graphs]
    cap_checks=0
    for i,(n,edges,ports) in enumerate(graphs):
        p,f=states[i,tuple(range(5))]
        for cap in itertools.combinations(range(5),3):
            left=[i for i in range(5) if i not in cap]
            capped=edges+[(n,ports[i]) for i in cap]
            assert paths(n+1,capped,ports[left[0]],ports[left[1]])==cap_path_prediction(p,f,cap)
            assert cycles(n+1,capped)==internal[i]+sum(p[pair] for pair in itertools.combinations(cap,2))
            assert len(capped)-(n+1)+1==len(edges)-n+3
            cap_checks+=1
    gluing_checks=0
    for i,(n,edges,ports) in enumerate(graphs):
        p,f=states[i,tuple(range(5))]
        for j,(m,other,other_ports) in enumerate(graphs):
            for perm in perms:
                q,g=states[j,perm]
                joined=edges+[(u+n,v+n) for u,v in other]
                joined += [(ports[t],n+other_ports[perm[t]]) for t in range(5)]
                exact=cycles(n+m,joined)
                predicted=internal[i]+internal[j]+sum(p[e]*q[e] for e in PAIRS)
                predicted+=sum(sum(f[s])*sum(g[s])-sum(a*b for a,b in zip(f[s],g[s])) for s in QUADS)
                assert exact==predicted,(i,j,perm,exact,predicted)
                gluing_checks+=1
    print(json.dumps(dict(status="pass",scope="exact identities only; no five-cut asymptotic theorem",shore_graphs=len(graphs),gluing_checks=gluing_checks,three_port_cap_checks=cap_checks),indent=2))

if __name__=="__main__":
    main()
