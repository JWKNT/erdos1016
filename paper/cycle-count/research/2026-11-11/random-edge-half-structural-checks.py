"""Independent finite checks of terminal and mean-length obstructions."""
from fractions import Fraction
import importlib.util
import itertools
import json
import math
from pathlib import Path

BASE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location("dfs",BASE/"random-edge-half-independent-dfs.py")
dfs=importlib.util.module_from_spec(sp);sp.loader.exec_module(dfs)

def connected(vertices,edges,removed=()):
    adj={v:[] for v in vertices}
    for i,(u,v) in enumerate(edges):
        if i not in removed:adj[u].append(v);adj[v].append(u)
    seen={min(vertices)};todo=list(seen)
    for v in todo:
        for w in adj[v]:
            if w not in seen:seen.add(w);todo.append(w)
    return len(seen)==len(vertices)

def girth(vertices,edges):
    adj={v:[] for v in vertices}
    for u,v in edges:adj[u].append(v);adj[v].append(u)
    ans=10**9
    for s in vertices:
        dist={s:0};par={s:None};todo=[s]
        for v in todo:
            for w in adj[v]:
                if w not in dist:dist[w]=dist[v]+1;par[w]=v;todo.append(w)
                elif par[v]!=w:ans=min(ans,dist[v]+dist[w]+1)
    return ans

def main():
    # The girth-five counterexample to terminal-local averaging.
    f=BASE/"random-edge-half-girth5-terminal-counterexample.json"
    terminal=json.loads(f.read_text())
    totals,freq,states=dfs.counts(terminal["edges"],terminal["terminals"],True)
    assert totals==[57,43,43,43] and freq==terminal["edge_counts"]
    visits=[];slacks=[]
    for i,t in enumerate(terminal["terminals"]):
        e=next(j for j,edge in enumerate(terminal["edges"]) if t in edge)
        other=3-i
        visits.append(freq[e][other])
        slacks.append([2*freq[e][0]-totals[0]-1,2*freq[e][other]-totals[other]])
    assert visits==[28]*3 and slacks==[[-2,13]]*3
    terminal.update(independent_dfs="PASS",terminal_surpluses=slacks)
    f.write_text(json.dumps(terminal,indent=2)+"\n")

    source=json.loads((BASE/"path-edge-half-path-mean-check.json").read_text())["first_all_pair_failure"]
    removed=source["deleted"]
    all_edges=[tuple(e) for e in source["edges"]]
    edges=[e for e in all_edges if removed not in e]
    terms=sorted(b if a==removed else a for a,b in all_edges if removed in (a,b))
    tot,ef,sets=dfs.counts(edges,terms,True)
    lengths=[sum(mask.bit_count() for mask in ss) for ss in sets]
    assert tot==[29,26,27,27] and lengths==[219,190,197,197]
    vertices=sorted({v for e in edges for v in e})
    assert len(vertices)==11 and terms==[4,7,10]

    base_edges=[(u,v) for u in range(3) for v in range(3,6)]
    base_adj={v:sorted(w if u==v else u for u,w in base_edges if v in (u,w)) for v in range(6)}
    _,_,bs=dfs.counts(base_edges,[0,1,2],True)
    cycles=bs[0];assert len(cycles)==15
    pairs=[(0,1),(0,2),(1,2)]
    total=6*tot[0];length=6*lengths[0]
    internal_freq=[[x[0] for x in ef] for v in range(6)]
    cut_freq=[0]*9
    for mask in cycles:
        edgeids=[i for i in range(9) if (mask>>i)&1]
        selected={}
        for v in range(6):
            ns=[w if u==v else u for i in edgeids for u,w in [base_edges[i]] if v in (u,w)]
            if ns:
                idx=tuple(sorted(base_adj[v].index(w) for w in ns))
                selected[v]=1+pairs.index(idx)
        mass=math.prod(tot[j] for j in selected.values())
        total+=mass
        length+=len(edgeids)*mass+sum(lengths[j]*(mass//tot[j]) for j in selected.values())
        for e in edgeids:cut_freq[e]+=mass
        for v,j in selected.items():
            for e in range(len(edges)):internal_freq[v][e]+=ef[e][j]*(mass//tot[j])
    assert total==2160078826 and length==107497549026

    index={v:i for i,v in enumerate(vertices)}
    expanded=[(11*b+index[u],11*b+index[v]) for b in range(6) for u,v in edges]
    for v,w in base_edges:
        tv=terms[base_adj[v].index(w)];tw=terms[base_adj[w].index(v)]
        expanded.append((11*v+index[tv],11*w+index[tw]))
    assert len(expanded)==99
    verts=list(range(66))
    assert girth(verts,expanded)==5
    cut_checks=0
    for i in range(99):
        for j in range(i):
            assert connected(verts,expanded,{i,j})
            cut_checks+=1
    freq_all=sum(internal_freq,[])+cut_freq
    assert sum(freq_all)==length
    result=dict(status="all independent exact checks passed",
                pole_totals=tot,pole_length_sums=lengths,
                graph_order=66,graph_edges=expanded,girth=5,
                cycle_count=total,cycle_length_sum=length,
                mean=str(Fraction(length,total)),mean_threshold="99/2",
                fourfold_mean_excess=4*length-3*66*total,
                minimum_edge_cycle_count=min(freq_all),
                edge_half_holds=(2*min(freq_all)<=total),
                deleted_edge_pairs_checked=cut_checks,
                method="Independent DFS for the pole and base; exact three-sum cycle products; exhaustive deletion of every pair of expanded edges.")
    (BASE/"random-edge-half-mean-expansion-check.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="graph_edges"},indent=2))

if __name__=="__main__":main()
