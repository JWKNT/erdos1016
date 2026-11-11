"""Standard-library independent DFS validation of selected pole certificates."""
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent

def counts(edges,terminals,full=False):
    edges=[tuple(x) for x in edges]
    adj={}
    for i,(u,v) in enumerate(edges):
        adj.setdefault(u,[]).append((v,i))
        adj.setdefault(v,[]).append((u,i))
    cycles=set()
    for start in adj:
        def visit(v,seen,mask):
            for w,e in adj[v]:
                if w==start and len(seen)>=3:cycles.add(mask|(1<<e))
                elif w>start and w not in seen:visit(w,seen|{w},mask|(1<<e))
        visit(start,{start},0)
    paths=[]
    for i,j in ((0,1),(0,2),(1,2)):
        start,target=terminals[i],terminals[j]
        found=[]
        def visit(v,seen,mask):
            if v==target:
                found.append(mask);return
            for w,e in adj[v]:
                if w not in seen:visit(w,seen|{w},mask|(1<<e))
        visit(start,{start},0)
        assert len(found)==len(set(found))
        paths.append(found)
    states=[cycles]+paths
    totals=[len(x) for x in states]
    freq=[[sum((mask>>e)&1 for mask in ss) for ss in states] for e in range(len(edges))]
    return (totals,freq,states) if full else (totals,freq)

def main():
    data=json.loads((BASE/"random-edge-half-profiles.json").read_text())
    checked=0;states=0
    for row in data["nonuniversal"]:
        totals,freq=counts(row["edges"],row["terminals"])
        assert totals==row["totals"]
        edgeindex={tuple(e):i for i,e in enumerate(row["edges"])}
        alpha=[Fraction(0)]*len(freq)
        for term in row["dual"]:alpha[edgeindex[tuple(term["edge"])]]=Fraction(term["weight"])
        assert sum(alpha)==1
        sums=[sum(alpha[e]*(2*freq[e][j]-totals[j]-(j==0)) for e in range(len(freq))) for j in range(4)]
        assert [str(x) for x in sums]==row["exact_dual_sums"]
        assert max(sums)<=0
        states+=sum(totals);checked+=1
    example=data["first_terminal_failures"][0]
    totals,freq=counts(example["edges"],example["terminals"])
    assert totals==[7,7,7,7]
    pairs=[(0,1),(0,2),(1,2)]
    visits=[]
    for i,v in enumerate(example["terminals"]):
        e=next(j for j,edge in enumerate(example["edges"]) if v in edge)
        other=pairs.index(tuple(j for j in range(3) if j!=i))+1
        visits.append(freq[e][other])
    assert visits==[4,4,4]
    result=dict(status="all independent exact DFS checks passed",
                certified_poles=checked,enumerated_cycles_and_paths=states,
                terminal_local_counterexample=dict(edges=example["edges"],terminals=example["terminals"],
                                                   totals=totals,other_terminal_visits=visits,
                                                   edge_counts=freq),
                scope="Finite certificates only; no general weighted theorem inferred.")
    (BASE/"random-edge-half-independent-dfs.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="terminal_local_counterexample"},indent=2))

if __name__=="__main__":main()
