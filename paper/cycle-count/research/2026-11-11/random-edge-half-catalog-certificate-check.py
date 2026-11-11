"""Independent stdlib DFS audit of every nontrivial catalogue certificate."""
from fractions import Fraction
import importlib.util
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location("dfs",BASE/"random-edge-half-independent-dfs.py")
dfs=importlib.util.module_from_spec(sp);sp.loader.exec_module(dfs)

def decode(s):
    n=ord(s[0])-63
    bits="".join(f"{ord(c)-63:06b}" for c in s[1:])
    edges=[];index=0
    for v in range(1,n):
        for u in range(v):
            if bits[index]=="1":edges.append((u,v))
            index+=1
    return edges

def main():
    data=json.loads((BASE/"random-edge-half-exact-catalog-through20.json").read_text())
    assert data["status"]=="search complete" and not data["violations"]
    families=states=0;local_failures=[]
    for row in data["exact_dual_certificates"]:
        all_edges=decode(row["graph6"]);v=row["deleted_vertex"]
        edges=[e for e in all_edges if v not in e]
        terms=sorted(b if a==v else a for a,b in all_edges if v in (a,b))
        totals,freq=dfs.counts(edges,terms)
        assert totals==row["totals"]
        diff=[[2*x-y-(j==0) for j,(x,y) in enumerate(zip(r,totals))] for r in freq]
        assert diff==row["edge_coefficients"]
        alpha=list(map(Fraction,row["edge_distribution"]))
        assert min(alpha)>=0 and sum(alpha)==1
        sums=[sum(alpha[e]*diff[e][j] for e in range(len(edges))) for j in range(4)]
        assert max(sums)<=0 and list(map(str,sums))==row["exact_sums"]
        pairs=[(0,1),(0,2),(1,2)];good=False
        for i,t in enumerate(terms):
            e=next(j for j,edge in enumerate(edges) if t in edge)
            other=pairs.index(tuple(j for j in range(3) if j!=i))+1
            good |= 2*freq[e][0]<=totals[0]+1 and 2*freq[e][other]<=totals[other]
        if not good:local_failures.append(dict(graph6=row["graph6"],deleted_vertex=v))
        families+=1;states+=sum(totals)
    result=dict(status="all independent exact DFS certificate checks passed",
                nontrivial_certificates=families,cycles_and_paths=states,
                failures_of_combined_universal_or_terminal_test=local_failures,
                catalogue_graphs=sum(r["counter"]["graphs"] for r in data["orders"]),
                connected_deleted_vertex_poles=sum(r["counter"]["poles"] for r in data["orders"]),
                scope="All connected simple cubic ambient graphs through order20; repeated isomorphic poles are retained.")
    (BASE/"random-edge-half-catalog-certificate-check.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=="__main__":main()
