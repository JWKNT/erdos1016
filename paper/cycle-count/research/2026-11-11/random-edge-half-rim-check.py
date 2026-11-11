"""Exact independent DFS checks of the triangle/square weighted identities."""
import importlib.util
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location("dfs",BASE/"random-edge-half-independent-dfs.py")
dfs=importlib.util.module_from_spec(sp);sp.loader.exec_module(dfs)

data=json.loads((BASE/"random-edge-half-profiles.json").read_text())
fixtures=data["nonuniversal"]+data["first_terminal_failures"]
cases=0;chorded=0;terminal_rims=0;counted_states=0
for row in fixtures:
    edges=row["edges"];terms=row["terminals"]
    totals,freq,states=dfs.counts(edges,terms,True)
    counted_states+=sum(totals)
    for mask in states[0]:
        q=mask.bit_count()
        if q not in (3,4):continue
        es=[i for i in range(len(edges)) if (mask>>i)&1]
        U=set(x for i in es for x in edges[i])
        forbidden=sum(1<<i for i,e in enumerate(edges) if U.intersection(e))
        if q==4 and any(set(e)<=U and i not in es for i,e in enumerate(edges)):chorded+=1
        if U.intersection(terms):terminal_rims+=1
        avoided=[sum(not(s&forbidden) for s in family) for family in states]
        for j in range(4):
            lhs=2*sum(freq[e][j] for e in es)
            rhs=q*(totals[j]+(j==0)-avoided[j])
            assert lhs==rhs,(row,mask,j,lhs,rhs)
        cases+=1
result=dict(status="all exact short-rim identities passed",fixtures=len(fixtures),
            rim_cases=cases,chorded_square_cases=chorded,rims_containing_terminals=terminal_rims,
            separately_checked_cycle_and_path_identities=4*cases,states=counted_states)
(BASE/"random-edge-half-rim-check.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
