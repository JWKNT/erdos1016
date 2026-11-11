"""Extract exact stronger-test failures and small LP dual supports."""
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import numpy as np
from scipy.optimize import linprog
from importlib.util import spec_from_file_location,module_from_spec

BASE=Path(__file__).resolve().parent
sp=spec_from_file_location("search",BASE/"random-edge-half-search.py")
search=module_from_spec(sp);sp.loader.exec_module(search)

def inspect(line):
    tok=line.split();g6=tok[0];deleted=int(tok[1])
    val=list(map(int,tok[2:]));tot=val[:4]
    freq=[val[i:i+4] for i in range(4,len(val),4)]
    n,all_edges=search.decode(g6)
    edges=[e for e in all_edges if deleted not in e]
    terms=sorted(v if u==deleted else u for u,v in all_edges if deleted in (u,v))
    pairs=[(0,1),(0,2),(1,2)]
    terminal=[]
    for i,v in enumerate(terms):
        edge=next(j for j,e in enumerate(edges) if v in e)
        other=pairs.index(tuple(j for j in range(3) if j!=i))+1
        terminal.append([freq[edge][0],freq[edge][other],tot[other],
                         2*freq[edge][0]<=tot[0]+1 and 2*freq[edge][other]<=tot[other]])
    diff=[[2*x-y-(j==0) for j,(x,y) in enumerate(zip(row,tot))] for row in freq]
    universal=any(all(x<=0 for x in row) for row in diff)
    data=dict(graph6=g6,deleted_vertex=deleted,ambient_order=n,edges=edges,
              terminals=terms,totals=tot,terminal_tests=terminal)
    if not universal:
        # Minimize the largest original unscaled coefficient under edge weights.
        A=np.array(diff,dtype=float).T
        lp=linprog([0]*len(edges)+[1],
                   A_ub=np.column_stack([A,-np.ones(4)]),b_ub=np.zeros(4),
                   A_eq=[[1]*len(edges)+[0]],b_eq=[1],
                   bounds=[(0,None)]*len(edges)+[(None,None)],method="highs")
        if not lp.success:raise RuntimeError(lp.message)
        alpha=[Fraction(float(x)).limit_denominator(1000000) for x in lp.x[:-1]]
        sums=[sum(alpha[i]*diff[i][j] for i in range(len(edges))) for j in range(4)]
        data.update(dual_max=lp.fun,
                    dual=[dict(edge=edges[i],weight=str(a)) for i,a in enumerate(alpha) if a],
                    exact_dual_sums=[str(x) for x in sums],
                    exact_dual_valid=(sum(alpha)==1 and max(sums)<=0))
    return universal,any(x[-1] for x in terminal),data

def main():
    hist=Counter();fail=[];special=[]
    for n in range(4,18,2):
        gen=subprocess.Popen(["/tmp/nauty2_8_9/geng","-cq","-d3","-D3",str(n)],stdout=subprocess.PIPE)
        cnt=subprocess.Popen(["/tmp/random-edge-half-count"],stdin=gen.stdout,stdout=subprocess.PIPE,text=True)
        for line in cnt.stdout:
            universal,local,data=inspect(line)
            hist[f"n{n}:universal:{universal}:terminal:{local}"]+=1
            if not local and len(fail)<30:fail.append(data)
            if not universal:special.append(data)
        assert cnt.wait()==gen.wait()==0
        print(n,dict(hist),flush=True)
    result=dict(counts=dict(hist),first_terminal_failures=fail,nonuniversal=special)
    (BASE/"random-edge-half-profiles.json").write_text(json.dumps(result,indent=2)+"\n")

if __name__=="__main__":main()
