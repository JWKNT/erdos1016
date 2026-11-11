"""Search the weighted three-pole inequality using exact integer counts.

The LP only proposes witnesses. Any positive witness is rechecked with
rational arithmetic here, and must receive a separate DFS audit.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import time

import numpy as np
from scipy.optimize import linprog

BASE=Path(__file__).resolve().parent
def decode(s):
    n=ord(s[0])-63
    es=[]; bit=0
    for j in range(1,n):
        for i in range(j):
            if ((ord(s[1+bit//6])-63)>>(5-bit%6))&1: es.append((i,j))
            bit+=1
    return n,es

def solve(record):
    tok=record.split()
    g6=tok[0]; removed=int(tok[1])
    vals=list(map(int,tok[2:])); totals=vals[:4]
    rows=[vals[i:i+4] for i in range(4,len(vals),4)]
    diff=[[2*x-y-(j==0) for j,(x,y) in enumerate(zip(row,totals))] for row in rows]
    if any(all(x<=0 for x in row) for row in diff):
        return "universal_edge",None
    mat=np.array(diff,dtype=float)
    # Scale per coordinate, keeping the existence problem unchanged.
    scales=np.maximum(1,np.max(abs(mat),axis=0))
    z=mat/scales
    lp=linprog([0,0,0,0,-1],A_ub=np.column_stack([-z,np.ones(len(z))]),
               b_ub=np.zeros(len(z)),A_eq=[[1,1,1,1,0]],b_eq=[1],
               bounds=[(0,None)]*4+[(None,None)],method="highs")
    if not lp.success: raise RuntimeError(lp.message)
    margin=-lp.fun
    if margin<1e-8:
        alpha=[Fraction(float(-x)).limit_denominator(10**8) for x in lp.ineqlin.marginals]
        sa=sum(alpha)
        alpha=[x/sa for x in alpha]
        sums=[sum(alpha[i]*diff[i][j] for i in range(len(diff))) for j in range(4)]
        if min(alpha)<0 or max(sums)>0:
            raise RuntimeError("Numerical feasible result lacks an exact dual certificate")
        cert=dict(graph6=g6,deleted_vertex=removed,totals=totals,
                  edge_coefficients=diff,
                  edge_distribution=[str(x) for x in alpha],
                  exact_sums=[str(x) for x in sums])
        return ("strict_feasible" if margin<-1e-8 else "tight"),cert
    coeff=[Fraction(float(x/s)).limit_denominator(10**8) for x,s in zip(lp.x[:4],scales)]
    if coeff[0]==0:
        # Introduce a positive finite coefficient on the cycle term.
        pos=min(sum(a*b for a,b in zip(row,coeff)) for row in diff)
        coeff[0]=pos/(2*(1+max(abs(row[0]) for row in diff)))
    residual=[sum(a*b for a,b in zip(row,coeff)) for row in diff]
    if min(residual)<=0: raise RuntimeError("Failed exact rational witness")
    w=[x/coeff[0] for x in coeff[1:]]
    n,edges=decode(g6)
    terms=sorted(v if u==removed else u for u,v in edges if removed in (u,v))
    witness=dict(graph6=g6,deleted_vertex=removed,ambient_order=n,
                 edges=[e for e in edges if removed not in e],terminals=terms,
                 totals=totals,edge_counts=rows,differences=diff,
                 weights=[str(x) for x in w],
                 minimum_violation=str(min(residual)/coeff[0]),
                 compact_margin=margin)
    return "violation",witness

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--min-order",type=int,default=4)
    ap.add_argument("--max-order",type=int,default=16)
    ap.add_argument("--girth-five",action="store_true")
    ap.add_argument("--input")
    ap.add_argument("--name",default="catalog")
    ap.add_argument("--stop",action="store_true")
    args=ap.parse_args()
    out=BASE/f"random-edge-half-{args.name}.json"
    result=dict(scope=vars(args),status="running",orders=[],violations=[],exact_dual_certificates=[])
    begin=time.time()
    if args.input: orders=[None]
    else: orders=range(args.min_order,args.max_order+1,2)
    for n in orders:
        if n is None:
            src=open(args.input)
        else:
            flags=["/tmp/nauty2_8_9/geng","-cq","-d3","-D3"]
            if args.girth_five: flags+=["-t","-f"]
            flags+=[str(n)]
            gen=subprocess.Popen(flags,stdout=subprocess.PIPE)
            src=gen.stdout
        cnt=subprocess.Popen(["/tmp/random-edge-half-count","--only-nonuniversal"],stdin=src,
                             stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,bufsize=1)
        hist={}
        for line in cnt.stdout:
            status,wit=solve(line)
            hist[status]=hist.get(status,0)+1
            if wit and status!="violation":
                result["exact_dual_certificates"].append(wit)
            if wit and status=="violation":
                result["violations"].append(wit)
                out.write_text(json.dumps(result,indent=2)+"\n")
                print("EXACT VIOLATION",json.dumps(wit),flush=True)
                if args.stop:
                    cnt.terminate()
                    if n is not None: gen.terminate()
                    result["status"]="exact violation found"
                    result["orders"].append(dict(order=n,counts=hist))
                    result["seconds"]=time.time()-begin
                    out.write_text(json.dumps(result,indent=2)+"\n")
                    return
        if cnt.wait()!=0: raise RuntimeError("counter process failed")
        counter_summary=json.loads(cnt.stderr.read())
        hist["universal_edge"]=counter_summary["universal_edges"]
        if n is not None and gen.wait()!=0: raise RuntimeError("geng process failed")
        result["orders"].append(dict(order=n,counts=hist,counter=counter_summary))
        result["seconds"]=time.time()-begin
        out.write_text(json.dumps(result,indent=2)+"\n")
        print(n,hist,round(time.time()-begin,2),flush=True)
    result["status"]="search complete"
    out.write_text(json.dumps(result,indent=2)+"\n")

if __name__=="__main__": main()
