#!/usr/bin/env python3
"""Check all local formulas on bounded capped ladders, plus sharp examples."""
import json
from check_second_order_saturated_blocks import paths


def compositions(k):
    if k==0:
        yield ()
    for z in (1,2):
        if z<=k:
            for tail in compositions(k-z):yield (z,)+tail


def capped_ladder(blocks):
    k=sum(blocks);a=2*k;c=2*k+1
    edges=[];spec=[];prefix_cap={0:1};p=0
    def put(u,v,kind,pref):
        edges.append((u,v));spec.append((kind,pref))
    put(a,0,'interface',0);put(a,k,'interface',0)
    for size in blocks:
        if size==1:
            put(p,k+p,'single',p)
            prefix_cap[p+1]=prefix_cap[p]+1
        else:
            for u,v in [(p,p+1),(k+p,k+p+1),(p,k+p+1),(p+1,k+p)]:
                put(u,v,'square',p)
            prefix_cap[p+2]=2+2*prefix_cap[p]
        p+=size
        if p<k:
            put(p-1,p,'interface',p);put(k+p-1,k+p,'interface',p)
    put(k-1,c,'interface',k);put(2*k-1,c,'interface',k)
    return 2*k+2,edges,a,c,spec,prefix_cap


def main():
    rows=[];witness=None
    for k in range(1,11):
        checked=pieces=0;max_nonfull=0
        for blocks in compositions(k):
            n,edges,a,c,spec,cap=capped_ladder(blocks)
            rank=k+1;full=2**rank
            assert len(edges)-n+1==rank
            assert paths(n,edges,a,c)==full
            for i,((u,v),(kind,p)) in enumerate(zip(edges,spec)):
                q=k-p
                if kind=='interface':expected=(1+cap[p])*2**q
                elif kind=='single':expected=2*(1+cap[p])*2**(q-1)
                else:expected=(4+3*cap[p])*2**(q-2)
                new=edges[:i]+edges[i+1:]+[(u,n),(n,v)]
                val=paths(n+1,new,n,c)
                assert val==expected,(blocks,i,kind,p,val,expected)
                assert val==full or 8*val<=7*full
                if val<full:max_nonfull=max(max_nonfull,val/full)
                if k==2 and kind=='square' and witness is None:
                    # Add s adjacent to the original left terminal and new b.
                    final=new+[(n+1,a),(n+1,n)]
                    assert len(final)-(n+2)+1==4
                    assert paths(n+2,final,n+1,c)==15
                    witness=dict(vertices=n+2,edges=final,terminals=[n+1,c],rank=4,paths=15)
                checked+=1
            pieces+=1
        rows.append(dict(positions=k,pieces=pieces,subdivision_checks=checked,max_nonfull_ratio=max_nonfull))
    print(json.dumps(dict(local_formula_checks=rows,sharp_gap_witness=witness),indent=2))


if __name__=='__main__':main()
