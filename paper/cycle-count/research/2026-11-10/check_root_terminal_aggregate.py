#!/usr/bin/env python3
"""Exact independent check of the marked-tree parity-fiber construction."""
import itertools
import json


def even_masks(n,edges):
    adj=[[] for _ in range(n)]
    for i,(u,v) in enumerate(edges):
        adj[u].append((v,i));adj[v].append((u,i))
    parents={0:(-1,-1)};todo=[0];roots=[0]*n
    for u in todo:
        for v,i in adj[u]:
            if v not in parents:
                parents[v]=(u,i);roots[v]=roots[u]^(1<<i);todo.append(v)
    tree={i for _,i in parents.values()}
    basis=[roots[u]^roots[v]^(1<<i) for i,(u,v) in enumerate(edges) if i not in tree]
    for word in range(1<<len(basis)):
        x=0
        for i,b in enumerate(basis):
            if word>>i&1:x^=b
        yield x


def is_forest(n,edges,mask):
    uf=list(range(n))
    def find(v):
        while uf[v]!=v:v=uf[v]
        return v
    for i,(u,v) in enumerate(edges):
        if mask>>i&1:
            a,b=find(u),find(v)
            if a==b:return False
            uf[a]=b
    return True


def tree_with_leaves(k):
    n=2;edges=[(0,1)];leaves=[0,1]
    for _ in range(k-2):
        old=leaves.pop();i=next(i for i,e in enumerate(edges) if old in e)
        u,v=edges.pop(i);new=n;leaf=n+1;n+=2
        edges.extend([(u,new),(v,new),(new,leaf)])
        leaves.extend([old,leaf])
    return n,edges,leaves


def main():
    rows=[]
    for k in range(2,7):
        for q in range(3):
            n=k+2*q
            edges=[(i,(i+1)%n) for i in range(n)]
            edges += [(2*i,2*i+1) for i in range(q)]
            ports=list(range(2*q,n));h=len(edges)-n+1
            tn,te,leaves=tree_with_leaves(k)
            glued=edges+[(u+n,v+n) for u,v in te]+[(p,n+l) for p,l in zip(ports,leaves)]
            assert len(glued)-(n+tn)+1==h+k-1
            restrictions={};fiber={};outside_forests=0
            for word in even_masks(n+tn,glued):
                internal=word & ((1<<len(edges))-1)
                restrictions[internal]=restrictions.get(internal,0)+1
                odd=0
                for i,(u,v) in enumerate(edges):
                    if internal>>i&1:odd^=(1<<u)|(1<<v)
                fiber[odd]=fiber.get(odd,0)+1
                outside_forests+=is_forest(n,edges,internal)
            expected={};local_forests=0
            for internal in range(1<<len(edges)):
                odd=0
                for i,(u,v) in enumerate(edges):
                    if internal>>i&1:odd^=(1<<u)|(1<<v)
                if odd & ~sum(1<<p for p in ports):continue
                expected[internal]=1
                local_forests+=is_forest(n,edges,internal)
            assert restrictions==expected
            assert len(fiber)==2**(k-1) and set(fiber.values())=={2**h}
            assert outside_forests==local_forests
            rows.append(dict(ports=k,rank=h,parity_patterns=len(fiber),even_extensions=len(restrictions),forests=local_forests))
    print(json.dumps(dict(status='pass',cases=rows,total_extensions=sum(x['even_extensions'] for x in rows)),indent=2))

if __name__=='__main__':main()
