#!/usr/bin/env python3
"""Exact finite checks for the saturated-block proofs, including multiedges."""
import json
from pathlib import Path


def adjacency(n, edges):
    a = [[] for _ in range(n)]
    for u,v in edges:
        assert u != v
        a[u].append(v)
        a[v].append(u)
    return a


def paths(n,edges,s,t):
    a = adjacency(n,edges)
    def go(v,seen):
        if v == t:
            return 1
        return sum(go(w,seen|(1<<w)) for w in a[v] if not (seen>>w)&1)
    return go(s,1<<s)


def cycles(n,edges):
    """Enumerate the binary cycle space; count connected degree-two supports."""
    a = [[] for _ in range(n)]
    for i,(u,v) in enumerate(edges):
        a[u].append((v,i));a[v].append((u,i))
    parent = {0:(-1,-1)}
    todo = [0]
    for v in todo:
        for w,e in a[v]:
            if w not in parent:
                parent[w]=(v,e);todo.append(w)
    assert len(parent)==n
    tree = {e for v,e in parent.values() if e>=0}
    rootpaths = [0]*n
    for v in todo[1:]:
        w,e=parent[v];rootpaths[v]=rootpaths[w]^(1<<e)
    basis = [rootpaths[u]^rootpaths[v]^(1<<i)
             for i,(u,v) in enumerate(edges) if i not in tree]
    count = 0
    for mask in range(1,1<<len(basis)):
        support=0
        for i,b in enumerate(basis):
            if (mask>>i)&1:support^=b
        deg=[0]*n;sel=[]
        for i,(u,v) in enumerate(edges):
            if (support>>i)&1:deg[u]+=1;deg[v]+=1;sel.append((u,v))
        if any(d not in (0,2) for d in deg):continue
        chosen={v for v,d in enumerate(deg) if d}
        seen={next(iter(chosen))}
        while True:
            nxt=seen|{v for u,v in sel if u in seen}|{u for u,v in sel if v in seen}
            if nxt==seen:break
            seen=nxt
        if seen==chosen:count+=1
    return count


def extremal_three_pole(h):
    if h==1:return 3,[(0,1),(1,2),(2,0)],(0,1,2)
    pi=list(range(h))
    for i in range(0,h-1,2):pi[i],pi[i+1]=pi[i+1],pi[i]
    edges=([(i,i+1) for i in range(h-1)]
           +[(h+i,h+i+1) for i in range(h-1)]
           +[(i,h+pi[i]) for i in range(h)]
           +[(2*h,h-1),(2*h,2*h-1)])
    return 2*h+1,edges,(0,h,2*h)


def normalize_after_deletion(n,edges,s,t,index):
    edges=edges[:index]+edges[index+1:]
    active=set(range(n))
    while True:
        inc=[i for i,(u,v) in enumerate(edges) if s in (u,v)]
        if len(inc)!=1:break
        i=inc[0];u,v=edges.pop(i);nxt=v if u==s else u
        active.remove(s);s=nxt
        assert s!=t
    while True:
        choice=None
        for v in active-{s,t}:
            inc=[i for i,e in enumerate(edges) if v in e]
            if len(inc)==2:choice=(v,inc);break
        if choice is None:break
        v,(i,j)=choice
        x=edges[i][0] if edges[i][1]==v else edges[i][1]
        y=edges[j][0] if edges[j][1]==v else edges[j][1]
        assert x!=y, 'unexpected pendant cycle'
        edges=[e for k,e in enumerate(edges) if k not in (i,j)]+[(x,y)]
        active.remove(v)
    order=sorted(active);remap={v:i for i,v in enumerate(order)}
    return len(order),[(remap[u],remap[v]) for u,v in edges],remap[s],remap[t]


def main():
    rows=[]
    for h in range(1,13):
        n,edges,(a,b,c)=extremal_three_pole(h)
        expected=(3*2**(h//2)-2) if h%2==0 else (4*2**(h//2)-2)
        assert len(edges)-n+1==h
        assert paths(n,edges,a,c)==paths(n,edges,b,c)==2**h
        assert paths(n,edges,a,b)==expected
        # Add a new terminal joined to a,b; this gives a saturated two-pole.
        n2=n+1;edges2=edges+[(n,a),(n,b)];s=n;t=c;rank=h+1
        assert paths(n2,edges2,s,t)==2**rank
        count=cycles(n2,edges2)
        M=lambda j:(3*2**(j//2)-2) if j%2==0 else (4*2**(j//2)-2)
        assert count<=sum(M(j)-1 for j in range(1,rank+1))
        normalization_checks=0
        for endpoint,other in [(s,t),(t,s)]:
            for i,e in enumerate(edges2):
                if endpoint not in e:continue
                nn,ee,ss,tt=normalize_after_deletion(n2,edges2,endpoint,other,i)
                assert len(ee)-nn+1==rank-1
                aa=adjacency(nn,ee)
                assert all(len(aa[v])==(2 if v in (ss,tt) else 3) for v in range(nn))
                assert paths(nn,ee,ss,tt)==2**(rank-1)
                normalization_checks+=1
        rows.append(dict(rank=h,cap_paths=expected,two_pole_cycles=count,
                         normalization_checks=normalization_checks))
    root=Path(__file__).resolve().parent
    searches=[]
    for row in map(json.loads,(root/'second-order-three-pole-search.jsonl').read_text().splitlines()):
        h=row['rank'];edges=row['edges'];n=2*h+1
        assert paths(n,edges,0,2)==paths(n,edges,1,2)==2**h
        assert paths(n,edges,0,1)==row['cap_paths']
        searches.append(dict(rank=h,cap_paths=row['cap_paths']))
    print(json.dumps(dict(equality_families=rows,independent_search_checks=searches),indent=2))


if __name__=='__main__':main()
