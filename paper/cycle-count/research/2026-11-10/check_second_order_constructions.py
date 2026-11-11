#!/usr/bin/env python3
"""Exact path checks for second-order constructions. No search optimality claim."""
from collections import deque
import json


def hk_even(q):
    """MC_(2q): q squares joined cyclically by two matching edges."""
    assert q >= 2
    edges = []
    for j in range(q):
        a, b, c, d = (4*j+i for i in range(4))
        edges += [(a,c), (a,d), (b,c), (b,d)]
        nxt = 4*((j+1) % q)
        edges += [(c,nxt), (d,nxt+1)]
    return 4*q, edges


def paths(n, edges, s, t):
    adj = [0]*n
    for a,b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    def dfs(v, seen):
        if v == t:
            return 1
        rest = adj[v] & ~seen
        ans = 0
        while rest:
            bit = rest & -rest
            rest -= bit
            ans += dfs(bit.bit_length()-1, seen | bit)
        return ans
    return dfs(s, 1 << s)


def distance(n, edges, s, t):
    adj = [[] for _ in range(n)]
    for a,b in edges:
        adj[a].append(b)
        adj[b].append(a)
    todo = deque([(s,0)])
    seen = {s}
    while todo:
        v,d = todo.popleft()
        if v == t:
            return d
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                todo.append((u,d+1))


def main():
    result = []
    for q in range(2,10):
        n,edges = hk_even(q)
        for kind,edge,excess in [
            ('square',(0,2),(4*q-3)*2**(q-2)+1),
            ('link',(2,4),(4*q-7)*2**(q-1)+4),
        ]:
            remaining = [e for e in edges if e != edge]
            b = len(remaining)-n+1
            count = paths(n,remaining,*edge)
            ell = distance(n,remaining,*edge)
            expected = 2**(2*q-1)+excess
            assert count == expected, (q,kind,count,expected)
            if kind == 'square':
                assert ell == 3
            result.append(dict(q=q, rank=b, kind=kind, distance=ell,
                               paths=count, excess=excess))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
