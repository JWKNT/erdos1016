#!/usr/bin/env python3
"""Exhaustive check of the "no full star" lemma for poles with four ports.

A 4-pole is a connected multigraph without loops whose vertices have degree two
(the four ports 0,1,2,3) or three.  Its rank is h = |E| - |V| + 1, and it has
2h + 2 vertices.  The pair (s, t) is full if the number of paths from s to t is 2^h.

Claim.  Let Y be a bridgeless 4-pole of rank h >= 4 in which the pairs (0,1), (0,2),
(0,3) are full.  Then there is a set A of vertices with 0 in A and 1, 2, 3 not in A
such that exactly two edges of Y leave A and Y[A] contains a cycle.

The program lists all 4-poles of a given rank (ports labelled, inner vertices up to
relabelling), selects those with the three full pairs, and tests the conclusion.
It uses no structure theorem.
"""
import sys
from itertools import combinations


def poles(h, visit):
    """Call visit(n, edges) for all 4-poles of rank h; inner vertices are generated up to symmetry."""
    n = 2 * h + 2
    deg = [2] * 4 + [3] * (n - 4)
    rem = deg[:]
    touched = [False] * n
    edges = []

    def rec(v, w, last_fresh_mult):
        # distribute the remaining degree of v among vertices w, w+1, ..., n-1
        if v == n:
            visit(n, edges)
            return
        if rem[v] == 0:
            rec_next(v)
            return
        if w == n:
            return
        fresh = (w >= 4) and (not touched[w])
        top = min(rem[v], rem[w], 2)
        if fresh and last_fresh_mult is not None:
            top = min(top, last_fresh_mult)
        for m in range(top, -1, -1):
            was = touched[w]
            if m:
                rem[v] -= m
                rem[w] -= m
                touched[w] = True
                edges.extend([(v, w)] * m)
            rec(v, w + 1, m if fresh else last_fresh_mult)
            if m:
                del edges[-m:]
                touched[w] = was
                rem[w] += m
                rem[v] += m

    def rec_next(v):
        was = touched[v]
        touched[v] = True
        rec(v + 1, v + 2, None)
        touched[v] = was

    touched[0] = True
    rec(0, 1, None)


def adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i))
        adj[b].append((a, i))
    return adj


def component(adj, start, removed=()):
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y, i in adj[x]:
            if i in removed or y in seen:
                continue
            seen.add(y)
            stack.append(y)
    return seen


def count_paths(adj, s, t):
    total = 0
    visited = [False] * len(adj)

    def dfs(x):
        nonlocal total
        if x == t:
            total += 1
            return
        visited[x] = True
        for y, _ in adj[x]:
            if not visited[y]:
                dfs(y)
        visited[x] = False

    dfs(s)
    return total


def conclusion(n, edges, adj):
    """Is there A with 0 in A, 1,2,3 not in A, two edges leaving A, and a cycle inside A?"""
    for i, j in combinations(range(len(edges)), 2):
        comp = component(adj, 0, removed=(i, j))
        if comp & {1, 2, 3}:
            continue
        leaving = [k for k, (a, b) in enumerate(edges) if (a in comp) != (b in comp)]
        if sorted(leaving) != [i, j]:
            continue
        inside = sum(1 for (a, b) in edges if a in comp and b in comp)
        if inside >= len(comp):
            return True
    return False


def main():
    ranks = [int(x) for x in sys.argv[1:]] or [2, 3, 4]
    for h in ranks:
        stats = {"graphs": 0, "stars": 0, "bridgeless": 0}
        bad = []

        def visit(n, edges):
            stats["graphs"] += 1
            adj = adjacency(n, edges)
            # cheap necessary condition first: the three pairs are full
            if any(count_paths(adj, 0, t) != 2 ** h for t in (1, 2, 3)):
                return
            if len(component(adj, 0)) != n:
                return
            stats["stars"] += 1
            if not all(len(component(adj, 0, removed=(i,))) == n for i in range(len(edges))):
                return
            stats["bridgeless"] += 1
            if not conclusion(n, edges, adj):
                bad.append(list(edges))

        poles(h, visit)
        print(f"rank {h}: {stats['graphs']} generated multigraphs, {stats['stars']} with a full star "
              f"at port 0, {stats['bridgeless']} of them bridgeless, {len(bad)} without the two-edge cut")
        for edges in bad[:5]:
            print("   exception:", edges)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
