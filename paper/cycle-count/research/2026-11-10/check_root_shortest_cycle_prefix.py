#!/usr/bin/env python3
"""Exact finite checks for shortest-cycle deletion; no asymptotic test is claimed."""
from collections import deque
from itertools import combinations
from pathlib import Path
import json
import random


def adjacency(vertices, edges):
    adj = {v: [] for v in vertices}
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i)); adj[v].append((u, i))
    return adj


def components(vertices, edges):
    adj = adjacency(vertices, edges); left = set(vertices); parts = []
    while left:
        seen = {next(iter(left))}; queue = list(seen)
        for u in queue:
            for v, _ in adj[u]:
                if v not in seen: seen.add(v); queue.append(v)
        left -= seen; parts.append(seen)
    return parts


def rank(vertices, edges):
    return len(edges)-len(vertices)+len(components(vertices, edges))


def shortest_cycle(vertices, edges):
    adj = adjacency(vertices, edges); best = None
    for skip, (s, t) in enumerate(edges):
        parent = {s: None}; queue = deque([s])
        while queue and t not in parent:
            u = queue.popleft()
            for v, eid in adj[u]:
                if eid != skip and v not in parent:
                    parent[v] = u; queue.append(v)
        if t not in parent: continue
        path = [t]
        while path[-1] != s: path.append(parent[path[-1]])
        path.reverse()
        if best is None or len(path) < len(best): best = path
    return best


def paths(vertices, edges, s, t):
    adj = adjacency(vertices, edges)
    def visit(u, seen):
        if u == t: return 1
        return sum(visit(v, seen | {v}) for v, _ in adj[u] if v not in seen)
    return visit(s, {s})


def cycle_space_count(vertices, edges):
    adj = adjacency(vertices, edges); root = next(iter(vertices))
    parent = {root: (-1, -1)}; queue = [root]; masks = {root: 0}
    for u in queue:
        for v, eid in adj[u]:
            if v not in parent:
                parent[v] = (u, eid); masks[v] = masks[u] ^ (1 << eid); queue.append(v)
    assert len(parent) == len(vertices)
    tree = {eid for _, eid in parent.values()}
    basis = [masks[u] ^ masks[v] ^ (1 << eid) for eid, (u, v) in enumerate(edges) if eid not in tree]
    total = 0
    for word in range(1, 1 << len(basis)):
        mask = 0
        for j, b in enumerate(basis):
            if word >> j & 1: mask ^= b
        selected = [e for j, e in enumerate(edges) if mask >> j & 1]
        used = {v for e in selected for v in e}
        deg = {v: 0 for v in used}
        for u, v in selected: deg[u] += 1; deg[v] += 1
        total += all(d == 2 for d in deg.values()) and len(components(used, selected)) == 1
    return total


def check_graph(vertices, edges, C=None):
    C = shortest_cycle(vertices, edges) if C is None else C
    g = len(C); assert g >= 5 and len(shortest_cycle(vertices, edges)) == g
    adj = adjacency(vertices, edges)
    outside = [next(v for v, _ in adj[u] if v not in C) for u in C]
    assert len(set(outside)) == g
    exterior = set(vertices)-set(C)
    ext_edges = [e for e in edges if set(e) <= exterior]
    ext_parts = components(exterior, ext_edges)
    assert all(rank(part, [e for e in ext_edges if set(e) <= part]) >= 1 for part in ext_parts)
    deleted_edge = frozenset((C[0], C[-1]))
    N = [e for e in edges if frozenset(e) != deleted_edge]
    b = rank(vertices, N); contributions = []
    for p in range(1, g):
        Vp = set(vertices)-set(C[:p]); Ep = [e for e in N if set(e) <= Vp]
        parts = components(Vp, Ep); target = next(part for part in parts if C[-1] in part)
        Et = [e for e in Ep if set(e) <= target]
        q = rank(target, Et); assert q <= b-p
        for part in parts:
            if part != target: assert rank(part, [e for e in Ep if set(e) <= part]) >= 1
        if outside[p-1] not in target: contributions.append(0); continue
        s = outside[p-1]; t = C[-1]
        if p == g-1:
            target = target-{t}; Et = [e for e in Et if t not in e]; t = outside[-1]
            assert rank(target, Et) == q
        adjt = adjacency(target, Et)
        assert s != t and len(adjt[s]) == len(adjt[t]) == 2
        assert all(len(a) in (2, 3) for a in adjt.values())
        assert sum(len(a) == 2 for a in adjt.values()) <= g
        contributions.append(paths(target, Et, s, t))
    total_paths = paths(vertices, N, C[0], C[-1])
    assert total_paths == 1+sum(contributions)
    assert cycle_space_count(vertices, edges)-cycle_space_count(vertices, N) == total_paths
    return dict(rank=b+1, girth=g, outside_components=len(ext_parts), branches=g-1,
                edge_cycles=total_paths, branch_counts=contributions)


def main():
    rng = random.Random(101620261111); rows = []; attempts = 0
    for n in (10, 12, 14, 16, 18, 20):
        accepted = 0
        while accepted < 12:
            attempts += 1; stubs = list(range(n))*3; rng.shuffle(stubs)
            edges = [tuple(sorted(stubs[i:i+2])) for i in range(0, len(stubs), 2)]
            if any(u == v for u, v in edges) or len(set(edges)) != len(edges): continue
            V = set(range(n))
            if len(components(V, edges)) != 1: continue
            C = shortest_cycle(V, edges)
            if len(C) < 5: continue
            rows.append(check_graph(V, edges, C)); accepted += 1
    # A shortest C5 whose exterior has two cyclic components.
    pet = [(i, (i+1)%5) for i in range(5)] + [(i, i+5) for i in range(5)]
    pet += [(i+5, (i+2)%5+5) for i in range(5)]
    left_vertices = list(range(1, 10)); leftmap = {v: 5+i for i, v in enumerate(left_vertices)}
    left = [(leftmap[u], leftmap[v]) for u, v in pet if 0 not in (u, v)]
    left_ports = [leftmap[v] for v in (1, 4, 5)]
    rightmap = {v: 14+v for v in range(10)}
    right = [(rightmap[u], rightmap[v]) for u, v in pet if set((u, v)) != {0, 1}]
    right_ports = [rightmap[0], rightmap[1]]
    edges = [(i, (i+1)%5) for i in range(5)] + left + right
    edges += list(zip(range(5), left_ports+right_ports))
    fixture = check_graph(set(range(24)), edges, list(range(5)))
    assert fixture['outside_components'] == 2
    result = dict(status='exact finite identities passed; no asymptotic numerical claim',
                  random_graphs=len(rows), configuration_attempts=attempts,
                  branch_checks=sum(r['branches'] for r in rows)+fixture['branches'],
                  disconnected_complement_fixture=fixture, random_checks=rows)
    Path(__file__).with_name('root-shortest-cycle-prefix-checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'random_checks'}))


if __name__ == '__main__': main()
