#!/usr/bin/env python3
"""Exact checks for the explicit long-minimum-cut construction.

The small-cut enumeration uses the cited cyclic-connectivity theorem for
the core. It does not claim an independent finite proof of that theorem.
All other checks use only the Python standard library.
"""
import argparse
from collections import deque
from itertools import combinations
import json
from pathlib import Path


def edge(u, v):
    return (min(u, v), max(u, v))


def graph(order, edges):
    adj = [set() for _ in range(order)]
    assert len(edges) == len(set(edges))
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    return adj


def distances(adj, source, omitted=None):
    dist = [-1] * len(adj)
    dist[source] = 0
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if omitted == edge(u, v) or dist[v] >= 0:
                continue
            dist[v] = dist[u] + 1
            queue.append(v)
    return dist


def is_forest(adj, vertices):
    unseen = set(vertices)
    while unseen:
        root = unseen.pop()
        stack = [(root, -1)]
        while stack:
            u, parent = stack.pop()
            for v in adj[u]:
                if v not in vertices or v == parent:
                    continue
                if v not in unseen:
                    return False
                unseen.remove(v)
                stack.append((v, u))
    return True


def check(M, enumerate_small_cuts):
    L = 5 * M
    def vertex(x, y, s):
        return 2 * (4 * (x % L) + (y % 4)) + s
    n = 8 * L
    edges = []
    for x in range(L):
        for y in range(4):
            for dx, dy in ((0, 0), (1, 0), (0, 1)):
                edges.append(edge(vertex(x, y, 0), vertex(x + dx, y + dy, 1)))
    edges = set(edges)
    adj = graph(n, edges)
    assert all(len(neighbors) == 3 for neighbors in adj)
    assert min(distances(adj, 0)) >= 0

    # These two translations and inversion generate a transitive action.
    actions = []
    for action in range(3):
        permutation = []
        for u in range(n):
            s = u % 2
            x, y = divmod(u // 2, 4)
            permutation.append(vertex(x + 1, y, s) if action == 0 else
                               vertex(x, y + 1, s) if action == 1 else
                               vertex(-x, -y, 1 - s))
        assert {edge(permutation[u], permutation[v]) for u, v in edges} == edges
        actions.append(permutation)
    orbit = {0}
    queue = deque([0])
    while queue:
        u = queue.popleft()
        for permutation in actions:
            v = permutation[u]
            if v not in orbit:
                orbit.add(v)
                queue.append(v)
    assert len(orbit) == n
    # Bipartiteness excludes odd cycles; no common-neighbor pair repeats.
    common_pairs = set()
    for u in range(0, n, 2):
        for pair in combinations(sorted(adj[u]), 2):
            assert pair not in common_pairs
            common_pairs.add(pair)
    six = [vertex(0, 0, 0), vertex(1, 0, 1), vertex(1, -1, 0),
           vertex(1, -1, 1), vertex(0, -1, 0), vertex(0, 0, 1)]
    assert len(set(six)) == 6
    assert all(edge(six[i], six[(i + 1) % 6]) in edges for i in range(6))

    chosen = [edge(vertex(j * M, 0, 0), vertex(j * M, 0, 1)) for j in range(5)]
    pole_edges = set(edges) - set(chosen)
    for j, (u, v) in enumerate(chosen):
        pole_edges.update((edge(u, n + j), edge(v, n + j)))
    pole_n = n + 5
    pole_adj = graph(pole_n, pole_edges)
    port_distances = [[distances(pole_adj, n + i)[n + j] for j in range(5)]
                      for i in range(5)]
    minimum_port_distance = min(port_distances[i][j] for i in range(5) for j in range(i))
    assert minimum_port_distance >= M
    G_edges = set(pole_edges) | {edge(u + pole_n, v + pole_n) for u, v in pole_edges}
    joining = [edge(n + j, pole_n + n + j) for j in range(5)]
    G_edges.update(joining)
    G_adj = graph(2 * pole_n, G_edges)
    assert all(len(neighbors) == 3 for neighbors in G_adj)
    rank = len(G_edges) - len(G_adj) + 1
    assert rank == 40 * M + 6
    edge_cycle_lengths = [distances(G_adj, u, edge(u, v))[v] + 1 for u, v in joining]
    assert min(edge_cycle_lengths) >= 2 * M + 2

    result = dict(M=M, core_order=n, order=len(G_adj), rank=rank, core_girth=6,
                  transitive_orbit_size=len(orbit), minimum_port_distance=minimum_port_distance,
                  joining_edge_shortest_cycles=edge_cycle_lengths)
    if not enumerate_small_cuts:
        return result

    # A projected core cut of size <=5 has one forest shore. Its order is
    # at most3, by boundary=order+2*components. It must be connected.
    # Both cores cannot be split: each nonempty core boundary has size>=3.
    # Enumerate every possible original-vertex pattern, up to global complement.
    minorities = [(frozenset((u,)), 3) for u in range(n)]
    minorities += [(frozenset((u, v)), 4) for u, v in edges]
    minorities += [(frozenset((u, v, w)), 5)
                   for u in range(n) for v, w in combinations(sorted(adj[u]), 2)]
    assert len(minorities) == len({vertices for vertices, _ in minorities})
    cross_count = [((mask & 31) ^ (mask >> 5)).bit_count() for mask in range(1024)]
    patterns = [(None, frozenset(), 0)]
    patterns += [(side, vertices, boundary) for side in (0, 1)
                 for vertices, boundary in minorities]
    tested = admitted = cyclic = 0
    for bulk1 in (0, 1):
        bulks = (0, bulk1)
        for side, minority, boundary in patterns:
            target = 31 << 5 if bulk1 else 0
            uniform = 1023
            if side is not None:
                for j, (u, v) in enumerate(chosen):
                    count = int(u in minority) + int(v in minority)
                    bit = 1 << (5 * side + j)
                    if count == 1:
                        uniform ^= bit
                    elif count == 2:
                        target ^= bit
            for mask in range(1024):
                tested += 1
                size = boundary + 2 * ((mask ^ target) & uniform).bit_count() + cross_count[mask]
                if size > 5:
                    continue
                admitted += 1
                if bulk1:
                    # Each shore contains all but <=3 original vertices of
                    # one cyclic core, so both are cyclic.
                    cyclic += 1
                    assert side is None and mask == (31 << 5) and size == 5
                else:
                    vertices = {n + j for j in range(5) if mask & (1 << j)}
                    vertices |= {pole_n + n + j for j in range(5) if mask & (1 << (5 + j))}
                    if side is not None:
                        vertices |= {u + side * pole_n for u in minority}
                    assert is_forest(G_adj, vertices)
    assert cyclic == 1
    result.update(small_cut_patterns_tested=tested, patterns_with_boundary_at_most_five=admitted,
                  cyclic_cut_patterns_at_most_five=cyclic,
                  reduction_input="Nedela-Skoviera1995 Theorem17: core cyclic connectivity6")
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('four-high-connectivity-long-cut-checks.json'))
    args = parser.parse_args()
    results = [check(10, True), check(11, False), check(20, False), check(50, False)]
    args.output.write_text(json.dumps(dict(status='all_checks_passed', results=results), indent=2) + '\n')
    print(json.dumps(results, indent=2))
