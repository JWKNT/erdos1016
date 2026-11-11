#!/usr/bin/env python3
"""Exact cycle-cell polynomial checks against independent cycle-space states."""
import json
import math
import random
from collections import Counter
from pathlib import Path


def component_count(n, edges):
    parent = list(range(n))
    active = set()
    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for u, v in edges:
        parent[root(u)] = root(v)
        active.update((u, v))
    return len({root(v) for v in active})


def even_states(n, edges):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    root_path = {0: 0}
    tree = set()
    queue = [0]
    for u in queue:
        for v, i in adj[u]:
            if v not in root_path:
                root_path[v] = root_path[u] ^ (1 << i)
                tree.add(i)
                queue.append(v)
    if len(queue) != n:
        return None
    states = [0]
    for i, (u, v) in enumerate(edges):
        if i not in tree:
            cycle = root_path[u] ^ root_path[v] ^ (1 << i)
            states += [s ^ cycle for s in states]
    return states


def audit(cells, matching):
    n = sum(map(len, cells))
    cycle_edges = [(cell[i], cell[(i + 1) % len(cell)])
                   for cell in cells for i in range(len(cell))]
    edges = cycle_edges + matching
    states = even_states(n, edges)
    if states is None:
        return None
    direct = Counter()
    for state in states:
        selected = [e for i, e in enumerate(edges) if state >> i & 1]
        direct[component_count(n, selected)] += 1
    expanded = Counter()
    quotient_even = connected_quotient = 0
    active_to_counts = Counter()
    for mask in range(1 << len(matching)):
        selected = [e for i, e in enumerate(matching) if mask >> i & 1]
        ports = set(v for edge in selected for v in edge)
        local = [[v for v in cell if v in ports] for cell in cells]
        if any(len(vs) % 2 for vs in local):
            continue
        quotient_even += 1
        active = [vs for vs in local if vs]
        zero = len(cells) - len(active)
        for signs in range(1 << len(active)):
            pairs = list(selected)
            for i, vs in enumerate(active):
                shift = (signs >> i) & 1
                pairs += [(vs[(j + shift) % len(vs)],
                           vs[(j + shift + 1) % len(vs)])
                          for j in range(0, len(vs), 2)]
            loops = component_count(n, pairs)
            for extra in range(zero + 1):
                expanded[loops + extra] += math.comb(zero, extra)
            if selected and loops == 1:
                active_to_counts[len(active)] += 1
        if selected:
            owner = {v: i for i, cell in enumerate(cells) for v in cell}
            quotient_edges = [(owner[u], owner[v]) for u, v in selected]
            connected_quotient += component_count(len(cells), quotient_edges) == 1
    assert expanded == direct, (cells, matching, direct, expanded)
    rank = len(edges) - n + 1
    assert quotient_even * 2**len(cells) == 2**rank
    assert direct[1] == len(cells) + sum(active_to_counts.values())
    return dict(order=n, rank=rank, cells=list(map(len, cells)),
                states=len(states), cycles=direct[1],
                quotient_even_states=quotient_even,
                connected_nonempty_quotient_states=connected_quotient,
                polynomial=dict(sorted(direct.items())))


def main():
    rng = random.Random(1016)
    results = []
    for lengths in [(6,), (8,), (10,), (4, 4), (5, 5), (6, 6),
                    (4, 4, 4), (4, 5, 5), (6, 6, 6)]:
        cells = []
        start = 0
        for length in lengths:
            cells.append(list(range(start, start + length)))
            start += length
        forbidden = {tuple(sorted((cell[i], cell[(i + 1) % len(cell)])))
                     for cell in cells for i in range(len(cell))}
        accepted = 0
        while accepted < 8:
            vertices = list(range(start))
            rng.shuffle(vertices)
            matching = [tuple(sorted(vertices[i:i + 2]))
                        for i in range(0, start, 2)]
            if any(e in forbidden for e in matching):
                continue
            row = audit(cells, matching)
            if row is not None:
                results.append(row)
                accepted += 1
    output = dict(fixtures=len(results),
                  even_states=sum(row["states"] for row in results),
                  all_polynomial_identities_pass=True, details=results)
    destination = Path(__file__).with_name("random-cycle-quotient-checks.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: v for k, v in output.items() if k != "details"}))


if __name__ == "__main__":
    main()
