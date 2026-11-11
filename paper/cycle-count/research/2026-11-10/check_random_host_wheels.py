#!/usr/bin/env python3
"""Exact finite checks for the wheel lemmas; these do not prove the asymptotics."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from math import comb, isqrt
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parent
KERNEL = [(0, 1), (1, 2), (2, 3), (3, 0)] + [(4, i) for i in range(4)]

def kernel_cores():
    out = []
    for mask in range(1, 256):
        edges = [i for i in range(8) if mask >> i & 1]
        adj = defaultdict(set)
        for i in edges:
            u, v = KERNEL[i]
            adj[u].add(v)
            adj[v].add(u)
        if min(map(len, adj.values())) < 2:
            continue
        seen = {next(iter(adj))}
        todo = list(seen)
        while todo:
            for v in adj[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        if len(seen) == len(adj):
            out.append((edges, len(edges) - len(adj) + 1))
    return out

CORES = kernel_cores()
CYCLES = [edges for edges, rank in CORES if rank == 1]
assert len(CYCLES) == 13

def explicit_path(weights):
    adj = defaultdict(set)
    paths = []
    nxt = 5
    for (u, v), size in zip(KERNEL, weights):
        path = [u] + list(range(nxt, nxt + size - 1)) + [v]
        nxt += size - 1
        paths.append(path)
        for a, b in zip(path, path[1:]):
            adj[a].add(b)
            adj[b].add(a)
    deleted = [(0, 1), (2, 3), (4, paths[4][1]), (4, paths[5][1])]
    for u, v in deleted:
        adj[u].remove(v)
        adj[v].remove(u)
    assert len(adj) == nxt
    ends = [v for v in adj if len(adj[v]) == 1]
    assert len(ends) == 2 and all(len(a) in (1, 2) for a in adj.values())
    seen = {ends[0]}
    todo = ends[:1]
    while todo:
        for v in adj[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    assert len(seen) == nxt

rng = random.Random(1016)
metric_count = path_count = 0
for h in [9, 18, 27, 36, 63, 90, 180, 360]:
    s = isqrt(h)
    if s * s < h:
        s += 1
    for _ in range(500):
        U, L, M = [rng.randint(s, 2 * s) for _ in range(3)]
        t = h + U
        cuts = sorted([0, t] + [rng.randint(0, t) for _ in range(3)])
        xs = [b - a for a, b in zip(cuts, cuts[1:])]
        rng.shuffle(xs)
        spokes = [h + s - x for x in xs]
        if min(spokes) <= 0:
            continue
        weights = [1, L, 1, M] + spokes
        assert sum(weights) >= 3 * h + 4 * s + 2
        for edges, rank in CORES:
            e = sum(weights[i] for i in edges)
            assert e >= (2 * s if rank == 1 else (rank - 1) * h)
        expected = []
        offsets = {(0, 1): (1, L + M + 1), (2, 3): (1, L + M + 1),
                   (1, 2): (L, M + 2), (0, 3): (M, L + 2),
                   (0, 2): (L + 1, M + 1), (1, 3): (L + 1, M + 1)}
        for (i, j), values in offsets.items():
            expected.extend(spokes[i] + spokes[j] + a for a in values)
        actual = [sum(weights[i] for i in edges) for edges in CYCLES if edges != [0, 1, 2, 3]]
        assert sorted(actual) == sorted(expected)
        assert min(expected) >= h + 1 and max(expected) <= 2 * h + 6 * s + 1
        metric_count += 1
        if path_count < 120:
            explicit_path(weights)
            path_count += 1

centered_count = 0
for h in [100000, 200000, 500000]:
    s = isqrt(h)
    if s * s < h:
        s += 1
    for _ in range(1000):
        U = rng.randint(s, 2 * s)
        R = rng.randint(6 * s, h // 12)
        middle = (R - 2) // 2
        L = rng.randint(middle - s // 2, middle + s // 2)
        M = R - 2 - L
        t = h + U
        cuts = sorted([0, t] + [rng.randint(0, t) for _ in range(3)])
        xs = [b - a for a, b in zip(cuts, cuts[1:])]
        rng.shuffle(xs)
        B = h - R // 4 + s
        spokes = [B - x for x in xs]
        if min(spokes) <= 0:
            continue
        weights = [1, L, 1, M] + spokes
        assert 3 * h + 2 * s <= sum(weights) <= 3 * h + 3 * s + 3
        for edges, rank in CORES:
            e = sum(weights[i] for i in edges)
            assert e >= (2 * s if rank == 1 else (rank - 1) * h)
        centered_count += 1

probability_checks = 0
for t in range(1, 17):
    c = [Fraction(comb(2 * j, j), 4 ** j) for j in range(t + 1)]
    totals = [defaultdict(Fraction) for _ in range(6)]
    mass = Fraction()
    for x0 in range(t + 1):
        for x1 in range(t - x0 + 1):
            for x2 in range(t - x0 - x1 + 1):
                xs = [x0, x1, x2, t - x0 - x1 - x2]
                p = c[xs[0]] * c[xs[1]] * c[xs[2]] * c[xs[3]] / (t + 1)
                mass += p
                for acc, (i, j) in zip(totals, combinations(range(4), 2)):
                    acc[xs[i] + xs[j]] += p
    assert mass == 1
    for acc in totals:
        assert set(acc) == set(range(t + 1))
        assert all(p == Fraction(1, t + 1) for p in acc.values())
        probability_checks += 1

result = {"metric_cases": metric_count, "centered_metric_cases": centered_count, "explicit_spanning_paths": path_count,
          "kernel_core_types": len(CORES), "kernel_cycles": len(CYCLES),
          "exact_pair_marginal_checks": probability_checks,
          "asymptotic_matching_and_embedding_theorems": "not certified by finite checks"}
(ROOT / 'random-host-wheel-results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
