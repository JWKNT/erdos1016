#!/usr/bin/env python3
"""Finite topology checks for the adaptive full-threshold construction."""
from collections import defaultdict
from math import ceil, log2, sqrt
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parent
rng = random.Random(1016)

def edge(u, v):
    return (min(u, v), max(u, v))

class Builder:
    def __init__(self):
        self.n = 0
        self.edges = set()
    def vertices(self, k):
        result = list(range(self.n, self.n + k))
        self.n += k
        return result
    def path(self, u, v, length):
        assert length >= 1
        p = [u] + self.vertices(length - 1) + [v]
        self.edges.update(edge(x, y) for x, y in zip(p, p[1:]))
        return p
    def cycle(self, length):
        c = self.vertices(length)
        self.edges.update(edge(c[i], c[(i + 1) % length]) for i in range(length))
        return c

def cycle_edges(c):
    return [(c[i], c[(i + 1) % len(c)]) for i in range(len(c))]

def alternate(c, index):
    return [c[(index - j) % len(c)] for j in range(len(c))]

def expand(c, replacement):
    out = [c[0]]
    for u, v in cycle_edges(c):
        p = replacement.get(edge(u, v), [u, v])
        if p[0] != u:
            p = list(reversed(p))
        assert p[0] == u and p[-1] == v
        out.extend(p[1:])
    return out

def check_cycle(g, walk):
    assert walk[0] == walk[-1]
    assert len(set(walk[:-1])) == len(walk) - 1
    assert all(edge(u, v) in g.edges for u, v in zip(walk, walk[1:]))

def matching(c, forbidden, number):
    options = cycle_edges(c)
    rng.shuffle(options)
    used = set(forbidden)
    chosen = []
    for u, v in options:
        if u not in used and v not in used:
            chosen.append((u, v))
            used.update((u, v))
            if len(chosen) == number:
                return chosen
    raise AssertionError('finite test has too few matching edges')

cases = binary_checks = digit_checks = hamilton_checks = 0
for d in [3, 4, 5, 7]:
    K0 = ceil(log2(4 * d))
    K = K0 + 2
    ell = (K0 + 2) * (d + 3)
    b = ceil(sqrt(2 * ell))
    c = 8 * b + 5
    T = c + 4 * d + 3
    for repetition in range(4):
        g = Builder()
        f0, f1 = g.vertices(2)
        g.edges.add(edge(f0, f1))
        bit_cycles = [g.cycle(2 ** i + 2) for i in range(K0 + 1)]
        short = g.cycle(c)
        singles = [g.cycle(j) for j in range(3, T + 1)]
        replacements = {}
        bit_edges = []
        base = [f0, f1]
        previous = f1
        for cyc in bit_cycles:
            index = rng.randrange(len(cyc))
            x, y = cyc[index], cyc[(index + 1) % len(cyc)]
            base.extend(g.path(previous, x, d + 2)[1:])
            base.append(y)
            replacements[edge(x, y)] = alternate(cyc, index)
            bit_edges.append(edge(x, y))
            previous = y
        base.extend(g.path(previous, f0, d + 2)[1:])
        base = base[:-1]
        assert len(base) == ell
        check_cycle(g, base + [base[0]])
        reserved = {f0, f1}
        for u, v in bit_edges:
            reserved.update((u, v))
        candidates = matching(base, reserved, 2 * (K - K0))
        rng.shuffle(candidates)
        for i, (x, y) in zip(range(K0 + 1, K + 1), candidates):
            replacements[edge(x, y)] = g.path(x, y, 2 ** i + 1)
            bit_edges.append(edge(x, y))
        for mask in range(1 << (K + 1)):
            chosen = {e: replacements[e] for i, e in enumerate(bit_edges) if mask >> i & 1}
            walk = expand(base, chosen)
            check_cycle(g, walk)
            assert len(walk) - 1 == ell + sum(2 ** i for i in range(K + 1) if mask >> i & 1)
            binary_checks += 1
        binary_path = expand(base, replacements)[1:]
        assert binary_path[0] == f1 and binary_path[-1] == f0
        assert len(binary_path) - 1 == ell + 2 ** (K + 1) - 2

        short_index = rng.randrange(c)
        a0, a1 = short[short_index], short[(short_index + 1) % c]
        previous = f1
        single_edges = []
        for cyc in singles:
            index = rng.randrange(len(cyc))
            x, y = cyc[index], cyc[(index + 1) % len(cyc)]
            g.path(previous, x, d + 2)
            single_edges.append(edge(x, y))
            previous = y
        g.path(previous, a0, d + 2)
        candidates = matching(short, {a0, a1}, 3 * b)
        rng.shuffle(candidates)
        digit_edges = []
        digit_replacements = {}
        for group in range(2):
            for j in range(b):
                x, y = candidates[group * b + j]
                length = 2 * d + 3 + (j if group == 0 else j * b)
                e = edge(x, y)
                digit_edges.append(e)
                digit_replacements[e] = g.path(x, y, length)
        for j0 in range(b):
            for j1 in range(b):
                chosen_edges = [digit_edges[j0], digit_edges[b + j1]]
                walk = expand(short, {e: digit_replacements[e] for e in chosen_edges})
                check_cycle(g, walk)
                assert len(walk) - 1 == T + 1 + j0 + b * j1
                digit_checks += 1

        g.path(f0, a1, 7)
        chords = set(bit_edges + digit_edges + single_edges + [edge(f0, f1), edge(a0, a1)])
        hamilton = g.edges - chords
        adj = defaultdict(set)
        for u, v in hamilton:
            adj[u].add(v)
            adj[v].add(u)
        assert len(adj) == g.n and all(len(a) == 2 for a in adj.values())
        seen = {0}
        todo = [0]
        while todo:
            for v in adj[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        assert len(seen) == g.n and len(hamilton) == g.n
        assert len(g.edges) - g.n == K + 2 * b + T + 1
        assert all(edge(u, v) in hamilton for u, v in zip(binary_path, binary_path[1:]))
        hamilton_checks += 1
        cases += 1

result = {"gadget_cases": cases, "binary_cycle_checks": binary_checks,
          "digit_cycle_checks": digit_checks, "spanning_hamilton_cycle_checks": hamilton_checks,
          "adaptive_exposure_and_asymptotic_probability_proofs": "not certified by finite checks"}
(ROOT / 'full-threshold-integration-results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
