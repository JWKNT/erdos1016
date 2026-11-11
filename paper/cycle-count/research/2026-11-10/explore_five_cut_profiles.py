#!/usr/bin/env python3
"""Numerical LP relaxations for five-cut profiles; not a proof certificate."""
import itertools
import json
import numpy as np
from scipy.optimize import linprog

V = tuple(range(5))
EDGES = list(itertools.combinations(V, 2))
INDEX = {e: i for i, e in enumerate(EDGES)}
PERMS = list(itertools.permutations(V))
SUBSETS = list(itertools.combinations(V, 4))
TAU = .51


def edge(u, v):
    return tuple(sorted((u, v)))


def graphs():
    seen = set()
    for mask in range(1 << 10):
        high = {EDGES[i] for i in range(10) if mask >> i & 1}
        if any(all(edge(u, v) in high for u, v in itertools.combinations(t, 2))
               for t in itertools.combinations(V, 3)):
            continue
        key = min(sum(1 << INDEX[edge(p[u], p[v])] for u, v in high) for p in PERMS)
        if key in seen:
            continue
        seen.add(key)
        yield high


def solve(high):
    forced = {e for e in EDGES if e not in high and
              any(edge(e[0], w) in high and edge(e[1], w) in high
                  for w in V if w not in e)}
    leaf_subsets = {tuple(v for v in V if v != c) for c in V
                    if all(edge(c, v) in high for v in V if v != c)}
    bounds = [(TAU, 1) if e in high else ((0, 0) if e in forced else (0, TAU))
              for e in EDGES]
    # On [lo,hi], x^2 <= (lo+hi)x-lo*hi.
    objective = np.array([lo+hi for lo, hi in bounds])
    constant = -sum(lo*hi for lo, hi in bounds)
    best = None
    for forest_mask in range(32):
        active = [SUBSETS[i] for i in range(5) if forest_mask >> i & 1]
        if any(s in leaf_subsets for s in active):
            continue
        matrix = []
        for subset in active:
            for left in itertools.combinations(subset, 2):
                right = set(subset)-set(left)
                row = np.zeros(10)
                for u in left:
                    for v in right:
                        row[INDEX[edge(u, v)]] = 1
                matrix.append(row)
        result = linprog(-objective, A_ub=np.array(matrix) if matrix else None,
                         b_ub=np.full(len(matrix), 2.01) if matrix else None,
                         bounds=bounds, method='highs')
        if not result.success:
            continue
        value = -result.fun+constant+len(active)
        if best is None or value > best['energy_bound']:
            best = dict(energy_bound=float(value), paths=result.x.tolist(),
                        active_forests=[list(s) for s in active])
    return dict(high_edges=sorted(high), forced_small=sorted(forced),
                degree_sequence=sorted(sum(v in e for e in high) for v in V),
                **best)


if __name__ == '__main__':
    print(json.dumps([solve(g) for g in graphs()], indent=2))
