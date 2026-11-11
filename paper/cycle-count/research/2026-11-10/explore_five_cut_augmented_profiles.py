#!/usr/bin/env python3
"""Numerical mixed-integer relaxation; all output is exploratory, not proof."""
import itertools
import json
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from explore_five_cut_profiles import V, EDGES, INDEX, SUBSETS, TAU, graphs, edge

PAIRINGS = []
for subset in SUBSETS:
    a, b, c, d = subset
    PAIRINGS.append([((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))])


def solve(high):
    # Ten paths, fifteen forest pairings, five forest-activity flags,
    # and three augmented high-path flags for each of ten added edges.
    n = 60
    lo = np.zeros(n)
    hi = np.ones(n)
    objective = np.zeros(n)
    constant = 0
    forced = {e for e in EDGES if e not in high and
              any(edge(e[0], w) in high and edge(e[1], w) in high
                  for w in V if w not in e)}
    for i, e in enumerate(EDGES):
        if e in high:
            lo[i], hi[i] = TAU, 1
        elif e in forced:
            hi[i] = 0
        else:
            hi[i] = TAU
        objective[i] = lo[i]+hi[i]
        constant -= lo[i]*hi[i]
    objective[10:25] = 1
    rows, upper = [], []

    def add(row, limit):
        rows.append(row)
        upper.append(limit)

    for s, subset in enumerate(SUBSETS):
        forest = np.zeros(n)
        forest[10+3*s:13+3*s] = 1
        row = forest.copy()
        row[25+s] = -1
        add(row, 0)
        for left in itertools.combinations(subset, 2):
            right = set(subset)-set(left)
            row = np.zeros(n)
            row[25+s] = 2
            for u in left:
                for v in right:
                    row[INDEX[edge(u, v)]] = 1
            add(row, 4.01)
        omitted = next(v for v in V if v not in subset)
        if all(edge(omitted, v) in high for v in subset):
            hi[25+s] = 0  # the pending far-leaf return-forest lemma

    for i, added in enumerate(EDGES):
        rest = [v for v in V if v not in added]
        z_rows = []
        for j, pair in enumerate(itertools.combinations(rest, 2)):
            subset = tuple(sorted(added+pair))
            s = SUBSETS.index(subset)
            pairing = frozenset((frozenset(added), frozenset(pair)))
            a = next(a for a, matching in enumerate(PAIRINGS[s])
                     if frozenset(map(frozenset, matching)) == pairing)
            z = np.zeros(n)
            z[INDEX[pair]] = 1
            z[10+3*s:13+3*s] = 1
            z[10+3*s+a] -= 1
            z_rows.append(z)
            row = z.copy()
            row[30+3*i+j] = -.99
            add(row, 1.01)
            if added in high:
                add(z.copy(), 1.01)
        add(sum(z_rows), 4.001)
        for j in range(3):
            row = z_rows[j].copy()
            for k in range(3):
                if k != j:
                    row[30+3*i+k] = 2
            add(row, 4)  # two augmented high pairs force the third to zero
    integrality = np.zeros(n)
    integrality[25:] = 1
    result = milp(-objective, integrality=integrality, bounds=Bounds(lo, hi),
                  constraints=LinearConstraint(np.array(rows), -np.inf, upper),
                  options={'time_limit': 30, 'mip_rel_gap': 1e-7})
    value = None if result.x is None else -result.fun+constant
    bound = getattr(result, 'mip_dual_bound', None)
    bound = None if bound is None else -bound+constant
    return dict(high_edges=sorted(high),
                degree_sequence=sorted(sum(v in e for e in high) for v in V),
                status=int(result.status), energy_value=value, energy_upper_bound=bound,
                paths=None if result.x is None else result.x[:10].tolist(),
                forest_pairings=None if result.x is None else result.x[10:25].reshape((5, 3)).tolist())


if __name__ == '__main__':
    for high in graphs():
        print(json.dumps(solve(high)), flush=True)
