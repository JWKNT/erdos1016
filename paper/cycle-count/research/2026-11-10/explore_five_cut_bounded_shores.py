#!/usr/bin/env python3
"""Exploratory LPs for bounded five-cut shores; not proof certificates."""
import itertools
import json
import numpy as np
from scipy.optimize import linprog

V = tuple(range(5))
EDGES = tuple(itertools.combinations(V, 2))
INDEX = {e: i for i, e in enumerate(EDGES)}
SUBSETS = tuple(itertools.combinations(V, 4))
PAIRINGS = []
for a, b, c, d in SUBSETS:
    PAIRINGS.append((((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))))


def solve(mask, delta=.001, allowance=.001, tau=.501):
    bounds = [(delta, tau) if mask >> i & 1 else (0, delta)
              for i in range(10)] + [(0, 1)] * 15
    objective = np.ones(25)
    for s in range(5):
        objective[10+3*s:13+3*s] = (.5, 1, .5)
    rows, rhs = [], []
    rows.append(np.ones(25)); rhs.append(8.001)
    for s in range(5):
        forest = np.zeros(25)
        forest[10+3*s:13+3*s] = 1
        rows.append(forest); rhs.append(1)
        for a, pairing in enumerate(PAIRINGS[s]):
            for added, other in (pairing, pairing[::-1]):
                if mask >> INDEX[added] & 1:
                    row = forest.copy()
                    row[10+3*s+a] -= 1
                    row[INDEX[other]] += 1
                    rows.append(row); rhs.append(1+allowance)
    result = linprog(-objective, A_ub=rows, b_ub=rhs, bounds=bounds,
                     method='highs')
    assert result.success
    return dict(mask=mask, value=-result.fun, paths=result.x[:10].tolist(),
                forest_pairings=result.x[10:].reshape((5, 3)).tolist())


if __name__ == '__main__':
    results = [solve(mask) for mask in range(1024)]
    results.sort(key=lambda r: r['value'], reverse=True)
    print(json.dumps(dict(status='exploratory only', delta=.001,
                         allowance=.001, tau=.501,
                         number_of_masks=1024, top=results[:20]), indent=2))
