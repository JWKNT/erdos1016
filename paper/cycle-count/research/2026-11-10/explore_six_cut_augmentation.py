#!/usr/bin/env python3
"""Exploratory six-cut MILP; its numerical output is not a proof."""
import itertools
import json
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

V = tuple(range(6))
PAIRS = tuple(itertools.combinations(V, 2))
INDEX = {e: i for i, e in enumerate(PAIRS)}
FOURS = tuple(itertools.combinations(V, 4))


def matchings(vertices):
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for b in vertices[1:]:
        rest = tuple(v for v in vertices if v not in (a, b))
        for tail in matchings(rest):
            yield tuple(sorted(((a, b),)+tail))


M4 = tuple(tuple(matchings(S)) for S in FOURS)
M6 = tuple(matchings(V))


def solve(aggregate=True, time_limit=120, six_cycle_shore=False, extra_caps=False, path_weight=1):
    # 15 path counts; 45 four-sector pairing counts; 15 six-sector counts;
    # 15 selected noncap masses; and 45 selection flags.
    n = 135
    lo = np.zeros(n)
    hi = np.ones(n)
    hi[:15] = .5
    objective = np.zeros(n)
    objective[:15] = path_weight
    objective[75:90] = 1
    target = M6[0]
    for a, matching in enumerate(M6):
        if set(target).isdisjoint(matching):
            objective[60+a] = 1
    if six_cycle_shore:
        objective[75:90] = 0
        for s in range(15):
            objective[15+3*s:18+3*s] = (.5, 1, .5)
        cycle_matchings = (((0, 1), (2, 3), (4, 5)),
                          ((0, 5), (1, 2), (3, 4)))
        for a, matching in enumerate(M6):
            objective[60+a] = sum(set(p).isdisjoint(matching)
                                 for p in cycle_matchings)/2
    rows, upper = [], []

    def add(row, bound):
        rows.append(row)
        upper.append(bound)

    def noncap(S, pairing):
        s = FOURS.index(tuple(sorted(S)))
        a = M4[s].index(tuple(sorted(pairing)))
        row = np.zeros(n)
        row[15+3*s:18+3*s] = 1
        row[15+3*s+a] -= 1
        return row

    for s, S in enumerate(FOURS):
        row = np.zeros(n)
        row[15+3*s:18+3*s] = 1
        add(row, 1)
        flags = np.zeros(n)
        flags[90+3*s:93+3*s] = 1
        add(flags, 1); add(-flags, -1)
        for a, pairing in enumerate(M4[s]):
            v = noncap(S, pairing)
            for edge in pairing:
                row = v.copy()
                row[INDEX[edge]] += 1
                add(row, 1)
            row = -v
            row[75+s] = 1
            row[90+3*s+a] = 1
            add(row, 1)
    row = np.zeros(n)
    row[60:75] = 1
    add(row, 1)
    if aggregate:
        row = np.zeros(n)
        row[:75] = 1
        add(row, 16)
    for matching in M6:
        compatible = np.zeros(n)
        for a, other in enumerate(M6):
            if set(matching).isdisjoint(other):
                compatible[60+a] = 1
        for terminal in matching:
            row = compatible.copy()
            row[INDEX[terminal]] += 1
            for added in matching:
                if added != terminal:
                    row += noncap(terminal+added, (terminal, added))
            add(row, 2)
    if extra_caps:
        for capped in itertools.combinations(V, 3):
            remaining = tuple(v for v in V if v not in capped)
            for terminal in itertools.combinations(remaining, 2):
                row = np.zeros(n)
                row[INDEX[terminal]] = 1
                for added in itertools.combinations(capped, 2):
                    row += noncap(terminal+added, (terminal, added))
                add(row, 2)
        for terminal in PAIRS:
            capped = tuple(v for v in V if v not in terminal)
            for pairing in matchings(capped):
                row = np.zeros(n)
                row[INDEX[terminal]] = 1
                for added in itertools.combinations(capped, 2):
                    row += noncap(terminal+added, (terminal, added))
                cap_matching = tuple(sorted((terminal,)+pairing))
                for a, other in enumerate(M6):
                    if set(cap_matching).isdisjoint(other):
                        row[60+a] = 1
                add(row, 4)
    integrality = np.zeros(n)
    if not six_cycle_shore:
        integrality[90:] = 1
    result = milp(-objective, integrality=integrality, bounds=Bounds(lo, hi),
                  constraints=LinearConstraint(np.array(rows), -np.inf, upper),
                  options={'time_limit': time_limit, 'mip_rel_gap': 1e-8})
    return dict(status='exploratory only', solver_status=int(result.status),
                aggregate=aggregate, target_matching=target,
                six_cycle_shore=six_cycle_shore,
                extra_caps=extra_caps,
                path_weight=path_weight,
                value=None if result.x is None else -result.fun,
                upper_bound=None if getattr(result, 'mip_dual_bound', None) is None
                else -result.mip_dual_bound,
                paths=None if result.x is None else result.x[:15].tolist(),
                four_pairings=None if result.x is None else result.x[15:60].reshape((15, 3)).tolist(),
                six_pairings=None if result.x is None else result.x[60:75].tolist(),
                selections=None if result.x is None else result.x[90:].reshape((15, 3)).tolist())


if __name__ == '__main__':
    print(json.dumps(solve(), indent=2), flush=True)
