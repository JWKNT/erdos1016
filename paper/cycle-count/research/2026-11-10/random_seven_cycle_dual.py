#!/usr/bin/env python3
"""Exact-dual search for a seven-cycle shore; only matching constraints."""
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

V = tuple(range(7))


def matchings(vertices):
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for b in vertices[1:]:
        for rest in matchings(tuple(v for v in vertices if v not in (a, b))):
            yield tuple(sorted(((a, b),)+rest))


PAIRS = tuple(itertools.combinations(V, 2))
FOURS = tuple(itertools.combinations(V, 4))
SIXES = tuple(itertools.combinations(V, 6))
M4 = {S: tuple(matchings(S)) for S in FOURS}
M6 = {S: tuple(matchings(S)) for S in SIXES}
STATES = tuple(('p', e) for e in PAIRS)
STATES += tuple(('f4', S, a) for S in FOURS for a in M4[S])
STATES += tuple(('f6', S, a) for S in SIXES for a in M6[S])
INDEX = {state: i for i, state in enumerate(STATES)}


def system(extra_caps=False):
    n = len(STATES)
    rows, rhs, labels = [], [], []
    def rho(matching):
        row = [0]*n
        if len(matching) == 1:
            row[INDEX['p', matching[0]]] = 1
        elif len(matching) == 2:
            S = tuple(sorted(v for e in matching for v in e))
            for other in M4[S]:
                if other != matching: row[INDEX['f4', S, other]] = 1
        else:
            S = tuple(sorted(v for e in matching for v in e))
            for other in M6[S]:
                if set(matching).isdisjoint(other): row[INDEX['f6', S, other]] = 1
        return row
    for size in (1, 2, 3):
        for ports in itertools.combinations(V, 2*size):
            for matching in matchings(ports):
                for terminal in matching:
                    row = [0]*n
                    rest = tuple(e for e in matching if e != terminal)
                    for mask in range(1 << len(rest)):
                        selected = tuple(sorted((terminal,)+tuple(e for i, e in enumerate(rest) if mask >> i & 1)))
                        row = [x+y for x, y in zip(row, rho(selected))]
                    rows.append(row); rhs.append(F(2)**(size-2))
                    labels.append(dict(matching=matching, terminal=terminal))
    if extra_caps:
        def add(row, bound, label):
            rows.append(row); rhs.append(F(bound)); labels.append(label)
        for S in FOURS:
            row = [0]*n
            for a in M4[S]: row[INDEX['f4', S, a]] = 1
            add(row, 1, dict(kind='four_total', ports=S))
        for S in SIXES:
            row = [0]*n
            for a in M6[S]: row[INDEX['f6', S, a]] = 1
            add(row, 1, dict(kind='six_total', ports=S))
        add([1]*n, 32, dict(kind='aggregate'))
        for Q in itertools.combinations(V, 3):
            remaining = tuple(v for v in V if v not in Q)
            for e in itertools.combinations(remaining, 2):
                row = rho((e,))
                for f in itertools.combinations(Q, 2):
                    row = [x+y for x, y in zip(row, rho(tuple(sorted((e, f)))))]
                add(row, 2, dict(kind='star', terminal=e, capped=Q))
        for Q in itertools.combinations(V, 4):
            remaining = tuple(v for v in V if v not in Q)
            for e in itertools.combinations(remaining, 2):
                for pairing in matchings(Q):
                    row = rho((e,))
                    for f in itertools.combinations(Q, 2):
                        row = [x+y for x, y in zip(row, rho(tuple(sorted((e, f)))))]
                    row = [x+y for x, y in zip(row, rho(tuple(sorted((e,)+pairing))))]
                    add(row, 4, dict(kind='binary', terminal=e, pairing=pairing))
        for e in PAIRS:
            remaining = tuple(v for v in V if v not in e)
            for Q in itertools.combinations(remaining, 3):
                g = tuple(v for v in remaining if v not in Q)
                row = rho((e,))
                row = [x+y for x, y in zip(row, rho(tuple(sorted((e, g)))))]
                for f in itertools.combinations(Q, 2):
                    row = [x+y for x, y in zip(row, rho(tuple(sorted((e, f)))))]
                    row = [x+y for x, y in zip(row, rho(tuple(sorted((e, f, g)))))]
                add(row, 4, dict(kind='star_edge', terminal=e, capped=Q, edge=g))
    objective = [F(0)]*n
    for e in PAIRS: objective[INDEX['p', e]] = 1
    for S in FOURS:
        for j, matching in enumerate(M4[S]):
            objective[INDEX['f4', S, matching]] = F(1) if j == 1 else F(1, 2)
    for S in SIXES:
        a, b, c, d, e, f = S
        alternating = (((a, b), (c, d), (e, f)), ((a, f), (b, c), (d, e)))
        for matching in M6[S]:
            objective[INDEX['f6', S, matching]] = F(sum(set(other).isdisjoint(matching)
                                                       for other in alternating), 2)
    return rows, rhs, labels, objective


def main(extra_caps=False):
    import numpy as np
    from scipy.optimize import linprog
    rows, rhs, labels, objective = system(extra_caps)
    result = linprog(-np.array(objective, dtype=float), A_ub=rows,
                     b_ub=np.array(rhs, dtype=float), bounds=(0, None), method='highs')
    assert result.success
    dual = [F(float(-v)).limit_denominator(1000000) for v in result.ineqlin.marginals]
    primal = [F(float(v)).limit_denominator(1000000) for v in result.x]
    assert all(v >= 0 for v in dual+primal)
    coefficients = [sum(dual[i]*rows[i][j] for i in range(len(rows))) for j in range(len(STATES))]
    assert all(v >= target for v, target in zip(coefficients, objective))
    assert all(sum(a*x for a, x in zip(row, primal)) <= bound
               for row, bound in zip(rows, rhs))
    bound = sum(v*b for v, b in zip(dual, rhs))
    value = sum(v*c for v, c in zip(primal, objective))
    assert value == bound
    payload = dict(status='exact rational primal and dual verified', scope='C7 shore only',
                   extra_caps=extra_caps,
                   bound=str(bound), states=len(STATES), constraints=len(rows),
                   nonzero_dual=[dict(index=i, label=labels[i], weight=str(v))
                                 for i, v in enumerate(dual) if v],
                   coefficients=list(map(str, coefficients)), objective=list(map(str, objective)),
                   primal=list(map(str, primal)))
    destination = Path(__file__).with_name('random-seven-cycle-cap-rational-dual.json' if extra_caps else 'random-seven-cycle-rational-dual.json')
    destination.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(dict(status=payload['status'], bound=str(bound), states=len(STATES),
                         constraints=len(rows), nonzero_dual_rows=len(payload['nonzero_dual']))))


if __name__ == '__main__': main()
