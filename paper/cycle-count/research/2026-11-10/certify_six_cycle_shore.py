#!/usr/bin/env python3
"""Generate and exactly verify a rational dual for the C6-shore functional."""
import json
from fractions import Fraction as F
from pathlib import Path
from check_six_cut_states import PAIRS, FOURS, M4, M6


def system():
    rows, rhs, labels = [], [], []
    def add(row, bound, label):
        rows.append(row); rhs.append(F(bound)); labels.append(label)
    def empty():
        return [0]*75
    def path_index(e):
        return PAIRS.index(e)
    def four_index(S, matching):
        return 15+3*FOURS.index(S)+M4[S].index(matching)
    def noncap(e, f):
        S = tuple(sorted(e+f)); matching = tuple(sorted((e, f)))
        row = empty()
        for alpha in M4[S]:
            if alpha != matching:
                row[four_index(S, alpha)] = 1
        return row
    for e in PAIRS:
        row = empty(); row[path_index(e)] = 1
        add(row, F(1, 2), ['path', e])
    for S in FOURS:
        row = empty()
        for alpha in M4[S]: row[four_index(S, alpha)] = 1
        add(row, 1, ['four_total', S])
    row = empty(); row[60:] = [1]*15
    add(row, 1, ['six_total'])
    add([1]*75, 16, ['aggregate'])
    for S in FOURS:
        for alpha in M4[S]:
            for e in alpha:
                f = next(edge for edge in alpha if edge != e)
                row = noncap(e, f); row[path_index(e)] = 1
                add(row, 1, ['one_edge', e, f])
    for alpha in M6:
        for e in alpha:
            row = empty(); row[path_index(e)] = 1
            for f in alpha:
                if f != e:
                    other = noncap(e, f)
                    row = [x+y for x, y in zip(row, other)]
            for j, beta in enumerate(M6):
                if set(alpha).isdisjoint(beta): row[60+j] = 1
            add(row, 2, ['two_edges', e, [f for f in alpha if f != e]])
    objective = [F(1)]*15+[F(0)]*60
    for S in FOURS:
        for j, alpha in enumerate(M4[S]):
            objective[four_index(S, alpha)] = F(1) if j == 1 else F(1, 2)
    cycle_matchings = (((0, 1), (2, 3), (4, 5)),
                      ((0, 5), (1, 2), (3, 4)))
    for j, beta in enumerate(M6):
        objective[60+j] = F(sum(set(alpha).isdisjoint(beta) for alpha in cycle_matchings), 2)
    return rows, rhs, labels, objective


def main():
    import numpy as np
    from scipy.optimize import linprog
    rows, rhs, labels, objective = system()
    result = linprog(-np.array(objective, dtype=float), A_ub=rows,
                     b_ub=np.array(rhs, dtype=float), bounds=(0, None), method='highs')
    assert result.success
    dual = [F(float(-v)).limit_denominator(100000) for v in result.ineqlin.marginals]
    primal = [F(float(v)).limit_denominator(100000) for v in result.x]
    assert all(v >= 0 for v in dual+primal)
    coefficient_sum = [sum(dual[i]*rows[i][j] for i in range(len(rows))) for j in range(75)]
    assert all(v >= target for v, target in zip(coefficient_sum, objective))
    assert all(sum(a*x for a, x in zip(row, primal)) <= bound
               for row, bound in zip(rows, rhs))
    bound = sum(v*b for v, b in zip(dual, rhs))
    value = sum(v*c for v, c in zip(primal, objective))
    assert bound == value == F(31, 2)
    nonzero = [dict(index=i, label=labels[i], weight=str(v)) for i, v in enumerate(dual) if v]
    payload = dict(status='exact rational primal and dual verified',
                   scope='six-cycle opposite shore only', bound=str(bound),
                   number_of_constraints=len(rows), nonzero_dual=nonzero,
                   coefficient_sum=list(map(str, coefficient_sum)),
                   objective=list(map(str, objective)), primal=list(map(str, primal)))
    destination = Path(__file__).with_name('six-cycle-shore-rational-dual.json')
    destination.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps({k: v for k, v in payload.items()
                      if k not in ('coefficient_sum', 'objective', 'primal')}, indent=2))


if __name__ == '__main__': main()
