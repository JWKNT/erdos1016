#!/usr/bin/env python3
"""Verify the saved C6 dual using only exact standard-library arithmetic."""
import json
from fractions import Fraction as F
from pathlib import Path
from certify_six_cycle_shore import system

folder = Path(__file__).resolve().parent
payload = json.loads((folder/'six-cycle-shore-rational-dual.json').read_text())
rows, rhs, labels, objective = system()
dual = [F(0)]*len(rows)
for item in payload['nonzero_dual']:
    index = item['index']
    assert json.loads(json.dumps(labels[index])) == item['label']
    dual[index] = F(item['weight'])
    assert dual[index] >= 0
coefficients = [sum(dual[i]*rows[i][j] for i in range(len(rows))) for j in range(75)]
assert coefficients == objective
assert sum(weight*bound for weight, bound in zip(dual, rhs)) == F(31, 2)
primal = list(map(F, payload['primal']))
assert all(x >= 0 for x in primal)
assert all(sum(a*x for a, x in zip(row, primal)) <= bound
           for row, bound in zip(rows, rhs))
assert sum(x*c for x, c in zip(primal, objective)) == F(31, 2)
print(json.dumps(dict(status='exact verification passed', bound='31/2',
                      objective_coefficients=75, nonzero_dual_rows=30,
                      numerical_solver_required=False)))
