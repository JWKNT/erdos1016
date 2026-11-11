#!/usr/bin/env python3
"""Optional sparse half-integral dual search for the C7 functional."""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csc_matrix
from random_seven_cycle_dual import system

rows, rhs, labels, objective = system(extra_caps=True)
target = [2*c for c in objective]
keep, upper, seen = [], [], set()
for i, (row, label) in enumerate(zip(rows, labels)):
    if label.get('kind') in ('aggregate', 'four_total', 'six_total'):
        continue
    bound = min(int(target[j]//a) for j, a in enumerate(row) if a)
    key = (tuple(row), rhs[i])
    if bound and key not in seen:
        keep.append(i); upper.append(bound); seen.add(key)
matrix = csc_matrix(np.array([rows[i] for i in keep], dtype=float).T)
result = milp(np.array([float(rhs[i]) for i in keep]),
              integrality=np.ones(len(keep)),
              bounds=Bounds(np.zeros(len(keep)), upper),
              constraints=LinearConstraint(matrix, np.array(target, dtype=float),
                                            np.array(target, dtype=float)),
              options={'time_limit': 120, 'mip_rel_gap': 1e-9})
payload = dict(status=int(result.status), eligible_constraints=len(keep),
               numerical_value=None if result.x is None else float(result.fun))
if result.x is not None:
    coefficients = [int(round(v)) for v in result.x]
    assert all(sum(coefficients[t]*rows[i][j] for t, i in enumerate(keep)) == target[j]
               for j in range(len(target)))
    bound = sum(F(coefficients[t], 2)*rhs[i] for t, i in enumerate(keep))
    payload.update(exact_bound=str(bound),
                   nonzero_dual=[dict(index=i, label=labels[i], weight=str(F(coefficients[t], 2)))
                                 for t, i in enumerate(keep) if coefficients[t]])
Path(__file__).with_name('random-seven-cycle-integer-dual.json').write_text(json.dumps(payload, indent=2)+'\n')
print(json.dumps({k: v for k, v in payload.items() if k != 'nonzero_dual'}))
