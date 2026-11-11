#!/usr/bin/env python3
"""Exact C7 certificate verification using only the standard library."""
import collections
import itertools
import json
from fractions import Fraction as F
from pathlib import Path
from random_seven_cycle_dual import PAIRS, FOURS, SIXES, system

folder = Path(__file__).resolve().parent
certificate = json.loads((folder/'random-seven-cycle-integer-dual.json').read_text())
rows, rhs, labels, objective = system(extra_caps=True)
weights = [F(0)]*len(rows)
symbols = collections.Counter()


def key(edges):
    return tuple(sorted(tuple(edge) for edge in edges))


def add(edges):
    symbols[key(edges)] += 1


for item in certificate['nonzero_dual']:
    i = item['index']
    label = item['label']
    assert json.loads(json.dumps(labels[i])) == label
    assert F(item['weight']) == F(1, 2)
    weights[i] = F(1, 2)
    e = tuple(label['terminal'])
    add([e])
    if 'matching' in label:
        rest = [tuple(f) for f in label['matching'] if tuple(f) != e]
        for f in rest:
            add([e, f])
        if len(rest) == 2:
            add([e]+rest)
    elif label['kind'] == 'star':
        for f in itertools.combinations(label['capped'], 2):
            add([e, f])
    elif label['kind'] == 'binary':
        filled = sorted(sum(label['pairing'], []))
        for f in itertools.combinations(filled, 2):
            add([e, f])
        add([e]+label['pairing'])
    elif label['kind'] == 'star_edge':
        g = tuple(label['edge'])
        add([e, g])
        for f in itertools.combinations(label['capped'], 2):
            add([e, f]); add([e, f, g])
    else:
        raise AssertionError(label)

target = collections.Counter({(e,): 2 for e in PAIRS})
for a, b, c, d in FOURS:
    target[key(((a, b), (c, d)))] += 1
    target[key(((a, d), (b, c)))] += 1
for a, b, c, d, e, f in SIXES:
    target[key(((a, b), (c, d), (e, f)))] += 1
    target[key(((a, f), (b, c), (d, e)))] += 1
assert symbols == target
coefficients = [sum(weights[i]*rows[i][j] for i in range(len(rows)))
                for j in range(len(objective))]
assert coefficients == objective
assert sum(a*b for a, b in zip(weights, rhs)) == F(63, 2)
result = dict(status='exact verification passed', scope='C7 shore only',
              bound='63/2', certificate_rows=42, nonzero_formal_symbols=len(target),
              expanded_coefficients=len(objective), numerical_solver_required=False)
(folder/'random-seven-cycle-verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result))
