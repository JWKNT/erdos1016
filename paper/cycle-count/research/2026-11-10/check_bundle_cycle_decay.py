"""Verify the bundle-cycle partition law by three exact rational counts."""

from fractions import Fraction
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).parent
spec = importlib.util.spec_from_file_location('smallcuts', HERE / 'check_exponential_small_cuts.py')
smallcuts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(smallcuts)


def multiply(left, right):
    return [[sum(left[i][j] * right[j][k] for j in range(2))
             for k in range(2)] for i in range(2)]


def check(k, m):
    s = Fraction(1, 1 << (m - 1))
    matrix = [[1 - s, s], [1 - s, s / 2]]
    power = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
    for _ in range(k):
        power = multiply(power, matrix)
    transfer = Fraction(1, 2) + (power[0][0] + power[1][1]) / 2
    independent = Fraction(0)
    for mask in range(1 << k):
        empty = mask.bit_count()
        closed = sum((mask >> i & 1) and (mask >> ((i + 1) % k) & 1)
                     for i in range(k))
        independent += s ** empty * (1 - s) ** (k - empty) / (1 << closed)
    independent = (1 + independent) / 2
    assert transfer == independent
    edges = [(i, (i + 1) % k) for i in range(k) for _ in range(m)]
    states, _, incidents, _ = smallcuts.cycle_data(k, edges)
    direct = sum(Fraction(1, 1 << sum(not mask & star for star in incidents))
                 for mask in states) / len(states)
    assert direct == transfer
    closure = [sum(not mask & star for mask in states) for star in incidents]
    assert all(Fraction(count, len(states)) == Fraction(1, 1 << (2 * m - 1))
               for count in closure)
    return {'vertices': k, 'bundle_multiplicity': m, 'degree': 2 * m,
            'rank': (m - 1) * k + 1,
            'cycle_space_states': len(states),
            'moment': [direct.numerator, direct.denominator]}


rows = [check(k, m) for m in range(1, 5) for k in range(3, 6)]
result = {'status': 'all exact rational checks passed',
          'methods': ['binary cycle-space enumeration',
                      'independent even-bundle emptiness sum',
                      'transfer-matrix trace'],
          'cases': rows}
(HERE / 'bundle-cycle-decay-results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'cases': len(rows),
                  'cycle_space_states': sum(row['cycle_space_states'] for row in rows)}, indent=2))
