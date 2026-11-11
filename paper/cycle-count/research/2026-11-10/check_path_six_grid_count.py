#!/usr/bin/env python3
"""Check the seven-token grid formula and sharp eleven-sector count exactly."""
import collections
import itertools
import json
import math
from pathlib import Path


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for first in range(total+1):
            for tail in compositions(total-first, parts-1):
                yield (first,)+tail


def choose2(value):
    return value*(value-1)//2


def good_formula(matrix):
    r = list(map(sum, matrix))
    d = [choose2(r[i])-sum(map(choose2, matrix[i])) for i in range(3)]
    answer = sum(d[i]*d[j] for i, j in itertools.combinations(range(3), 2))
    for i in range(3):
        j, k = [v for v in range(3) if v != i]
        different = r[j]*r[k]-sum(matrix[j][c]*matrix[k][c] for c in range(3))
        answer += d[i]*different
        for c in range(3):
            u, v = [a for a in range(3) if a != c]
            minor = matrix[j][u]*matrix[k][v]+matrix[j][v]*matrix[k][u]
            answer += choose2(matrix[i][c])*minor
    return answer


def main():
    rows = collections.defaultdict(lambda: dict(cases=0, maximum_good=0))
    count = equality = 0
    smallest_bad = 35
    for weights in compositions(7, 9):
        matrix = [weights[3*i:3*i+3] for i in range(3)]
        tokens = [divmod(cell, 3) for cell, mass in enumerate(weights) for _ in range(mass)]
        bad = 0
        for subset in itertools.combinations(range(7), 4):
            bad += any(all(tokens[t][0] == row or tokens[t][1] == col for t in subset)
                       for row, col in itertools.product(range(3), repeat=2))
        good = good_formula(matrix)
        assert good == 35-bad
        assert good <= 24
        count += 1
        equality += bad == 11
        smallest_bad = min(smallest_bad, bad)
        profile = ','.join(map(str, sorted(map(sum, matrix), reverse=True)))
        rows[profile]['cases'] += 1
        rows[profile]['maximum_good'] = max(rows[profile]['maximum_good'], good)
    assert count == math.comb(15, 8) == 6435
    result = dict(status='all exact grid and counting-formula checks passed',
                  compositions=count, four_token_subsets=count*35,
                  minimum_bad=smallest_bad, equality_compositions=equality,
                  row_profiles=dict(rows), numerical_solver_used=False)
    Path(__file__).with_name('path-six-seven-grid-checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
