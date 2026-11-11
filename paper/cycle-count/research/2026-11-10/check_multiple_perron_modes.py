#!/usr/bin/env python3
"""Numerical operator checks for the independently proved multi-mode lemma."""

import json
from pathlib import Path

import numpy as np

from check_two_scale_structure import square_ring


def check(blocks, width, starts, theta):
    n, edges, adj, cycles = square_ring(blocks)
    sets = [set().union(*cycles[start:start + width]) for start in starts]
    for left, right in zip(sets, sets[1:]):
        assert not left & right
        assert not any(v in right for u in left for v in adj[u])
    adjacency = np.zeros((n, n))
    for u, v in edges:
        adjacency[u, v] = adjacency[v, u] = 1
    lam = 2 - theta
    pencil = lam * lam * np.eye(n) - lam * adjacency + 2 * np.eye(n)
    indicators = np.zeros((n, len(sets)))
    for column, vertices in enumerate(sets):
        boundary = sum((u in vertices) != (v in vertices) for u, v in edges)
        assert 3 * boundary <= theta * len(vertices) + 1e-10
        indicators[list(vertices), column] = 1
    restriction = indicators.T @ pencil @ indicators
    assert np.max(np.linalg.eigvalsh(restriction)) <= 1e-9
    nonpositive = int(np.sum(np.linalg.eigvalsh(pencil) <= 1e-9))
    assert nonpositive >= len(sets)

    directed = [(u, v) for u, v in edges for u, v in ((u, v), (v, u))]
    lookup = {edge: i for i, edge in enumerate(directed)}
    nb = np.zeros((len(directed), len(directed)))
    for index, (u, v) in enumerate(directed):
        for w in adj[v]:
            if w != u:
                nb[index, lookup[v, w]] = 1
    eigenvalues = np.linalg.eigvals(nb)
    real_near_two = sum(abs(z.imag) < 1e-7 and lam - 1e-7 <= z.real <= 2 + 1e-7
                        for z in eigenvalues)
    assert real_near_two >= len(sets)
    errors = []
    for power in (20, 30, 40):
        trace = float(np.real(np.sum((eigenvalues / 2) ** power)))
        lower = len(sets) * (lam / 2) ** power - 3 * n * 2 ** (-power / 2)
        assert trace >= lower - 1e-7
        errors.append({'power': power, 'normalized_trace': trace,
                       'claimed_lower_bound': lower})
    return {'vertices': n, 'test_sets': len(sets), 'theta': theta,
            'pencil_nonpositive_eigenvalues': nonpositive,
            'nonbacktracking_real_eigenvalues_in_interval': int(real_near_two),
            'even_trace_checks': errors}


def main():
    result = {'status': 'all numerical operator checks passed',
              'precision_note': 'Numerical checks supplement, and do not replace, the exact proof.',
              'cases': [check(28, 6, [0, 9, 18], .5),
                        check(64, 30, [0, 32], .1)]}
    Path(__file__).with_name('multiple-perron-mode-checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
