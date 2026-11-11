#!/usr/bin/env python3
"""Verify exact 15/2 linear certificates for every five-pairing choice."""

import itertools
import json
from fractions import Fraction
from pathlib import Path


def main():
    edges = list(itertools.combinations(range(5), 2))
    index = {edge: i for i, edge in enumerate(edges)}
    subsets = list(itertools.combinations(range(5), 4))
    local = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    pairings = [[tuple(tuple(s[i] for i in pair) for pair in matching)
                 for matching in local] for s in subsets]
    certificates = []
    for excluded in itertools.product(range(3), repeat=5):
        representatives = next(
            choice for choice in itertools.product(
                *(pairings[s][excluded[s]] for s in range(5)))
            if len(set(choice)) == 5)
        target = [1] * 25
        actual = [0] * 25
        rhs = Fraction(0)
        for s, edge in enumerate(representatives):
            actual[index[edge]] += 1
            for a in range(3):
                if a == excluded[s]:
                    target[10 + 3 * s + a] = 0
                else:
                    actual[10 + 3 * s + a] += 1
            rhs += 1
        for edge in edges:
            if edge not in representatives:
                actual[index[edge]] += 1
                rhs += Fraction(1, 2)
        assert actual == target
        assert rhs == Fraction(15, 2)

        # A feasible equality vector makes the relaxation certificate sharp.
        witness = [Fraction(1, 2)] * 10 + [Fraction(0)] * 15
        for s in range(5):
            witness[10 + 3 * s + (excluded[s] + 1) % 3] = Fraction(1, 2)
            forest = sum(witness[10 + 3 * s:13 + 3 * s])
            assert forest <= 1
            for a, matching in enumerate(pairings[s]):
                for edge in matching:
                    assert witness[index[edge]] + forest - witness[10 + 3 * s + a] <= 1
        assert sum(c * x for c, x in zip(target, witness)) == Fraction(15, 2)
        certificates.append({'excluded_pairing_indices': excluded,
                             'representative_edges': representatives})

    result = {
        'status': 'all 243 exact linear certificates and equality vectors passed',
        'exact_bound': '15/2',
        'uses_aggregate_constraint': False,
        'constraint_rows_per_certificate': {'augmented': 5, 'path_upper': 5},
        'subsets_in_order': subsets,
        'certificates': certificates,
        'scope': 'Exact finite verification of the five-port functional; graph-theoretic hypotheses are proved separately.'
    }
    Path(__file__).with_name('four-regular-five-pairing-dual-checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'certificates'}, indent=2))


if __name__ == '__main__':
    main()
