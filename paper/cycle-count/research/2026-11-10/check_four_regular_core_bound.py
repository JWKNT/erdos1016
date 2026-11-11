"""Exact arithmetic certificates for the four-regular core bound.

This checks the finite numerical inequalities in four-regular-phase2.tex.
It does not enumerate graphs or verify the cited degree-sequence theorem.
All pass/fail decisions use fractions and integer powers.
"""

from fractions import Fraction as F
import json
from pathlib import Path


KAPPA_UPPER = F(423, 500)
LAMBDA = F(18, 7)
R = F(7, 6)


def short_cycle_bound(n, k, length):
    ordinary = F((6 * n + 2 * k) * 3 ** (length - 3), length)
    weighted = (F(49, 81) * (n - F(2 * k, 9)) *
                LAMBDA ** length * R ** (n - 2 * k) / length)
    return min(ordinary, weighted)


def finite_certificate(n, k, cutoff=None):
    if cutoff is None:
        cutoff = (4 * n + 3 * k) // 7
    short = (k + sum(((1 - F(length, cutoff)) *
                      short_cycle_bound(n, k, length)
                      for length in range(3, cutoff)), F(0))) / 2 ** n
    long_coefficient = (2 * KAPPA_UPPER * (n - k) + k) / cutoff
    long_fourth = long_coefficient ** 4 * F(3, 4) ** (n - k)
    assert short < 1
    assert long_fourth < (1 - short) ** 4, (n, k)
    return {
        'n': n, 'parallel_pairs': k, 'length_cutoff': cutoff,
        'short_normalized': str(short),
        'long_normalized_fourth_power': str(long_fourth),
        'remaining_allowance_fourth_power': str((1 - short) ** 4),
        'display_only_upper_ratio': float(short) + float(long_fourth) ** 0.25,
    }


def tail_certificate(n):
    cutoff = 4 * n // 7
    short = (F(n, 2) + sum((F(2 * n * 3 ** (length - 1), length)
                            for length in range(3, cutoff)), F(0))) / 2 ** n
    long_eighth = (F(2 * n, cutoff) * F(17, 20)) ** 8 * F(3, 4) ** n
    assert short < 1
    assert long_eighth < (1 - short) ** 8, n
    return {
        'n': n, 'length_cutoff': cutoff,
        'short_normalized': str(short),
        'long_normalized_eighth_power': str(long_eighth),
        'remaining_allowance_eighth_power': str((1 - short) ** 8),
        'display_only_upper_ratio': float(short) + float(long_eighth) ** 0.125,
    }


def main():
    exact_kappa_sixteenth = F(3 ** 19, 2 ** 34)
    assert exact_kappa_sixteenth < KAPPA_UPPER ** 16
    assert KAPPA_UPPER < F(17, 20)
    assert 1 + 2 * F(7, 9) <= LAMBDA
    assert 2 == LAMBDA * F(7, 9)
    assert F(14, 9) / LAMBDA == F(49, 81)
    assert F(1, 2) <= F(49, 81)
    assert F(1, 3) <= F(49, 81)

    finite = [finite_certificate(n, k)
              for n in range(19, 33) for k in range(n // 2 + 1)]
    tail = [tail_certificate(n) for n in range(33, 40)]
    cutoff_by_order = {14: 10, 15: 10, 16: 11, 17: 12, 18: 12}
    small_matching = [finite_certificate(n, k, cutoff_by_order[n])
                      for k in range(3) for n in range(14 + k, 19)]
    # The manuscript proves induction from these seven consecutive orders.
    assert F(81 * (33 + 7), 128 * 33) < 1
    summary = {
        'status': 'all exact inequalities passed',
        'finite_orders': [19, 32],
        'finite_cases': len(finite),
        'tail_base_orders': [33, 39],
        'tail_base_cases': len(tail),
        'maximum_finite_display_ratio': max(x['display_only_upper_ratio'] for x in finite),
        'maximum_tail_base_display_ratio': max(x['display_only_upper_ratio'] for x in tail),
        'remaining_possible_minimum_counterexample_orders': [11, 18],
        'small_matching_cases': len(small_matching),
        'small_matching_cutoffs': {'0': 14, '1': 15, '2': 16},
        'maximum_small_matching_display_ratio': max(
            x['display_only_upper_ratio'] for x in small_matching),
        'kappa_sixteenth': str(exact_kappa_sixteenth),
        'kappa_upper': str(KAPPA_UPPER),
    }
    output = Path(__file__).with_name('four-regular-core-bound-results.json')
    output.write_text(json.dumps({'summary': summary, 'finite': finite, 'tail': tail,
                                  'small_matching': small_matching}, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
