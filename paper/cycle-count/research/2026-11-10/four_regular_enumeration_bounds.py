"""Create exact integer cycle bounds for the twelve residual graph classes.

This script uses only integer and rational arithmetic.  It exports a certified
integer upper bound for sum_C |C| and for each individual short-cycle count.
A checker can therefore test all cutoffs without algebraic numbers.
"""
from fractions import Fraction as F
import json
from pathlib import Path

KAPPA = F(845071, 1000000)
assert F(3**19, 2**34) < KAPPA**16


def floor_fourth_root_fraction(value):
    lo, hi = 0, 1
    while hi**4 <= value:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**4 <= value:
            lo = mid
        else:
            hi = mid
    assert lo**4 <= value < (lo + 1)**4
    return lo


def row(n, k):
    # Lemma core-edge-frequency, with the displayed rational upper kappa.
    fourth = ((2 * KAPPA * (n-k) + k) * 2**n)**4 * F(3, 4)**(n-k)
    root_floor = floor_fourth_root_fraction(fourth)
    root_ceil = root_floor + (root_floor**4 != fourth)
    short = {}
    for ell in range(3, n+1):
        elementary = F((6*n+2*k)*3**(ell-3), ell)
        weighted = (F(49, 81*ell) * (n-F(2*k, 9)) *
                    F(18, 7)**ell * F(7, 6)**(n-2*k))
        bound = min(elementary, weighted)
        short[str(ell)] = bound.numerator // bound.denominator
    return {
        'n': n, 'k': k,
        'target_cycle_count': 2**n+n,
        'length_sum_upper': 2*k+root_floor,
        'length_sum_ceiling': 2*k+root_ceil,
        'length_sum_minus_digon_term_fourth': {
            'numerator': fourth.numerator,
            'denominator': fourth.denominator,
        },
        'short_cycle_upper': {'2': k, **short},
        'cutoffs': list(range(3, n+1)),
    }


def main():
    rows = [row(n, k) for k in range(3) for n in range(11, 14+k)]
    assert len(rows) == 12
    result = {
        'status': 'all integer fourth-power certificates passed',
        'kappa_upper': str(KAPPA),
        'kappa_exact_sixteenth': str(F(3**19, 2**34)),
        'certificate_rule': (
            'For any g in cutoffs, certify c <= target when '
            'length_sum_upper + sum((g-ell)*c_ell for ell=2..g-1) '
            '<= g*target_cycle_count. Each c_ell may be replaced by its '
            'short_cycle_upper or by an exact observed count.'
        ),
        'rows': rows,
    }
    output = Path(__file__).with_name('four-regular-enumeration-bounds.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'cases': len(rows),
                      'bounds': [(r['n'], r['k'], r['length_sum_upper']) for r in rows]}))

if __name__ == '__main__':
    main()
