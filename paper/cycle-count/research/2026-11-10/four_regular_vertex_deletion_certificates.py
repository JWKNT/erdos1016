"""Exact arithmetic certificates for four-regular-vertex-deletion.tex."""
from fractions import Fraction as F
import json
from pathlib import Path

KAPPA = F(845071, 10**6)
RHO = F(1074570, 10**6)
RHO_CUBED = F(1240807, 10**6)
CHI = F(1398653, 10**6)
DELTA_TWO = F(1023197, 10**6)


def constants():
    assert F(3**19, 2**34) < KAPPA**16
    assert F(4, 3) < RHO**4
    assert F(4, 3)**3 < RHO_CUBED**4
    assert F(1, 3) < F(577351, 10**6)**2
    assert F(3, 8)**16 * F(4, 3) / 6**4 < F(243951, 10**6)**16
    assert 2*F(577351, 10**6) + F(243951, 10**6) == CHI
    assert KAPPA**2 < F(3, 4)  # kappa < delta
    assert 16*F(3, 4)**9 < DELTA_TWO**8
    # Tail induction n -> n+2 in the standalone proof.
    assert 2*3**(6-2) >= 6*5*4
    assert F(5, 7*8) < F(1, 10)
    assert F(11, 10)**2 * F(3, 4) < 1
    assert F(3*12, 4*10) < 1
    assert 2*KAPPA > 1 and CHI > 1
    assert RHO/3 < 1 and RHO_CUBED/4 < 1


def certificate(n, k):
    g = (n+3)//2
    k_remaining = max(k-1, 0)
    short = (int(k > 0) + (1-F(2, g))*k_remaining +
             sum(((1-F(ell, g))*F((6*(n-1)+2*k_remaining)*3**(ell-3), ell)
                  for ell in range(3, g)), F(0))) / 2**n
    if k == 0:
        coefficient = 2*KAPPA + F(2*n-4, 6*g)*RHO
    else:
        coefficient = CHI + F(2*n-4, 8*g)*RHO_CUBED
    fourth = coefficient**4 * F(3, 4)**(n-k)
    assert short < 1
    assert fourth < (1-short)**4, (n, k)
    return {
        'n': n, 'k': k, 'cutoff': g,
        'short_normalized': str(short),
        'long_coefficient_upper': str(coefficient),
        'long_normalized_fourth': str(fourth),
        'allowance_fourth': str((1-short)**4),
        'display_only_ratio': float(short)+float(fourth)**0.25,
    }


def two_deletion_certificate():
    n, g = 11, 6
    short = sum(((1-F(ell, g))*F(18*3**(ell-2), ell)
                 for ell in range(3, g)), F(0)) / 2**n
    coefficient = 2*KAPPA + RHO/4 + F(5, 36)*DELTA_TWO*RHO_CUBED
    fourth = coefficient**4 * F(3, 4)**n
    assert short < 1
    assert fourth < (1-short)**4
    return {
        'n': n, 'k': 0, 'cutoff': g, 'deleted_vertices': 2,
        'short_normalized': str(short),
        'long_coefficient_upper': str(coefficient),
        'long_normalized_fourth': str(fourth),
        'allowance_fourth': str((1-short)**4),
        'display_only_ratio': float(short)+float(fourth)**0.25,
    }


def main():
    constants()
    rows = [certificate(n, k) for k in range(3)
            for n in range(12 if k == 0 else 11, 19)]
    assert len(rows) == 23
    rows.append(two_deletion_certificate())
    assert len(rows) == 24
    result = {
        'status': 'all exact inequalities passed',
        'finite_cases': len(rows),
        'standalone_induction_base_cases': 7,
        'tail_monotonicity': 'all exact constant checks passed',
        'maximum_display_ratio': max(r['display_only_ratio'] for r in rows),
        'kappa_upper': str(KAPPA), 'rho_upper': str(RHO),
        'rho_cubed_upper': str(RHO_CUBED), 'chi_upper': str(CHI),
        'delta_two_upper': str(DELTA_TWO),
        'rows': rows,
    }
    Path(__file__).with_name('four-regular-vertex-deletion-results.json').write_text(
        json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'rows'}, indent=2))

if __name__ == '__main__':
    main()
