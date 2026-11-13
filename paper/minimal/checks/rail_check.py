#!/usr/bin/env python3
"""Test of the fact on seven integers.

Source: the proof of the lemma on rigid pairs at girth five in `research/slabs.tex`
(Lemma 3.1 there), and `Erdos1016.ExactMaximum.GirthFive.rail_bound` in the Lean library.

Integers p_0, ..., p_m are a rail sequence if, for all k < l,
  (i)   p_k != p_l;
  (ii)  |p_k - p_l| <= (l - k) + 2;
  (iii) |p_k - p_(k+1)| >= 2.
By (ii) and (iii) every step p_(k+1) - p_k is 2, 3, -2 or -3. The test enumerates all
sequences of such steps with p_0 = 0 and checks:

1. no rail sequence has seven terms;
2. rail sequences with six terms exist, and 5, 2, 4, 1, 3, 0 is one of them;
3. in every rail sequence, two consecutive steps of the same sign are both 2 or both -2, of
   two consecutive steps of different signs one has absolute value 2 and the other 3, and no
   three consecutive steps have the same sign (the three statements that the proof uses).

Exit code 0 if all checks pass, 1 if one fails.
"""
import itertools
import sys


def is_rail(p):
    m = len(p)
    for k in range(m):
        for l in range(k + 1, m):
            if p[k] == p[l] or abs(p[k] - p[l]) > (l - k) + 2:
                return False
        if k + 1 < m and abs(p[k] - p[k + 1]) < 2:
            return False
    return True


def rails(terms):
    out = []
    for steps in itertools.product((2, 3, -2, -3), repeat=terms - 1):
        p = [0]
        for s in steps:
            p.append(p[-1] + s)
        if is_rail(p):
            out.append((p, steps))
    return out


def main():
    ok = True
    counts = {m: len(rails(m)) for m in range(2, 8)}
    print("rail sequences with p_0 = 0, by the number of terms:", counts)
    if counts[7] != 0:
        print("FAIL: a rail sequence with seven terms exists")
        ok = False
    if counts[6] == 0 or not is_rail([5, 2, 4, 1, 3, 0]):
        print("FAIL: no rail sequence with six terms")
        ok = False
    # a rail sequence has steps of absolute value 2 or 3 only
    for p in ([0, 1], [0, 4], [0, -4]):
        if is_rail(p):
            print("FAIL: a step of absolute value 1 or 4 is allowed")
            ok = False
    for m in range(3, 7):
        for p, steps in rails(m):
            for a, b in zip(steps, steps[1:]):
                if a * b > 0 and not (a == b and abs(a) == 2):
                    print("FAIL: two steps of the same sign", p)
                    ok = False
                if a * b < 0 and sorted((abs(a), abs(b))) != [2, 3]:
                    print("FAIL: two steps of different signs", p)
                    ok = False
            for a, b, c in zip(steps, steps[1:], steps[2:]):
                if a * b > 0 and b * c > 0:
                    print("FAIL: three steps of the same sign", p)
                    ok = False
    print("all checks pass" if ok else "a check failed")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
