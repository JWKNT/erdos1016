"""A marked cycle of linear size can block every cycle outside it (Fable 5.2).

Construction. Take a cubic graph J0 with n0 vertices and m = 3 n0 / 2 edges.
Subdivide every edge once. Add a cycle W on m new vertices and join the k-th
vertex of W to the k-th subdivision vertex. The result G is cubic, has
4 n0 vertices and rank r = 2 n0 + 1, and |E(W)| = m = 3 (r - 1) / 4.

For a uniform even subgraph xi of G, the part of xi outside W is a forest
unless xi contains a cycle of G - V(W). Such a cycle C comes from a cycle of
J0 of half its length, and exactly 2^(beta(G - V(C))) even subgraphs contain it.
Inclusion and exclusion over families of disjoint cycles gives p(G, W) exactly.
The script checks this formula against direct enumeration for K4 and K_{3,3},
and then evaluates it for cubic graphs of girth 5, 6, 7 and 8.
Run:  python3 fable_check_blocking.py
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "paper-checks"))
from lib import comps, cyc_basis, span, is_forest  # noqa: E402


def lcf(shifts, reps):
    n = len(shifts) * reps
    E = {(i, (i + 1) % n) for i in range(n)}
    for i in range(n):
        E.add((i, (i + shifts[i % len(shifts)]) % n))
    return n, sorted({(min(a, b), max(a, b)) for a, b in E})


def cycles_of(n, E):
    """All cycles of a simple graph, each as a pair (vertex mask, edge mask)."""
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(E):
        adj[a].append((b, i))
        adj[b].append((a, i))
    out = set()

    def go(start, x, vmask, emask):
        for y, i in adj[x]:
            if y == start and bin(emask).count("1") >= 2 and not (emask >> i) & 1:
                out.add((vmask, emask | 1 << i))
            elif y > start and not (vmask >> y) & 1:
                go(start, y, vmask | 1 << y, emask | 1 << i)
    for s in range(n):
        go(s, s, 1 << s, 0)
    return sorted(out)


def build(n0, E0):
    m = len(E0)
    E = []
    for i, (a, b) in enumerate(E0):
        E += [(a, n0 + i), (n0 + i, b), (n0 + i, n0 + m + i)]
    first_w = len(E)
    E += [(n0 + m + i, n0 + m + (i + 1) % m) for i in range(m)]
    wmask = sum(1 << i for i in range(first_w, len(E)))
    return n0 + 2 * m, E, wmask


def exact_by_formula(n0, E0):
    n, E, _ = build(n0, E0)
    r = len(E) - n + 1
    cyc = cycles_of(n0, E0)
    # vertex set in G of a cycle of J0: its vertices and its subdivision vertices
    gsets = [vm | (em << n0) for vm, em in cyc]

    def beta_without(vmask):
        keep = [e for e in E if not ((vmask >> e[0]) & 1 or (vmask >> e[1]) & 1)]
        gone = bin(vmask).count("1")
        return len(keep) - (n - gone) + (comps(n, keep) - gone)
    total = Fraction(0)
    first_moment = Fraction(0)

    def extend(start, vmask, size):
        nonlocal total
        for k in range(start, len(gsets)):
            if gsets[k] & vmask:
                continue
            v2 = vmask | gsets[k]
            total += (-1) ** size * Fraction(2) ** (beta_without(v2) - r)
            extend(k + 1, v2, size + 1)
    extend(0, 0, 0)
    for g in gsets:
        first_moment += Fraction(2) ** (beta_without(g) - r)
    return 1 - total, first_moment, r, len(E0), len(cyc)


def exact_by_enumeration(n0, E0):
    n, E, wmask = build(n0, E0)
    Z = span(cyc_basis(n, E))
    return Fraction(sum(1 for z in Z if is_forest(n, E, z & ~wmask)), len(Z))


K4 = (4, [(a, b) for a in range(4) for b in range(a + 1, 4)])
K33 = (6, [(a, b) for a in range(3) for b in range(3, 6)])
PETERSEN = (10, sorted([(i, (i + 1) % 5) for i in range(5)]
                       + [(i, i + 5) for i in range(5)]
                       + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]))
PETERSEN = (10, sorted({(min(a, b), max(a, b)) for a, b in PETERSEN[1]}))
HEAWOOD = lcf([5, -5], 7)
MCGEE = lcf([12, 7, -7], 8)
TUTTE_COXETER = lcf([-13, -9, 7, -7, 9, 13], 5)

if __name__ == "__main__":
    for name, (n0, E0) in (("K4", K4), ("K33", K33)):
        p, fm, r, m, _ = exact_by_formula(n0, E0)
        assert p == exact_by_enumeration(n0, E0)
        print(f"{name}: formula agrees with enumeration, p = {p} = {float(p):.4f}, "
              f"|E(W)| = {m}, r = {r}")
    for name, (n0, E0) in (("Petersen", PETERSEN), ("Heawood", HEAWOOD),
                           ("McGee", MCGEE), ("Tutte-Coxeter", TUTTE_COXETER)):
        p, fm, r, m, nc = exact_by_formula(n0, E0)
        assert 1 - fm <= p <= 1
        print(f"{name}: {nc} cycles in J0, |E(W)| = {m}, r = {r}, "
              f"|E(W)|/r = {m / r:.3f}, p(G, W) = {float(p):.6f}, "
              f"first-moment bound 1 - {float(fm):.6f}")
    print("all assertions passed")
