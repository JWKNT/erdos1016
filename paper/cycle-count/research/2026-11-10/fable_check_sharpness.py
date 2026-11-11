"""Checks for fable-sharpness.md (Fable 5.2, 10 November 2026).

The model. W is a cycle w_0 .. w_(m-1). The vertex s_i is joined to w_i by a
spoke and has two free points. There are n0 further vertices with three free
points each. A perfect matching ("pairing") of the M = 3 n0 + 2 m free points
gives a cubic multigraph G, and J = G - V(W).

  Test 1 (exact, all pairings). For every length t,
        sum over pairings and over cycles C of J with |C| = t of 2^beta(G - V(C))
     equals the closed formula of Lemma 2 of fable-sharpness.md, and
        sum over pairings of 2^beta(G)
     equals the number of pairs (pairing, even subgraph) counted by local states.
  Test 2 (exact, all pairings). The moment bounds of Lemma 3:
        E 2^(comp(G) - 1) <= 1 + 3 / (n0/2 + m)   and   E 2^comp(J) <= 3 (m + 1).
  Test 3 (random pairings). The weighted mean of the first-moment sum agrees with
     the closed formula at a larger size.
  Test 4 (exact, explicit graphs). Cubic cages with W attached to a few edges only:
     the exact value of p(G, W) when |E(W)| is about a quarter of the rank.
All counts in Tests 1, 2 and 4 are exact integers or fractions.
Run:  python3 fable_check_sharpness.py
"""
import itertools
import os
import random
import sys
from fractions import Fraction
from math import comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fable_check_blocking import HEAWOOD, MCGEE, PETERSEN, TUTTE_COXETER, cycles_of  # noqa: E402


def dfact(k):
    """(k)!! for odd k, with (-1)!! = 1."""
    out = 1
    while k > 1:
        out *= k
        k -= 2
    return out


def all_pairings(points):
    if not points:
        yield []
        return
    first, rest = points[0], points[1:]
    for i, other in enumerate(rest):
        for tail in all_pairings(rest[:i] + rest[i + 1:]):
            yield [(first, other)] + tail


class Model:
    """Vertex numbering: s_i = i, cubic vertices m .. m + n0 - 1, w_i = m + n0 + i."""

    def __init__(self, n0, m):
        self.n0, self.m = n0, m
        self.points = [v for v in range(m) for _ in range(2)] + \
                      [m + j for j in range(n0) for _ in range(3)]
        self.M = len(self.points)
        self.nv = 2 * m + n0
        self.fixed = [(i, m + n0 + i) for i in range(m)] + \
                     [(m + n0 + i, m + n0 + (i + 1) % m) for i in range(m)]

    def j_edges(self, pairing):
        return [(self.points[a], self.points[b]) for a, b in pairing]


def components(nv, edges, removed=()):
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    return len({find(x) for x in range(nv) if x not in removed})


def beta_without(nv, edges, removed):
    keep = [e for e in edges if e[0] not in removed and e[1] not in removed]
    return len(keep) - (nv - len(removed)) + components(nv, keep, removed)


def cycles_in_multigraph(edges):
    """All cycles (as vertex sets with their length), loops and digons included."""
    out = []
    for size in range(1, len(edges) + 1):
        for sub in itertools.combinations(range(len(edges)), size):
            deg = {}
            for i in sub:
                a, b = edges[i]
                deg[a] = deg.get(a, 0) + 1
                deg[b] = deg.get(b, 0) + 1
            if any(d != 2 for d in deg.values()) or len(deg) != size:
                continue
            if components(max(deg) + 1, [edges[i] for i in sub],
                          removed=set(range(max(deg) + 1)) - set(deg)) == 1:
                out.append((frozenset(deg), size))
    return out


def formula_pairs(model):
    """Number of pairs (pairing, even subgraph), from the local states."""
    n0, m, M = model.n0, model.m, model.M
    total = 0
    for tau in range(0, m + 1, 2):
        for ks in range(m - tau + 1):
            for k3 in range(n0 + 1):
                U = tau + 2 * ks + 2 * k3
                total += (2 * comb(m, tau) * 2 ** tau * comb(m - tau, ks) * comb(n0, k3)
                          * 3 ** k3 * dfact(U - 1) * dfact(M - U - 1))
    return total


def formula_cycles(model, t):
    """Sum over pairs (pairing, even subgraph x) of the number of t-cycles of J in x."""
    n0, m, M = model.n0, model.m, model.M
    total = Fraction(0)
    for tau in range(0, m + 1, 2):
        for ks in range(m - tau + 1):
            for k3 in range(n0 + 1):
                k = ks + k3
                if k < t:
                    continue
                U = tau + 2 * k
                weight = (2 * comb(m, tau) * 2 ** tau * comb(m - tau, ks) * comb(n0, k3)
                          * 3 ** k3 * dfact(U - 1) * dfact(M - U - 1))
                mean = Fraction(1, 2 * t)
                for i in range(t):
                    mean *= Fraction(2 * k - 2 * i, 2 * k + tau - 2 * i - 1)
                total += weight * mean
    return total


def test_exact(n0, m):
    model = Model(n0, m)
    beta0 = m + n0 // 2 + 1
    pairs = 0
    by_length = {}
    count = 0
    sum_free = 0
    sum_j = 0
    for pairing in all_pairings(list(range(model.M))):
        count += 1
        je = model.j_edges(pairing)
        edges = je + model.fixed
        comp = components(model.nv, edges)
        pairs += 2 ** (beta0 + comp - 1)
        sum_free += 2 ** (comp - 1)
        sum_j += 2 ** components(m + n0, je)
        for vertices, t in cycles_in_multigraph(je):
            by_length[t] = by_length.get(t, 0) + 2 ** beta_without(model.nv, edges, vertices)
    assert count == dfact(model.M - 1)
    assert pairs == formula_pairs(model)
    for t in range(1, m + n0 + 1):
        assert by_length.get(t, 0) == formula_cycles(model, t), (n0, m, t)
    # Lemma 3
    assert Fraction(sum_free, count) <= 1 + Fraction(3, n0 // 2 + m)
    assert Fraction(sum_j, count) <= 3 * (m + 1)
    print(f"  n0 = {n0}, m = {m}: {count} pairings, {pairs} pairs; cycle sums by length "
          f"{[by_length.get(t, 0) for t in range(1, m + n0 + 1)]} agree with the formula; "
          f"E 2^(comp(G)-1) = {float(Fraction(sum_free, count)):.4f}, "
          f"E 2^comp(J) = {float(Fraction(sum_j, count)):.4f}")


def simple_cycles_by_dfs(nv, edges):
    """Cycles of a multigraph of maximum degree three, as (vertex set, length)."""
    out = set()
    adj = {}
    for i, (a, b) in enumerate(edges):
        if a == b:
            out.add((frozenset([a]), frozenset([i])))
            continue
        adj.setdefault(a, []).append((b, i))
        adj.setdefault(b, []).append((a, i))

    def go(start, x, vs, es):
        for y, i in adj.get(x, []):
            if i in es:
                continue
            if y == start:
                out.add((frozenset(vs), frozenset(es | {i})))
            elif y > start and y not in vs:
                go(start, y, vs | {y}, es | {i})
    for s in adj:
        go(s, s, {s}, frozenset())
    return [(vs, len(es)) for vs, es in out]


def test_random(n0, m, samples, rng):
    model = Model(n0, m)
    weight_sum = 0
    by_length = {}
    for _ in range(samples):
        pts = list(range(model.M))
        rng.shuffle(pts)
        pairing = [(pts[2 * i], pts[2 * i + 1]) for i in range(model.M // 2)]
        je = model.j_edges(pairing)
        edges = je + model.fixed
        comp = components(model.nv, edges)
        beta = m + n0 // 2 + comp
        w = 2 ** (comp - 1)
        weight_sum += w
        for vertices, t in simple_cycles_by_dfs(model.nv, je):
            p = Fraction(2) ** (beta_without(model.nv, edges, vertices) - beta)
            by_length[t] = by_length.get(t, 0) + w * p
    pairs = formula_pairs(model)
    print(f"  n0 = {n0}, m = {m}, {samples} random pairings: "
          "length, sampled mean, formula")
    worst = 0.0
    for t in range(1, 9):
        sampled = float(by_length.get(t, 0) / weight_sum)
        exact = float(formula_cycles(model, t) / pairs)
        worst = max(worst, abs(sampled - exact))
        print(f"    t = {t}: {sampled:.4f}  {exact:.4f}")
    assert worst < 0.03


def attach(n0, E0, D):
    """Subdivide the edges of J0 with index in D and join the new vertices to a cycle W."""
    m = len(D)
    assert m >= 3
    E = []
    for i, (a, b) in enumerate(E0):
        if i in D:
            z = n0 + D.index(i)
            E += [(a, z), (z, b), (z, n0 + m + D.index(i))]
        else:
            E.append((a, b))
    E += [(n0 + m + i, n0 + m + (i + 1) % m) for i in range(m)]
    return n0 + 2 * m, E


def exact_forest_probability(n0, E0, D, cyc):
    """p(G, W) by inclusion and exclusion over families of disjoint cycles of J."""
    nv, E = attach(n0, E0, D)
    r = len(E) - nv + 1
    index = {i: n0 + k for k, i in enumerate(D)}
    sets = []
    for vm, em in cyc:
        vs = {v for v in range(n0) if (vm >> v) & 1}
        vs |= {index[i] for i in D if (em >> i) & 1}
        sets.append(frozenset(vs))
    first = sum(Fraction(2) ** (beta_without(nv, E, s) - r) for s in sets)
    total = Fraction(1)

    def extend(start, used, sign):
        nonlocal total
        for k in range(start, len(sets)):
            if sets[k] & used:
                continue
            u2 = used | sets[k]
            total += sign * Fraction(2) ** (beta_without(nv, E, u2) - r)
            extend(k + 1, u2, -sign)
    extend(0, frozenset(), -1)
    return total, first, r


def first_moment(n0, E0, D, cyc):
    nv, E = attach(n0, E0, D)
    r = len(E) - nv + 1
    index = {i: n0 + k for k, i in enumerate(D)}
    out = Fraction(0)
    for vm, em in cyc:
        vs = {v for v in range(n0) if (vm >> v) & 1}
        vs |= {index[i] for i in D if (em >> i) & 1}
        out += Fraction(2) ** (beta_without(nv, E, vs) - r)
    return out


def test_cages(rng):
    for name, (n0, E0), m, tries in (("Petersen", PETERSEN, 3, 40), ("Heawood", HEAWOOD, 3, 40),
                                     ("Heawood", HEAWOOD, 4, 40), ("McGee", MCGEE, 4, 12),
                                     ("McGee", MCGEE, 5, 12)):
        cyc = cycles_of(n0, E0)
        best = None
        for _ in range(tries):
            D = sorted(rng.sample(range(len(E0)), m))
            fm = first_moment(n0, E0, D, cyc)
            if best is None or fm < best[0]:
                best = (fm, D)
        p, fm, r = exact_forest_probability(n0, E0, best[1], cyc)
        assert 1 - fm <= p <= 1
        print(f"  {name}: |E(W)| = {m}, rank {r}, |E(W)|/r = {m / r:.3f}, "
              f"p(G, W) = {float(p):.4f}, first-moment bound {float(1 - fm):.4f}, "
              f"attached edges {best[1]}")


if __name__ == "__main__":
    print("Test 1 and Test 2 (all pairings):")
    for n0, m in ((0, 3), (0, 4), (0, 5), (2, 3), (2, 4)):
        test_exact(n0, m)
    print("Test 3 (random pairings):")
    test_random(12, 6, 4000, random.Random(5))
    print("Test 4 (cages with few attachments):")
    test_cages(random.Random(9))
    print("all assertions passed")
