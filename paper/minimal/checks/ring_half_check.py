#!/usr/bin/env python3
"""Test of the fine print after Theorem 1.1 of the forest paper.

The ring of k copies of K_{2,2}: vertices a_i, b_i, c_i, d_i for i in Z/k, edges
a_i c_i, a_i d_i, b_i c_i, b_i d_i, c_i a_{i+1}, d_i b_{i+1}. The paper says:

  * the graph is cubic and has rank r = 2k + 1;
  * exactly 2^(2k) cycles contain exactly one of the edges c_i a_{i+1}, d_i b_{i+1}
    for every i, and each of them meets P = {a_0, b_0, c_0, d_0};
  * so q(Gamma, P) >= 1/2, where q is the proportion of the even subgraphs whose
    edges without an end in P form a forest.

The script enumerates all even subgraphs for k = 2, ..., 6 and checks the three
statements. It prints q(Gamma, P) as a fraction. Exit code 0 if all checks pass.
"""
import sys
from fractions import Fraction
from itertools import product


def ring(k):
    V = [(x, i) for i in range(k) for x in "abcd"]
    idx = {v: n for n, v in enumerate(V)}
    E = []
    link = []
    for i in range(k):
        j = (i + 1) % k
        for u, w in [("a", "c"), ("a", "d"), ("b", "c"), ("b", "d")]:
            E.append((idx[(u, i)], idx[(w, i)]))
        link.append((len(E), len(E) + 1))
        E.append((idx[("c", i)], idx[("a", j)]))
        E.append((idx[("d", i)], idx[("b", j)]))
    P = {idx[(x, 0)] for x in "abcd"}
    return len(V), E, link, P


def components_and_forest(n, edges):
    """Number of components that contain an edge, and whether the edge set is a forest."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    forest = True
    for u, w in edges:
        ru, rw = find(u), find(w)
        if ru == rw:
            forest = False
        else:
            parent[ru] = rw
    roots = {find(u) for u, _ in edges}
    return len(roots), forest


def cycle_space_basis(n, E):
    """A basis of the even subgraphs, as bit masks over the edges (Gaussian elimination)."""
    m = len(E)
    rows = []
    for v in range(n):
        mask = 0
        for e, (u, w) in enumerate(E):
            if u != w and v in (u, w):
                mask |= 1 << e
        rows.append(mask)
    pivots = {}
    for r in rows:
        for p, pr in pivots.items():
            if r >> p & 1:
                r ^= pr
        if r:
            p = r.bit_length() - 1
            for q in list(pivots):
                if pivots[q] >> p & 1:
                    pivots[q] ^= r
            pivots[p] = r
    free = [e for e in range(m) if e not in pivots]
    basis = []
    for f in free:
        x = 1 << f
        for p, pr in pivots.items():
            if pr >> f & 1:
                x |= 1 << p
        basis.append(x)
    return basis


def main():
    ok = True
    for k in range(2, 7):
        n, E, link, P = ring(k)
        deg = [0] * n
        for u, w in E:
            deg[u] += 1
            deg[w] += 1
        basis = cycle_space_basis(n, E)
        r = len(basis)
        cubic = all(d == 3 for d in deg)
        around = 0
        around_meet = 0
        forests = 0
        for coeffs in product((0, 1), repeat=r):
            x = 0
            for c, b in zip(coeffs, basis):
                if c:
                    x ^= b
            edges = [E[e] for e in range(len(E)) if x >> e & 1]
            outside = [(u, w) for u, w in edges if u not in P and w not in P]
            if components_and_forest(n, outside)[1]:
                forests += 1
            if not edges:
                continue
            d = [0] * n
            for u, w in edges:
                d[u] += 1
                d[w] += 1
            is_cycle = all(t in (0, 2) for t in d) and components_and_forest(n, edges)[0] == 1
            if is_cycle and all((x >> e1 & 1) + (x >> e2 & 1) == 1 for e1, e2 in link):
                around += 1
                if any(d[v] for v in P):
                    around_meet += 1
        q = Fraction(forests, 2 ** r)
        good = (cubic and r == 2 * k + 1 and around == 2 ** (2 * k)
                and around_meet == around and q >= Fraction(1, 2))
        ok = ok and good
        print(f"k={k}: cubic={cubic} rank={r} cycles around the ring={around} "
              f"(2^(2k)={2 ** (2 * k)}), all meet P: {around_meet == around}, "
              f"q={q} = {float(q):.4f}  {'ok' if good else 'FAIL'}")
    print("all checks passed" if ok else "A CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
