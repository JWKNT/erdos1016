"""Numerical check of Lemma T6 of fable-thin-chain.md (Fable 5.2, 10 November 2026).

Lemma T6. Let J be a graph with all degrees at most three, and let V_1, ..., V_m be
pairwise disjoint, pairwise non-adjacent vertex sets. Let b_i be the number of edges
that leave V_i and delta_i the sum of 3 - deg(w) over w in V_i. If 0 < theta <= 1/2 and
delta_i + 3 b_i <= theta |V_i| for all i, then the non-backtracking matrix B of J has at
least m real eigenvalues in [2 - theta, 2].

The script builds random graphs that consist of m random cubic pieces, joined in a
ring through separator vertices of degree two, with a few vertices deleted inside the
pieces. For each graph it checks, in floating point:
  1. the formula for the quadratic form of M(lambda) = lambda^2 I - lambda A + Delta - I
     on the indicator vector of each piece;
  2. M(2) is positive semidefinite and M(2 - theta) has at least m eigenvalues <= 0;
  3. B has at least m real eigenvalues in [2 - theta, 2];
  4. every non-real eigenvalue of B has modulus at most sqrt(2).
This is a numerical test, not a proof. It needs numpy.
Run:  python3 fable_check_test_pieces.py
"""
import random

import numpy as np


def random_cubic(n, rng):
    """A random connected simple cubic graph on n vertices (n even), by pairing."""
    while True:
        pts = [v for v in range(n) for _ in range(3)]
        rng.shuffle(pts)
        edges = set()
        ok = True
        for i in range(0, len(pts), 2):
            a, b = pts[i], pts[i + 1]
            if a == b or (min(a, b), max(a, b)) in edges:
                ok = False
                break
            edges.add((min(a, b), max(a, b)))
        if not ok:
            continue
        adj = {v: [] for v in range(n)}
        for a, b in edges:
            adj[a].append(b)
            adj[b].append(a)
        seen, stack = {0}, [0]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        if len(seen) == n:
            return sorted(edges)


def build(m, size, deletions, rng):
    """m cubic pieces in a ring; consecutive pieces are joined through two new vertices."""
    edges, pieces, offset = [], [], 0
    piece_edges = []
    for _ in range(m):
        e = [(a + offset, b + offset) for a, b in random_cubic(size, rng)]
        piece_edges.append(e)
        pieces.append(set(range(offset, offset + size)))
        offset += size
    n = offset
    removed_vertices = set()
    for i in range(m):
        j = (i + 1) % m
        a, b = piece_edges[i].pop(rng.randrange(len(piece_edges[i])))
        c, d = piece_edges[j].pop(rng.randrange(len(piece_edges[j])))
        p, q = n, n + 1
        n += 2
        edges += [(a, p), (p, c), (b, q), (q, d)]
    for i in range(m):
        edges += piece_edges[i]
        for v in rng.sample(sorted(pieces[i]), deletions):
            removed_vertices.add(v)
            pieces[i].discard(v)
    edges = [(a, b) for a, b in edges if a not in removed_vertices and b not in removed_vertices]
    keep = sorted(set(range(n)) - removed_vertices)
    index = {v: k for k, v in enumerate(keep)}
    edges = [(index[a], index[b]) for a, b in edges]
    pieces = [{index[v] for v in piece} for piece in pieces]
    return len(keep), edges, pieces


def check(m, size, deletions, rng):
    n, edges, pieces = build(m, size, deletions, rng)
    A = np.zeros((n, n))
    for a, b in edges:
        A[a, b] += 1
        A[b, a] += 1
    deg = A.sum(axis=1)
    assert deg.max() <= 3
    theta = 0.0
    for piece in pieces:
        ind = np.zeros(n)
        ind[sorted(piece)] = 1
        size_i = len(piece)
        b_i = sum(1 for a, b in edges if (a in piece) != (b in piece))
        delta_i = sum(3 - deg[w] for w in piece)
        theta = max(theta, (delta_i + 3 * b_i) / size_i)
        for lam in (1.3, 1.8, 2.0):
            M = lam * lam * np.eye(n) - lam * A + np.diag(deg) - np.eye(n)
            formula = lam * lam * size_i - lam * (3 * size_i - delta_i - b_i) + 2 * size_i - delta_i
            assert abs(ind @ M @ ind - formula) < 1e-8
    # the pieces are pairwise non-adjacent
    owner = {}
    for k, piece in enumerate(pieces):
        for v in piece:
            owner[v] = k
    assert all(not (a in owner and b in owner and owner[a] != owner[b]) for a, b in edges)
    assert 0 < theta <= 0.5, theta
    M2 = 4 * np.eye(n) - 2 * A + np.diag(deg) - np.eye(n)
    assert np.linalg.eigvalsh(M2).min() > -1e-8
    lam = 2 - theta
    Mt = lam * lam * np.eye(n) - lam * A + np.diag(deg) - np.eye(n)
    assert (np.linalg.eigvalsh(Mt) <= 1e-8).sum() >= m
    # non-backtracking matrix
    darts = [(a, b) for a, b in edges] + [(b, a) for a, b in edges]
    pos = {d: k for k, d in enumerate(darts)}
    out = {}
    for a, b in darts:
        out.setdefault(a, []).append((a, b))
    B = np.zeros((len(darts), len(darts)))
    for (i, j), k in pos.items():
        for (_, w) in out.get(j, []):
            if w != i:
                B[k, pos[(j, w)]] = 1
    ev = np.linalg.eigvals(B)
    real = ev[np.abs(ev.imag) < 1e-7].real
    near_top = int(((real >= 2 - theta - 1e-7) & (real <= 2 + 1e-7)).sum())
    assert near_top >= m, (near_top, m, theta)
    nonreal = ev[np.abs(ev.imag) >= 1e-7]
    assert (np.abs(nonreal) <= np.sqrt(2) + 1e-6).all()
    return n, theta, near_top


if __name__ == "__main__":
    rng = random.Random(77)
    cases = [(3, 40, 0), (4, 60, 0), (5, 60, 1), (6, 80, 1), (4, 100, 2), (8, 60, 0)]
    for m, size, deletions in cases:
        for _ in range(3):
            n, theta, near_top = check(m, size, deletions, rng)
            print(f"m = {m}, piece size {size}, deletions {deletions}: n = {n}, "
                  f"theta = {theta:.3f}, real eigenvalues of B in [2 - theta, 2]: {near_top} >= {m}")
    print("all assertions passed")
