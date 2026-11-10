"""Section 3 of the paper (chords). Random connected simple graphs G of rank r.

For every k with 1 <= k <= r the script takes a set D of k edges outside a
random spanning tree (Lemma 3.1), a second neighbour for each edge of D, the
chords, the graph G+ and the union W of the triangles. It then checks:
  * exactly 2^(r-k) even subgraphs of G avoid D          (Lemma 3.1)
  * every edge of D has a second neighbour               (the construction)
  * beta(G+) = r + a, |E(W)| <= 3k, comp(W) <= k         (the construction)
  * (cycles of G through D) * 2^a <= p(G+,W) * 2^(r+a)   (Lemma 3.2)
  * at most 2^(r-k) cycles of G avoid D
All arithmetic is exact. Run:  python3 check_chords.py
"""
import random
from lib import *

rng = random.Random(12)
cases = 0
for trial in range(300):
    n = rng.randint(4, 8)
    m = min(n - 1 + rng.randint(1, 5), n * (n - 1) // 2)
    E = rand_connected(n, m, rng)
    basis = cyc_basis(n, E)
    r = len(basis)
    if r == 0:
        continue
    Z = span(basis)
    cycles = [z for z in Z if is_cycle(n, E, z)]
    adj = {v: set() for v in range(n)}
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    Eset = set(E)
    # A random spanning tree: add the edges in random order, skip those that close a cycle.
    order = list(range(len(E)))
    rng.shuffle(order)
    tree = 0
    for i in order:
        if is_forest(n, E, tree | (1 << i)):
            tree |= 1 << i
    outside = [i for i in range(len(E)) if not (tree >> i) & 1]
    assert len(outside) == r
    for k in range(1, r + 1):
        # Lemma 3.1: D consists of k edges outside the spanning tree.
        D = rng.sample(outside, k)
        Dmask = sum(1 << e for e in D)
        assert sum(1 for z in Z if not z & Dmask) == 2 ** (r - k)
        # Second neighbours and chords.
        chords, triangles = [], []
        for e in D:
            u, v = E[e]
            if rng.random() < 0.5:
                u, v = v, u
            second = [w for w in adj[v] if w != u]
            assert second
            w = rng.choice(second)
            f = (min(u, w), max(u, w))
            if f not in Eset and f not in chords:
                chords.append(f)
            triangles.append((E[e], (min(v, w), max(v, w)), f))
        a = len(chords)
        Ep = list(E) + chords
        index = {x: i for i, x in enumerate(Ep)}
        basis_p = cyc_basis(n, Ep)
        assert len(basis_p) == r + a
        W = 0
        for T in triangles:
            for x in T:
                W |= 1 << index[x]
        assert bin(W).count('1') <= 3 * k
        VW = sorted({v for i in bits(W) for v in Ep[i]})
        pos = {v: j for j, v in enumerate(VW)}
        EW = [(pos[Ep[i][0]], pos[Ep[i][1]]) for i in bits(W)]
        assert comps(len(VW), EW) <= k
        # Lemma 3.2: count the even subgraphs of G+ with a forest outside W.
        forest = sum(1 for z in span(basis_p) if is_forest(n, Ep, z & ~W))
        through = sum(1 for c in cycles if c & Dmask)
        assert through * 2 ** a <= forest
        assert len(cycles) - through <= 2 ** (r - k)
        cases += 1
print("cases", cases, "- all assertions passed")
