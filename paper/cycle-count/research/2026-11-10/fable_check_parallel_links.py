#!/usr/bin/env python3
"""Exact check of the parallel-link lemma (fable-parallel-links.md).

Setting. Gamma is a connected multigraph. A and B are disjoint connected
vertex sets. c_0, ..., c_m are components of Gamma - (A u B), and each of
them has an edge to A and an edge to B. xi is a uniform element of the
cycle space of Gamma. The event Z_i says that no edge between c_i and the
rest of the graph is in xi.

Claims checked, by enumeration of the whole cycle space:

 (1) If there are at least three links between A and B (link components
     plus direct edges), then for every family T of link components that
     omits at least one link, the events Z_i (i in T) are mutually
     independent.
 (2) If c_i and c_j are the only two links, then
     P(Z_i and Z_j) = 2 P(Z_i) P(Z_j).
 (3) With k cyclic link components c_1..c_k and one more link,
     P(xi is a forest inside every c_i) <= prod_i (1 - P(Z_i)(1 - 2^-b_i)),
     where b_i is the cycle rank of c_i. (This is an equality.)

Run: python3 fable_check_parallel_links.py [number of random graphs]
No third-party package is needed. Run time: about 20 seconds for 300 graphs.
"""
import itertools
import random
import sys
from fractions import Fraction


def connected_random(n, extra, rng, base):
    """A connected multigraph on vertices base..base+n-1: a random tree plus
    `extra` random edges (parallel edges allowed, no loops unless n == 1)."""
    edges = []
    for v in range(1, n):
        edges.append((base + rng.randrange(v), base + v))
    for _ in range(extra):
        if n == 1:
            edges.append((base, base))
        else:
            u, v = rng.sample(range(n), 2)
            edges.append((base + u, base + v))
    return edges


def cycle_space_basis(nv, edges):
    """Fundamental cycles of a spanning forest, as bit masks over edges."""
    parent = list(range(nv))
    tree_adj = [[] for _ in range(nv)]

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    nontree = []
    for idx, (u, v) in enumerate(edges):
        ru, rv = find(u), find(v)
        if u != v and ru != rv:
            parent[ru] = rv
            tree_adj[u].append((v, idx))
            tree_adj[v].append((u, idx))
        else:
            nontree.append(idx)
    basis = []
    for idx in nontree:
        u, v = edges[idx]
        mask = 1 << idx
        if u != v:
            # path from u to v in the tree
            stack = [(u, -1, 0)]
            found = None
            seen = {u}
            while stack:
                w, _, m = stack.pop()
                if w == v:
                    found = m
                    break
                for (y, e) in tree_adj[w]:
                    if y not in seen:
                        seen.add(y)
                        stack.append((y, w, m | (1 << e)))
            assert found is not None
            mask |= found
        basis.append(mask)
    return basis


def is_connected(nv, edges):
    parent = list(range(nv))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for u, v in edges:
        parent[find(u)] = find(v)
    return len({find(v) for v in range(nv)}) == 1


def rank_of(nv_set, edges_inside):
    """Cycle rank of the multigraph on the vertex set with the given edges."""
    verts = sorted(nv_set)
    index = {v: i for i, v in enumerate(verts)}
    parent = list(range(len(verts)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    comps = len(verts)
    for u, v in edges_inside:
        ru, rv = find(index[u]), find(index[v])
        if ru != rv:
            parent[ru] = rv
            comps -= 1
    return len(edges_inside) - len(verts) + comps


def one_case(rng, links, direct, cyclic_only=False):
    """Build one graph. `links` link components, `direct` direct A-B edges."""
    edges = []
    nA = rng.randint(1, 3)
    nB = rng.randint(1, 3)
    A = list(range(nA))
    B = list(range(nA, nA + nB))
    edges += connected_random(nA, rng.randint(0, 1), rng, 0)
    edges += connected_random(nB, rng.randint(0, 1), rng, nA)
    nv = nA + nB
    comps = []
    for _ in range(links):
        n = rng.randint(1, 3)
        extra = rng.randint(1, 2) if cyclic_only else rng.randint(0, 2)
        inside = connected_random(n, extra, rng, nv)
        verts = list(range(nv, nv + n))
        nv += n
        cut = []
        for _ in range(rng.randint(1, 2)):
            cut.append((rng.choice(verts), rng.choice(A)))
        for _ in range(rng.randint(1, 2)):
            cut.append((rng.choice(verts), rng.choice(B)))
        comps.append((verts, inside, cut))
        edges += inside + cut
    # one pendant component at A only, sometimes
    if rng.random() < 0.5:
        n = rng.randint(1, 2)
        inside = connected_random(n, rng.randint(0, 1), rng, nv)
        verts = list(range(nv, nv + n))
        nv += n
        edges += inside
        for _ in range(rng.randint(1, 2)):
            edges.append((rng.choice(verts), rng.choice(A)))
    for _ in range(direct):
        edges.append((rng.choice(A), rng.choice(B)))
    return nv, edges, comps


def check(nv, edges, comps, total_links):
    assert is_connected(nv, edges)
    basis = cycle_space_basis(nv, edges)
    r = len(basis)
    if r > 20:
        return None
    edge_index = {}
    # masks of cut edges and internal edges of each link component
    cut_masks = []
    in_masks = []
    ranks = []
    used = [False] * len(edges)
    for verts, inside, cut in comps:
        vs = set(verts)
        cm = 0
        im = 0
        for idx, (u, v) in enumerate(edges):
            a, b = (u in vs), (v in vs)
            if a != b:
                cm |= 1 << idx
            elif a and b:
                im |= 1 << idx
        cut_masks.append(cm)
        in_masks.append(im)
        ranks.append(rank_of(vs, inside))
    m = len(comps)
    # enumerate the cycle space by Gray code
    count_closed = {}
    forest_count = 0
    x = 0
    size = 1 << r
    counts = [0] * (1 << m)
    forest_all = 0
    for g in range(size):
        if g:
            low = (g & -g).bit_length() - 1
            x ^= basis[low]
        pattern = 0
        ok_forest = True
        for i in range(m):
            if x & cut_masks[i] == 0:
                pattern |= 1 << i
        counts[pattern] += 1
    total = Fraction(size)
    # probability that all of a set T are closed
    def p_closed(T):
        s = 0
        for pat in range(1 << m):
            if pat & T == T:
                s += counts[pat]
        return Fraction(s) / total

    singles = [p_closed(1 << i) for i in range(m)]
    results = []
    if total_links >= 3:
        for T in range(1, 1 << m):
            members = [i for i in range(m) if T >> i & 1]
            if len(members) == total_links:
                continue  # the family must omit a link
            prod = Fraction(1)
            for i in members:
                prod *= singles[i]
            results.append(p_closed(T) == prod)
    if total_links == 2 and m == 2:
        results.append(p_closed(3) == 2 * singles[0] * singles[1])
    return all(results), len(results), singles, ranks


def forest_check(nv, edges, comps):
    """Claim (3): the first component is the extra link; the others are cyclic."""
    basis = cycle_space_basis(nv, edges)
    r = len(basis)
    if r > 20:
        return None
    m = len(comps)
    cut_masks, in_edges, ranks = [], [], []
    for verts, inside, cut in comps:
        vs = set(verts)
        cm = 0
        ins = []
        for idx, (u, v) in enumerate(edges):
            a, b = (u in vs), (v in vs)
            if a != b:
                cm |= 1 << idx
            elif a and b:
                ins.append(idx)
        cut_masks.append(cm)
        in_edges.append(ins)
        ranks.append(rank_of(vs, inside))

    def acyclic(x, ins):
        parent = {}

        def find(a):
            while parent.setdefault(a, a) != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for idx in ins:
            if x >> idx & 1:
                u, v = edges[idx]
                ru, rv = find(u), find(v)
                if ru == rv:
                    return False
                parent[ru] = rv
        return True

    x = 0
    good = 0
    closed = [0] * m
    for g in range(1 << r):
        if g:
            low = (g & -g).bit_length() - 1
            x ^= basis[low]
        for i in range(1, m):
            if x & cut_masks[i] == 0:
                closed[i] += 1
        if all(acyclic(x, in_edges[i]) for i in range(1, m)):
            good += 1
    total = Fraction(1 << r)
    bound = Fraction(1)
    for i in range(1, m):
        p = Fraction(closed[i]) / total
        bound *= 1 - p * (1 - Fraction(1, 2 ** ranks[i]))
    return Fraction(good) / total <= bound, Fraction(good) / total, bound


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(20261110)
    done1 = done2 = done3 = 0
    fam = 0
    for t in range(trials):
        links = rng.randint(2, 4)
        direct = rng.randint(0, 1)
        nv, edges, comps = one_case(rng, links, direct)
        res = check(nv, edges, comps, links + direct)
        if res is None:
            continue
        ok, n, singles, ranks = res
        if not ok:
            print("FAIL (1)/(2)", nv, edges, comps)
            sys.exit(1)
        if links + direct >= 3:
            done1 += 1
            fam += n
        elif n:
            done2 += 1
        nv, edges, comps = one_case(rng, rng.randint(2, 4), 0, cyclic_only=True)
        res = forest_check(nv, edges, comps)
        if res is None:
            continue
        ok, p, bound = res
        if not ok:
            print("FAIL (3)", nv, edges, comps, p, bound)
            sys.exit(1)
        done3 += 1
    print(f"(1) mutual independence: {done1} graphs, {fam} families, all pass")
    print(f"(2) factor two with exactly two links: {done2} graphs, all pass")
    print(f"(3) forest bound: {done3} graphs, all pass")


if __name__ == "__main__":
    main()
