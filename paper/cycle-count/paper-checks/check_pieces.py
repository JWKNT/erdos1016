#!/usr/bin/env python3
"""Exact tests of three lemmas of Sections 8 and 9 of the paper.

(1) Lemma 8.2(c), localisation. For a connected multigraph G and a set X
    with a connected complement, the part of a uniform even subgraph inside
    G[X] has the same distribution in G and in the graph G_X, in which the
    complement is replaced by a cycle through new vertices.

(2) Lemma 8.7, the product structure. For two disjoint vertex sets U1, U2
    and a fixed set x of edges outside G[U1] and G[U2], the even subgraphs
    that extend x are the unions of x with a T1-join of G[U1] and a T2-join
    of G[U2].

(3) Lemma 9.1, strings. For a connected multigraph Q without loops and a
    set A, the script computes the relevant vertices by linear algebra over
    GF(2), follows the construction in the proof (feet, tree, exceptions,
    threads, strings) and checks the bounds 2b and the properties (i), (ii)
    and (iii) of the sets M(i, j).

All arithmetic is exact. Run: python3 check_pieces.py   (a few seconds)
"""
import itertools
import random
from collections import Counter
from fractions import Fraction


# ---------------------------------------------------------------- basics

def components(vertices, edges):
    """Connected components of the graph on `vertices` with the given edges."""
    vertices = list(vertices)
    parent = {v: v for v in vertices}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for u, w in edges:
        if u in parent and w in parent:
            parent[find(u)] = find(w)
    groups = {}
    for v in vertices:
        groups.setdefault(find(v), set()).add(v)
    return list(groups.values())


def cycle_basis(n, edges):
    """A basis of the cycle space, as bit masks over the edge indices."""
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    tree = [[] for _ in range(n)]
    nontree = []
    for idx, (u, w) in enumerate(edges):
        ru, rw = find(u), find(w)
        if u != w and ru != rw:
            parent[ru] = rw
            tree[u].append((w, idx))
            tree[w].append((u, idx))
        else:
            nontree.append(idx)
    basis = []
    for idx in nontree:
        u, w = edges[idx]
        mask = 1 << idx
        if u != w:
            stack = [(u, 0)]
            seen = {u}
            found = None
            while stack:
                a, m = stack.pop()
                if a == w:
                    found = m
                    break
                for (b, e) in tree[a]:
                    if b not in seen:
                        seen.add(b)
                        stack.append((b, m | 1 << e))
            mask |= found
        basis.append(mask)
    return basis


def even_subgraphs(n, edges):
    basis = cycle_basis(n, edges)
    x = 0
    yield 0
    for g in range(1, 1 << len(basis)):
        x ^= basis[(g & -g).bit_length() - 1]
        yield x


def random_connected(rng, n, extra, loops=True):
    edges = []
    for v in range(1, n):
        edges.append((rng.randrange(v), v))
    for _ in range(extra):
        u = rng.randrange(n)
        w = rng.randrange(n)
        if u == w and not loops:
            continue
        edges.append((u, w))
    return edges


# ---------------------------------------------------------------- (1)

def test_localisation(rng, trials):
    done = 0
    while done < trials:
        n = rng.randint(4, 8)
        edges = random_connected(rng, n, rng.randint(2, 6))
        X = set(rng.sample(range(n), rng.randint(1, n - 1)))
        rest = [v for v in range(n) if v not in X]
        if len(components(rest, edges)) != 1:
            continue
        inside = [i for i, (u, w) in enumerate(edges) if u in X and w in X]
        boundary = [i for i, (u, w) in enumerate(edges) if (u in X) != (w in X)]
        d = len(boundary)
        if d == 0:
            continue
        # distribution in G
        dist_g = Counter()
        total_g = 0
        for xi in even_subgraphs(n, edges):
            dist_g[tuple(xi >> i & 1 for i in inside)] += 1
            total_g += 1
        # the graph G_X
        xs = sorted(X)
        index = {v: i for i, v in enumerate(xs)}
        edges_x = [(index[edges[i][0]], index[edges[i][1]]) for i in inside]
        m = len(xs)
        new = []
        for i in boundary:
            u, w = edges[i]
            end = u if u in X else w
            edges_x.append((index[end], m))
            new.append(m)
            m += 1
        while len(new) < 3:
            new.append(m)
            m += 1
        for a, b in zip(new, new[1:] + new[:1]):
            edges_x.append((a, b))
        # rank formula of Lemma 8.2(a)
        comp_x = len(components(xs, [edges[i] for i in inside]))
        rank_inside = len(inside) - len(xs) + comp_x
        rank_x = len(edges_x) - m + 1
        assert rank_x == rank_inside + d - comp_x + 1
        dist_x = Counter()
        total_x = 0
        for xi in even_subgraphs(m, edges_x):
            dist_x[tuple(xi >> i & 1 for i in range(len(inside)))] += 1
            total_x += 1
        assert set(dist_g) == set(dist_x)
        for key in dist_g:
            assert Fraction(dist_g[key], total_g) == Fraction(dist_x[key], total_x)
        done += 1
    return done


# ---------------------------------------------------------------- (2)

def test_product(rng, trials):
    done = 0
    fibres = 0
    while done < trials:
        n = rng.randint(5, 9)
        edges = random_connected(rng, n, rng.randint(3, 7))
        order = list(range(n))
        rng.shuffle(order)
        a = rng.randint(1, n - 2)
        b = rng.randint(1, n - a - 1) if n - a - 1 >= 1 else 0
        if b == 0:
            continue
        U1, U2 = set(order[:a]), set(order[a:a + b])
        in1 = [i for i, (u, w) in enumerate(edges) if u in U1 and w in U1]
        in2 = [i for i, (u, w) in enumerate(edges) if u in U2 and w in U2]
        if not in1 or not in2:
            continue
        other = [i for i in range(len(edges)) if i not in in1 and i not in in2]
        fibre = {}
        for xi in even_subgraphs(n, edges):
            key = tuple(xi >> i & 1 for i in other)
            p1 = tuple(xi >> i & 1 for i in in1)
            p2 = tuple(xi >> i & 1 for i in in2)
            fibre.setdefault(key, set()).add((p1, p2))

        def joins(U, inside, T):
            """All sets of inside edges with odd degree exactly on T."""
            out = set()
            for bits in itertools.product((0, 1), repeat=len(inside)):
                deg = Counter()
                for bit, i in zip(bits, inside):
                    if bit:
                        u, w = edges[i]
                        deg[u] += 1
                        deg[w] += 1
                if all((deg[v] % 2 == 1) == (v in T) for v in U):
                    out.add(bits)
            return out

        if len(in1) > 10 or len(in2) > 10:
            continue
        for key, pairs in fibre.items():
            deg = Counter()
            for bit, i in zip(key, other):
                if bit:
                    u, w = edges[i]
                    deg[u] += 1
                    deg[w] += 1
            T1 = {v for v in U1 if deg[v] % 2 == 1}
            T2 = {v for v in U2 if deg[v] % 2 == 1}
            j1 = joins(U1, in1, T1)
            j2 = joins(U2, in2, T2)
            assert pairs == {(p, q) for p in j1 for q in j2}
            assert len(T1) % 2 == 0 and len(T2) % 2 == 0
            fibres += 1
        done += 1
    return done, fibres


# ---------------------------------------------------------------- (3)

def rank_gf2(vectors):
    basis = []
    for v in vectors:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def test_strings(rng, trials):
    done = 0
    long_strings = 0
    pairs_checked = 0
    while done < trials:
        if done % 2 == 0:
            n = rng.randint(7, 11)
            edges = random_connected(rng, n, rng.randint(1, 3), loops=False)
            A = set(rng.sample(range(n), rng.randint(1, 3)))
        else:
            # a chain of small blocks between two vertices of A, with pendant parts
            k = rng.randint(5, 8)
            edges = []
            n = k + 1
            for i in range(k):
                kind = rng.randrange(3)
                if kind == 0:
                    edges.append((i, i + 1))
                elif kind == 1:
                    edges += [(i, i + 1), (i, n), (n, i + 1)]
                    n += 1
                else:
                    edges += [(i, n), (n, i + 1), (i, n + 1), (n + 1, i + 1)]
                    n += 2
            for _ in range(rng.randint(0, 2)):
                edges.append((rng.randrange(1, k), n))
                n += 1
            a0, a1 = n, n + 1
            n += 2
            edges += [(a0, 0), (a1, k)]
            if rng.random() < 0.5:
                edges.append((a0, a1))
            A = {a0, a1}
            if rng.random() < 0.3:
                edges.append((a0, rng.randrange(1, k)))
        basis = cycle_basis(n, edges)
        r = len(basis)
        if r == 0:
            continue

        def functional(i):
            """The functional of edge i, as a vector over the cycle basis."""
            return sum(((basis[k] >> i) & 1) << k for k in range(r))

        at = {v: [i for i, (u, w) in enumerate(edges) if v in (u, w)] for v in range(n)}
        UA = [functional(i) for v in A for i in at[v]]
        rank_A = rank_gf2(UA)
        relevant = set()
        for v in range(n):
            if v in A:
                continue
            Lv = [functional(i) for i in at[v]]
            if rank_gf2(Lv) + rank_A > rank_gf2(Lv + UA):
                relevant.add(v)
        terminals = [i for i, (u, w) in enumerate(edges) if (u in A) != (w in A)]
        b = len(terminals)
        foot = {i: (edges[i][0] if edges[i][1] in A else edges[i][1]) for i in terminals}
        feet = set(foot.values())
        inner_edges = [(u, w) for (u, w) in edges if u not in A and w not in A]
        comps = components([v for v in range(n) if v not in A], inner_edges)
        comp_of = {v: k for k, K in enumerate(comps) for v in K}
        # the forest T: nodes are vertices and ("leaf", terminal)
        T_adj = {}

        def add_edge(a, c):
            T_adj.setdefault(a, set()).add(c)
            T_adj.setdefault(c, set()).add(a)

        for K in comps:
            terms = [i for i in terminals if foot[i] in K]
            if len(terms) < 2:
                continue
            # spanning tree of K by search
            root = next(iter(K))
            parent = {root: None}
            queue = [root]
            for v in queue:
                for (u, w) in inner_edges:
                    if v in (u, w):
                        y = w if u == v else u
                        if y in K and y not in parent:
                            parent[y] = v
                            queue.append(y)
            # union of the tree paths between the feet
            kfeet = {foot[i] for i in terms}
            # count feet below each vertex to find the Steiner tree
            below = Counter()
            for f in kfeet:
                v = f
                while v is not None:
                    below[v] += 1
                    v = parent[v]
            total = len(kfeet)
            for v in K:
                p = parent[v]
                if p is not None and 0 < below[v] < total:
                    add_edge(v, p)
                elif p is not None and below[v] == total and total >= 1:
                    pass
            for i in terms:
                add_edge(foot[i], ("leaf", i))
        deg = {a: len(c) for a, c in T_adj.items()}
        exceptions = {v for v in relevant if v in feet or deg.get(v, 0) >= 3}
        assert len(exceptions) <= 2 * b
        for v in relevant - exceptions:
            assert deg.get(v, 0) == 2, (edges, A, v)
        # threads: maximal paths whose inner vertices have degree two
        threads = []
        seen_edges = set()
        for start in T_adj:
            if deg[start] == 2:
                continue
            for nxt in T_adj[start]:
                if (start, nxt) in seen_edges:
                    continue
                path = [start, nxt]
                seen_edges.add((start, nxt))
                while deg[path[-1]] == 2:
                    a, c = path[-2], path[-1]
                    (d,) = T_adj[c] - {a}
                    path.append(d)
                seen_edges.add((path[-1], path[-2]))
                threads.append(path)
        assert len(threads) <= 2 * b
        strings = [[v for v in path[1:-1] if v in relevant and v not in exceptions]
                   for path in threads]
        covered = {v for s in strings for v in s}
        assert covered == relevant - exceptions
        for s in strings:
            if len(s) < 3:
                continue
            long_strings += 1
            K = comps[comp_of[s[0]]]
            M = {}
            for i in range(len(s)):
                for j in range(i + 2, len(s)):
                    rest = K - {s[i], s[j]}
                    parts = components(rest, inner_edges)
                    (part,) = [p for p in parts if s[i + 1] in p]
                    # (i)
                    assert all(s[l] in part for l in range(i + 1, j))
                    # (ii)
                    for (u, w) in edges:
                        if (u in part) != (w in part):
                            other = w if u in part else u
                            assert other in (s[i], s[j]), (edges, A, s, i, j)
                    M[(i, j)] = part
                    pairs_checked += 1
            # (iii)
            for (i, j), (i2, j2) in itertools.product(M, M):
                if j <= i2:
                    assert not (M[(i, j)] & M[(i2, j2)])
        done += 1
    return done, long_strings, pairs_checked


def main():
    rng = random.Random(20261111)
    a = test_localisation(rng, 400)
    print(f"(1) localisation: {a} cases, all pass")
    b, fibres = test_product(rng, 300)
    print(f"(2) product structure: {b} graphs, {fibres} fibres, all pass")
    c, long_strings, pairs = test_strings(rng, 4000)
    print(f"(3) strings: {c} cases, {long_strings} strings with at least three vertices, "
          f"{pairs} sets M(i,j), all pass")


if __name__ == "__main__":
    main()
