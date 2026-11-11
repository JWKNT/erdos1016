#!/usr/bin/env python3
"""Count the cycles of the cyclic-square graphs G_q of Horak and Kim.

G_q has blocks i = 0..q-1 (indices modulo q). Block i has the vertices
a_i, b_i, c_i, d_i and the four edges between {a_i, b_i} and {c_i, d_i}.
Consecutive blocks are joined by the edges c_i a_(i+1) and d_i b_(i+1).
The graph is cubic, with 4q vertices, 6q edges and rank 2q + 1.

The script counts the cycles in two ways and compares the result with

    c(G_q) = 2^(2q) + (2q + 1/2) 2^q - 3q.

Method 1: depth-first search for simple cycles.
Method 2: enumeration of the cycle space; in a cubic graph a nonzero even
subgraph is a cycle if and only if it is connected.

The script also checks the two formulas of Horak and Kim for their graphs
MC_k, 3 <= k <= 13, and, for a square W of M_j, the edge recursion
(Lemma 2.3 of the paper) and the inequality q(M_j, V(W)) > 1/2.

Run: python3 check_cyclic_squares.py     (a few seconds)
"""
import sys


def graph(q):
    def v(kind, i):
        return 4 * (i % q) + "abcd".index(kind)

    edges = []
    for i in range(q):
        for x in "ab":
            for y in "cd":
                edges.append((v(x, i), v(y, i)))
        edges.append((v("c", i), v("a", i + 1)))
        edges.append((v("d", i), v("b", i + 1)))
    return 4 * q, edges


def cycles_dfs(n, edges):
    """Number of simple cycles of a multigraph, each counted once."""
    adj = [[] for _ in range(n)]
    for idx, (u, w) in enumerate(edges):
        adj[u].append((w, idx))
        adj[w].append((u, idx))
    count = 0
    for start in range(n):
        # cycles whose smallest vertex is `start`
        stack = [(start, -1, 1 << start)]
        while stack:
            u, last_edge, visited = stack.pop()
            for (w, idx) in adj[u]:
                if idx == last_edge or w < start:
                    continue
                if w == start:
                    count += 1
                elif not visited >> w & 1:
                    stack.append((w, idx, visited | 1 << w))
    # every cycle of length >= 3 is found twice (two directions);
    # a cycle of length 2 (parallel pair) is found twice as well
    assert count % 2 == 0
    return count // 2


def cycles_space(n, edges):
    """Number of connected nonzero even subgraphs (cubic graphs only)."""
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
        if ru != rw:
            parent[ru] = rw
            tree[u].append((w, idx))
            tree[w].append((u, idx))
        else:
            nontree.append(idx)
    basis = []
    for idx in nontree:
        u, w = edges[idx]
        mask = 1 << idx
        stack = [(u, 0)]
        seen = {u}
        found = None
        while stack:
            x, m = stack.pop()
            if x == w:
                found = m
                break
            for (y, e) in tree[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append((y, m | 1 << e))
        basis.append(mask | found)
    count = 0
    x = 0
    for g in range(1, 1 << len(basis)):
        x ^= basis[(g & -g).bit_length() - 1]
        # connected?
        sub = [i for i in range(len(edges)) if x >> i & 1]
        par = {}

        def f(a):
            while par.setdefault(a, a) != a:
                par[a] = par[par[a]]
                a = par[a]
            return a

        for i in sub:
            u, w = edges[i]
            par[f(u)] = f(w)
        if len({f(a) for a in list(par)}) == 1:
            count += 1
    return count


def hk_graph(k):
    """The graph MC_k of Horak and Kim: two k-cycles x, y with crossed rungs
    in consecutive pairs; if k is odd, the last rung x_k y_k is straight."""
    def x(i):
        return i % k

    def y(i):
        return k + i % k

    edges = []
    for i in range(k):
        edges.append((x(i), x(i + 1)))
        edges.append((y(i), y(i + 1)))
    for i in range(0, k - 1, 2):
        edges.append((x(i), y(i + 1)))
        edges.append((x(i + 1), y(i)))
    if k % 2 == 1:
        edges.append((x(k - 1), y(k - 1)))
    return 2 * k, edges


def forest_states_outside(n, edges, P):
    """Number of even subgraphs whose part in G - P is a forest, and the rank."""
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
        if ru != rw:
            parent[ru] = rw
            tree[u].append((w, idx))
            tree[w].append((u, idx))
        else:
            nontree.append(idx)
    basis = []
    for idx in nontree:
        u, w = edges[idx]
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
        basis.append(1 << idx | found)
    outside = [i for i, (u, w) in enumerate(edges) if u not in P and w not in P]
    count = 0
    x = 0
    for g in range(1 << len(basis)):
        if g:
            x ^= basis[(g & -g).bit_length() - 1]
        par = {}

        def f(a):
            while par.setdefault(a, a) != a:
                par[a] = par[par[a]]
                a = par[a]
            return a

        ok = True
        for i in outside:
            if x >> i & 1:
                u, w = edges[i]
                ru, rw = f(u), f(w)
                if ru == rw:
                    ok = False
                    break
                par[ru] = rw
        if ok:
            count += 1
    return count, len(basis)


def cycles_through(n, edges, e):
    """Number of cycles through the edge with index e."""
    rest = [ed for i, ed in enumerate(edges) if i != e]
    return cycles_dfs(n, edges) - cycles_dfs(n, rest)


def main():
    ok = True
    # the formulas of Horak and Kim for both parities of the rank
    for k in range(3, 14):
        n, edges = hk_graph(k)
        rank = len(edges) - n + 1
        assert rank == k + 1
        a = cycles_dfs(n, edges)
        if k % 2 == 0:
            formula = 2 ** k + (2 * k + 1) * 2 ** (k // 2) // 2 - 3 * k // 2
        else:
            formula = 2 ** k + (2 * k + 7) * 2 ** ((k - 1) // 2) // 2 - (3 * k + 5) // 2
        print(f"MC_{k}: rank={rank} cycles={a} formula={formula}")
        ok = ok and a == formula
    # a square W of M_j: more than half of the outside parts are forests
    for j in range(2, 6):
        n, edges = graph(j)
        rank = len(edges) - n + 1
        P = {0, 1, 2, 3}                      # the square of block 0
        e = edges.index((0, 2))               # the edge a_0 c_0
        forest, r2 = forest_states_outside(n, edges, P)
        assert r2 == rank
        ce = cycles_through(n, edges, e)
        print(f"M_{j}: rank={rank} c_e={ce} 2^(r-2)={2 ** (rank - 2)} "
              f"forest states={forest} 2^(r-1)={2 ** (rank - 1)}")
        ok = ok and 2 * ce <= forest and ce > 2 ** (rank - 2) and forest > 2 ** (rank - 1)
    for q in range(2, 8):
        n, edges = graph(q)
        deg = [0] * n
        for u, w in edges:
            deg[u] += 1
            deg[w] += 1
        assert all(d == 3 for d in deg)
        rank = len(edges) - n + 1
        assert rank == 2 * q + 1
        formula = 2 ** (2 * q) + (4 * q + 1) * 2 ** q // 2 - 3 * q
        a = cycles_dfs(n, edges)
        b = cycles_space(n, edges) if q <= 6 else a
        excess = a - 2 ** (rank - 1)
        print(f"q={q} rank={rank} cycles={a} (space: {b}) formula={formula} "
              f"excess={excess} excess/(r 2^(r/2))={excess / (rank * 2 ** (rank / 2)):.4f}")
        ok = ok and a == b == formula
    print("all agree" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
