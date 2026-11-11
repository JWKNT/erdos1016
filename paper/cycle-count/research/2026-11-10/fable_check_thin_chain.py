"""Checks of the combinatorial lemmas in fable-thin-chain.md (Fable 5.2, 10 November 2026).

The lemmas are statements about a connected graph H, a connected vertex set P,
and vertex-disjoint cycles. The script tests them on random graphs that are
rings of small random blocks, because such graphs have many pairs of cycles
with two links.

  T1. If C and C' are disjoint cycles that avoid P, with no edge between them
      and with at least two links, then some component Y of H - C - C' avoids P
      and is adjacent to both C and C'.
  T4. If u is joined to P in H - C, and two disjoint cycles C1, C2 (disjoint from
      C, u and P) each separate u from P in H - C, then they are nested: exactly
      one of them lies in the component of P after the other is deleted.
  T5. For a nested chain C1 < C2 < ... the slabs between consecutive cycles are
      pairwise disjoint, avoid P, and every edge that leaves a slab ends in
      one of its two cycles or in C.
Run:  python3 fable_check_thin_chain.py
"""
import itertools
import random


def components(n, adj, removed):
    comp = [-1] * n
    k = 0
    for s in range(n):
        if comp[s] >= 0 or s in removed:
            continue
        comp[s] = k
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if comp[y] < 0 and y not in removed:
                    comp[y] = k
                    stack.append(y)
        k += 1
    return comp, k


def short_cycles(n, adj, bound):
    out = set()

    def go(start, path, seen):
        x = path[-1]
        for y in adj[x]:
            if y == start and len(path) >= 3:
                out.add(frozenset(path))
            elif y > start and y not in seen and len(path) < bound:
                go(start, path + [y], seen | {y})
    for s in range(n):
        go(s, [s], {s})
    return [c for c in out]


def ring_graph(rng, blocks, size, extra):
    """A ring of random connected blocks; consecutive blocks are joined by one or two edges."""
    edges = set()
    n = blocks * size
    for b in range(blocks):
        base = b * size
        order = list(range(size))
        rng.shuffle(order)
        for i in range(1, size):
            edges.add(frozenset((base + order[i], base + order[rng.randrange(i)])))
        for _ in range(extra):
            a, c = rng.sample(range(size), 2)
            edges.add(frozenset((base + a, base + c)))
        nxt = ((b + 1) % blocks) * size
        for _ in range(rng.choice((1, 2))):
            edges.add(frozenset((base + rng.randrange(size), nxt + rng.randrange(size))))
    adj = [[] for _ in range(n)]
    for e in edges:
        a, c = tuple(e)
        adj[a].append(c)
        adj[c].append(a)
    return n, adj


def links(n, adj, A, B):
    comp, k = components(n, adj, A | B)
    touchA, touchB = set(), set()
    direct = 0
    for a in A:
        for y in adj[a]:
            if y in B:
                direct += 1
            elif y not in A:
                touchA.add(comp[y])
    for b in B:
        for y in adj[b]:
            if y not in A and y not in B:
                touchB.add(comp[y])
    return direct, touchA & touchB, comp


def run(seed, trials):
    rng = random.Random(seed)
    t1 = t4 = t5 = 0
    for _ in range(trials):
        n, adj = ring_graph(rng, rng.randrange(4, 7), rng.randrange(4, 7), rng.randrange(1, 4))
        if components(n, adj, set())[1] != 1:
            continue
        cycles = short_cycles(n, adj, 6)
        if len(cycles) < 3:
            continue
        # a connected marked set P: one vertex and one of its neighbours
        p0 = rng.randrange(n)
        P = {p0, rng.choice(adj[p0])}
        free = [c for c in cycles if not (c & P)]
        rng.shuffle(free)
        # T1
        for C, C2 in itertools.islice(itertools.combinations(free, 2), 300):
            if C & C2:
                continue
            direct, both, comp = links(n, adj, set(C), set(C2))
            if direct or len(both) < 2:
                continue
            pcomp = comp[p0]
            assert any(k != pcomp for k in both)
            t1 += 1
        # T4 and T5
        for C in free[:6]:
            compC, _ = components(n, adj, set(C))
            nbrs = {y for c in C for y in adj[c] if y not in C}
            for u in nbrs:
                if u in P or compC[u] != compC[p0]:
                    continue
                seps = []
                for D in free:
                    if D & C or u in D:
                        continue
                    comp, _ = components(n, adj, set(C) | set(D))
                    if comp[u] != comp[p0]:
                        seps.append((D, comp))
                for (D1, comp1), (D2, comp2) in itertools.combinations(seps, 2):
                    if D1 & D2:
                        continue
                    first = all(comp1[x] == comp1[p0] for x in D2)      # D2 behind D1
                    second = all(comp2[x] == comp2[p0] for x in D1)     # D1 behind D2
                    assert first != second
                    assert first or all(comp1[x] == comp1[u] for x in D2)
                    t4 += 1
                    near, far, cn, cf = (D1, D2, comp1, comp2) if first else (D2, D1, comp2, comp1)
                    slab = {x for x in range(n) if cf[x] == cf[u] and cn[x] != cn[u]
                            and x not in near and x not in C}
                    assert not (slab & P)
                    for x in slab:
                        for y in adj[x]:
                            assert y in slab or y in near or y in far or y in C
                    t5 += 1
    return t1, t4, t5


if __name__ == "__main__":
    t1, t4, t5 = run(1016, 400)
    print(f"T1: {t1} pairs with at least two links; each has a link that avoids P")
    print(f"T4: {t4} pairs of disjoint separating cycles; each pair is nested in exactly one order")
    print(f"T5: {t5} slabs; every edge that leaves a slab ends in its two cycles or in C")
    assert min(t1, t4, t5) > 50
    print("all assertions passed")
