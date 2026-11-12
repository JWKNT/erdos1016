# Sanity check of the "winding parity" picture for a necklace of rings.
# Graph: M rings of length 4; vertex (i,j); ring edges (i,j)-(i,j+1);
# rungs (i,0)-(i+1,1) and (i,2)-(i+1,3), indices of rings mod M.  The graph is cubic.
import itertools, sys
from fractions import Fraction

def build(M, k=4):
    V = [(i, j) for i in range(M) for j in range(k)]
    idx = {v: n for n, v in enumerate(V)}
    E = []
    ring_edges = []
    for i in range(M):
        r = []
        for j in range(k):
            r.append(len(E)); E.append((idx[(i, j)], idx[(i, (j + 1) % k)]))
        ring_edges.append(r)
    rungs = []
    for i in range(M):
        rr = []
        for j in range(0, k, 2):
            rr.append(len(E)); E.append((idx[(i, j)], idx[((i + 1) % M, j + 1)]))
        rungs.append(rr)
    return len(V), E, ring_edges, rungs

def cycle_space(n, E):
    # a basis of the even subgraphs, as bit masks over the edges (spanning tree and fundamental cycles)
    parent = list(range(n)); adj = [[] for _ in range(n)]
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    tree = []; rest = []
    for e, (a, b) in enumerate(E):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb; tree.append(e); adj[a].append((b, e)); adj[b].append((a, e))
        else:
            rest.append(e)
    def path(a, b):
        stack = [(a, -1, 0)]; seen = {a: (None, None)}
        while stack:
            u, pe, _ = stack.pop()
            if u == b: break
            for (w, e) in adj[u]:
                if w not in seen:
                    seen[w] = (u, e); stack.append((w, e, 0))
        m = 0; u = b
        while seen[u][0] is not None:
            m ^= 1 << seen[u][1]; u = seen[u][0]
        return m
    return [path(a, b) ^ (1 << e) for e in rest for (a, b) in [E[e]]]

def run(M):
    n, E, ring_edges, rungs = build(M)
    basis = cycle_space(n, E)
    r = len(basis)
    ring_mask = [sum(1 << e for e in r_) for r_ in ring_edges]
    cut_mask = sum(1 << e for e in rungs[0])          # the rungs between ring 0 and ring 1
    tot = 1 << r
    sel = list(range(0, M - (M % 2), 2))               # rings that are pairwise not adjacent
    cnt_ring = [0] * M; cnt_ring_even = [0] * M
    cnt_pair = 0; cnt_adj = 0; cnt_even = 0
    none_sel_even = 0; none_sel_odd = 0; none_all = 0
    for code in range(tot):
        x = 0
        for b in range(r):
            if code >> b & 1: x ^= basis[b]
        par = bin(x & cut_mask).count('1') & 1
        has = [(x & m) == m for m in ring_mask]
        for i in range(M):
            if has[i]:
                cnt_ring[i] += 1
                if par == 0: cnt_ring_even[i] += 1
        if has[0] and has[2]: cnt_pair += 1
        if has[0] and has[1]: cnt_adj += 1
        if par == 0: cnt_even += 1
        if not any(has): none_all += 1
        if not any(has[i] for i in sel):
            if par == 0: none_sel_even += 1
            else: none_sel_odd += 1
    F = lambda a: Fraction(a, tot)
    p = F(cnt_ring[0]); pe = Fraction(cnt_ring_even[0], cnt_even)
    prod = (1 - pe) ** len(sel)
    print(f"M={M}: rank {r}; P(ring)={p}; rings 0,2: {F(cnt_pair)} = 2*product {2*p*p}; "
          f"adjacent rings 0,1: {F(cnt_adj)} = {F(cnt_adj)/(p*p)} * product; P(even)={F(cnt_even)}")
    print(f"      rings with odd parity: {sum(cnt_ring)-sum(cnt_ring_even)}; "
          f"no ring of {sel} given even: {Fraction(none_sel_even, cnt_even)} (product {prod}); "
          f"given odd: {Fraction(none_sel_odd, tot-cnt_even)}; P(no ring at all)={F(none_all)}")
    return (F(cnt_pair) == 2*p*p and sum(cnt_ring) == sum(cnt_ring_even)
            and Fraction(none_sel_even, cnt_even) == prod and none_sel_odd == tot - cnt_even
            and F(cnt_even) == Fraction(1, 2))

ok = all(run(M) for M in (4, 5, 6, 7))
print("all checks passed" if ok else "A CHECK FAILED")
sys.exit(0 if ok else 1)
