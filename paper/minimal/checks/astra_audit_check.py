# Tests, on small graphs, the statements of Astra's notes of 12 November 2026 that the audit note
# research/astra-audit.pdf adopts.  These tests do not replace a proof.
#
# Test 1 (a shortest path).  N is a bridgeless 2-pole of rank b >= 2 with ports s, t; A = w_0 ... w_l
#   is a shortest path from s to t, J = N - V(A), Delta = b - l.  A layer L_j (0 < j < l) is thin if
#   it has exactly two vertices.  For every shortest path the script tests:
#     (a) 0 <= Delta <= beta(J);
#     (b) at most 2 Delta layers between are not thin; at most 4 Delta vertices of J are outside
#         the thin layers;
#     (c) every cycle of J has at most 4 Delta + 2 vertices;
#     (d) at most 2^beta(J) cycles have the same edges in A; an index i is FREE if the further edge
#         of w_(i-1) leads to L_i and that of w_i leads to L_(i-1); no two consecutive indices are
#         free; if e_a, e_z are the first and the last edge of A in a cycle Z, a < i < z, the
#         layers L_(i-1), L_i are thin and i is not free, then e_i is in Z;
#         c(N) <= 10 * 2^(beta(J) + 4 Delta + l/2).
# Test 2 (three full pairs).  Y is a capped ladder with caps p, q and two more ports v, v' on its
#   edges.  If the pairs p,v and p,v' are full, then no port is on an edge with both ends in
#   A = {p} + the first tile, and exactly two edges leave A.
# Test 3 (limits).  All states (a_ij, u_alpha) on a grid with F <= 1, S + F >= 4 and
#     (T1) a_ik + a_jk > 1  =>  a_ij = 0,
#     (T2) a_ik + a_il + a_jk + a_jl > 2  =>  u_{ik|jl} + u_{il|jk} = 0,
#     (T3) a_kl > 0  =>  a_ij + F - u_{ij|kl} <= 1
#   have three numbers a_ij = 1 at a common port, or four numbers a_ij = 1 between two pairs.
# Test 4 (two links).  For a family of regions with weights in a cubic graph:
#     W_2 <= 2 mu (e + N M), with the numbers N, e, M of the lemma.
# Test 5 (the window).  (t + 1/6)^4 <= t^4 + t^3 for t >= 1, and 132 g^2 <= 2^(g/4) for g >= 100.
# Test 6 (caps for two and three ports).  c(capped pole) = c(pole) + sum of the path counts.
#
# Usage: python3 astra_audit_check.py [samples] [seed]     Exit code 0: all tests passed.
import sys, random, itertools
from fractions import Fraction

SAMPLES = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
ok = True


def adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i)); adj[b].append((a, i))
    return adj


def components(n, edges, removed_vertices=frozenset(), removed_edges=frozenset()):
    comp = [-1] * n; c = 0
    adj = adjacency(n, edges)
    for s in range(n):
        if s in removed_vertices or comp[s] >= 0: continue
        comp[s] = c; q = [s]
        for u in q:
            for (w, i) in adj[u]:
                if i in removed_edges or w in removed_vertices or comp[w] >= 0: continue
                comp[w] = c; q.append(w)
        c += 1
    return comp, c


def all_cycles(n, edges):
    """All cycles of a multigraph without loops, as frozensets of edge indices."""
    adj = adjacency(n, edges); found = set()
    by_pair = {}
    for i, (a, b) in enumerate(edges):
        by_pair.setdefault((min(a, b), max(a, b)), []).append(i)
    for ids in by_pair.values():
        for x, y in itertools.combinations(ids, 2): found.add(frozenset((x, y)))
    for s in range(n):
        seen = [False] * n; stack = []
        def go(u):
            seen[u] = True
            for (w, i) in adj[u]:
                if w == s and len(stack) >= 2 and i != stack[0]:
                    found.add(frozenset(stack + [i]))
                elif w > s and not seen[w]:
                    stack.append(i); go(w); stack.pop()
            seen[u] = False
        go(s)
    return [c for c in found if len(c) >= 2 and is_cycle(n, edges, c)]


def is_cycle(n, edges, c):
    deg = {}
    for i in c:
        a, b = edges[i]; deg[a] = deg.get(a, 0) + 1; deg[b] = deg.get(b, 0) + 1
    return all(d == 2 for d in deg.values()) and len(deg) == len(c)


def count_paths(n, adj, s, t, forbidden=frozenset()):
    seen = [False] * n
    for v in forbidden: seen[v] = True
    def go(u):
        if u == t: return 1
        seen[u] = True; total = 0
        for (w, _) in adj[u]:
            if not seen[w]: total += go(w)
        seen[u] = False
        return total
    return go(s)


def random_pole(b, ports):
    """A random connected multigraph without loops and bridges: `ports` vertices of degree two
    (the first ones), the others of degree three, of rank b."""
    n = 2 * b + ports - 2
    while True:
        stubs = [v for v in range(ports) for _ in range(2)] + [v for v in range(ports, n) for _ in range(3)]
        random.shuffle(stubs)
        edges = [(stubs[i], stubs[i + 1]) for i in range(0, len(stubs), 2)]
        if any(a == c for (a, c) in edges): continue
        if components(n, edges)[1] != 1: continue
        if any(components(n, edges, removed_edges=frozenset([i]))[1] != 1 for i in range(len(edges))): continue
        return n, edges


# ------------------------------------------------------------------ Test 1
n1 = paths1 = worst_d = 0; worst_ratio = 0.0
for _ in range(SAMPLES):
    b = random.randint(2, 7)
    n, edges = random_pole(b, 2)
    adj = adjacency(n, edges)
    s, t = 0, 1
    dist = [-1] * n; dist[s] = 0; q = [s]
    for u in q:
        for (w, _) in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; q.append(w)
    l = dist[t]
    layer_size = {}
    for v in range(n): layer_size[dist[v]] = layer_size.get(dist[v], 0) + 1
    thin = {j for j in range(1, l) if layer_size[j] == 2}
    cycles = all_cycles(n, edges)
    # all shortest paths as vertex sequences
    seqs = []
    def back(path):
        u = path[-1]
        if u == s: seqs.append(path[::-1]); return
        for w in sorted(set(w for (w, _) in adj[u])):
            if dist[w] == dist[u] - 1: back(path + [w])
    back([t])
    n1 += 1
    for seq in seqs:
        paths1 += 1
        Aset = set(seq)
        Aedge = []                                  # e_1 .. e_l as edge indices
        for i in range(1, l + 1):
            Aedge.append(min(j for (w, j) in adj[seq[i - 1]] if w == seq[i]))
        Aedges = set(Aedge)
        jv = [v for v in range(n) if v not in Aset]
        je = [i for i, (x, y) in enumerate(edges) if x not in Aset and y not in Aset]
        if jv:
            idx = {v: k for k, v in enumerate(jv)}
            jcomp = components(len(jv), [(idx[edges[i][0]], idx[edges[i][1]]) for i in je])[1]
        else:
            jcomp = 0
        beta = len(je) - len(jv) + jcomp
        Delta = b - l
        if not (0 <= Delta <= beta):
            ok = False; print("FAILED 1(a):", edges, seq)
        not_thin = sum(1 for j in range(1, l) if layer_size[j] != 2)
        outside = sum(1 for v in jv if dist[v] not in thin)
        if not_thin > 2 * Delta or outside > 4 * Delta:
            ok = False; print("FAILED 1(b):", edges, seq)
        for c in cycles:
            if not (c & Aedges) and all(edges[i][0] not in Aset and edges[i][1] not in Aset for i in c):
                if len(c) > 4 * Delta + 2:
                    ok = False; print("FAILED 1(c):", edges, seq, sorted(c))
        # (d)
        further = {}
        for j, v in enumerate(seq):
            fe = [(w, i) for (w, i) in adj[v] if i not in Aedges]
            further[j] = fe[0] if len(fe) == 1 else None
        def free(i):                                # 1 <= i <= l
            f0, f1 = further[i - 1], further[i]
            return f0 is not None and f1 is not None and dist[f0[0]] == i and dist[f1[0]] == i - 1
        for i in range(1, l):
            if free(i) and free(i + 1):
                ok = False; print("FAILED 1(d), two consecutive free indices:", edges, seq, i)
        classes = {}
        for c in cycles:
            pat = tuple(1 if Aedge[i] in c else 0 for i in range(l))
            classes[pat] = classes.get(pat, 0) + 1
            if any(pat):
                a = pat.index(1) + 1; z = l - pat[::-1].index(1)
                for i in range(a + 1, z):
                    if (i - 1) in thin and i in thin and not free(i) and pat[i - 1] == 0:
                        ok = False; print("FAILED 1(d), a forced edge is absent:", edges, seq, pat, i)
        if any(k > 2 ** beta for k in classes.values()):
            ok = False; print("FAILED 1(d), too many cycles with the same edges in A:", edges, seq)
        bound = 10 * 2 ** (beta + 4 * Delta + l / 2)
        if len(cycles) > bound:
            ok = False; print("FAILED 1(d), the bound:", edges, seq, len(cycles), bound)
        worst_ratio = max(worst_ratio, len(cycles) / 2 ** (beta + 4 * Delta + l / 2)); worst_d = max(worst_d, beta)
print(f"Test 1: {n1} bridgeless 2-poles of rank 2..7, {paths1} shortest paths; largest beta(J): {worst_d}; "
      f"largest c(N) / 2^(beta(J) + 4 Delta + l/2): {worst_ratio:.3f} (the lemma allows 10)")

# ------------------------------------------------------------------ Test 2
def capped_ladder(tiles):
    """tiles: list of 1 (single rung) and 2 (square).  Returns n, edges, p, q, first_piece."""
    edges = []; nxt = 1; p = 0
    prev_right = None; first_piece = None
    for k, kind in enumerate(tiles):
        if kind == 1:
            a, b = nxt, nxt + 1; nxt += 2
            edges.append((a, b)); left = (a, b); right = (a, b); verts = (a, b)
        else:
            a, b, a2, b2 = nxt, nxt + 1, nxt + 2, nxt + 3; nxt += 4
            edges += [(a, a2), (a, b2), (b, a2), (b, b2)]; left = (a, b); right = (a2, b2); verts = (a, b, a2, b2)
        if k == 0:
            edges += [(p, left[0]), (p, left[1])]; first_piece = {p, *verts}
        else:
            edges += [(prev_right[0], left[0]), (prev_right[1], left[1])]
        prev_right = right
    q = nxt
    edges += [(prev_right[0], q), (prev_right[1], q)]
    return q + 1, edges, p, q, first_piece

def tile_sequences(W):
    if W == 0: return [[]]
    out = [[1] + r for r in tile_sequences(W - 1)]
    if W >= 2: out += [[2] + r for r in tile_sequences(W - 2)]
    return out

n2 = n2_full = 0
for W in range(3, 7):
    for tiles in tile_sequences(W):
        n, edges, p, q, piece = capped_ladder(tiles)
        inner = {i for i, (x, y) in enumerate(edges) if x in piece and y in piece}
        for i1 in range(len(edges)):
            for i2 in range(len(edges)):
                for order in ((0, 1) if i1 == i2 else (0,)):
                    v, v2 = n, n + 1
                    new = [e for k, e in enumerate(edges) if k not in (i1, i2)]
                    if i1 != i2:
                        x, y = edges[i1]; new += [(x, v), (v, y)]
                        x, y = edges[i2]; new += [(x, v2), (v2, y)]
                    else:
                        x, y = edges[i1]
                        new += [(x, v), (v, v2), (v2, y)] if order == 0 else [(x, v2), (v2, v), (v, y)]
                    adj = adjacency(n + 2, new)
                    n2 += 1
                    full = 2 ** (W + 1)
                    if count_paths(n + 2, adj, p, v) == full and count_paths(n + 2, adj, p, v2) == full:
                        n2_full += 1
                        leaving = sum(1 for (x, y) in new if (x in piece) != (y in piece))
                        if i1 in inner or i2 in inner or leaving != 2:
                            ok = False; print("FAILED 2:", tiles, edges[i1], edges[i2])
print(f"Test 2: {n2} capped ladders of weight 3..6 with two more ports; in {n2_full} of them both pairs at the cap are full")

# ------------------------------------------------------------------ Test 3
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PAIRINGS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
def t1_holds(a, one):
    g = lambda i, j: a[(min(i, j), max(i, j))]
    for i, j in PAIRS:
        for k in range(4):
            if k not in (i, j) and g(i, k) + g(j, k) > one and g(i, j) > 0: return False
    return True
def shape(a, one):
    g = lambda i, j: a[(min(i, j), max(i, j))]
    for c in range(4):
        if all(g(c, j) == one for j in range(4) if j != c): return "star"
    for (p1, p2) in PAIRINGS:
        if all(g(i, k) == one for i in p1 for k in p2): return "cross"
    return None
n3 = 0; shapes = {"star": 0, "cross": 0}
for one in (4, 6, 8):                               # the numbers are multiples of 1/one
    for vals in itertools.product(range(one + 1), repeat=6):
        S = sum(vals)
        if S < 3 * one: continue                    # F <= 1 and S + F >= 4
        a = dict(zip(PAIRS, vals))
        if not t1_holds(a, one): continue
        g = lambda i, j: a[(min(i, j), max(i, j))]
        for u in itertools.product(range(one + 1), repeat=3):
            F = sum(u)
            if F > one or S + F < 4 * one: continue
            good = True
            for idx, (p1, p2) in enumerate(PAIRINGS):
                if sum(g(i, k) for i in p1 for k in p2) > 2 * one and F - u[idx] > 0: good = False
                if a[p2] > 0 and a[p1] + F - u[idx] > one: good = False
                if a[p1] > 0 and a[p2] + F - u[idx] > one: good = False
            if not good: continue
            n3 += 1
            sh = shape(a, one)
            if sh is None:
                ok = False; print("FAILED 3:", one, vals, u)
            else:
                shapes[sh] += 1
print(f"Test 3: {n3} states on the grids 1/4, 1/6, 1/8 with S + F >= 4 and (T1), (T2), (T3): "
      f"{shapes['cross']} crosses, {shapes['star']} stars, no other state")

# ------------------------------------------------------------------ Test 4
def random_cubic(n):
    while True:
        stubs = [v for v in range(n) for _ in range(3)]
        random.shuffle(stubs)
        edges = [(min(stubs[i], stubs[i + 1]), max(stubs[i], stubs[i + 1])) for i in range(0, len(stubs), 2)]
        if any(a == b for (a, b) in edges) or len(set(edges)) < len(edges): continue
        if components(n, edges)[1] != 1: continue
        return edges

n4 = 0; tight = 0.0; n4_two = 0
for _ in range(max(60, SAMPLES // 10)):
    n = random.choice([12, 14, 16])
    edges = random_cubic(n); adj = adjacency(n, edges)
    nb = [set(w for (w, _) in adj[v]) for v in range(n)]
    p = random.randrange(n)
    regions = set()
    for _ in range(40):
        start = random.choice([v for v in range(n) if v != p])
        A = {start}
        for _ in range(random.randint(0, 4)):
            cand = [w for v in A for w in nb[v] if w not in A and w != p]
            if not cand: break
            A.add(random.choice(cand))
        regions.add(frozenset(A))
    regions = list(regions)[:10]
    weight = {A: Fraction(random.randint(1, 4), 4) for A in regions}
    mu = sum(weight.values())
    def links(A, B):
        cnt = sum(1 for (x, y) in edges if (x in A and y in B) or (x in B and y in A))
        comp, c = components(n, edges, removed_vertices=A | B)
        for k in range(c):
            vs = [v for v in range(n) if comp[v] == k]
            if any(nb[v] & A for v in vs) and any(nb[v] & B for v in vs): cnt += 1
        return cnt
    W2 = Fraction(0)
    for A in regions:
        for B in regions:
            if A != B and not (A & B) and links(A, B) == 2:
                W2 += weight[A] * weight[B]; n4_two += 1
    N = e = M = Fraction(0)
    for A in regions:
        out = {w for v in A for w in nb[v] if w not in A}
        N = max(N, len(out))
        e = max(e, sum((weight[B] for B in regions if not (A & B) and any(nb[v] & B for v in A)), Fraction(0)))
        compA, _ = components(n, edges, removed_vertices=A)
        for u in out:
            if compA[u] != compA[p]: continue
            tot = Fraction(0)
            for B in regions:
                if (A & B) or u in B or p in B: continue
                compAB, _ = components(n, edges, removed_vertices=A | B)
                if compAB[u] != compAB[p]: tot += weight[B]
            M = max(M, tot)
    n4 += 1
    bound = 2 * mu * (e + N * M)
    if W2 > bound:
        ok = False; print("FAILED 4:", edges, p, [sorted(A) for A in regions], W2, bound)
    if bound > 0: tight = max(tight, float(W2 / bound))
print(f"Test 4: {n4} families of regions with weights in cubic graphs, {n4_two} ordered pairs with two links; "
      f"largest W_2 / (2 mu (e + N M)): {tight:.3f}")

# ------------------------------------------------------------------ Test 5
bad5 = 0
for k in range(0, 4001):
    t_ = Fraction(1) + Fraction(k, 40)
    if (t_ + Fraction(1, 6)) ** 4 > t_ ** 4 + t_ ** 3: bad5 += 1
for g in range(100, 20001):
    if (132 * g * g) ** 4 > 2 ** g: bad5 += 1      # 132 g^2 <= 2^(g/4)
if bad5: ok = False; print("FAILED 5")
print("Test 5: the two inequalities of the window step hold on the tested range (t in [1, 101], g in [100, 20000])")

# ------------------------------------------------------------------ Test 6
n6 = 0
for _ in range(max(40, SAMPLES // 20)):
    ports = random.choice([2, 3]); b = random.randint(2, 5)
    n, edges = random_pole(b, ports)
    adj = adjacency(n, edges)
    total = sum(count_paths(n, adj, i, j) for i in range(ports) for j in range(i + 1, ports))
    capped = edges + ([(0, 1)] if ports == 2 else [(n, 0), (n, 1), (n, 2)])
    n6 += 1
    if len(all_cycles(n + (ports == 3), capped)) != len(all_cycles(n, edges)) + total:
        ok = False; print("FAILED 6:", edges, ports)
print(f"Test 6: {n6} poles with two or three ports and their caps")

print("all checks passed" if ok else "A CHECK FAILED")
sys.exit(0 if ok else 1)
