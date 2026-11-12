# Tests, on small multigraphs, two statements of the research note research/fewer-cases.pdf.
#
# Test A (ladders).  Let N be a bridgeless 2-pole of rank b >= 2 with ports s, t (a connected
#   multigraph without loops and without bridge; s and t have degree two, all other vertices have
#   degree three).  Let A be a shortest path from s to t and J = N - V(A).  Then
#       J is a forest   <=>   the pair s, t is full (P_st = 2^b),
#   for every choice of the shortest path A.  If J has a cycle Z, then
#       P_st <= 2^b - 2^(b - |Z| + k - 1),   k = number of components of N - E(Z)
#   (Lemma 5.1 of the paper).  The note derives the gap theorem from these two facts.
#
# Test B (a cycle of length four).  Let G be a cubic graph, C = c1 c2 c3 c4 a cycle of length four
#   whose four outside neighbours 1, 2, 3, 4 are distinct and outside C, and Y = G - V(C).  Then
#       c(G) = 1 + c(Y) + 2 * sum_{i<j} P_ij(Y) + f_{12|34}(Y) + f_{14|23}(Y) + 2 f_{13|24}(Y),
#   and  c(G) + c(Y) = 1 + c(Y with the cap for 12|34) + c(Y with the cap for 14|23).
#   The cap for ij|kl has two new adjacent vertices x, y; x is joined to i, j and y to k, l.
#
# Test C (a marked set), Test D (the arithmetic of the rigidity lemma) and Test E (three states
#   that show which tools the arithmetic needs) are described at their places below.
#
# Usage: python3 gap_and_square_check.py [samples] [seed]     Exit code 0: all tests passed.
import sys, random

SAMPLES = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)


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


def is_forest(n, edges, removed_vertices=frozenset()):
    par = list(range(n))
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for (a, b) in edges:
        if a in removed_vertices or b in removed_vertices: continue
        ra, rb = find(a), find(b)
        if ra == rb: return False
        par[ra] = rb
    return True


def count_paths(n, adj, s, t, forbidden=frozenset()):
    """Number of paths from s to t (as edge sets) that avoid the vertices in `forbidden`."""
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


def paths_as_vertex_sets(n, adj, s, t):
    """All paths from s to t, as (frozenset of vertices) with multiplicity for parallel edges."""
    out = []; seen = [False] * n; stack = []
    def go(u):
        stack.append(u)
        if u == t:
            out.append(frozenset(stack))
        else:
            seen[u] = True
            for (w, _) in adj[u]:
                if not seen[w]: go(w)
            seen[u] = False
        stack.pop()
    go(s)
    return out


def count_cycles(n, edges):
    """Number of cycles of a multigraph without loops."""
    adj = adjacency(n, edges); total = 0
    # cycles of length two: pairs of parallel edges
    mult = {}
    for (a, b) in edges:
        key = (min(a, b), max(a, b)); mult[key] = mult.get(key, 0) + 1
    for m in mult.values(): total += m * (m - 1) // 2
    # longer cycles: least vertex s, counted once for each direction, so divide by two
    longer = 0
    for s in range(n):
        seen = [False] * n
        def go(u, length):
            c = 0
            seen[u] = True
            for (w, _) in adj[u]:
                if w == s and length >= 2: c += 1
                elif w > s and not seen[w]: c += go(w, length + 1)
            seen[u] = False
            return c
        longer += go(s, 0)
    return total + longer // 2


def shortest_paths(n, adj, s, t):
    dist = [-1] * n; dist[s] = 0; q = [s]
    for u in q:
        for (w, _) in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; q.append(w)
    out = []
    def back(path):
        u = path[-1]
        if u == s: out.append(frozenset(path)); return
        for w in set(w for (w, _) in adj[u]):
            if dist[w] == dist[u] - 1: back(path + [w])
    back([t])
    return out


def girth_cycle_in(n, edges, removed):
    """A shortest cycle (as a list of edge indices) of the multigraph without the vertices `removed`."""
    adj = adjacency(n, edges); best = None
    for i, (a, b) in enumerate(edges):
        if a in removed or b in removed: continue
        # shortest path from a to b that avoids the edge i
        par = {a: None}; q = [a]
        for u in q:
            if u == b: break
            for (w, j) in adj[u]:
                if j == i or w in removed or w in par: continue
                par[w] = (u, j); q.append(w)
        if b in par:
            cyc = [i]; u = b
            while par[u] is not None:
                cyc.append(par[u][1]); u = par[u][0]
            if best is None or len(cyc) < len(best): best = cyc
    return best


def random_two_pole(b):
    n = 2 * b
    while True:
        stubs = [0, 0, 1, 1] + [v for v in range(2, n) for _ in range(3)]
        random.shuffle(stubs)
        edges = [(stubs[i], stubs[i + 1]) for i in range(0, len(stubs), 2)]
        if any(a == b_ for (a, b_) in edges): continue
        if components(n, edges)[1] != 1: continue
        if any(components(n, edges, removed_edges=frozenset([i]))[1] != 1 for i in range(len(edges))): continue
        return n, edges


ok = True
# ------------------------------------------------------------------ Test A
nA = full = forestJ = cyc = 0
for _ in range(SAMPLES):
    b = random.randint(2, 6)
    n, edges = random_two_pole(b)
    adj = adjacency(n, edges)
    P = count_paths(n, adj, 0, 1)
    is_full = (P == 2 ** b)
    nA += 1; full += is_full
    for A in shortest_paths(n, adj, 0, 1):
        f = is_forest(n, edges, removed_vertices=A)
        forestJ += f
        if f != is_full:
            ok = False; print("FAILED A (forest <=> full):", edges, sorted(A))
        if not f:
            Z = girth_cycle_in(n, edges, A); cyc += 1
            k = components(n, edges, removed_edges=frozenset(Z))[1]
            if P > 2 ** b - 2 ** (b - len(Z) + k - 1):
                ok = False; print("FAILED A (Lemma 5.1):", edges, sorted(A), Z)
print(f"Test A: {nA} bridgeless 2-poles of rank 2..6; full pairs: {full}; "
      f"shortest paths with J a forest: {forestJ}, with a cycle in J: {cyc}")

# ------------------------------------------------------------------ Test B
def random_cubic(n):
    while True:
        stubs = [v for v in range(n) for _ in range(3)]
        random.shuffle(stubs)
        edges = [(min(stubs[i], stubs[i + 1]), max(stubs[i], stubs[i + 1])) for i in range(0, len(stubs), 2)]
        if any(a == b for (a, b) in edges) or len(set(edges)) < len(edges): continue
        if components(n, edges)[1] != 1: continue
        return edges

nB = 0
tries = 0
while nB < max(40, SAMPLES // 30) and tries < 200000:
    tries += 1
    n = random.choice([10, 12, 14])
    edges = random_cubic(n)
    adj = adjacency(n, edges)
    nb = [set(w for (w, _) in adj[v]) for v in range(n)]
    square = None
    for c1 in range(n):
        for c2 in nb[c1]:
            for c3 in nb[c2] - {c1}:
                for c4 in (nb[c3] & nb[c1]) - {c2}:
                    square = (c1, c2, c3, c4); break
                if square: break
            if square: break
        if square: break
    if not square: continue
    C = set(square)
    ports = []
    for v in square:
        out = [w for w in nb[v] if w not in C]
        if len(out) != 1: ports = None; break
        ports.append(out[0])
    if ports is None or len(set(ports)) < 4: continue
    keep = sorted(set(range(n)) - C); idx = {v: i for i, v in enumerate(keep)}
    yedges = [(idx[a], idx[b]) for (a, b) in edges if a in idx and b in idx]
    m = len(keep)
    if components(m, yedges)[1] != 1: continue
    yadj = adjacency(m, yedges)
    p = [idx[v] for v in ports]
    Pij = {(i, j): count_paths(m, yadj, p[i], p[j]) for i in range(4) for j in range(i + 1, 4)}
    def linkage(i, j, k, l):
        total = 0
        for vs in paths_as_vertex_sets(m, yadj, p[i], p[j]):
            if p[k] in vs or p[l] in vs: continue
            total += count_paths(m, yadj, p[k], p[l], forbidden=vs)
        return total
    f12_34 = linkage(0, 1, 2, 3); f14_23 = linkage(0, 3, 1, 2); f13_24 = linkage(0, 2, 1, 3)
    lhs = count_cycles(n, edges)
    rhs = 1 + count_cycles(m, yedges) + 2 * sum(Pij.values()) + f12_34 + f14_23 + 2 * f13_24
    def capped(i, j, k, l):
        x, y = m, m + 1
        return count_cycles(m + 2, yedges + [(x, y), (x, p[i]), (x, p[j]), (y, p[k]), (y, p[l])])
    nB += 1
    if lhs != rhs:
        ok = False; print("FAILED B:", edges, square, lhs, rhs)
    if lhs + count_cycles(m, yedges) != 1 + capped(0, 1, 2, 3) + capped(0, 3, 1, 2):
        ok = False; print("FAILED B (caps):", edges, square)
print(f"Test B: {nB} cubic graphs with a cycle of length four; the formula for c(G) was compared with a direct count")

# ------------------------------------------------------------------ Test C
# The count with a marked set.  G is a cubic graph without a bridge, P a connected set of p
# vertices.  q(G,P) is the proportion of the even subgraphs whose edges without an end in P form a
# forest.  The note claims  c(G) <= q(G,P) 2^r + 2^(r-1-p/2)  and  beta(G-P) <= r-1-p/2.
def even_subgraphs(n, edges):
    """A basis of the cycle space as bit masks (the graph is connected)."""
    adj = adjacency(n, edges)
    parent = {0: -1}; pedge = {}; order = [0]; tree = set()
    for u in order:
        for (w, i) in adj[u]:
            if w not in parent:
                parent[w] = u; pedge[w] = i; tree.add(i); order.append(w)
    def path(v):
        m = 0
        while parent[v] != -1:
            m ^= 1 << pedge[v]; v = parent[v]
        return m
    return [(1 << i) ^ path(a) ^ path(b) for i, (a, b) in enumerate(edges) if i not in tree]

nC = 0
while nC < max(40, SAMPLES // 30):
    n = random.choice([10, 12, 14])
    edges = random_cubic(n)
    if any(components(n, edges, removed_edges=frozenset([i]))[1] != 1 for i in range(len(edges))): continue
    r = len(edges) - n + 1
    adj = adjacency(n, edges)
    P = {random.randrange(n)}
    for _ in range(random.randint(1, 5)):
        nb = [w for v in P for (w, _) in adj[v] if w not in P]
        P.add(random.choice(nb))
    pp = len(P)
    outside = [i for i, (a, b) in enumerate(edges) if a not in P and b not in P]
    basis = even_subgraphs(n, edges)
    forests = 0
    for mask in range(1 << r):
        xi = 0
        for j in range(r):
            if mask >> j & 1: xi ^= basis[j]
        if is_forest(n, [edges[i] for i in outside if xi >> i & 1]): forests += 1
    cG = count_cycles(n, edges)
    keep = sorted(set(range(n)) - P); idx = {v: i for i, v in enumerate(keep)}
    sub_edges = [(idx[a], idx[b]) for (a, b) in edges if a in idx and b in idx]
    beta = len(sub_edges) - len(keep) + components(len(keep), sub_edges)[1]
    nC += 1
    if 2 * beta > 2 * r - 2 - pp or cG > forests + 2 ** beta:
        ok = False; print("FAILED C:", edges, sorted(P), cG, forests, beta)
print(f"Test C: {nC} cubic graphs without a bridge with a marked set of 2 to 6 vertices")

# ------------------------------------------------------------------ Test D
# The arithmetic of the rigidity lemma.  A state consists of numbers a_ij in [0,1] and
# u_1,u_2,u_3 >= 0 with sum F <= 1 that satisfy (T1), (T2), (T3) for eta and kappa <= eta.  The
# lemma claims: if S + F >= 4 - 2 eta, then three numbers a_ij at a common port are more than
# 1 - 8 eta, or the four numbers between two disjoint pairs of ports are more than 1 - 7 eta.
# The test is a local search: among the states WITHOUT this conclusion it makes S + F as large as
# it can.  The lemma says that the result stays below 4 - 2 eta.
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PAIRINGS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
def consistent(a, u, eta, kappa):
    F = sum(u)
    if F > 1 or min(u) < 0 or min(a.values()) < 0 or max(a.values()) > 1: return False
    g = lambda i, j: a[(min(i, j), max(i, j))]
    for i, j in PAIRS:
        for k in range(4):
            if k not in (i, j) and g(i, k) + g(j, k) >= 1 + 2 * eta and g(i, j) > kappa: return False
    for idx, (p1, p2) in enumerate(PAIRINGS):
        cross = sum(g(i, k) for i in p1 for k in p2)
        if cross >= 2 + 4 * eta and F - u[idx] > kappa: return False
        if a[p2] > kappa and a[p1] + F - u[idx] >= 1 + 2 * eta: return False
        if a[p1] > kappa and a[p2] + F - u[idx] >= 1 + 2 * eta: return False
    return True
def conclusion(a, eta):
    g = lambda i, j: a[(min(i, j), max(i, j))]
    for c in range(4):
        if all(g(c, j) > 1 - 8 * eta for j in range(4) if j != c): return True
    for (p1, p2) in PAIRINGS:
        if all(g(i, k) > 1 - 7 * eta for i in p1 for k in p2): return True
    return False
def start_state(eta, kappa):
    kind = random.randrange(4)
    a = {pr: 0.0 for pr in PAIRS}; u = [0.0, 0.0, 0.0]
    if kind == 0:                                   # a cross with one number too small
        idx = random.randrange(3); p1, p2 = PAIRINGS[idx]
        for i in p1:
            for k in p2: a[(min(i, k), max(i, k))] = 1.0
        bad = random.choice([pr for pr in PAIRS if a[pr] == 1.0]); a[bad] = 1 - 7 * eta
        u[idx] = random.uniform(0, 2 * eta)
    elif kind == 1:                                 # a star with one number too small
        c = random.randrange(4)
        for j in range(4):
            if j != c: a[(min(c, j), max(c, j))] = 1.0
        bad = random.choice([pr for pr in PAIRS if a[pr] == 1.0]); a[bad] = 1 - 8 * eta
        u[random.randrange(3)] = 1 - random.uniform(0, 8 * eta)
    elif kind == 2:                                 # three full pairs on a path, for example 12, 13, 24
        perm = random.sample(range(4), 4)
        for (x, y) in ((perm[0], perm[1]), (perm[1], perm[2]), (perm[2], perm[3])):
            a[(min(x, y), max(x, y))] = 1.0
        u[random.randrange(3)] = random.random()
    else:                                           # a random state
        a = {pr: random.random() for pr in PAIRS}
        u = [random.random() / 3 for _ in range(3)]
    return a, u
best_margin = None; nD = 0
for eta in (1 / 80, 1 / 400, 1 / 5000):
    for kappa in (eta, eta / 10):
        for restart in range(max(20, SAMPLES // 25)):
            a, u = start_state(eta, kappa)
            if not consistent(a, u, eta, kappa) or conclusion(a, eta): continue
            nD += 1
            value = sum(a.values()) + sum(u)
            for step in range(1500):
                scale = eta * random.choice([8, 2, 0.5, 0.1, 0.01])
                a2 = dict(a); u2 = list(u)
                for _ in range(random.randint(1, 3)):
                    if random.random() < 0.65:
                        pr = random.choice(PAIRS); a2[pr] = min(1.0, max(0.0, a2[pr] + random.uniform(-1, 1) * scale))
                    else:
                        x = random.randrange(3); u2[x] = max(0.0, u2[x] + random.uniform(-1, 1) * scale)
                v2 = sum(a2.values()) + sum(u2)
                if v2 > value and consistent(a2, u2, eta, kappa) and not conclusion(a2, eta):
                    a, u, value = a2, u2, v2
            margin = (4 - 2 * eta - value) / eta        # positive: the lemma holds for this state
            if best_margin is None or margin < best_margin: best_margin = margin
            if value >= 4 - 2 * eta:
                ok = False; print("FAILED D:", a, u, eta, kappa, value)
print(f"Test D: {nD} local searches; the largest S + F without the conclusion was 4 - 2 eta - {best_margin:.3f} eta")

# ------------------------------------------------------------------ Test E
# Three states with S + F = 4 that are neither a star nor a cross.  Each satisfies the three cap
# inequalities S + F - u_alpha <= 4 and all but one of the tools.  So the proof needs each tool.
def tools(a, u, eta, kappa):
    """Which of (T1), (T2), (T3) hold."""
    F = sum(u); g = lambda i, j: a[(min(i, j), max(i, j))]
    t1 = all(not (g(i, k) + g(j, k) >= 1 + 2 * eta and g(i, j) > kappa)
             for i, j in PAIRS for k in range(4) if k not in (i, j))
    t2 = all(not (sum(g(i, k) for i in p1 for k in p2) >= 2 + 4 * eta and F - u[idx] > kappa)
             for idx, (p1, p2) in enumerate(PAIRINGS))
    t3 = all(not (a[q2] > kappa and a[q1] + F - u[idx] >= 1 + 2 * eta)
             for idx, pq in enumerate(PAIRINGS) for (q1, q2) in (pq, pq[::-1]))
    return t1, t2, t3
eta = kappa = 1 / 80
zero = {pr: 0.0 for pr in PAIRS}
witnesses = [
    ("needs (T3)", {**zero, (0, 2): 1.0, (0, 3): 1.0, (1, 2): 1.0, (1, 3): 0.5}, [0.5, 0.0, 0.0], (True, True, False)),
    ("needs (T2)", {**zero, (0, 2): 1.0, (0, 3): 1.0, (1, 2): 1.0}, [0.0, 0.0, 1.0], (True, False, True)),
    ("needs the lemma on a full star", {**zero, (0, 1): 1.0, (0, 2): 1.0, (0, 3): 1.0}, [0.0, 1.0, 0.0], (True, True, True)),
]
for name, a, u, expected in witnesses:
    S = sum(a.values()); F = sum(u)
    caps = all(S + F - x <= 4 + eta for x in u)
    star = any(all(a[(min(c, j), max(c, j))] == 1.0 for j in range(4) if j != c) for c in range(4))
    cross = any(all(a[(min(i, k), max(i, k))] == 1.0 for i in p1 for k in p2) for (p1, p2) in PAIRINGS)
    good = (S + F == 4 and caps and tools(a, u, eta, kappa) == expected and not cross
            and star == (name == "needs the lemma on a full star"))
    if not good:
        ok = False; print("FAILED E:", name, tools(a, u, eta, kappa), caps, star, cross)
print("Test E: three states with S + F = 4 that only (T3), only (T2), or only the lemma on a full star excludes")
print("all checks passed" if ok else "A CHECK FAILED")
sys.exit(0 if ok else 1)
