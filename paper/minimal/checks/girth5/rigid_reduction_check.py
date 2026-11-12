# Tests, on small graphs, the reduction that the note research/girth-five.pdf uses for rigid pairs.
#
# A pair (M, U) is RIGID if M is a connected subcubic graph, U is an even set of boundary vertices
# (vertices of degree less than three), and every U-join of M is a forest.
#
# Fact 1 (reduction).  Let (M, U) be rigid, and let B be a connected set of vertices without a
#   vertex of U.  Count the vertices of U in each component of M - B.
#   (a) If all counts are even, then M[B] has no cycle.
#   (b) If exactly two components K1, K2 have an odd count, then for all x1 != x2 in B with
#       xi adjacent to Ki, every {x1,x2}-join of M[B] is a path (the pair is full).
# Fact 2 (full pairs at girth five).  If M has girth at least five and a full pair x, y of
#   vertices of degree at most two, then |V(M)| < 15 d(M), where d(M) is the sum of 3 - deg(v).
#   The script tests this for the graphs M[B] of Fact 1(b) and for whole graphs.
#
# Usage: python3 rigid_reduction_check.py [seed]      Exit code 0 means that all tests passed.
import sys, random, itertools

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)

class Graph:
    def __init__(self, n, edges):
        self.n = n; self.edges = list(edges)
        self.adj = [[] for _ in range(n)]
        for i, (a, b) in enumerate(self.edges):
            self.adj[a].append((b, i)); self.adj[b].append((a, i))
        self.deg = [len(x) for x in self.adj]
    def components(self, removed=frozenset()):
        comp = {}; c = 0
        for s in range(self.n):
            if s in removed or s in comp: continue
            comp[s] = c; q = [s]
            for u in q:
                for (w, _) in self.adj[u]:
                    if w not in removed and w not in comp:
                        comp[w] = c; q.append(w)
            c += 1
        return comp, c
    def girth(self):
        best = 10 ** 9
        for s in range(self.n):
            dist = {s: 0}; par = {s: -1}; q = [s]
            for u in q:
                for (w, e) in self.adj[u]:
                    if w not in dist:
                        dist[w] = dist[u] + 1; par[w] = e; q.append(w)
                    elif par[u] != e:
                        best = min(best, dist[u] + dist[w] + 1)
        return best
    def induced(self, vs):
        idx = {v: i for i, v in enumerate(sorted(vs))}
        return Graph(len(idx), [(idx[a], idx[b]) for (a, b) in self.edges if a in idx and b in idx]), idx
    def joins(self, T):
        """All T-joins as bit masks (the graph must be connected)."""
        parent = {0: -1}; pedge = {}; order = [0]; tree = set()
        for u in order:
            for (w, i) in self.adj[u]:
                if w not in parent:
                    parent[w] = u; pedge[w] = i; tree.add(i); order.append(w)
        def path(v):
            m = 0
            while parent[v] != -1:
                m ^= 1 << pedge[v]; v = parent[v]
            return m
        j0 = 0
        for v in T: j0 ^= path(v)
        out = [j0]
        for i, (a, b) in enumerate(self.edges):
            if i not in tree:
                c = (1 << i) ^ path(a) ^ path(b)
                out += [j ^ c for j in out]
        return out
    def is_forest(self, mask):
        par = list(range(self.n))
        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]; x = par[x]
            return x
        for i, (a, b) in enumerate(self.edges):
            if mask >> i & 1:
                ra, rb = find(a), find(b)
                if ra == rb: return False
                par[ra] = rb
        return True
    def rigid(self, T):
        return all(self.is_forest(j) for j in self.joins(T))
    def deficit(self):
        return sum(3 - d for d in self.deg)

# ---------------------------------------------------------------- test graphs
def ladder(m):
    return Graph(2 * m, [(i, i + 1) for i in range(m - 1)] + [(m + i, m + i + 1) for i in range(m - 1)] + [(i, m + i) for i in range(m)])
def necklace(lcf, M):
    n = len(lcf); vid = lambda v, i: (v % n) + n * i; e = []
    for i in range(M):
        for v in range(n): e.append((vid(v, i), vid(v + 1, i)))
        if i < M - 1:
            for v in range(0, n, 2): e.append((vid(v, i), vid(v + lcf[v], i + 1)))
    return Graph(n * M, e)
def gp_strip(m, step):
    return Graph(2 * m, [(i, i + 1) for i in range(m - 1)] + [(i, m + i) for i in range(m)] + [(m + i, m + i + step) for i in range(m - step)])
def random_subcubic(n, mingirth):
    while True:
        deg = [0] * n; edges = set()
        for _ in range(5 * n):
            a, b = random.sample(range(n), 2)
            if deg[a] < 3 and deg[b] < 3 and (min(a, b), max(a, b)) not in edges:
                g = Graph(n, sorted(edges | {(min(a, b), max(a, b))}))
                if g.girth() >= mingirth:
                    edges.add((min(a, b), max(a, b))); deg[a] += 1; deg[b] += 1
        g = Graph(n, sorted(edges))
        if g.components()[1] == 1 and len(edges) - n + 1 >= 2:
            return g

tests = [("ladder 5", ladder(5)), ("ladder 7", ladder(7)), ("rings of 6, 2 rings", necklace([1, -1] * 3, 2)),
         ("rings of 6, 3 rings", necklace([1, -1] * 3, 3)), ("rings of 8, 2 rings", necklace([1, -1] * 4, 2)),
         ("GP(.,2) segment 6", gp_strip(6, 2)), ("GP(.,3) segment 8", gp_strip(8, 3))]
for i in range(40):
    tests.append((f"random girth 3, #{i}", random_subcubic(random.randint(8, 11), 3)))
for i in range(40):
    tests.append((f"random girth 5, #{i}", random_subcubic(random.randint(10, 13), 5)))

ok = True; n_rigid = n_sets = n_even = n_two = n_pairs = n_full5 = 0; worst = 0.0
for name, M in tests:
    boundary = [v for v in range(M.n) if M.deg[v] < 3]
    if len(boundary) > 10: boundary = boundary[:10]
    girth = M.girth()
    for size in range(2, len(boundary) + 1, 2):
        for U in itertools.combinations(boundary, size):
            if M.rigid(U):
                n_rigid += 1
                Uset = set(U)
                free = [v for v in range(M.n) if v not in Uset]
                # connected sets B without a vertex of U: grown at random
                seenB = set()
                for _ in range(60):
                    B = {random.choice(free)}
                    target = random.randint(2, max(2, M.n - size - 1))
                    while len(B) < target:
                        nb = [w for v in B for (w, _) in M.adj[v] if w not in B and w not in Uset]
                        if not nb: break
                        B.add(random.choice(nb))
                    fb = frozenset(B)
                    if fb in seenB or len(B) == M.n: continue
                    seenB.add(fb); n_sets += 1
                    comp, c = M.components(fb)
                    counts = [0] * c
                    for u in U: counts[comp[u]] += 1
                    odd = [j for j in range(c) if counts[j] % 2 == 1]
                    sub, idx = M.induced(fb)
                    if not odd:
                        n_even += 1
                        if len(sub.edges) - sub.n + 1 != 0:
                            ok = False; print("FAILED fact 1(a):", name, U, sorted(B))
                    elif len(odd) == 2:
                        n_two += 1
                        X = [[v for v in fb if any(comp.get(w) == j for (w, _) in M.adj[v])] for j in odd]
                        for x1 in X[0]:
                            for x2 in X[1]:
                                if x1 == x2: continue
                                n_pairs += 1
                                if not sub.rigid((idx[x1], idx[x2])):
                                    ok = False; print("FAILED fact 1(b):", name, U, sorted(B), x1, x2)
                                elif girth >= 5:
                                    n_full5 += 1
                                    worst = max(worst, sub.n / sub.deficit())
                                    if sub.n >= 15 * sub.deficit():
                                        ok = False; print("FAILED fact 2:", name, U, sorted(B))
                if girth >= 5 and size == 2 and M.n >= 15 * M.deficit():
                    ok = False; print("FAILED fact 2 for the whole graph:", name, U)
print(f"rigid pairs found: {n_rigid}; sets B tested: {n_sets} (all counts even: {n_even}, two odd counts: {n_two})")
print(f"pairs x1,x2 tested in fact 1(b): {n_pairs}; full pairs at girth five: {n_full5}, largest |V|/d among them: {worst:.2f}")
print("all checks passed" if ok else "A CHECK FAILED")
sys.exit(0 if ok else 1)
