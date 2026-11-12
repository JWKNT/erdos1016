# Tests, by complete enumeration on small graphs, the facts about T-joins that the note
# research/one-scale.pdf uses in the proof of the pieces lemma at a fixed girth.
#
#   1. Free regions.  Let A be a region (connected vertex set) without a vertex of T.
#      Some T-join avoids the cut of A  if and only if  every component of N - A has an even
#      number of vertices of T.  In this case the proportion of the T-joins that avoid the cut is
#      2^(comp(N-A) - |cut|), which is the value for even subgraphs (link formula).
#   2. Two regions.  For disjoint regions A, B without a vertex of T, the proportion of the
#      T-joins that avoid both cuts is 0 or 2^(links-1) * P(A) * P(B).
#   3. The ladder.  In a ladder with n rungs and T = {two ends of one rail}, every T-join is a
#      path.  So the forest proportion is 1, for every n: large pieces of girth 4 can have forest
#      proportion 1.
#
# Usage: python3 tjoin_check.py [seed]        Exit code 0 means that all tests passed.
import sys, random, itertools

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)

def components(n, edges, removed):
    comp = {}
    c = 0
    adj = {v: [] for v in range(n)}
    for (a, b) in edges:
        adj[a].append(b); adj[b].append(a)
    for s in range(n):
        if s in removed or s in comp: continue
        comp[s] = c; q = [s]
        for u in q:
            for w in adj[u]:
                if w not in removed and w not in comp:
                    comp[w] = c; q.append(w)
        c += 1
    return comp, c

def cycle_space(n, edges):
    """A basis of the cycle space as bit masks over the edges, and a spanning-tree parent map."""
    parent = {0: -1}; pedge = {}; order = [0]
    adj = {v: [] for v in range(n)}
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i)); adj[b].append((a, i))
    tree = set()
    for u in order:
        for (w, i) in adj[u]:
            if w not in parent:
                parent[w] = u; pedge[w] = i; tree.add(i); order.append(w)
    def path_mask(v):
        m = 0
        while parent[v] != -1:
            m ^= 1 << pedge[v]; v = parent[v]
        return m
    basis = []
    for i, (a, b) in enumerate(edges):
        if i not in tree:
            basis.append((1 << i) ^ path_mask(a) ^ path_mask(b))
    return basis, path_mask

def all_joins(n, edges, T):
    basis, path_mask = cycle_space(n, edges)
    j0 = 0
    for v in T: j0 ^= path_mask(v)
    joins = [j0]
    for b in basis:
        joins += [j ^ b for j in joins]
    return joins

def is_forest(n, edges, mask):
    par = list(range(n))
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for i, (a, b) in enumerate(edges):
        if mask >> i & 1:
            ra, rb = find(a), find(b)
            if ra == rb: return False
            par[ra] = rb
    return True

def random_subcubic(n):
    while True:
        deg = [0] * n; edges = set()
        for _ in range(4 * n):
            a, b = random.sample(range(n), 2)
            if deg[a] < 3 and deg[b] < 3 and (min(a, b), max(a, b)) not in edges:
                edges.add((min(a, b), max(a, b))); deg[a] += 1; deg[b] += 1
        edges = sorted(edges)
        _, c = components(n, edges, set())
        if c == 1 and len(edges) - n + 1 >= 3:
            return edges, deg

def random_region(n, edges, forbidden, size):
    adj = {v: set() for v in range(n)}
    for (a, b) in edges:
        adj[a].add(b); adj[b].add(a)
    free = [v for v in range(n) if v not in forbidden]
    if not free: return None
    A = {random.choice(free)}
    while len(A) < size:
        nb = [w for v in A for w in adj[v] if w not in A and w not in forbidden]
        if not nb: break
        A.add(random.choice(nb))
    return A

def cut_mask(edges, A):
    m = 0
    for i, (a, b) in enumerate(edges):
        if (a in A) != (b in A): m |= 1 << i
    return m

ok = True; tests1 = tests2 = 0
for trial in range(300):
    n = random.randint(8, 13)
    edges, deg = random_subcubic(n)
    beta = len(edges) - n + 1
    boundary = [v for v in range(n) if deg[v] < 3]
    if len(boundary) < 2: continue
    size = random.choice(range(0, len(boundary) + 1, 2))
    T = set(random.sample(boundary, size))
    joins = all_joins(n, edges, T)
    assert len(joins) == 2 ** beta
    regions = []
    for _ in range(6):
        A = random_region(n, edges, T, random.randint(1, 4))
        if A and len(A) < n - 1: regions.append(A)
    info = []
    for A in regions:
        comp, c = components(n, edges, A)
        even = all(sum(1 for v in T if comp.get(v) == j) % 2 == 0 for j in range(c))
        cm = cut_mask(edges, A)
        cnt = sum(1 for j in joins if j & cm == 0)
        expect = 2 ** (beta + c - bin(cm).count("1")) if even else 0
        tests1 += 1
        if cnt != expect:
            ok = False; print("FAILED fact 1", edges, T, A, cnt, expect)
        info.append((A, cm, c, cnt))
    for (A, cma, ca, na), (B, cmb, cb, nb) in itertools.combinations(info, 2):
        if A & B: continue
        comp, c = components(n, edges, A | B)
        direct = sum(1 for (a, b) in edges if (a in A and b in B) or (a in B and b in A))
        touchA = {comp[w] for (a, b) in edges for (v, w) in ((a, b), (b, a)) if v in A and w not in A and w not in B}
        touchB = {comp[w] for (a, b) in edges for (v, w) in ((a, b), (b, a)) if v in B and w not in A and w not in B}
        links = direct + len(touchA & touchB)
        cnt = sum(1 for j in joins if j & (cma | cmb) == 0)
        # value for even subgraphs: 2^(links-1) P(A) P(B), as a count out of 2^beta
        pa = 2 ** (ca - bin(cma).count("1")); pb = 2 ** (cb - bin(cmb).count("1"))
        expect = 2 ** beta * 2 ** (links - 1) * pa * pb
        tests2 += 1
        if cnt not in (0, expect):
            ok = False; print("FAILED fact 2", edges, T, A, B, cnt, expect)
print(f"fact 1: {tests1} regions tested; fact 2: {tests2} pairs of regions tested")

for rungs in range(3, 11):
    # rails u_0..u_{n-1} = 0..n-1 and v_0..v_{n-1} = n..2n-1
    n = rungs
    edges = [(i, i + 1) for i in range(n - 1)] + [(n + i, n + i + 1) for i in range(n - 1)] + [(i, n + i) for i in range(n)]
    joins = all_joins(2 * n, edges, {0, n - 1})
    forests = sum(1 for j in joins if is_forest(2 * n, edges, j))
    if forests != len(joins):
        ok = False; print("FAILED fact 3", rungs, forests, len(joins))
print("fact 3: ladders with 3 to 10 rungs tested")
print("all checks passed" if ok else "A CHECK FAILED")
sys.exit(0 if ok else 1)
