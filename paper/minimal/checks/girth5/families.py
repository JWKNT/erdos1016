# Forest proportions in families of subcubic graphs of girth at least five.
#
# For each graph the script prints the largest forest proportion over all nonempty even sets T of
# boundary vertices (complete enumeration by the C program fpmax in this folder).  The question is:
# does a large piece with few boundary vertices have a set T with forest proportion at least 3/5?
# The pieces theorem at girth five says no; these runs test small cases only.
#
# Usage: python3 families.py [quick]
import subprocess, sys, os, random, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
FPMAX = os.path.join(HERE, "fpmax")
if not os.path.exists(FPMAX):          # compile the C program on first use
    subprocess.run(["cc", "-O2", "-o", FPMAX, os.path.join(HERE, "fpmax.c")], check=True)
QUICK = len(sys.argv) > 1 and sys.argv[1] == "quick"

def girth(n, edges):
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i)); adj[b].append((a, i))
    best = 10 ** 9
    for s in range(n):
        dist = {s: 0}; par = {s: -1}; q = [s]
        for u in q:
            for (w, e) in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; par[w] = e; q.append(w)
                elif par[u] != e:
                    best = min(best, dist[u] + dist[w] + 1)
    return best

def connected(n, edges):
    adj = [[] for _ in range(n)]
    for (a, b) in edges:
        adj[a].append(b); adj[b].append(a)
    seen = {0}; q = [0]
    for u in q:
        for w in adj[u]:
            if w not in seen:
                seen.add(w); q.append(w)
    return len(seen) == n

def run(n, edges, maxT=None):
    text = f"{n} {len(edges)}\n" + "".join(f"{a} {b}\n" for (a, b) in edges)
    args = [FPMAX] + ([str(maxT)] if maxT else [])
    out = subprocess.run(args, input=text, capture_output=True, text=True)
    if out.returncode != 0:
        return None
    f = out.stdout.split()
    n_, m_, beta, k, best, tsz, nT, good, rigid = map(int, f[:9])
    return dict(n=n_, m=m_, beta=beta, k=k, best=best, tsize=tsz, nT=nT, good=good, rigid=rigid,
                fp=best / 2 ** beta)

def show(name, n, edges, maxT=None):
    r = run(n, edges, maxT)
    if r is None:
        print(f"{name:34s} n={n:3d}  (not computed)"); return None
    g = girth(n, edges)
    flag = "  >= 3/5" if r["fp"] >= 0.6 else ""
    print(f"{name:34s} n={n:3d} girth={g if g < 10**9 else '-':>2} k={r['k']:2d} rank={r['beta']:2d} "
          f"max fp={r['fp']:.4f} (|T|={r['tsize']}) sets with fp>=3/5: {r['good']:4d} of {r['nT']:5d}, rigid: {r['rigid']}{flag}")
    r["girth"] = g
    return r

def relabel(vertices, edges):
    idx = {v: i for i, v in enumerate(sorted(vertices))}
    return len(idx), [(idx[a], idx[b]) for (a, b) in edges]

# ---------------------------------------------------------------- the families
def ladder(m):                       # girth 4: the control
    return 2 * m, [(i, i + 1) for i in range(m - 1)] + [(m + i, m + i + 1) for i in range(m - 1)] + [(i, m + i) for i in range(m)]

def gp_strip(m, step):               # a segment of the generalised Petersen graph GP(.,step)
    e = [(i, i + 1) for i in range(m - 1)] + [(i, m + i) for i in range(m)] + [(m + i, m + i + step) for i in range(m - step)]
    return 2 * m, e

def necklace(lcf, M):                # M rings over a cubic Hamiltonian graph in LCF notation, not closed
    n = len(lcf)
    vid = lambda v, i: (v % n) + n * i
    e = []
    for i in range(M):
        for v in range(n):
            e.append((vid(v, i), vid(v + 1, i)))
        if i < M - 1:
            for v in range(0, n, 2):
                e.append((vid(v, i), vid(v + lcf[v], i + 1)))
    return n * M, e

HEAWOOD = [5, -5] * 7
ZIGZAG5 = [1, -1] * 5                # rings of length 10 with five edges between consecutive rings
ZIGZAG4 = [1, -1] * 4
ZIGZAG3 = [1, -1] * 3

def pentagon_necklace(M):
    """Rings of length five; two and three edges between consecutive rings, in turn.  Girth five."""
    best = None
    for perm in itertools.permutations(range(3)):
        for swap in (0, 1):
            e = []
            for i in range(M):
                for j in range(5):
                    e.append((5 * i + j, 5 * i + (j + 1) % 5))
                if i < M - 1:
                    if i % 2 == 0:       # three edges: positions 0,2,4 of ring i to positions 0,2,4 of ring i+1
                        for a in range(3):
                            e.append((5 * i + 2 * a, 5 * (i + 1) + 2 * perm[a]))
                    else:                # two edges: positions 1,3 of ring i to positions 1,3 of ring i+1
                        e.append((5 * i + 1, 5 * (i + 1) + (3 if swap else 1)))
                        e.append((5 * i + 3, 5 * (i + 1) + (1 if swap else 3)))
            g = girth(5 * M, e)
            if best is None or g > best[0]:
                best = (g, e)
    assert best is not None
    return 5 * M, best[1]

def random_cubic(n, g, rng, tries=20000):
    for _ in range(tries):
        pts = [v for v in range(n) for _ in range(3)]
        rng.shuffle(pts)
        e = set(); ok = True
        for i in range(0, len(pts), 2):
            a, b = pts[i], pts[i + 1]
            if a == b or (min(a, b), max(a, b)) in e:
                ok = False; break
            e.add((min(a, b), max(a, b)))
        if ok and connected(n, sorted(e)) and girth(n, sorted(e)) >= g:
            return sorted(e)
    return None

def minus(n, edges, removed):
    keep = [v for v in range(n) if v not in removed]
    e = [(a, b) for (a, b) in edges if a not in removed and b not in removed]
    return relabel(keep, e)

def lcf_graph(lcf):
    n = len(lcf); e = set()
    for v in range(n):
        for w in ((v + 1) % n, (v + lcf[v]) % n):
            e.add((min(v, w), max(v, w)))
    return n, sorted(e)

print("Control at girth four: ladders (the forest proportion stays 1)")
for m in (4, 8, 12, 16):
    show(f"ladder, {m} rungs", *ladder(m))

print("\nSegments of generalised Petersen graphs, three edges at each end")
for m in ((6, 8, 10, 12, 14) if QUICK else (6, 8, 10, 12, 14, 16, 18, 20, 22)):
    show(f"GP(.,2) segment, {m} spokes", *gp_strip(m, 2))
for m in ((8, 10, 12) if QUICK else (8, 10, 12, 14, 16, 18, 20)):
    show(f"GP(.,3) segment, {m} spokes", *gp_strip(m, 3))

print("\nNecklaces of pentagons with two and three edges in turn (girth five, cuts of size four)")
for M in ((2, 3, 4) if QUICK else (2, 3, 4, 5, 6, 7, 8)):
    show(f"pentagon necklace, {M} rings", *pentagon_necklace(M))

print("\nTubes: rings with k/2 edges between consecutive rings")
for M in ((2, 3) if QUICK else (2, 3, 4, 5, 6)):
    show(f"rings of length 6, {M} rings", *necklace(ZIGZAG3, M))
for M in ((2, 3) if QUICK else (2, 3, 4, 5)):
    show(f"rings of length 8, {M} rings", *necklace(ZIGZAG4, M))
for M in ((2,) if QUICK else (2, 3, 4)):
    show(f"rings of length 10, {M} rings", *necklace(ZIGZAG5, M))
for M in ((2,) if QUICK else (2, 3)):
    show(f"Heawood necklace, {M} rings", *necklace(HEAWOOD, M), maxT=(None if M == 2 else 4))

print("\nKnown cubic graphs of girth at least five, minus a vertex or minus the two ends of an edge")
def petersen():
    e = [(i, (i + 1) % 5) for i in range(5)] + [(i, 5 + i) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    return 10, e
def dodecahedron():
    return lcf_graph([10, 7, 4, -4, -7, 10, -4, 7, -7, 4] * 2)
graphs = [("Petersen", petersen()), ("Heawood", lcf_graph(HEAWOOD)), ("Pappus", lcf_graph([5, 7, -7, 7, -7, -5] * 3)),
          ("dodecahedron", dodecahedron()), ("Desargues", lcf_graph([5, -5, 9, -9] * 5)),
          ("McGee", lcf_graph([12, 7, -7] * 8)), ("Tutte-Coxeter", lcf_graph([-13, -9, 7, -7, 9, 13] * 5))]
for name, (n, e) in graphs:
    g = girth(n, e)
    if g < 5:
        print(f"{name}: girth {g}, skipped"); continue
    show(f"{name} minus a vertex", *minus(n, e, {0}))
    a, b = e[0]
    show(f"{name} minus an edge", *minus(n, e, {a, b}))

print("\nRandom cubic graphs of girth at least five, minus a path of two or three vertices")
rng = random.Random(5)
for n in ((14, 18) if QUICK else (14, 18, 22, 26, 30, 34)):
    for rep in range(2 if QUICK else 4):
        e = random_cubic(n, 5, rng)
        if e is None:
            print(f"no random cubic graph of girth five on {n} vertices found"); continue
        adj = {v: [] for v in range(n)}
        for (a, b) in e:
            adj[a].append(b); adj[b].append(a)
        u = rng.randrange(n); v = adj[u][0]; w = [x for x in adj[v] if x != u][0]
        show(f"random, {n} vertices, minus 2", *minus(n, e, {u, v}))
        show(f"random, {n} vertices, minus 3", *minus(n, e, {u, v, w}))
