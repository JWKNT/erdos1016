# A random search for large rigid pairs.
#
# A pair (M, T) is rigid if every T-join of M is a forest.  Rigid pairs are closed under the
# deletion of an edge and of a vertex of degree one (with the obvious change of T).  So every
# rigid pair arises from a single edge by these two steps, through rigid pairs only:
#   A: add a new vertex of degree one at a boundary vertex;
#   B: add an edge between two boundary vertices.
# The search applies random steps and keeps a graph if it has at most k boundary vertices, girth
# at least g, and some nonempty even set T that is rigid.  It reports the largest rank that it
# found.  The search space is small: every graph on the way has at most k boundary vertices.
#
# At girth four the search finds ladders, and the rank grows without bound.
# At girth five the note proves that the size is bounded in terms of the deficit.
#
# Usage: python3 rigid_search.py [steps] [seed]
import subprocess, sys, os, random

HERE = os.path.dirname(os.path.abspath(__file__))
FPMAX = os.path.join(HERE, "fpmax")
if not os.path.exists(FPMAX):          # compile the C program on first use
    subprocess.run(["cc", "-O2", "-o", FPMAX, os.path.join(HERE, "fpmax.c")], check=True)
STEPS = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
SLACK = 0

def rigid_sets(n, edges):
    text = f"{n} {len(edges)}\n" + "".join(f"{a} {b}\n" for (a, b) in edges)
    out = subprocess.run([FPMAX], input=text, capture_output=True, text=True)
    if out.returncode != 0:
        return 0
    return int(out.stdout.split()[8])

def distances(n, adj, s):
    dist = {s: 0}; q = [s]
    for u in q:
        for w in adj[u]:
            if w not in dist:
                dist[w] = dist[u] + 1; q.append(w)
    return dist

def search(g, k, steps, cap):
    best = (0, 2, [(0, 1)])
    n, edges = 2, [(0, 1)]
    stuck = 0
    for _ in range(steps):
        adj = [[] for _ in range(n)]
        for (a, b) in edges:
            adj[a].append(b); adj[b].append(a)
        boundary = [v for v in range(n) if len(adj[v]) < 3]
        if rng.random() < 0.5:
            u = rng.choice(boundary)
            cand = (n + 1, edges + [(u, n)])
        else:
            if len(boundary) < 2:
                continue
            u, v = rng.sample(boundary, 2)
            if distances(n, adj, u).get(v, 10 ** 9) < g - 1:
                continue
            cand = (n, edges + [(min(u, v), max(u, v))])
        cn, ce = cand
        deg = [0] * cn
        for (a, b) in ce:
            deg[a] += 1; deg[b] += 1
        nb = sum(1 for d in deg if d < 3)
        if nb > k + SLACK or len(ce) - cn + 1 > cap:
            stuck += 1
        elif rigid_sets(cn, ce) > 0:
            n, edges = cn, ce; stuck = 0
            rank = len(edges) - n + 1
            if nb <= k and rank > best[0]:
                best = (rank, n, list(edges))
        else:
            stuck += 1
        if stuck > 60:                      # restart
            n, edges, stuck = 2, [(0, 1)], 0
    return best

print("largest rank of a rigid pair found by the search (rank capped at 14)")
for g in (4, 5):
    for k in (4, 5, 6):
        rank, size, _ = search(g, k, STEPS, 14)
        print(f"girth >= {g}, at most {k} boundary vertices: rank {rank:2d}, {size:2d} vertices")
