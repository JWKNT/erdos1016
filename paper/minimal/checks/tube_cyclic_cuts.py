# A necklace over the Heawood graph: M rings of length 14, seven edges between consecutive rings.
# The script checks, by complete enumeration:
#   1. the graph is cubic and has girth 6;
#   2. it has no cyclic cut of size at most four (every set of at most four edges);
#   3. two rings that are not consecutive have exactly two links.
# Usage: python3 tube_cyclic_cuts.py [M]      (default M = 4: 56 vertices, 84 edges)
import sys, itertools

M = int(sys.argv[1]) if len(sys.argv) > 1 else 4
n = 14 * M
vid = lambda v, i: (v % 14) + 14 * (i % M)
E = []
for i in range(M):
    for v in range(14):
        E.append((vid(v, i), vid(v + 1, i)))                 # ring edges (a Hamiltonian cycle of Heawood)
    for v in range(0, 14, 2):
        E.append((vid(v, i), vid(v + 5, i + 1)))             # the chords of Heawood, lifted to the next ring
m = len(E)
deg = [0] * n
for a, b in E:
    deg[a] += 1; deg[b] += 1
assert all(d == 3 for d in deg), "not cubic"
adj = [[] for _ in range(n)]
for e, (a, b) in enumerate(E):
    adj[a].append((b, e)); adj[b].append((a, e))

def girth():
    best = n + 1
    for s in range(n):
        dist = {s: 0}; par = {s: -1}; q = [s]
        for u in q:
            for (w, e) in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; par[w] = e; q.append(w)
                elif par[u] != e:
                    best = min(best, dist[u] + dist[w] + 1)
    return best

def components(removed_edges, removed_vertices=()):
    rem = set(removed_edges); rv = set(removed_vertices)
    comp = [-1] * n; c = 0
    for s in range(n):
        if comp[s] != -1 or s in rv: continue
        comp[s] = c; q = [s]
        for u in q:
            for (w, e) in adj[u]:
                if e not in rem and w not in rv and comp[w] == -1:
                    comp[w] = c; q.append(w)
        c += 1
    return comp, c

g = girth()
print(f"M={M}: {n} vertices, {m} edges, cubic, girth {g}")

# cyclic cuts: after the deletion of the edge set F, at least two components contain a cycle
bad = 0; cuts = 0
for k in range(1, 5):
    for F in itertools.combinations(range(m), k):
        comp, c = components(F)
        if c < 2: continue
        cuts += 1
        nv = [0] * c; ne = [0] * c
        for v in range(n): nv[comp[v]] += 1
        Fs = set(F)
        for e, (a, b) in enumerate(E):
            if e not in Fs: ne[comp[a]] += 1
        cyclic = sum(1 for j in range(c) if ne[j] >= nv[j])
        if cyclic >= 2:
            bad += 1
print(f"edge sets of size at most 4 that disconnect the graph: {cuts}; with two cyclic sides: {bad}")

# links between ring 0 and ring 2
ring = lambda i: [vid(v, i) for v in range(14)]
A, B = set(ring(0)), set(ring(2 % M))
comp, c = components((), A | B)
joinA = set(); joinB = set(); direct = 0
for (a, b) in E:
    if (a in A and b in B) or (a in B and b in A): direct += 1
    for x, y in ((a, b), (b, a)):
        if x in A and y not in A and y not in B: joinA.add(comp[y])
        if x in B and y not in A and y not in B: joinB.add(comp[y])
links = direct + len(joinA & joinB)
print(f"links between ring 0 and ring 2: {links}")
ok = (g == 6 and bad == 0 and (M < 4 or links == 2))
print("all checks passed" if ok else "A CHECK FAILED")
sys.exit(0 if ok else 1)
