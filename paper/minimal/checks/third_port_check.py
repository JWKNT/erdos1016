# Check of the new proof of the third-port lemma on all capped ladders of small weight.
# A capped ladder: caps s,t; tiles 'S' (square, weight 2) or 'R' (single rung, weight 1).
import itertools, sys
from fractions import Fraction

def ladder(tiles):
    edges = []; n = 0
    s = n; n += 1
    pairs = []          # (left pair, right pair) of each tile
    kind = []           # tag of each edge: ('cap_s',), ('tile', i), ('iface', i), ('cap_t',)
    for i, tl in enumerate(tiles):
        if tl == 'R':
            a, b = n, n + 1; n += 2
            edges.append((a, b)); kind.append(('tile', i))
            pairs.append(((a, b), (a, b)))
        else:
            a, b, c, d = n, n + 1, n + 2, n + 3; n += 4
            for x in (a, b):
                for y in (c, d):
                    edges.append((x, y)); kind.append(('tile', i))
            pairs.append(((a, b), (c, d)))
    t = n; n += 1
    for x in pairs[0][0]:
        edges.append((s, x)); kind.append(('cap_s',))
    for i in range(len(tiles) - 1):
        r, l = pairs[i][1], pairs[i + 1][0]
        edges.append((r[0], l[0])); kind.append(('iface', i))
        edges.append((r[1], l[1])); kind.append(('iface', i))
    for x in pairs[-1][1]:
        edges.append((x, t)); kind.append(('cap_t',))
    return n, edges, kind, s, t

def count_paths(n, edges, a, b):
    adj = [[] for _ in range(n)]
    for (x, y) in edges:
        adj[x].append(y); adj[y].append(x)
    seen = [False] * n
    def dfs(u):
        if u == b: return 1
        seen[u] = True; tot = 0
        for w in adj[u]:
            if not seen[w]: tot += dfs(w)
        seen[u] = False
        return tot
    return dfs(a)

bad = 0; cases = 0; full = 0; worst = Fraction(0)
maxw = int(sys.argv[1]) if len(sys.argv) > 1 else 7
for m in range(1, maxw + 1):
    for tiles in itertools.product('RS', repeat=m):
        W = sum(1 if x == 'R' else 2 for x in tiles)
        if W > maxw: continue
        n, edges, kind, s, t = ladder(tiles)
        h = len(edges) - n + 1
        assert h == W + 1
        assert count_paths(n, edges, s, t) == 2 ** h          # the pair of caps is full
        for idx, (x, y) in enumerate(edges):
            v = n
            e2 = edges[:idx] + edges[idx + 1:] + [(x, v), (v, y)]
            P = count_paths(n + 1, e2, v, t)
            cases += 1
            k = kind[idx]
            predicted_full = (k == ('cap_s',)) or (k == ('tile', 0) and tiles[0] == 'R')
            if P == 2 ** h:
                full += 1
                if not predicted_full: bad += 1; print('unexpected full', tiles, k)
            else:
                if predicted_full: bad += 1; print('unexpected not full', tiles, k)
                ratio = Fraction(P, 2 ** h)
                worst = max(worst, ratio)
                if ratio > Fraction(7, 8): bad += 1; print('ratio above 7/8', tiles, k, ratio)
                # the case "a tile lies before e": bound 7/8 for a first square, 3/4 for a first rung
                before = (k[0] == 'iface') or (k[0] == 'tile' and k[1] >= 1) or k == ('cap_t',)
                if before and tiles[0] == 'R' and ratio > Fraction(3, 4):
                    bad += 1; print('ratio above 3/4 after a first rung', tiles, k, ratio)
print(f'ladders up to weight {maxw}: {cases} cases, {full} full, largest ratio of a pair that is not full: {worst}, exceptions: {bad}')
sys.exit(1 if bad else 0)
