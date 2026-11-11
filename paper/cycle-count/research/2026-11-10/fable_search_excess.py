"""Local search for graphs with many terminal paths and a short terminal path (Fable 5.2).

For a rank b and a length l, the script looks for a connected simple graph of
rank b that contains a u-v path of length l and has as many u-v paths as it can
find. It prints the best excess  P_uv - 2^(b-1)  for each pair (b, l), next to
2^((b+l)/2), the scale in Conjecture A of fable-notes.md.

The values are lower bounds for the true maxima. The search is random, with a
fixed seed. It is not exhaustive.
The script writes the witnesses to fable-search-excess-results.json.
Run:  python3 fable_search_excess.py [max_rank] [steps] [seed]
The table in fable-notes.md comes from:  python3 fable_search_excess.py 7 6000 1016
"""
import json
import math
import random
import sys


def count_paths(adj, s, t, n):
    seen = [False] * n

    def go(x):
        if x == t:
            return 1
        seen[x] = True
        total = 0
        for y in adj[x]:
            if not seen[y]:
                total += go(y)
        seen[x] = False
        return total
    return go(s)


def connected(adj, n):
    seen = {0}
    stack = [0]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == n


def search(b, l, n, rng, steps):
    """Vertices 0 = u, 1 = v; the path u, 2, 3, ..., l, v is always present."""
    chain = [0] + list(range(2, l + 1)) + [1]
    fixed = {(min(a, c), max(a, c)) for a, c in zip(chain, chain[1:])}
    m = b + n - 1
    pairs = [(a, c) for a in range(n) for c in range(a + 1, n) if (a, c) not in fixed]
    if m - len(fixed) > len(pairs) or m < len(fixed):
        return -1, None

    def adjacency(edges):
        adj = [[] for _ in range(n)]
        for a, c in edges:
            adj[a].append(c)
            adj[c].append(a)
        return adj
    best, best_edges = -1, None
    for _ in range(6):
        while True:
            extra = set(rng.sample(pairs, m - len(fixed)))
            adj = adjacency(fixed | extra)
            if connected(adj, n):
                break
        cur = count_paths(adj, 0, 1, n)
        temp = 2.0
        for _ in range(steps):
            out = rng.choice(sorted(extra))
            new = rng.choice(pairs)
            if new in extra:
                continue
            cand = (extra - {out}) | {new}
            adj = adjacency(fixed | cand)
            if not connected(adj, n):
                continue
            val = count_paths(adj, 0, 1, n)
            if val >= cur or rng.random() < math.exp((val - cur) / temp):
                extra, cur = cand, val
                if cur > best:
                    best, best_edges = cur, sorted(fixed | extra)
            temp = max(0.05, temp * 0.9995)
    return best, best_edges


if __name__ == "__main__":
    max_rank = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1016)
    results = {}
    for b in range(2, max_rank + 1):
        for l in range(2, b + 1):
            best, witness = -1, None
            for n in range(max(l + 1, 4), min(2 * b + 2, 13) + 1):
                val, edges = search(b, l, n, rng, steps=steps)
                if val > best:
                    best, witness = val, edges
            excess = best - 2 ** (b - 1)
            scale = 2 ** ((b + l) / 2)
            results[f"{b},{l}"] = {"paths": best, "excess": excess, "edges": witness}
            print(f"b = {b}, l = {l}: best P = {best}, excess = {excess}, "
                  f"2^((b+l)/2) = {scale:.1f}, ratio = {excess / scale:.3f}")
    with open("fable-search-excess-results.json", "w") as fh:
        json.dump(results, fh, indent=1)
