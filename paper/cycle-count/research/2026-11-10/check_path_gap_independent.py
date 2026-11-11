#!/usr/bin/env python3
"""Independent finite audit of capped-ladder saturation and subdivisions."""
import itertools
import json
from pathlib import Path


def count_paths(n, edges, start, end):
    adjacency = [[] for _ in range(n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)

    def visit(v, seen):
        if v == end:
            return 1
        return sum(visit(w, seen | (1 << w))
                   for w in adjacency[v] if not seen & (1 << w))

    return visit(start, 1 << start)


def capped_permutation(permutation):
    k = len(permutation)
    a, c = 2*k, 2*k+1
    if k == 0:
        return 2, [(a, c), (a, c)], a, c
    edges = [(a, 0), (a, k), (k-1, c), (2*k-1, c)]
    edges += [(i, i+1) for i in range(k-1)]
    edges += [(k+i, k+i+1) for i in range(k-1)]
    edges += [(i, k+j) for i, j in enumerate(permutation)]
    return 2*k+2, edges, a, c


def is_block_permutation(permutation):
    i = 0
    while i < len(permutation):
        if permutation[i] == i:
            i += 1
        elif (i+1 < len(permutation)
              and permutation[i] == i+1 and permutation[i+1] == i):
            i += 2
        else:
            return False
    return True


def main():
    rows = []
    for k in range(7):
        permutations = saturated = subdivisions = 0
        maximum_nonfull = 0
        for permutation in itertools.permutations(range(k)):
            n, edges, a, c = capped_permutation(permutation)
            full = 1 << (k+1)
            value = count_paths(n, edges, a, c)
            assert (value == full) == is_block_permutation(permutation)
            permutations += 1
            if value != full:
                continue
            saturated += 1
            for index, (u, v) in enumerate(edges):
                divided = edges[:index] + edges[index+1:] + [(u, n), (n, v)]
                value = count_paths(n+1, divided, n, c)
                assert value == full or 8*value <= 7*full
                if value != full:
                    maximum_nonfull = max(maximum_nonfull, value/full)
                subdivisions += 1
        rows.append(dict(positions=k, permutations=permutations,
                         saturated=saturated, subdivisions=subdivisions,
                         maximum_nonfull=maximum_nonfull))
    result = dict(method="Independent vertex DFS; all permutations through six positions",
                  rows=rows)
    output = Path(__file__).with_name("path-gap-independent-checks.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
