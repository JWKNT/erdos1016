#!/usr/bin/env python3
"""Exhaust all local width-two cubic strips used in the short-cycle lemma."""
import collections
import itertools
import json
from pathlib import Path


def shortest_cycle(edges):
    adjacency = [[] for _ in range(8)]
    multiplicity = collections.Counter(tuple(sorted(edge)) for edge in edges)
    if any(count >= 2 for count in multiplicity.values()):
        return 2
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    best = 9

    def visit(start, at, path):
        nonlocal best
        for nxt in adjacency[at]:
            if nxt == start and len(path) >= 3:
                best = min(best, len(path))
            elif nxt not in path and len(path) < min(best, 4):
                visit(start, nxt, path+(nxt,))

    for start in range(8):
        visit(start, start, (start,))
    return best


def main():
    matrices = []
    for matrix in itertools.product(range(3), repeat=4):
        rows = (matrix[0]+matrix[1], matrix[2]+matrix[3])
        cols = (matrix[0]+matrix[2], matrix[1]+matrix[3])
        if all(1 <= value <= 2 for value in rows+cols):
            matrices.append((matrix, rows, cols))
    stats = collections.Counter()
    cut_patterns = collections.Counter()
    for cuts in itertools.product(matrices, repeat=3):
        for rung2, rung3 in itertools.product(range(2), repeat=2):
            if any(cuts[0][2][v]+cuts[1][1][v]+rung2 != 3 for v in range(2)):
                continue
            if any(cuts[1][2][v]+cuts[2][1][v]+rung3 != 3 for v in range(2)):
                continue
            edges = []
            for layer, (matrix, _, _) in enumerate(cuts):
                for u, v in itertools.product(range(2), repeat=2):
                    edges.extend([(2*layer+u, 2*layer+2+v)]*matrix[2*u+v])
            if rung2:
                edges.append((2, 3))
            if rung3:
                edges.append((4, 5))
            length = shortest_cycle(edges)
            assert length <= 4
            stats[f"shortest_cycle_{length}"] += 1
            cut_patterns["-".join(str(sum(cut[0])) for cut in cuts)] += 1
    result = dict(status="all exact local strips contain a cycle of length at most four",
                  cut_matrices=len(matrices), total_strips=sum(stats.values()),
                  shortest_cycles=dict(stats), cut_size_patterns=dict(cut_patterns),
                  scope="All edge multiplicities 0,1,2; exact cubic degrees at both middle layers; outer incidences admit predecessors and successors.")
    Path(__file__).with_name("path-four-thin-layer-checks.json").write_text(
        json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
