#!/usr/bin/env python3
"""Check finite identities used in the path-stability research note.

This script does not prove the asymptotic forest estimate.
It uses exact integer arithmetic for the series-parallel composition checks.
"""

import json
from pathlib import Path


def enumerate_paths(edges, source, target):
    adjacency = {}
    for a, b in edges:
        adjacency.setdefault(a, []).append(b)
        adjacency.setdefault(b, []).append(a)
    result = []

    def visit(path):
        if path[-1] == target:
            result.append(path)
            return
        for vertex in adjacency[path[-1]]:
            if vertex not in path:
                visit(path + [vertex])

    visit([source])
    return result


def check_compositions(edge_limit=12):
    # Each state is (rank, distance, number of terminal paths).
    states = {1: {(0, 1, 1)}}
    transition_count = 0
    for size in range(2, edge_limit + 1):
        current = set()
        for left_size in range(1, size):
            for b1, l1, p1 in states[left_size]:
                for b2, l2, p2 in states[size - left_size]:
                    current.add((b1 + b2, l1 + l2, p1 * p2))
                    current.add((b1 + b2 + 1, min(l1, l2), p1 + p2))
                    transition_count += 2
        for rank, distance, count in current:
            assert count <= 2**rank
            assert 2 * count <= 2**rank + 2**distance
        states[size] = current
    return {
        "edge_limit": edge_limit,
        "distinct_states": sum(map(len, states.values())),
        "composition_transitions": transition_count,
        "all_integer_inequalities_pass": True,
    }


def main():
    edges = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3)]
    paths = enumerate_paths(edges, 3, 4)
    counterexample_rank = len(edges) - 5 + 1
    distance = min(len(path) - 1 for path in paths)
    assert (counterexample_rank, distance, len(paths)) == (3, 2, 7)
    assert 2 * len(paths) > 2**counterexample_rank + 2**distance

    sharp = []
    for rank in range(3, 10):
        stages = rank - 1
        edges = [(0, stages)]
        for i in range(stages):
            middle = stages + 1 + i
            edges += [(i, i + 1), (i, middle), (middle, i + 1)]
        paths_n = len(enumerate_paths(edges, 0, stages))
        vertices_n = 2 * stages + 1
        assert len(edges) - vertices_n + 1 == rank
        assert paths_n == 2 ** (rank - 1) + 1
        sharp.append({"rank": rank, "distance": 1, "paths": paths_n})

    result = {
        "series_parallel": check_compositions(),
        "counterexample": {
            "vertices": 5,
            "rank": counterexample_rank,
            "distance": distance,
            "path_count": len(paths),
            "paths": paths,
        },
        "sharp_simple_examples": sharp,
        "scope": "Finite exact checks of the terminal series-parallel inequalities; the general additive theorem is proved separately.",
    }
    output = Path(__file__).with_name("path-stability-results.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
