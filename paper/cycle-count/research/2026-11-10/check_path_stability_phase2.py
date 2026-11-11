#!/usr/bin/env python3
"""Independent exact checks for the second path-stability note."""

import json
from functools import lru_cache
from pathlib import Path


def count_paths(edges, source, target):
    vertices = sorted({v for edge in edges for v in edge})
    index = {v: i for i, v in enumerate(vertices)}
    adjacency = [0] * len(vertices)
    for a, b in edges:
        adjacency[index[a]] |= 1 << index[b]
        adjacency[index[b]] |= 1 << index[a]
    source, target = index[source], index[target]

    @lru_cache(None)
    def visit(vertex, used):
        if vertex == target:
            return 1
        result = 0
        todo = adjacency[vertex] & ~used
        while todo:
            bit = todo & -todo
            todo -= bit
            result += visit(bit.bit_length() - 1, used | bit)
        return result

    return visit(source, 1 << source)


def rank_and_distance(edges, source, target):
    adjacency = {}
    for a, b in edges:
        adjacency.setdefault(a, []).append(b)
        adjacency.setdefault(b, []).append(a)
    distances = {source: 0}
    queue = [source]
    for vertex in queue:
        for other in adjacency[vertex]:
            if other not in distances:
                distances[other] = distances[vertex] + 1
                queue.append(other)
    assert len(distances) == len(adjacency)
    return len(edges) - len(adjacency) + 1, distances[target]


def ladder_obstruction(columns):
    edges = [(i, i + 1) for i in range(columns - 1)]
    edges += [(columns + i, columns + i + 1) for i in range(columns - 1)]
    edges += [(i, columns + i) for i in range(columns)]
    edges += [(0, columns - 1)]
    ports = [2 * columns, 2 * columns + 1, 2 * columns + 2]
    neighbors = [1, columns, columns - 1]
    assignment = dict(zip(neighbors, ports))
    replacement = []
    for a, b in edges:
        if a == 0:
            replacement.append((assignment[b], b))
        elif b == 0:
            replacement.append((a, assignment[a]))
        else:
            replacement.append((a, b))
    replacement += [(ports[0], ports[1]), (ports[1], ports[2])]
    return replacement, ports[0], ports[2]


def main():
    family = []
    for columns in range(3, 18):
        edges, source, target = ladder_obstruction(columns)
        rank, distance = rank_and_distance(edges, source, target)
        count = count_paths(edges, source, target)
        assert rank == columns and distance == 2
        assert count == 2 ** (rank - 1) + rank
        family.append({"rank": rank, "distance": distance, "paths": count})

    edges = [(a, b) for a in range(3) for b in range(3, 6) if (a, b) != (0, 3)]
    edges += [(6, 3), (6, 4)]
    assert rank_and_distance(edges, 0, 6) == (4, 2)
    assert count_paths(edges, 0, 6) == 13

    result = {
        "status": "all exact checks passed",
        "rank_four_distance_two_paths": 13,
        "unbounded_distance_two_excess_family": family,
        "limitations": "Finite path counts only; the planar stability proof is a mathematical argument.",
    }
    Path(__file__).with_name("path-stability-phase2-results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
