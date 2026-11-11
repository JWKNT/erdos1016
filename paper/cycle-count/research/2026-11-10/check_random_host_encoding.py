"""Check the two-digit cycle gadget used in random-hosts.tex.

These finite checks verify the encoding and rank identities.
They do not verify the asymptotic probability estimates.
"""

from collections import Counter, defaultdict
import json


def edge(u, v):
    return tuple(sorted((u, v)))


def build_gadget(base, depth):
    size = 2 * base + 1
    cycle = {edge(i, (i + 1) % size) for i in range(size)}
    paths = {}
    next_vertex = size
    graph = set(cycle)
    for digit in range(2):
        for value in range(base):
            index = digit * base + value
            length = depth + 2 + value * base**digit
            vertices = [index] + list(range(next_vertex, next_vertex + length - 1))
            next_vertex += length - 1
            vertices.append(index + 1)
            path = {edge(a, b) for a, b in zip(vertices, vertices[1:])}
            assert len(path) == length
            assert graph.isdisjoint(path)
            graph.update(path)
            paths[digit, value] = path
    assert len(graph) - next_vertex + 1 == 2 * base + 1
    return cycle, paths


def cycle_length(edges):
    degrees = Counter(vertex for pair in edges for vertex in pair)
    assert all(degree == 2 for degree in degrees.values())
    adjacency = defaultdict(list)
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    seen = set()
    todo = [next(iter(degrees))]
    while todo:
        u = todo.pop()
        if u in seen:
            continue
        seen.add(u)
        todo.extend(adjacency[u])
    assert seen == set(degrees)
    return len(edges)


def main():
    checked = 0
    parameters = 0
    for base in range(2, 21):
        for depth in range(1, 7):
            original, paths = build_gadget(base, depth)
            lengths = set()
            start = 2 * (depth + base + 1)
            for first in range(base):
                for second in range(base):
                    selected = set(original)
                    for digit, value in enumerate((first, second)):
                        index = digit * base + value
                        selected.remove(edge(index, index + 1))
                        selected.update(paths[digit, value])
                    length = cycle_length(selected)
                    assert length == start + 1 + first + base * second
                    lengths.add(length)
                    checked += 1
            assert lengths == set(range(start + 1, start + base**2 + 1))
            parameters += 1
    print(json.dumps({"status": "pass", "parameter_pairs": parameters,
                      "explicit_cycles_checked": checked,
                      "scope": "two-digit gadget, exact ranks, and interval coverage"}, indent=2))


if __name__ == "__main__":
    main()
