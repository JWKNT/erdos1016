"""Explore a path plus a matched cycle; this is not an exhaustive graph search."""
import itertools
import json
import random
from pathlib import Path


def count_paths(adj, start, end):
    def visit(vertex, used):
        if vertex == end:
            return 1
        return sum(visit(other, used | (1 << other))
                   for other in adj[vertex] if not used & (1 << other))
    return visit(start, 1 << start)


def graph(order):
    b = len(order)
    adj = [[] for _ in range(2 * b)]
    edges = [(i, i + 1) for i in range(b - 1)]
    edges += [(i, b + i) for i in range(b)]
    edges += [(b + order[i], b + order[(i + 1) % b]) for i in range(b)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj, edges


def main():
    rng = random.Random(1016)
    records = []
    for b in range(3, 13):
        if b <= 8:
            orders = ((0,) + tail for tail in itertools.permutations(range(1, b))
                      if tail[0] < tail[-1])
        else:
            orders = [(0,) + tuple(rng.sample(range(1, b), b - 1)) for _ in range(200)]
        maximum = -1
        witness = None
        count = 0
        for order in orders:
            adj, edges = graph(order)
            paths = count_paths(adj, 0, b - 1)
            assert paths < (1 << b)  # The displayed path is disjoint from a cycle.
            count += 1
            if paths > maximum:
                maximum, witness = paths, order
        record = dict(rank=b, displayed_path_length=b - 1, cases=count,
                      maximum=maximum, total_joins=1 << b,
                      maximum_density=maximum / (1 << b), witness=witness,
                      exhaustive_within_family=b <= 8)
        records.append(record)
        print(record, flush=True)
    Path(__file__).with_name("near-full-path-results.json").write_text(
        json.dumps(records, indent=2) + "\n")


if __name__ == "__main__":
    main()
