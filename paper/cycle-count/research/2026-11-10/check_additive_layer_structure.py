#!/usr/bin/env python3
"""Check the minimum-span windows and greedy rank bound on explicit graphs.

Requires NetworkX. The checks are independent of the asymptotic forest input.
They validate the finite structural step used for additive path stability.
"""

import json
import random
from pathlib import Path

import networkx as nx

from fable_check_tools import shortest_path, split


def rank(graph):
    return graph.number_of_edges() - len(graph) + nx.number_connected_components(graph)


def check_graph(original, u, v):
    edges = list(original.edges())
    path_edges = shortest_path(len(original), edges, u, v)
    count, expanded_edges, vertex_map = split(len(original), edges, path_edges)
    graph = nx.Graph(expanded_edges)
    assert len(graph) == count
    assert rank(graph) == rank(original)
    u, v = vertex_map[u], vertex_map[v]
    path = nx.shortest_path(graph, u, v)
    assert len(path) - 1 == len(path_edges)
    assert graph.degree(u) <= 2 and graph.degree(v) <= 2
    assert all(graph.degree(w) == 3 for w in graph if w not in (u, v))
    distances = nx.single_source_shortest_path_length(graph, u)
    marked = set(path)
    depth = max(distances.values())
    layers = [{w for w in graph if distances[w] == j and w not in marked}
              for j in range(depth + 1)]
    bound = max(map(len, layers), default=0)
    limit = 20 * bound + 2
    outside = graph.subgraph(set(graph) - marked)
    assert rank(outside) >= rank(graph) - (len(path) - 1)
    intervals = [(0, depth)]
    deleted = set()
    chosen = []
    max_span = max_window = 0

    while True:
        cyclic_intervals = []
        for lo, hi in intervals:
            vertices = set().union(*layers[lo:hi + 1])
            if rank(graph.subgraph(vertices)):
                cyclic_intervals.append((lo, hi))
        if not cyclic_intervals:
            break
        witness = None
        for span in range(1 + max(hi - lo for lo, hi in cyclic_intervals)):
            for lo, hi in cyclic_intervals:
                for first in range(lo, hi - span + 1):
                    last = first + span
                    vertices = set().union(*layers[first:last + 1])
                    induced = graph.subgraph(vertices)
                    if rank(induced):
                        witness = (lo, hi, first, last, vertices, induced)
                        break
                if witness:
                    break
            if witness:
                break
        assert witness is not None
        lo, hi, first, last, vertices, induced = witness
        span = last - first
        cycle = nx.cycle_basis(induced)[0]
        assert min(distances[w] for w in cycle) == first
        assert max(distances[w] for w in cycle) == last
        assert rank(induced.subgraph(vertices - layers[first])) == 0
        assert rank(induced) <= 2 * len(layers[first]) <= 2 * bound
        boundary = sum(1 for _ in nx.edge_boundary(graph, vertices))
        assert boundary <= 6 * bound + span + 3
        assert len(vertices) == 2 * rank(induced) + boundary - 2 * nx.number_connected_components(induced)
        assert 2 * span <= len(cycle) <= len(vertices) <= 10 * bound + span + 1
        assert span <= 10 * bound + 1
        assert len(vertices) <= limit
        assert vertices.isdisjoint(deleted)
        assert sum(1 for _ in nx.edge_boundary(graph, cycle)) <= len(cycle) <= limit
        deleted.update(vertices)
        chosen.append(cycle)
        max_span = max(max_span, span)
        max_window = max(max_window, len(vertices))
        intervals.remove((lo, hi))
        if lo < first:
            intervals.append((lo, first - 1))
        if last < hi:
            intervals.append((last + 1, hi))

    assert rank(outside.subgraph(set(outside) - deleted)) == 0
    assert len(deleted) <= limit * len(chosen)
    assert rank(outside) <= 2 * len(deleted) <= 2 * limit * len(chosen)
    return dict(vertices=len(graph), rank=rank(graph), distance=len(path) - 1,
                outside_rank=rank(outside), layer_width=bound,
                selected_windows=len(chosen), max_selected_span=max_span,
                max_selected_window_size=max_window)


def main():
    random.seed(1016)
    results = []
    for degree in (3, 4):
        for n in range(6, 35, 2):
            for seed in range(5):
                graph = nx.random_regular_graph(degree, n, seed=1000 * degree + 100 * n + seed)
                if nx.is_connected(graph):
                    results.append(check_graph(graph, 0, n // 2))
    for columns in (4, 6, 10, 20, 40, 80, 160):
        graph = nx.circular_ladder_graph(columns)
        results.append(check_graph(graph, 0, columns // 2))
    result = dict(status="all exact checks passed", networkx_version=nx.__version__,
                  graphs_checked=len(results),
                  selected_windows=sum(row["selected_windows"] for row in results),
                  largest_expanded_graph=max(row["vertices"] for row in results),
                  largest_outside_rank=max(row["outside_rank"] for row in results),
                  largest_selected_window=max(row["max_selected_window_size"] for row in results),
                  examples=results[-7:],
                  limitations="Finite checks of the cubic-layer argument only; the probability theorem remains a mathematical proof.")
    Path(__file__).with_name("additive-layer-structure-results.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
