#!/usr/bin/env python3
"""Check the minor-preserving path reduction on the graph atlas through order 7.

Requires NetworkX. This is a finite check of the reduction, not a proof of the
excluded-minor stability theorem or the separator theorem.
"""

import itertools
import json
from pathlib import Path

import networkx as nx


def rank(graph):
    return graph.number_of_edges() - len(graph) + nx.number_connected_components(graph)


def reduce_graph(route, marked):
    reduced = nx.MultiGraph(route)
    while True:
        candidates = [v for v in reduced if v not in marked and reduced.degree(v) == 2]
        if not candidates:
            return reduced
        vertex = candidates[0]
        neighbors = [v if u == vertex else u for u, v in reduced.edges(vertex)]
        assert len(neighbors) == 2 and neighbors[0] != neighbors[1]
        reduced.remove_node(vertex)
        reduced.add_edge(*neighbors)


def main():
    counters = dict(connected_graphs=0, above_half_cycle_graphs=0,
                    terminal_pairs=0, above_half_pairs=0,
                    marked_paths_checked=0, suppressed_vertices=0)
    for graph in nx.graph_atlas_g():
        if len(graph) < 2 or not nx.is_connected(graph):
            continue
        counters["connected_graphs"] += 1
        b = rank(graph)
        cycle_count = sum(1 for _ in nx.simple_cycles(graph))
        if 2 * cycle_count > 2 ** b:
            counters["above_half_cycle_graphs"] += 1
            cyclic_blocks = [graph.subgraph(vertices) for vertices in
                             nx.biconnected_components(graph)
                             if graph.subgraph(vertices).number_of_edges() >= len(vertices)]
            assert len(cyclic_blocks) == 1
            block = cyclic_blocks[0]
            assert rank(block) == b
            assert max(dict(block.degree()).values()) <= 5
        for u, v in itertools.combinations(graph, 2):
            counters["terminal_pairs"] += 1
            paths = list(nx.all_simple_paths(graph, u, v))
            if 2 * len(paths) <= 2 ** b:
                continue
            counters["above_half_pairs"] += 1
            route = nx.Graph()
            for path in paths:
                route.add_edges_from(zip(path, path[1:]))
            assert rank(route) == b
            for path in paths:
                counters["marked_paths_checked"] += 1
                marked = set(path)
                length = len(path) - 1
                reduced = reduce_graph(route, marked)
                counters["suppressed_vertices"] += len(route) - len(reduced)
                assert rank(reduced) == b
                assert not list(nx.selfloop_edges(reduced))
                assert all(3 <= reduced.degree(w) <= 5 for w in reduced if w not in marked)
                assert len(reduced) <= 2 * b + length + 1
                outside = reduced.subgraph(set(reduced) - marked)
                assert rank(outside) >= b - 3 * length
                assert sum(1 for _ in nx.all_simple_paths(reduced, u, v)) == len(paths)
    result = dict(status="all exact checks passed", networkx_version=nx.__version__,
                  graph_order_limit=7, **counters,
                  limitations="Finite checks of the reduction only. The stability theorem uses a mathematical separator argument.")
    Path(__file__).with_name("path-minor-reduction-results.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
