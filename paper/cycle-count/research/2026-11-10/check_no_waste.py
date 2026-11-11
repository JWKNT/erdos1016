"""Exhaustive finite checks of the sharp no-waste theorem and refinements.

Requires NetworkX for its unlabeled graph atlas. Pass --deps if installed in
an isolated directory, such as /tmp/erdos1016-research-deps.
"""
from pathlib import Path
import argparse
import json
import sys
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'paper-checks'))
from lib import cyc_basis, span, is_cycle, rank


def marked_components(edges, mask):
    vertices = {v for i, e in enumerate(edges) if (mask >> i) & 1 for v in e}
    parents = {v: v for v in vertices}
    def find(v):
        while parents[v] != v:
            parents[v] = parents[parents[v]]
            v = parents[v]
        return v
    for i, (u, v) in enumerate(edges):
        if (mask >> i) & 1:
            parents[find(u)] = find(v)
    sizes = Counter(find(v) for v in vertices)
    return len(vertices), len(sizes), max(sizes.values())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=6)
    parser.add_argument('--deps')
    args = parser.parse_args()
    if args.deps:
        sys.path.insert(0, args.deps)
    import networkx as nx
    graph_counts = Counter()
    pair_counts = Counter()
    accepted = Counter()
    equality = Counter()
    witnesses = {}
    for graph in nx.graph_atlas_g():
        n = len(graph)
        if n < 3 or n > args.max_n or not nx.is_connected(graph):
            continue
        edges = sorted(graph.edges())
        b = len(cyc_basis(n, edges))
        if b == 0:
            continue
        graph_counts[n] += 1
        cycles = [z for z in span(cyc_basis(n, edges)) if is_cycle(n, edges, z)]
        all_edges = (1 << len(edges))-1
        for marked in range(1, all_edges+1):
            t = rank(n, edges, marked)
            if t == 0:
                continue
            pair_counts[n] += 1
            quotient_rank = b-t
            outside = all_edges ^ marked
            if len({cycle & outside for cycle in cycles}) != 1 << quotient_rank:
                continue
            accepted[n] += 1
            m, c, largest = marked_components(edges, marked)
            sharp = m-c+1+max(0, 4-largest)
            assert quotient_rank <= sharp, (n, edges, marked, quotient_rank, sharp)
            assert quotient_rank <= m+1
            if quotient_rank == m+1:
                equality[n] += 1
                assert m == 3 and c == 1 and marked.bit_count() == 3
                witnesses.setdefault(n, {'edges': edges, 'marked_edges': [edge for i,edge in enumerate(edges) if marked>>i&1]})
    result = {'networkx_version': nx.__version__, 'max_n': args.max_n,
              'connected_cyclic_graphs': dict(graph_counts),
              'marked_subgraphs_containing_cycles': dict(pair_counts),
              'no_waste_pairs': dict(accepted),
              'sharp_equality_pairs': dict(equality),
              'equality_witnesses': witnesses, 'status': 'PASS',
              'scope': 'All edge subsets W containing a cycle in every connected atlas graph through max_n. Isolated marked vertices omitted.'}
    Path(__file__).with_name('no-waste-results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
