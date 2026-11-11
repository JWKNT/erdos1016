#!/usr/bin/env python3
"""Check exact thin-layer encodings, including parallel-edge choices."""

import argparse
import collections
import itertools
import json
import subprocess
from pathlib import Path

from check_cubic_edge_frequency import graph6_edges, cycle_space_cycles
from check_second_order_path_gap import capped_ladder, compositions


def graph_data(n, edges, s, t):
    adj = [[] for _ in range(n)]
    for index, (u, v) in enumerate(edges):
        adj[u].append((v, index))
        adj[v].append((u, index))
    assert all(len(adj[v]) == (2 if v in (s, t) else 3) for v in range(n))
    parent = {s: None}
    distance = {s: 0}
    queue = [s]
    for u in queue:
        for v, edge in adj[u]:
            if v not in parent:
                parent[v] = (u, edge)
                distance[v] = distance[u] + 1
                queue.append(v)
    assert len(queue) == n
    path = {t}
    at = t
    while at != s:
        at = parent[at][0]
        path.add(at)
    layers = collections.defaultdict(set)
    for v, depth in distance.items():
        layers[depth].add(v)
    return adj, distance, path, layers


def induced_rank(n, edges, vertices):
    vertices = set(vertices)
    parent = {v: v for v in vertices}

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    count = 0
    components = len(vertices)
    for u, v in edges:
        if u in vertices and v in vertices:
            count += 1
            ru, rv = root(u), root(v)
            if ru != rv:
                parent[rv] = ru
                components -= 1
    return count - len(vertices) + components


def verify(n, edges, s, t):
    rank = len(edges) - n + 1
    assert n == 2 * rank
    cycles, incident = cycle_space_cycles(n, edges)
    frequencies = [sum(bool(mask >> e & 1) for mask, _ in cycles)
                   for e in range(len(edges))]
    if not all(frequencies):
        return collections.Counter(skipped_with_bridges=1)
    adj, dist, path, layers = graph_data(n, edges, s, t)
    ell = dist[t]
    delta = rank - ell
    assert delta >= 0
    assert max(dist.values()) <= ell + 2 * delta
    assert all(len(layers[i]) >= 2 for i in range(1, ell))
    marked_layers = {i for i, vertices in layers.items()
                     if not 1 <= i < ell or len(vertices) >= 3}
    base = set().union(*(layers[i] for i in marked_layers))
    assert len(base) <= 6 * delta + 2
    outside_rank = induced_rank(n, edges, set(range(n)) - path)
    multiplicity = collections.Counter(tuple(sorted(edge)) for edge in edges)
    outside_pairs = 0
    for (u, v), mult in multiplicity.items():
        if mult >= 2:
            assert mult == 2
            assert (u in path) == (v in path)
            if u not in path:
                outside_pairs += 1
                marked_layers.update((dist[u], dist[v]))
            else:
                assert abs(dist[u] - dist[v]) == 1
    assert outside_pairs <= outside_rank
    base = set().union(*(layers[i] for i in marked_layers))
    assert len(base) <= 6 * delta + 4 * outside_rank + 2
    stats = collections.Counter(poles=1, cycles=len(cycles),
                                outside_parallel_pairs=outside_pairs)
    encodings = set()
    for mask, vertex_mask in cycles:
        active = [v for v in range(n) if vertex_mask >> v & 1]
        lo, hi = min(dist[v] for v in active), max(dist[v] for v in active)
        exceptional = base | layers[lo] | layers[hi]
        assert len(exceptional) <= 6 * delta + 4 * outside_rank + 6
        fixed_edges = 0
        for v in exceptional:
            fixed_edges |= incident[v]
        fixed_value = mask & fixed_edges
        reconstructed = fixed_value
        matching_indices = []
        choice_cuts = []
        for level in range(lo + 1, hi):
            if level in marked_layers:
                continue
            assert len(layers[level]) == 2
            for v in layers[level]:
                selected = [dist[w] for w, edge in adj[v] if mask >> edge & 1]
                assert sorted(selected) == [level - 1, level + 1]
        for level in range(lo + 1, hi - 1):
            if level in marked_layers or level + 1 in marked_layers:
                continue
            left, right = layers[level], layers[level + 1]
            cut = [e for e, (u, v) in enumerate(edges)
                   if (u in left and v in right) or (v in left and u in right)]
            matchings = []
            for pair in itertools.combinations(cut, 2):
                covered = {v for e in pair for v in edges[e]}
                if covered == left | right:
                    matchings.append(sum(1 << e for e in pair))
            assert 1 <= len(matchings) <= 2
            chosen = mask & sum(1 << e for e in cut)
            assert chosen in matchings
            reconstructed |= chosen
            matching_indices.append((level, matchings.index(chosen)))
            if len(matchings) == 2:
                choice_cuts.append(level)
        assert all(v - u >= 2 for u, v in zip(choice_cuts, choice_cuts[1:]))
        assert 2 * len(choice_cuts) <= rank
        assert 2 * len(choice_cuts) <= hi - lo + 1
        assert reconstructed == mask
        encoding = (lo, hi, fixed_value, tuple(matching_indices))
        assert encoding not in encodings
        encodings.add(encoding)
        stats['exact_reconstructions'] += 1
        stats['two_choice_cuts'] += len(choice_cuts)
    return stats


def alternating_doubled_rails(k):
    """Width-two poles with many outside digons and small terminal density."""
    assert k >= 2 and k % 2 == 0
    s, t = 2 * k, 2 * k + 1
    edges = [(s, 0), (s, k), (k - 1, t), (2 * k - 1, t)]
    for rail in (0, k):
        for i in range(k - 1):
            edges.extend([(rail + i, rail + i + 1)] * (2 if i % 2 == 0 else 1))
    return 2 * k + 2, edges, s, t


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geng', default='/tmp/nauty2_8_9/geng')
    parser.add_argument('--maximum-order', type=int, default=12)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name(
        'high-path-cycle-layers-results.json'))
    args = parser.parse_args()
    rows = []
    for n in range(4, args.maximum_order + 1, 2):
        process = subprocess.Popen([args.geng, '-cq', '-d3', '-D3', str(n)],
                                   stdout=subprocess.PIPE)
        stats = collections.Counter()
        for line in process.stdout:
            order, edges = graph6_edges(line)
            stats['cubic_graphs'] += 1
            full_cycles, _ = cycle_space_cycles(order, edges)
            for index, (s, t) in enumerate(edges):
                reduced = edges[:index] + edges[index + 1:]
                # A bridge deletion is disconnected and is outside this lemma.
                if not any(mask >> index & 1 for mask, _ in full_cycles):
                    stats['skipped_bridge_deletions'] += 1
                    continue
                stats.update(verify(order, reduced, s, t))
        assert process.wait() == 0
        rows.append({'order': n, **dict(stats)})
    structured = collections.Counter()
    for k in range(1, 9):
        for blocks in compositions(k):
            n, edges, s, t, _, _ = capped_ladder(blocks)
            structured.update(verify(n, edges, s, t))
    for k in range(2, 13, 2):
        structured.update(verify(*alternating_doubled_rails(k)))
    structured.update(verify(2, [(0, 1), (0, 1)], 0, 1))
    result = {'status': 'all exact structural checks passed',
              'simple_cubic_edge_deletions': rows,
              'structured_ladders_and_multigraphs': dict(structured)}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
