#!/usr/bin/env python3
"""Reconstruct three-pole return paths from exact distance-layer data."""

import argparse
import collections
import itertools
import json
import subprocess
from pathlib import Path

from check_cubic_edge_frequency import graph6_edges, cycle_space_cycles
from check_high_path_cycle_layers import induced_rank, alternating_doubled_rails
from check_second_order_path_gap import capped_ladder, compositions


def connected(n, edges):
    reached = {0}
    while True:
        extra = {v for u, v in edges if u in reached} | {u for u, v in edges if v in reached}
        if extra <= reached:
            return len(reached) == n
        reached |= extra


def path_masks(adj, s, t):
    def walk(v, vertices, mask):
        if v == t:
            yield mask, vertices
            return
        for w, edge in adj[v]:
            if not vertices >> w & 1:
                yield from walk(w, vertices | 1 << w, mask | 1 << edge)
    return walk(s, 1 << s, 0)


def verify(n, edges, ports):
    if not connected(n, edges):
        return collections.Counter(skipped_disconnected=1)
    cycles, incident = cycle_space_cycles(n, edges)
    used = 0
    for mask, _ in cycles:
        used |= mask
    if used != (1 << len(edges)) - 1:
        return collections.Counter(skipped_with_bridges=1)
    rank = len(edges) - n + 1
    assert n == 2 * rank + 1
    adj = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        adj[u].append((v, e))
        adj[v].append((u, e))
    assert all(len(adj[v]) == (2 if v in ports else 3) for v in range(n))
    stats = collections.Counter(three_poles=1)
    multiplicities = collections.Counter(tuple(sorted(e)) for e in edges)
    for c in ports:
        a, b = [v for v in ports if v != c]
        dist = {c: 0}
        parent = {c: None}
        queue = [c]
        for v in queue:
            for w, e in adj[v]:
                if w not in dist:
                    dist[w] = dist[v] + 1
                    parent[w] = v
                    queue.append(w)
        path = {a}
        at = a
        while at != c:
            at = parent[at]
            path.add(at)
        layers = collections.defaultdict(set)
        for v, level in dist.items():
            layers[level].add(v)
        d = min(dist[a], dist[b])
        delta = rank - d
        assert delta >= 0
        assert all(len(layers[j]) >= 2 for j in range(1, d))
        marked = {j for j, vertices in layers.items()
                  if j == 0 or j >= d or len(vertices) >= 3}
        base = set().union(*(layers[j] for j in marked))
        assert len(base) <= 6 * delta + 3
        residual_rank = induced_rank(n, edges, set(range(n)) - path)
        pairs = 0
        for (u, v), mult in multiplicities.items():
            if mult >= 2:
                assert mult == 2
                assert (u in path) == (v in path)
                if u not in path:
                    pairs += 1
                    marked.update((dist[u], dist[v]))
                else:
                    assert abs(dist[u] - dist[v]) == 1
        assert pairs <= residual_rank
        base = set().union(*(layers[j] for j in marked))
        assert len(base) <= 6 * delta + 4 * residual_rank + 3
        encodings = set()
        for mask, vertices in path_masks(adj, a, b):
            lo = min(dist[v] for v in range(n) if vertices >> v & 1)
            exceptional = base if lo >= d else base | layers[lo]
            assert len(exceptional) <= 6 * delta + 4 * residual_rank + 5
            fixed = 0
            for v in exceptional:
                fixed |= incident[v]
            encoded = mask & fixed
            reconstructed = encoded
            choice_indices = []
            two_choices = []
            for j in range(lo + 1, d):
                if j in marked:
                    continue
                for v in layers[j]:
                    selected = [dist[w] for w, e in adj[v] if mask >> e & 1]
                    assert sorted(selected) == [j - 1, j + 1]
            for j in range(lo + 1, d - 1):
                if j in marked or j + 1 in marked:
                    continue
                left, right = layers[j], layers[j + 1]
                cut = [e for e, (u, v) in enumerate(edges)
                       if (u in left and v in right) or (v in left and u in right)]
                matchings = [sum(1 << e for e in pair)
                             for pair in itertools.combinations(cut, 2)
                             if {v for e in pair for v in edges[e]} == left | right]
                assert 1 <= len(matchings) <= 2
                chosen = mask & sum(1 << e for e in cut)
                assert chosen in matchings
                reconstructed |= chosen
                choice_indices.append((j, matchings.index(chosen)))
                if len(matchings) == 2:
                    two_choices.append(j)
            assert all(v - u >= 2 for u, v in zip(two_choices, two_choices[1:]))
            assert 2 * len(two_choices) <= max(d - lo, 0)
            assert reconstructed == mask
            key = (lo, encoded, tuple(choice_indices))
            assert key not in encodings
            encodings.add(key)
            stats['exact_path_reconstructions'] += 1
            stats['two_choice_cuts'] += len(two_choices)
        stats['terminal_source_choices'] += 1
    return stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geng', default='/tmp/nauty2_8_9/geng')
    parser.add_argument('--maximum-order', type=int, default=14)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name(
        'three-pole-return-layers-results.json'))
    args = parser.parse_args()
    rows = []
    for n in range(4, args.maximum_order + 1, 2):
        process = subprocess.Popen([args.geng, '-cq', '-d3', '-D3', str(n)],
                                   stdout=subprocess.PIPE)
        stats = collections.Counter()
        for line in process.stdout:
            _, edges = graph6_edges(line)
            stats['cubic_graphs'] += 1
            for removed in range(n):
                ports = [u ^ v ^ removed for u, v in edges if removed in (u, v)]
                relabel = {v: v - (v > removed) for v in range(n) if v != removed}
                reduced = [(relabel[u], relabel[v]) for u, v in edges
                           if removed not in (u, v)]
                stats.update(verify(n - 1, reduced, [relabel[v] for v in ports]))
        assert process.wait() == 0
        rows.append({'order': n, **dict(stats)})
    structured = collections.Counter()
    for k in range(1, 7):
        for blocks in compositions(k):
            n, edges, s, t, _, _ = capped_ladder(blocks)
            for e, (u, v) in enumerate(edges):
                subdivided = edges[:e] + edges[e + 1:] + [(u, n), (n, v)]
                structured.update(verify(n + 1, subdivided, [s, t, n]))
    for k in range(2, 11, 2):
        n, edges, s, t = alternating_doubled_rails(k)
        for e in (0, 4):
            u, v = edges[e]
            subdivided = edges[:e] + edges[e + 1:] + [(u, n), (n, v)]
            structured.update(verify(n + 1, subdivided, [s, t, n]))
    result = {'status': 'all exact return-path layer checks passed',
              'simple_cubic_vertex_deletions': rows,
              'subdivided_ladders_and_multigraphs': dict(structured)}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
