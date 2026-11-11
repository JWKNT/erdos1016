#!/usr/bin/env python3
"""Exact checks for far antisymmetry and full-slab restoration geometry."""

import collections
import itertools
import json
import random
from pathlib import Path

from fable_check_thin_chain import components, ring_graph, short_cycles


def square_ring(blocks):
    n = 4 * blocks
    edges = []
    cycles = []
    for i in range(blocks):
        base, nxt = 4 * i, 4 * ((i + 1) % blocks)
        cycles.append(set(range(base, base + 4)))
        edges.extend((base + j, base + ((j + 1) % 4)) for j in range(4))
        edges.extend([(base + 2, nxt), (base + 3, nxt + 1)])
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    assert all(len(row) == 3 for row in adj)
    return n, edges, adj, cycles


def far_checks(rng, trials):
    stats = collections.Counter()
    for _ in range(trials):
        n, adj = ring_graph(rng, rng.randrange(4, 8), rng.randrange(4, 7),
                            rng.randrange(1, 4))
        p = rng.randrange(n)
        marked = {p, rng.choice(adj[p])}
        cycles = [set(c) for c in short_cycles(n, adj, 6) if not (c & marked)]
        rng.shuffle(cycles)
        cycles = cycles[:80]
        comps = [components(n, adj, c)[0] for c in cycles]
        weights = [1 << (6 - len(c)) for c in cycles]
        ordered_far_weight = 0
        for i, j in itertools.combinations(range(len(cycles)), 2):
            if cycles[i] & cycles[j]:
                continue
            ci, cj = cycles[i], cycles[j]
            # Each connected cycle lies in one component after deleting the other.
            assert len({comps[i][v] for v in cj}) == 1
            assert len({comps[j][v] for v in ci}) == 1
            far_ij = comps[i][next(iter(cj))] != comps[i][p]
            far_ji = comps[j][next(iter(ci))] != comps[j][p]
            assert not (far_ij and far_ji)
            stats['disjoint_cycle_pairs'] += 1
            stats['one_way_far_pairs'] += far_ij + far_ji
            ordered_far_weight += (far_ij + far_ji) * weights[i] * weights[j]
        total = sum(weights)
        assert 2 * ordered_far_weight <= total * total - sum(w * w for w in weights)
        stats['exact_weighted_antisymmetry_checks'] += 1
    assert stats['one_way_far_pairs'] > 0
    return dict(stats)


def restoration_checks(rng, trials):
    stats = collections.Counter()
    for _ in range(trials):
        block_count = rng.randrange(48, 121)
        n, edges, adj, cycles = square_ring(block_count)
        p_index = block_count // 2
        marked = cycles[p_index]
        anchor = cycles[0]
        u = 4
        chain_indices = list(range(2, p_index - 1, 2))
        chain = [cycles[i] for i in chain_indices]
        inner = []
        for separator in chain:
            comp, _ = components(n, adj, anchor | separator)
            assert comp[u] != comp[next(iter(marked))]
            inner.append({v for v in range(n) if comp[v] == comp[u]})
        assert all(inner[i] | chain[i] <= inner[i + 1]
                   for i in range(len(chain) - 1))
        slabs = [inner[i + 1] - inner[i] - chain[i]
                 for i in range(len(chain) - 1)]
        for i, slab in enumerate(slabs):
            assert not (slab & marked)
            assert all(v in slab | chain[i] | chain[i + 1] | anchor
                       for w in slab for v in adj[w])
            stats['exact_slab_boundaries'] += 1
        q = rng.randrange(2, 5)
        blocks = []
        for first in range(0, len(chain) - q, q + 1):
            last = first + q - 1
            assert last + 1 < len(chain)
            vertices = set().union(*chain[first:last + 1], *slabs[first:last])
            assert len(vertices) >= 4 * q
            assert vertices <= inner[last + 1]
            assert not any(v in marked for w in vertices for v in adj[w])
            blocks.append(vertices)
        for left, right in itertools.combinations(blocks, 2):
            assert not (left & right)
            assert not any(v in right for w in left for v in adj[w])
            stats['nonadjacent_block_pairs'] += 1
        medium_indices = [i for i in range(1, p_index) if i not in chain_indices]
        early_indices = rng.sample(medium_indices, min(2, len(medium_indices)))
        early = set().union(*(cycles[i] for i in early_indices))
        medium = set().union(*(cycles[i] for i in medium_indices if i not in early_indices))
        closed_early = early | {v for w in early for v in adj[w]}
        anchor_neighbors = {v for w in anchor for v in adj[w] if v not in anchor}
        rejected = [v for v in blocks if v & (closed_early | anchor_neighbors)]
        assert len(rejected) <= 4 * len(early) + len(anchor)
        for vertices in blocks:
            if vertices & (closed_early | anchor_neighbors):
                continue
            assert not (vertices & (marked | early | anchor))
            boundary = [(u0, v0) for u0, v0 in edges
                        if (u0 in vertices) != (v0 in vertices)]
            assert len(boundary) <= 2 * len(anchor)
            deficit_restored = sum(sum(w in marked | early for w in adj[v])
                                   for v in vertices)
            assert deficit_restored == 0
            restored_vertices = len(vertices & medium)
            stats['restored_medium_vertices'] += restored_vertices
            old_vertices = vertices - medium
            old_deficit = sum(sum(w in marked | early | medium for w in adj[v])
                              for v in old_vertices)
            stats['blocks_with_strict_deficit_reduction'] += old_deficit > 0
            stats['clean_zero_deficit_blocks'] += 1
        stats['nested_chains'] += 1
    assert stats['clean_zero_deficit_blocks'] > 50
    assert stats['blocks_with_strict_deficit_reduction'] > 50
    return dict(stats)


def main():
    rng = random.Random(101620261110)
    result = {'status': 'all exact two-scale structural checks passed',
              'far_antisymmetry': far_checks(rng, 200),
              'full_slab_restoration': restoration_checks(rng, 160)}
    output = Path(__file__).with_name('two-scale-structure-checks.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
