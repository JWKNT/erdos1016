#!/usr/bin/env python3
"""Exact K3,3 port-assignment and nonforest parity witnesses; standard library only."""

import collections
import itertools
import json
import random
from pathlib import Path

CORE_EDGES = tuple((u, v) for u in range(3) for v in range(3, 6))
CORE_INDEX = {edge: i for i, edge in enumerate(CORE_EDGES)}
SQUARES = tuple(frozenset(CORE_INDEX[u, v] for u in left for v in right)
                for left in itertools.combinations(range(3), 2)
                for right in itertools.combinations(range(3, 6), 2))


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, parts - 1):
                yield (first,) + rest


def build(on_core, groups=()):
    """Each group is (port count, attachment core edges, chosen attachment)."""
    operations = [[('port', None)] * count for count in on_core]
    for g, (_, attachments, _) in enumerate(groups):
        for j, edge in enumerate(attachments):
            operations[edge].append(('attach', (g, j)))
    edges, paths, assignments = [], [], {}
    attachment_vertices = {}
    n = 6
    for i, (a, b) in enumerate(CORE_EDGES):
        vertices = [a]
        for kind, key in operations[i]:
            vertices.append(n)
            if kind == 'port':
                assignments[n] = i
            else:
                attachment_vertices[key] = n
            n += 1
        vertices.append(b)
        mask = 0
        for u, v in zip(vertices, vertices[1:]):
            mask |= 1 << len(edges)
            edges.append((u, v))
        paths.append(mask)
    for g, (count, attachments, chosen) in enumerate(groups):
        attachment_nodes = list(range(n, n + len(attachments)))
        n += len(attachments)
        outside_ports = list(range(n, n + count))
        n += count
        cycle = attachment_nodes + outside_ports
        assert len(cycle) >= 2
        edges.extend(zip(cycle, cycle[1:] + cycle[:1]))
        for j, outside in enumerate(attachment_nodes):
            edges.append((attachment_vertices[g, j], outside))
        for port in outside_ports:
            assignments[port] = attachments[chosen]
    return n, edges, paths, assignments


def odd_vertices(edges, mask):
    result = set()
    for i, (u, v) in enumerate(edges):
        if mask >> i & 1:
            for vertex in (u, v):
                if vertex in result:
                    result.remove(vertex)
                else:
                    result.add(vertex)
    return result


def is_forest(n, edges, mask):
    parent = list(range(n))
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for i, (u, v) in enumerate(edges):
        if mask >> i & 1:
            a, b = find(u), find(v)
            if a == b:
                return False
            parent[a] = b
    return True


def tree_paths(n, edges, source, forbidden=frozenset()):
    adjacency = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        if u not in forbidden and v not in forbidden:
            adjacency[u].append((v, i))
            adjacency[v].append((u, i))
    roots = {source: 0}
    tree_edges = set()
    queue = [source]
    for u in queue:
        for v, edge in adjacency[u]:
            if v not in roots:
                roots[v] = roots[u] ^ (1 << edge)
                tree_edges.add(edge)
                queue.append(v)
    return roots, tree_edges


def verify(graph, enumerate_sector=False):
    n, edges, core_paths, assignments = graph
    assert len(assignments) == 6
    degree = collections.Counter(v for edge in edges for v in edge)
    assert all(degree[v] == (2 if v in assignments else 3) for v in range(n))
    weights = collections.Counter(assignments.values())
    omitted_weights = [sum(weights[i] for i in range(9) if i not in square)
                       for square in SQUARES]
    assert sum(omitted_weights) == 30
    assert max(omitted_weights) >= 4
    square = SQUARES[omitted_weights.index(max(omitted_weights))]
    cycle_mask = 0
    for i in square:
        cycle_mask |= core_paths[i]
    cycle_vertices = {v for i, edge in enumerate(edges) if cycle_mask >> i & 1 for v in edge}
    assert not odd_vertices(edges, cycle_mask)
    assert not is_forest(n, edges, cycle_mask)
    surviving_ports = [v for v, i in assignments.items() if i not in square]
    assert len(surviving_ports) >= 4
    selected_ports = set(surviving_ports[:4])
    paths, _ = tree_paths(n, edges, surviving_ports[0], cycle_vertices)
    assert all(v in paths for v in surviving_ports)
    join = 0
    for v in selected_ports:
        join ^= paths[v]
    assert odd_vertices(edges, join) == selected_ports
    assert is_forest(n, edges, join)
    assert not (join & cycle_mask)
    witness = join | cycle_mask
    assert odd_vertices(edges, witness) == selected_ports
    assert not is_forest(n, edges, witness)
    stats = collections.Counter(parity_nonforest_witnesses=1,
                                omitted_weight=max(omitted_weights))
    if enumerate_sector:
        roots, tree_edges = tree_paths(n, edges, 0)
        assert len(roots) == n
        basis = [roots[u] ^ roots[v] ^ (1 << e)
                 for e, (u, v) in enumerate(edges) if e not in tree_edges]
        assert len(basis) == 4
        forests = 0
        for word in range(16):
            state = join
            for i, mask in enumerate(basis):
                if word >> i & 1:
                    state ^= mask
            assert odd_vertices(edges, state) == selected_ports
            forests += is_forest(n, edges, state)
        assert forests <= 15
        stats['affine_states_checked'] = 16
        stats['forest_states_in_witness_sector'] = forests
    return stats


def main():
    totals = collections.Counter()
    histogram = collections.Counter()
    for counts in compositions(6, 9):
        stats = verify(build(counts), enumerate_sector=True)
        totals['core_compositions'] += 1
        totals['affine_states_checked'] += stats['affine_states_checked']
        totals['core_parity_witnesses'] += 1
        histogram[stats['forest_states_in_witness_sector']] += 1
    assert totals['core_compositions'] == 3003

    rng = random.Random(20261112)
    for trial in range(500):
        remaining = 6
        counts = [0] * 9
        groups = []
        while remaining:
            if trial % 3 == 0 or rng.random() < .35:
                counts[rng.randrange(9)] += 1
                remaining -= 1
            else:
                count = rng.randint(1, remaining)
                attachments = tuple(rng.sample(range(9), rng.randint(1, 3)))
                groups.append((count, attachments, rng.randrange(len(attachments))))
                remaining -= count
        verify(build(counts, groups))
        totals['outside_attachment_fixtures'] += 1
        totals['outside_components'] += len(groups)
        totals['multiple_attachment_components'] += sum(len(g[1]) > 1 for g in groups)
    result = {
        'status': 'all exact omitted-weight, connectivity, parity, and nonforest checks passed',
        'checks': dict(totals),
        'rank_four_forest_count_histogram': dict(sorted(histogram.items())),
        'scope': 'The abstract graph theorem is proved separately; these checks test all3003 core assignments and500 deterministic outside-component fixtures.'
    }
    Path(__file__).with_name('four-six-planarity-checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
