"""Check the cubic frequency identities using exact binary cycle spaces."""

import argparse
import collections
import json
import subprocess
from pathlib import Path


def graph6_edges(line):
    data = line.strip()
    n = data[0] - 63
    assert n < 63
    bits = [(char - 63) >> shift & 1 for char in data[1:]
            for shift in range(5, -1, -1)]
    return n, [(u, v) for bit, (u, v) in zip(
        bits, ((u, v) for v in range(1, n) for u in range(v))) if bit]


def cycle_space_cycles(n, edges):
    tree = [[] for _ in range(n)]
    components = list(range(n))
    chords = []
    incidents = [0] * n
    for i, (u, v) in enumerate(edges):
        incidents[u] |= 1 << i
        incidents[v] |= 1 << i
        if components[u] == components[v]:
            chords.append((i, u, v))
        else:
            old, new = components[v], components[u]
            components = [new if c == old else c for c in components]
            tree[u].append((v, i))
            tree[v].append((u, i))

    def tree_path(u, target, previous=-1):
        if u == target:
            return 0
        for v, i in tree[u]:
            if v != previous:
                tail = tree_path(v, target, u)
                if tail is not None:
                    return tail | (1 << i)
        return None

    masks = [0]
    for i, u, v in chords:
        vector = (1 << i) | tree_path(u, v)
        masks += [mask ^ vector for mask in masks]
    result = []
    for mask in masks[1:]:
        active = [v for v in range(n) if incidents[v] & mask]
        assert all((incidents[v] & mask).bit_count() == 2 for v in active)
        reached = 1 << active[0]
        pending = [active[0]]
        while pending:
            u = pending.pop()
            remaining = incidents[u] & mask
            while remaining:
                bit = remaining & -remaining
                remaining ^= bit
                x, y = edges[bit.bit_length() - 1]
                v = x ^ y ^ u
                if not reached >> v & 1:
                    reached |= 1 << v
                    pending.append(v)
        if reached.bit_count() == len(active):
            result.append((mask, reached))
    return result, incidents


def perfect_matchings(n, edges, incidents):
    all_vertices = (1 << n) - 1

    def extend(used, chosen):
        if used == all_vertices:
            yield chosen
            return
        bit = (all_vertices ^ used) & -(all_vertices ^ used)
        u = bit.bit_length() - 1
        remaining = incidents[u]
        while remaining:
            edgebit = remaining & -remaining
            remaining ^= edgebit
            x, y = edges[edgebit.bit_length() - 1]
            v = x ^ y ^ u
            if not used >> v & 1:
                yield from extend(used | bit | (1 << v), chosen | edgebit)

    yield from extend(0, 0)


def verify_graph(n, edges):
    cycles, incidents = cycle_space_cycles(n, edges)
    count = len(cycles)
    frequencies = [sum(bool(mask >> i & 1) for mask, _ in cycles)
                   for i in range(len(edges))]
    stats = collections.Counter(graphs=1, cycles=count)
    for rim, vertices in cycles:
        size = rim.bit_count()
        if size not in (3, 4):
            continue
        if size == 4 and any((vertices >> u & 1) and (vertices >> v & 1)
                             and not (rim >> i & 1)
                             for i, (u, v) in enumerate(edges)):
            continue
        outside = sum(not (vset & vertices) for _, vset in cycles)
        rim_edges = [i for i in range(len(edges)) if rim >> i & 1]
        if size == 3:
            assert all(2 * frequencies[i] == count + 1 - outside
                       for i in rim_edges)
            stats['triangles'] += 1
        else:
            assert sum(frequencies[i] for i in rim_edges) == 2 * count + 2 - 2 * outside
            stats['induced_squares'] += 1
        if n >= 8 or (n >= 6 and size == 3):
            assert min(2 * frequencies[i] for i in rim_edges) <= count
    if n >= 6:
        for matching in perfect_matchings(n, edges, incidents):
            weighted = sum(1 << (mask & matching).bit_count() for mask, _ in cycles)
            assert weighted <= (1 << n) - n // 2
            stats['perfect_matchings'] += 1
    return stats


def expanded_k33():
    # The old vertex 0 is replaced by triangle vertices 0, 6, 7.
    edges = [(u, v) for u in (1, 2) for v in (3, 4, 5)]
    edges += [(0, 3), (6, 4), (7, 5), (0, 6), (6, 7), (7, 0)]
    cycles, _ = cycle_space_cycles(8, edges)
    histogram = collections.Counter(mask.bit_count() for mask, _ in cycles)
    assert histogram == {3: 1, 4: 3, 5: 6, 6: 6, 7: 6, 8: 6}
    triangle_frequencies = [sum(mask >> i & 1 for mask, _ in cycles)
                            for i in (9, 10, 11)]
    assert triangle_frequencies == [13, 13, 13]
    return {'vertices': 8, 'cycles': len(cycles),
            'cycle_length_sum': sum(k * v for k, v in histogram.items()),
            'histogram': dict(sorted(histogram.items())),
            'triangle_edge_frequencies': triangle_frequencies}


def terminal_visitation_counterexample():
    edges = [(0, 5), (1, 6), (2, 7), (0, 8), (1, 8), (3, 8), (0, 9),
             (2, 9), (4, 9), (2, 10), (5, 10), (6, 10), (1, 11), (4, 11),
             (7, 11), (3, 12), (4, 12), (6, 12), (3, 13), (5, 13), (7, 13)]
    cycles, _ = cycle_space_cycles(14, edges)
    assert min(mask.bit_count() for mask, _ in cycles) == 5
    columns = [sum(1 << j for j, (mask, _) in enumerate(cycles) if mask >> i & 1)
               for i in range(len(edges))]
    # A bridge has zero cycle-space coordinate. A two-edge cut has equal coordinates.
    assert 0 not in columns and len(set(columns)) == len(columns)
    pair = [edges.index((2, 7)), edges.index((2, 9))]
    paths = [(mask, vertices) for mask, vertices in cycles
             if all(mask >> i & 1 for i in pair)]
    visiting = sum(vertices >> 10 & 1 for _, vertices in paths)
    assert len(paths) == 50 and visiting == 26
    return {'vertices': 14, 'edges': edges, 'girth': 5, 'edge_connectivity': 3,
            'removed_vertex': 2, 'terminals': [7, 9, 10],
            'paths_between_first_two': len(paths), 'paths_visiting_third': visiting}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geng', default='/tmp/nauty2_8_9/geng')
    parser.add_argument('--maximum-order', type=int, default=14)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name(
        'cubic-edge-frequency-results.json'))
    args = parser.parse_args()
    rows = []
    for n in range(4, args.maximum_order + 1, 2):
        process = subprocess.Popen([args.geng, '-cq', '-d3', '-D3', str(n)],
                                   stdout=subprocess.PIPE)
        stats = collections.Counter()
        for line in process.stdout:
            order, edges = graph6_edges(line)
            assert order == n and len(edges) == 3 * n // 2
            stats.update(verify_graph(n, edges))
        assert process.wait() == 0
        rows.append({'order': n, **dict(stats)})
    result = {'status': 'all exact checks passed',
              'method': 'fundamental binary cycle space; connected nonzero even sets',
              'generator': 'nauty 2.8.9 geng -cq -d3 -D3 n',
              'classes': rows, 'mean_length_counterexample': expanded_k33(),
              'terminal_visitation_counterexample': terminal_visitation_counterexample()}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
