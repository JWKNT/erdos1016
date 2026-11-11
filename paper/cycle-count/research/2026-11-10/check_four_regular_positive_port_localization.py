#!/usr/bin/env python3
"""Exact tests of the full-pair distance and product inequalities."""

import collections
import itertools
import json
import random
from fractions import Fraction
from pathlib import Path

from check_second_order_path_gap import capped_ladder, compositions
from check_second_order_saturated_blocks import paths


def piece(blocks):
    if not blocks:
        return 2, [(0, 1), (0, 1)], 0, 1
    n, edges, a, c, _, _ = capped_ladder(blocks)
    return n, edges, a, c


def chain(pieces):
    edges = []
    total = 0
    first = previous = None
    for blocks in pieces:
        n, local, a, c = piece(blocks)
        edges.extend((u + total, v + total) for u, v in local)
        if previous is None:
            first = a + total
        else:
            edges.append((previous, a + total))
        previous = c + total
        total += n
    return total, edges, first, previous


def distances(n, edges, source):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    result = {source: 0}
    queue = [source]
    for v in queue:
        for w in adj[v]:
            if w not in result:
                result[w] = result[v] + 1
                queue.append(w)
    return result


def main():
    cases = {(blocks,) for k in range(9) for blocks in compositions(k)}
    small = [blocks for k in range(4) for blocks in compositions(k)]
    cases.update(itertools.product(small, repeat=2))
    rng = random.Random(20261110)
    for _ in range(250):
        candidate = tuple(rng.choice(small) for _ in range(rng.randint(3, 5)))
        if sum(sum(blocks) + 1 for blocks in candidate) <= 11:
            cases.add(candidate)

    stats = collections.Counter()
    max_product = Fraction(0)
    max_distance = Fraction(0)
    for pieces in sorted(cases):
        n, edges, a, c = chain(pieces)
        rank = len(edges) - n + 1
        full = 1 << rank
        assert paths(n, edges, a, c) == full
        stats['full_two_poles'] += 1
        stats['with_series_bridges'] += len(pieces) > 1
        for e, (u, v) in enumerate(edges):
            split = edges[:e] + edges[e + 1:] + [(u, n), (n, v)]
            left = paths(n + 1, split, a, n)
            right = paths(n + 1, split, n, c)
            assert paths(n + 1, split, a, c) == full
            product = Fraction((left * right) ** 2, 1 << (3 * rank))
            assert product <= 49
            max_product = max(max_product, product)
            dist = distances(n + 1, split, n)
            for count, target in ((left, c), (right, a)):
                # delta^2 * 2^(distance-3) <= 9/4 is the exact
                # logarithm-free form of the localization assertion.
                ratio = Fraction(count * count, full * full)
                exponent = dist[target] - 3
                ratio *= Fraction(1 << max(exponent, 0),
                                  1 << max(-exponent, 0))
                assert ratio <= Fraction(9, 4)
                max_distance = max(max_distance, ratio)
                stats['exact_distance_checks'] += 1
            stats['exact_product_checks'] += 1
    # Count bridge subdivisions directly, independently of insertion order.
    stats['subdivided_bridge_checks'] = sum(len(pieces) - 1 for pieces in cases)
    result = {
        'status': 'all exact localization and product inequalities passed',
        'checks': dict(stats),
        'maximum_squared_product_normalized_by_2_to_3h': str(max_product),
        'maximum_delta_squared_times_2_to_distance_minus_3': str(max_distance),
        'limits': 'Finite evidence only. The symbolic proof covers all ranks.'
    }
    output = Path(__file__).with_name('four-regular-positive-port-localization-checks.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
