#!/usr/bin/env python3
"""Exact endpoint-avoidance and full-K22 forest-concentration checks."""

import collections
import itertools
import json
from fractions import Fraction
from pathlib import Path

from check_four_regular_positive_port_localization import chain, piece
from check_second_order_path_gap import capped_ladder, compositions
from check_second_order_saturated_blocks import paths
from check_second_order_four_cut_states import forest_states


def delete_edges_at(edges, vertex):
    return [(u, v) for u, v in edges if vertex not in (u, v)]


def uncapped(blocks):
    n, edges, a, c, _, _ = capped_ladder(blocks)
    kept = [v for v in range(n) if v not in (a, c)]
    relabel = {v: i for i, v in enumerate(kept)}
    result = [(relabel[u], relabel[v]) for u, v in edges
              if u in relabel and v in relabel]
    w = len(kept) // 2
    return len(kept), result, [0, w, w - 1, 2 * w - 1]


def full_tripole(blocks):
    n, edges, a, c = piece(blocks)
    e = next(i for i, edge in enumerate(edges) if a in edge)
    u, v = edges[e]
    return n + 1, edges[:e] + edges[e + 1:] + [(u, n), (v, n)], c, [a, n]


def bridged(left, right):
    n, edges, center, ports = full_tripole(left)
    m, other, other_center, other_ports = full_tripole(right)
    result = edges + [(u + n, v + n) for u, v in other]
    result.append((center, other_center + n))
    return n + m, result, ports + [v + n for v in other_ports]


def main():
    stats = collections.Counter()
    maximum_used_fraction = Fraction(0)
    small = [blocks for k in range(4) for blocks in compositions(k)]
    chains = [(blocks,) for k in range(9) for blocks in compositions(k)]
    chains += list(itertools.product(small, repeat=2))
    chains += [((), (), blocks, ()) for blocks in small]
    for blocks in chains:
        n, edges, a, c = chain(blocks)
        rank = len(edges) - n + 1
        assert paths(n, edges, a, c) == 1 << rank
        for e, (u, v) in enumerate(edges):
            split = edges[:e] + edges[e + 1:] + [(u, n), (v, n)]
            for terminal, avoided in ((a, c), (c, a)):
                total = paths(n + 1, split, n, terminal)
                avoiding = paths(n + 1, delete_edges_at(split, avoided), n, terminal)
                assert 2 * avoiding >= total
                maximum_used_fraction = max(maximum_used_fraction,
                                            Fraction(total - avoiding, total))
                stats['endpoint_avoidance_checks'] += 1
        stats['full_two_poles'] += 1

    four_poles = [uncapped(blocks) for k in range(2, 8) for blocks in compositions(k)]
    four_poles += [bridged(left, right) for left, right in itertools.product(small, repeat=2)]
    maximum_excess_ratio = Fraction(0)
    for n, edges, ports in four_poles:
        rank = len(edges) - n + 1
        full = 1 << rank
        assert all(paths(n, edges, l, r) == full
                   for l in ports[:2] for r in ports[2:])
        for e, (u, v) in enumerate(edges):
            split = edges[:e] + edges[e + 1:] + [(u, n), (v, n)]
            for same, opposite in ((ports[:2], ports[2:]), (ports[2:], ports[:2])):
                deficit = 0
                total_paths = sum(paths(n + 1, split, n, j) for j in same)
                for j in same:
                    counts = forest_states(n + 1, split, [n, j, *opposite])
                    # The first canonical pairing is b-j | opposite pair.
                    deficit += counts[1] + counts[2]
                assert deficit <= total_paths
                maximum_excess_ratio = max(maximum_excess_ratio,
                                           Fraction(deficit, total_paths))
                stats['exact_forest_concentration_checks'] += 1
            stats['five_pole_subdivisions'] += 1
        stats['full_K22_four_poles'] += 1

    result = {
        'status': 'all endpoint-avoidance and forest-concentration checks passed',
        'checks': dict(stats),
        'maximum_fraction_of_paths_using_other_terminal': str(maximum_used_fraction),
        'maximum_off_cap_forest_mass_over_corresponding_path_sum': str(maximum_excess_ratio),
        'limits': 'Finite checks supplement the symbolic proof; they are not an exhaustive graph classification.'
    }
    Path(__file__).with_name('four-regular-terminal-avoidance-checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
