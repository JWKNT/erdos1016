#!/usr/bin/env python3
"""Exact cycle-space checks of the four-cut sharp-order examples."""

import itertools
import json
from pathlib import Path

from check_cubic_edge_frequency import cycle_space_cycles
from check_second_order_constructions import hk_even
from check_second_order_path_gap import capped_ladder


def main():
    rings = []
    for q in range(2, 8):
        n, edges = hk_even(q)
        cycles, _ = cycle_space_cycles(n, edges)
        expected = 4 ** q + (4 * q + 1) * 2 ** (q - 1) - 3 * q
        assert len(cycles) == expected
        ring_square = set(range(4))
        cut = [(u, v) for u, v in edges if (u in ring_square) != (v in ring_square)]
        assert len(cut) == 4
        assert any(vertices & 15 == 0 for _, vertices in cycles)
        rings.append({'squares': q, 'rank': 2 * q + 1,
                      'cycles': len(cycles), 'excess': len(cycles) - 4 ** q})

    caps = []
    for m in range(1, 7):
        n, edges, a, c, _, _ = capped_ladder((2,) * m)
        cycles, _ = cycle_space_cycles(n, edges)
        left = [vertices for _, vertices in cycles if vertices >> a & 1]
        right = [vertices for _, vertices in cycles if vertices >> c & 1]
        disjoint_caps = sum(not (u & v) for u in left for v in right)
        expected = (m - 2) * 2 ** (m + 1) + 4
        assert disjoint_caps == expected
        # These are unordered two-cycle unions: the two terminal labels identify their order.
        all_two_cycle_unions = sum(not (u & v) for (_, u), (_, v)
                                   in itertools.combinations(cycles, 2))
        assert all_two_cycle_unions >= disjoint_caps
        caps.append({'square_blocks': m, 'rank': 2 * m + 1,
                     'cycles': len(cycles),
                     'disjoint_terminal_cap_cycles': disjoint_caps,
                     'all_two_cycle_unions': all_two_cycle_unions})

    result = {'status': 'all exact sharp-order family checks passed',
              'cyclic_square_cycle_counts': rings,
              'capped_square_two_cycle_packings': caps}
    output = Path(__file__).with_name('four-cut-sharp-order-checks.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
