#!/usr/bin/env python3
"""Exact finite checks for the one-full tripole sum lemma."""
import json
from check_second_order_path_gap import compositions, capped_ladder
from check_second_order_saturated_blocks import paths


def main():
    rows = []
    maximum = (0.0, None)
    for k in range(1, 11):
        checked = 0
        for blocks in compositions(k):
            n, edges, a, c, _, _ = capped_ladder(blocks)
            h = len(edges) - n + 1
            for i, (u, v) in enumerate(edges):
                new = edges[:i] + edges[i+1:] + [(u, n), (n, v)]
                left = paths(n+1, new, a, n)
                right = paths(n+1, new, n, c)
                excess = max(0, left + right - 2**h)
                assert excess**2 <= 36 * 2**h
                assert min(left, right)**4 <= 81 * 2**(3*h)
                ratio = excess / 2**(h/2)
                if ratio > maximum[0]:
                    maximum = (ratio, dict(blocks=blocks, edge=i, rank=h,
                                           left_paths=left, right_paths=right))
                for side_rank in range(1, 9):
                    total_rank = h + side_rank
                    excess = max(0, left + 2**side_rank * right - 2**total_rank)
                    assert excess**2 <= 36 * 2**total_rank
                    excess = max(0, right + 2**side_rank * left - 2**total_rank)
                    assert excess**2 <= 36 * 2**total_rank
                    assert min(left, 2**side_rank*right)**4 <= 81 * 2**(3*total_rank)
                    assert min(right, 2**side_rank*left)**4 <= 81 * 2**(3*total_rank)
                checked += 1
        rows.append(dict(positions=k, subdivision_checks=checked,
                         side_rank_checks=16*checked))
    # A subdivided edge of a digon gives a triangle.
    assert paths(3, [(0, 1), (0, 2), (2, 1)], 0, 2) == 2
    print(json.dumps(dict(checks=rows, maximum_observed_excess=maximum), indent=2))


if __name__ == '__main__':
    main()
