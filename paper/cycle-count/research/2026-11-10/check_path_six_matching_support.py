#!/usr/bin/env python3
"""Exact standard-library check of six-terminal compatibility supports."""

import json
from collections import Counter
from itertools import combinations
from pathlib import Path


def matchings(vertices):
    if not vertices:
        yield ()
        return
    first, *rest = vertices
    for partner in rest:
        remaining = [v for v in rest if v != partner]
        for suffix in matchings(remaining):
            yield ((first, partner),) + suffix


def main():
    states = list(matchings(list(range(6))))
    neighbors = [
        {j for j, other in enumerate(states) if set(state).isdisjoint(other)}
        for state in states
    ]
    assert len(states) == 15
    assert all(len(n) == 8 for n in neighbors)
    pair_counts = Counter()
    triple_counts = Counter()
    for a, b in combinations(range(15), 2):
        count = len(neighbors[a] & neighbors[b])
        assert count == 4
        pair_counts[count] += 1
    for a, b, c in combinations(range(15), 3):
        count = len(neighbors[a] & neighbors[b] & neighbors[c])
        assert count in (0, 2)
        triple_counts[count] += 1
    result = {
        "matching_states": len(states),
        "compatible_partners_per_state": 8,
        "pair_common_partner_counts": dict(sorted(pair_counts.items())),
        "triple_common_partner_counts": dict(sorted(triple_counts.items())),
        "all_checks_passed": True,
    }
    output = Path(__file__).with_name("path-six-matching-support-checks.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
