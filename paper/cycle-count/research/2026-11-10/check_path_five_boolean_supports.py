#!/usr/bin/env python3
"""Exact independent enumeration of Boolean five-pole support constraints."""
import itertools
import json
from pathlib import Path

VERTICES = tuple(range(5))
EDGES = tuple(itertools.combinations(VERTICES, 2))
INDEX = {edge: index for index, edge in enumerate(EDGES)}
PERMUTATIONS = tuple(itertools.permutations(VERTICES))
FOUR_SETS = tuple(itertools.combinations(VERTICES, 4))


def canonical(edges):
    return min(sum(1 << INDEX[tuple(sorted((p[u], p[v])))]
                   for u, v in edges) for p in PERMUTATIONS)


def main():
    records = []
    seen = set()
    for mask in range(1 << len(EDGES)):
        edges = {edge for i, edge in enumerate(EDGES) if mask & (1 << i)}
        if any(set(itertools.combinations(triple, 2)) <= edges
               for triple in itertools.combinations(VERTICES, 3)):
            continue
        key = canonical(edges)
        if key in seen:
            continue
        seen.add(key)
        forbidden = []
        for subset in FOUR_SETS:
            reasons = []
            for left in itertools.combinations(subset, 2):
                right = set(subset) - set(left)
                crossing = sum(tuple(sorted((u, v))) in edges
                               for u in left for v in right)
                if crossing >= 3:
                    reasons.append("at least three full cross pairs")
                    break
            omitted = next(v for v in VERTICES if v not in subset)
            if all(tuple(sorted((omitted, v))) in edges for v in subset):
                reasons.append("four full arms from omitted center")
            if reasons:
                forbidden.append(dict(ports=subset, reasons=reasons))
        records.append(dict(edges=sorted(edges),
                            degrees=sorted(sum(v in edge for edge in edges)
                                           for v in VERTICES),
                            forbidden_forests=forbidden,
                            maximum_boolean_mass=len(edges)+5-len(forbidden)))
    survivors = [row for row in records if row["maximum_boolean_mass"] >= 8]
    expected = {(0, 1, 1, 1, 3), (0, 2, 2, 2, 2), (1, 1, 1, 1, 2),
                (1, 1, 1, 1, 4), (2, 2, 2, 3, 3)}
    assert {tuple(row["degrees"]) for row in survivors} == expected
    assert all(row["maximum_boolean_mass"] == 8 for row in survivors)
    result = dict(method="Exact enumeration of all 1,024 labeled edge masks; integer constraints only",
                  triangle_free_isomorphism_classes=len(records),
                  surviving_classes=len(survivors),
                  survivors=survivors, all_classes=records)
    output = Path(__file__).with_name("path-five-boolean-support-checks.json")
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key != "all_classes"}, indent=2))


if __name__ == "__main__":
    main()
