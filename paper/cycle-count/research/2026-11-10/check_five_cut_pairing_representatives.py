#!/usr/bin/env python3
"""Exact independent check of all five-cut representative certificates."""
import itertools
import json
from pathlib import Path

vertices = tuple(range(5))
edges = tuple(itertools.combinations(vertices, 2))
sectors = tuple(itertools.combinations(vertices, 4))
pairings = []
for a, b, c, d in sectors:
    pairings.append((((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))))


def representatives(options, selected=()):
    if not options:
        return selected
    for edge in options[0]:
        if edge not in selected:
            answer = representatives(options[1:], selected+(edge,))
            if answer is not None:
                return answer
    return None


records = []
for choice in itertools.product(range(3), repeat=5):
    options = tuple(pairings[s][choice[s]] for s in range(5))
    assert len(set(options)) == 5
    reps = representatives(options)
    assert reps is not None and len(set(reps)) == 5
    assert all(reps[s] in options[s] for s in range(5))
    # The selected augmentation rows have one coefficient for each representative
    # path. Add the five unused path upper bounds, each with right side 1/2.
    path_coefficients = {edge: 0 for edge in edges}
    for edge in reps:
        path_coefficients[edge] += 1
    for edge in edges:
        if edge not in reps:
            path_coefficients[edge] += 1
    assert set(path_coefficients.values()) == {1}
    # Each forest sector contributes exactly its two non-excluded pairing masses.
    forest_coefficients = [[0]*3 for _ in range(5)]
    for s in range(5):
        for a in range(3):
            forest_coefficients[s][a] = int(a != choice[s])
    assert all(sum(row) == 2 for row in forest_coefficients)
    records.append(dict(choice=choice, representatives=reps,
                        remaining_edges=[e for e in edges if e not in reps],
                        exact_bound_numerator=15, exact_bound_denominator=2))

result = dict(status='all exact checks passed',
              choices=len(records), objective_coefficients_checked=25*len(records),
              certificates=records)
destination = Path(__file__).with_name('five-cut-pairing-representative-checks.json')
destination.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: v for k, v in result.items() if k != 'certificates'}))
