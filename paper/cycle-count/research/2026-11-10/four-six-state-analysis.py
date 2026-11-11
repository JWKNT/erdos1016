#!/usr/bin/env python3
"""Exploratory two-shore six-cut optimization. Numerical output is not proof."""

import argparse
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

PORTS = tuple(range(6))
PAIRS = tuple(itertools.combinations(PORTS, 2))
PAIR_INDEX = {edge: i for i, edge in enumerate(PAIRS)}
FOURS = tuple(itertools.combinations(PORTS, 4))


def matchings(vertices):
    if not vertices:
        yield ()
        return
    first = vertices[0]
    for other in vertices[1:]:
        for tail in matchings(tuple(v for v in vertices if v not in (first, other))):
            yield tuple(sorted(((first, other),) + tail))


M4 = tuple(tuple(matchings(s)) for s in FOURS)
M6 = tuple(matchings(PORTS))


def noncap(first, second):
    subset = tuple(sorted(first + second))
    s = FOURS.index(subset)
    pairing = M4[s].index(tuple(sorted((first, second))))
    row = np.zeros(75)
    row[15 + 3 * s:18 + 3 * s] = 1
    row[15 + 3 * s + pairing] = 0
    return row


def compatible_row(matching):
    row = np.zeros(75)
    for j, other in enumerate(M6):
        if set(matching).isdisjoint(other):
            row[60 + j] = 1
    return row


def polytope(aggregate=True):
    rows, bounds, labels = [], [], []
    def add(row, bound, label):
        rows.append(row)
        bounds.append(bound)
        labels.append(label)
    for s, subset in enumerate(FOURS):
        row = np.zeros(75)
        row[15 + 3 * s:18 + 3 * s] = 1
        add(row, 1, ('forest', subset))
        for pairing in M4[s]:
            for edge in pairing:
                row = noncap(*pairing)
                row[PAIR_INDEX[edge]] += 1
                add(row, 1, ('one_added', pairing, edge))
    row = np.zeros(75)
    row[60:] = 1
    add(row, 1, ('six_forest',))
    for matching in M6:
        for terminal in matching:
            row = compatible_row(matching)
            row[PAIR_INDEX[terminal]] += 1
            for edge in matching:
                if edge != terminal:
                    row += noncap(terminal, edge)
            add(row, 2, ('two_added', matching, terminal))
    if aggregate:
        add(np.ones(75), 16, ('aggregate',))
    return np.array(rows), np.array(bounds), labels


def gluing_matrix():
    matrix = np.zeros((75, 75))
    matrix[:15, :15] = np.eye(15)
    for s in range(15):
        start = 15 + 3 * s
        matrix[start:start + 3, start:start + 3] = np.ones((3, 3)) - np.eye(3)
    for i, matching in enumerate(M6):
        for j, other in enumerate(M6):
            matrix[60 + i, 60 + j] = set(matching).isdisjoint(other)
    return matrix


def summarize(vector):
    return {'paths': vector[:15].tolist(),
            'four_pairings': vector[15:60].reshape(15, 3).tolist(),
            'six_pairings': vector[60:].tolist()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--starts', type=int, default=200)
    parser.add_argument('--seed', type=int, default=20261111)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('four-six-bilinear-exploration.json'))
    args = parser.parse_args()
    matrix, rhs, _ = polytope()
    coupling = gluing_matrix()
    variable_bounds = [(0, .5)] * 15 + [(0, None)] * 60
    rng = np.random.default_rng(args.seed)

    def optimize(objective):
        result = linprog(-objective, A_ub=matrix, b_ub=rhs,
                         bounds=variable_bounds, method='highs')
        assert result.success, result.message
        return result.x

    results = []
    best = None
    for start in range(args.starts):
        # Positive starts favor states with substantial forest mass.
        objective = rng.uniform(0, 1, 75) if start % 2 else rng.normal(size=75)
        right = optimize(objective)
        history = []
        for iteration in range(100):
            left = optimize(coupling @ right)
            right = optimize(coupling @ left)
            value = float(left @ coupling @ right)
            history.append(value)
            if len(history) > 1 and history[-1] <= history[-2] + 1e-9:
                break
        row = {'start': start, 'iterations': len(history), 'value': value}
        results.append(row)
        if best is None or value > best['value'] + 1e-8:
            best = dict(row, left=summarize(left), right=summarize(right),
                        left_mass=float(sum(left)), right_mass=float(sum(right)))
            print(json.dumps({'new_best': value, 'start': start}), flush=True)
    output = {'status': 'numerical alternating-LP evidence only; no global upper bound',
              'starts': args.starts, 'seed': args.seed, 'best': best,
              'outcomes': results}
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({'best_value': best['value'],
                      'distinct_final_values': sorted(set(round(r['value'], 9) for r in results))},
                     indent=2))


if __name__ == '__main__':
    main()
