#!/usr/bin/env python3
"""Independently reconstruct the C7 shore and its 42-row exact cap dual."""
import collections
import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def matchings(vertices):
    if not vertices:
        return [()]
    a = vertices[0]
    return [tuple(sorted(((a, b),)+tail))
            for b in vertices[1:]
            for tail in matchings(tuple(v for v in vertices if v not in (a, b)))]


def canonical(edges):
    return tuple(sorted(tuple(sorted(edge)) for edge in edges))


def compatible(alpha, beta):
    vertices = {v for edge in alpha for v in edge}
    reached = {next(iter(vertices))}
    while True:
        larger = reached | {v for edge in alpha+beta if set(edge) & reached for v in edge}
        if larger == reached:
            return reached == vertices
        reached = larger


def main():
    folder = Path(__file__).parent
    data = json.loads((folder/'random-seven-cycle-integer-dual.json').read_text())
    n = 7
    all_matchings = [alpha for size in (2, 4, 6)
                     for subset in itertools.combinations(range(n), size)
                     for alpha in matchings(subset)]
    cap_coefficients = collections.defaultdict(F)
    for mask in range(1, (1 << n)-1):
        adjacency = [[] for _ in range(n)]
        for u in range(n):
            if mask & (1 << u):
                v = (u+1) % n
                adjacency[u].append(v)
                adjacency[v].append(u)
        endpoints = [v for v in range(n) if len(adjacency[v]) == 1]
        pairs = []
        used = set()
        for start in endpoints:
            if start in used:
                continue
            previous, at = -1, start
            while True:
                nxt = next((v for v in adjacency[at] if v != previous), None)
                if nxt is None:
                    break
                previous, at = at, nxt
            pairs.append((start, at))
            used.update((start, at))
        cap_coefficients[canonical(pairs)] += F(1, 2)

    dual = collections.defaultdict(F)
    rhs = F(0)
    kinds = collections.Counter()
    for item in data['nonzero_dual']:
        weight = F(item['weight'])
        assert weight == F(1, 2)
        label = item['label']
        terminal = tuple(label['terminal'])
        local = collections.Counter()
        if 'matching' in label:
            alpha = canonical(label['matching'])
            assert terminal in alpha
            rest = tuple(edge for edge in alpha if edge != terminal)
            for size in range(len(rest)+1):
                for subset in itertools.combinations(rest, size):
                    local[canonical((terminal,)+subset)] += 1
            bound = F(2)**(len(alpha)-2)
            kinds[f'matching_{len(alpha)}'] += 1
        else:
            kind = label['kind']
            kinds[kind] += 1
            local[canonical((terminal,))] += 1
            if kind == 'star':
                for edge in itertools.combinations(label['capped'], 2):
                    local[canonical((terminal, edge))] += 1
                bound = F(2)
            elif kind == 'binary':
                pairing = canonical(label['pairing'])
                ports = tuple(sorted(v for edge in pairing for v in edge))
                for edge in itertools.combinations(ports, 2):
                    local[canonical((terminal, edge))] += 1
                local[canonical((terminal,)+pairing)] += 1
                bound = F(4)
            else:
                assert kind == 'star_edge'
                added = tuple(label['edge'])
                local[canonical((terminal, added))] += 1
                for edge in itertools.combinations(label['capped'], 2):
                    local[canonical((terminal, edge))] += 1
                    local[canonical((terminal, edge, added))] += 1
                bound = F(4)
        for matching, coefficient in local.items():
            assert len({v for edge in matching for v in edge}) == 2*len(matching)
            dual[matching] += weight*coefficient
        rhs += weight*bound
    assert rhs == F(63, 2)
    assert all(dual[alpha] == cap_coefficients[alpha] for alpha in all_matchings)
    actual_coordinates = 0
    for beta in all_matchings:
        vertices = {v for edge in beta for v in edge}
        options = [alpha for alpha in all_matchings if {v for edge in alpha for v in edge} == vertices]
        lhs = sum(dual[alpha] for alpha in options if compatible(alpha, beta))
        target = sum(cap_coefficients[alpha] for alpha in options if compatible(alpha, beta))
        assert lhs == target
        actual_coordinates += 1
    result = dict(status='independent exact C7 cap certificate passed',
                  actual_cycle_edge_subsets=126, formal_rho_coordinates=len(all_matchings),
                  actual_forest_coordinates=actual_coordinates, dual_rows=len(data['nonzero_dual']),
                  dual_types=dict(kinds), exact_bound=str(rhs),
                  author_modules_imported=False, numerical_solver_used=False)
    (folder/'path-six-seven-cycle-dual-checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
