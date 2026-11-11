#!/usr/bin/env python3
"""Independent exact C6 objective reconstruction and dual verification."""
import collections
import itertools
import json
from fractions import Fraction
from pathlib import Path


def pairings(vertices):
    if not vertices:
        return [()]
    first = vertices[0]
    result = []
    for second in vertices[1:]:
        remaining = tuple(v for v in vertices if v not in (first, second))
        for tail in pairings(remaining):
            result.append(tuple(sorted(((first, second),)+tail)))
    return result


def main():
    folder = Path(__file__).parent
    certificate = json.loads((folder/'six-cycle-shore-rational-dual.json').read_text())
    vertices = tuple(range(6))
    pairs = tuple(itertools.combinations(vertices, 2))
    fours = tuple(itertools.combinations(vertices, 4))
    m4 = {s: pairings(s) for s in fours}
    m6 = pairings(vertices)
    keys = [('path', e) for e in pairs]
    keys += [('four', s, alpha) for s in fours for alpha in m4[s]]
    keys += [('six', alpha) for alpha in m6]
    profile = collections.Counter()
    cycle_edges = [(i, (i+1) % 6) for i in range(6)]
    for mask in range(1, 63):
        adjacency = [[] for _ in vertices]
        for i, (u, v) in enumerate(cycle_edges):
            if mask & (1 << i):
                adjacency[u].append(v)
                adjacency[v].append(u)
        endpoints = tuple(v for v in vertices if len(adjacency[v]) == 1)
        matching = []
        used = set()
        for endpoint in endpoints:
            if endpoint in used:
                continue
            previous, at = -1, endpoint
            while True:
                nxt = next((v for v in adjacency[at] if v != previous), None)
                if nxt is None:
                    break
                previous, at = at, nxt
            matching.append(tuple(sorted((endpoint, at))))
            used.update((endpoint, at))
        profile[(endpoints, tuple(sorted(matching)))] += 1

    objective = collections.defaultdict(Fraction)
    for (endpoints, alpha), count in profile.items():
        if len(endpoints) == 2:
            objective[('path', endpoints)] += Fraction(count, 2)
        elif len(endpoints) == 4:
            for beta in m4[endpoints]:
                if beta != alpha:
                    objective[('four', endpoints, beta)] += Fraction(count, 2)
        else:
            assert len(endpoints) == 6
            for beta in m6:
                if set(alpha).isdisjoint(beta):
                    objective[('six', beta)] += Fraction(count, 2)

    combined = collections.defaultdict(Fraction)
    bound = Fraction(0)
    kinds = collections.Counter()

    def noncap(e, f, weight):
        subset = tuple(sorted(e+f))
        cap = tuple(sorted((e, f)))
        for beta in m4[subset]:
            if beta != cap:
                combined[('four', subset, beta)] += weight

    for term in certificate['nonzero_dual']:
        weight = Fraction(term['weight'])
        assert weight >= 0
        kind, *data = term['label']
        kinds[kind] += 1
        if kind == 'path':
            e = tuple(data[0])
            combined[('path', e)] += weight
            bound += weight/2
        elif kind == 'one_edge':
            e, f = map(tuple, data)
            assert set(e).isdisjoint(f)
            combined[('path', e)] += weight
            noncap(e, f, weight)
            bound += weight
        else:
            assert kind == 'two_edges'
            e = tuple(data[0])
            added = [tuple(f) for f in data[1]]
            alpha = tuple(sorted([e]+added))
            assert alpha in m6
            combined[('path', e)] += weight
            for f in added:
                noncap(e, f, weight)
            for beta in m6:
                if set(alpha).isdisjoint(beta):
                    combined[('six', beta)] += weight
            bound += 2*weight
    assert all(combined[key] == objective[key] for key in keys)
    assert bound == Fraction(31, 2)
    result = dict(status='independent exact dual verification passed',
                  method='Reconstruct C6 states by all62 nonempty proper edge subsets; reconstruct inequalities directly from matching definitions.',
                  variables=len(keys), dual_terms=dict(kinds),
                  bound=str(bound), coefficient_equality=True,
                  imported_author_modules=False, used_numerical_solver=False)
    (folder/'path-six-cycle-dual-checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
