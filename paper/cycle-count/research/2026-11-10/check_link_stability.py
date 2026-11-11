"""Exact finite checks of the inverse small-cut theorem.

The cases include loops and parallel edges. They test the proof inequalities,
not the asymptotic assertions or a general decomposition theorem.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import random
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'paper-checks'))
from lib import cyc_basis, span, is_forest


def links(n, edges, a, b):
    rest = set(range(n)) - a - b
    adj = {v: set() for v in rest}
    direct = 0
    for u, v in edges:
        direct += (u in a and v in b) or (u in b and v in a)
        if u in rest and v in rest:
            adj[u].add(v)
            adj[v].add(u)
    count = direct
    while rest:
        stack = [rest.pop()]
        comp = set(stack)
        while stack:
            u = stack.pop()
            for v in adj[u] & rest:
                rest.remove(v)
                comp.add(v)
                stack.append(v)
        toa = tob = False
        for u, v in edges:
            toa |= (u in comp and v in a) or (v in comp and u in a)
            tob |= (u in comp and v in b) or (v in comp and u in b)
        count += toa and tob
    return count


def check(n, edges, regions):
    zs = span(cyc_basis(n, edges))
    k = len(regions)
    cuts = [sum(1 << j for j, (u, v) in enumerate(edges) if (u in a) != (v in a)) for a in regions]
    ins = [sum(1 << j for j, (u, v) in enumerate(edges) if u in a and v in a) for a in regions]
    d = max(x.bit_count() for x in cuts)
    delta = max(d - 2, 0)
    K = 1 + delta
    flags = [[not (z & cuts[i]) and bool(z & ins[i]) for i in range(k)] for z in zs]
    probs = [Q(sum(row[i] for row in flags), len(zs)) for i in range(k)]
    mu = sum(probs)
    assert all(p >= Q(1, 2**d) for p in probs)
    vals = [sum(row) for row in flags]
    moment = Q(sum(z*z for z in vals), len(zs))
    nu = Q(sum(z > 0 for z in vals), len(zs))
    f = Q(sum(all(is_forest(n, edges, z & mask) for mask in ins) for z in zs), len(zs))
    ls = {(i,j): links(n, edges, regions[i], regions[j]) for i in range(k) for j in range(k) if i != j}
    one = sum(probs[i]*probs[j] for (i,j), l in ls.items() if l == 1) / mu**2
    two = sum(probs[i]*probs[j] for (i,j), l in ls.items() if l == 2) / mu**2
    for i in range(k):
        assert sum(ls[i,j] >= 3 for j in range(k) if i != j) <= delta
    for (i,j), l in ls.items():
        joint = Q(sum(row[i] and row[j] for row in flags), len(zs))
        assert joint == 2**(l-1)*probs[i]*probs[j]
    assert moment <= 2*mu**2-one*mu**2+K*mu
    assert 1/(2+K/mu) <= nu
    if f > 0:
        eta = max(Q(0), Q(1,2)-f)
        assert one <= 4*eta/(1+2*eta)+K/mu
        assert two >= 1-4*eta/(1+2*eta)-2*K/mu
        assert nu*moment/mu**2-1 <= 2*eta+(Q(1,2)+eta)*K/mu
    return {'rank': len(cyc_basis(n, edges)), 'k': k, 'd': d, 'forest_probability': str(f)}


def main():
    rng = random.Random(101620261110)
    cases = []
    # Each region begins as a loop, a double edge, or a triangle.
    for trial in range(180):
        k = rng.randint(2, 5)
        regions, edges, n = [], [], 0
        for _ in range(k):
            size = rng.randint(1, 3)
            vertices = list(range(n, n+size))
            regions.append(set(vertices))
            edges.extend((vertices[j], vertices[(j+1)%size]) for j in range(size))
            n += size
        for i in range(1, k):
            edges.append((rng.choice(sorted(regions[i])), rng.choice(sorted(regions[rng.randrange(i)]))))
        for _ in range(rng.randint(0, 5)):
            edges.append(tuple(rng.sample(range(n), 2)))
        cases.append(check(n, edges, regions))
    result = {'seed': 101620261110, 'cases': len(cases), 'max_rank': max(x['rank'] for x in cases),
              'exact_rational_checks': True, 'status': 'PASS'}
    dest = Path(__file__).with_name('link-stability-results.json')
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
