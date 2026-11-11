#!/usr/bin/env python3
"""Exact six-cut gluing and two-edge augmentation checks, plus an LP obstruction."""
import itertools
import json
from fractions import Fraction
from pathlib import Path
from check_second_order_saturated_blocks import paths, cycles

V = tuple(range(6))
PAIRS = tuple(itertools.combinations(V, 2))
FOURS = tuple(itertools.combinations(V, 4))


def matchings(vertices):
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for b in vertices[1:]:
        for tail in matchings(tuple(v for v in vertices if v not in (a, b))):
            yield tuple(sorted(((a, b),)+tail))


M4 = {S: tuple(matchings(S)) for S in FOURS}
M6 = tuple(matchings(V))


def forest_states(n, edges, ports):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i)); adj[v].append((u, i))
    parent = {0: (-1, -1)}; order = [0]; roots = [0]*n
    for u in order:
        for v, e in adj[u]:
            if v not in parent:
                parent[v] = (u, e); order.append(v)
                roots[v] = roots[u] ^ (1 << e)
    tree = {e for _, e in parent.values()}
    basis = [roots[u] ^ roots[v] ^ (1 << e)
             for e, (u, v) in enumerate(edges) if e not in tree]
    base = 0
    for p in ports:
        base ^= roots[p]
    result = {matching: 0 for matching in matchings(tuple(range(len(ports))))}
    for word in range(1 << len(basis)):
        mask = base
        for i, support in enumerate(basis):
            if word >> i & 1:
                mask ^= support
        uf = list(range(n))
        def find(v):
            while uf[v] != v:
                uf[v] = uf[uf[v]]; v = uf[v]
            return v
        cyclic = False
        for i, (u, v) in enumerate(edges):
            if mask >> i & 1:
                a, b = find(u), find(v)
                if a == b:
                    cyclic = True; break
                uf[a] = b
        if cyclic:
            continue
        components = {}
        for i, p in enumerate(ports):
            components.setdefault(find(p), []).append(i)
        assert all(len(part) == 2 for part in components.values())
        key = tuple(sorted(tuple(part) for part in components.values()))
        result[key] += 1
    return result


def state(graph, order):
    n, edges, port_vertices = graph
    ports = [port_vertices[i] for i in order]
    pair = {e: paths(n, edges, ports[e[0]], ports[e[1]]) for e in PAIRS}
    four = {}
    for S in FOURS:
        local = forest_states(n, edges, [ports[i] for i in S])
        four[S] = {tuple(sorted(tuple(S[i] for i in edge) for edge in matching)): count
                   for matching, count in local.items()}
    six = forest_states(n, edges, ports)
    return pair, four, six


def noncap(four, e, f):
    S = tuple(sorted(e+f)); matching = tuple(sorted((e, f)))
    return sum(four[S].values())-four[S][matching]


def check_relaxation(folder):
    numerical = json.loads((folder/'six-cut-augmentation-exploration.json').read_text())
    half = lambda x: Fraction(round(2*x), 2)
    p = dict(zip(PAIRS, map(half, numerical['paths'])))
    f = {S: dict(zip(M4[S], map(half, numerical['four_pairings'][s])))
         for s, S in enumerate(FOURS)}
    t = dict(zip(M6, map(half, numerical['six_pairings'])))
    assert all(0 <= x <= Fraction(1, 2) for x in p.values())
    assert all(all(x >= 0 for x in sector.values()) and sum(sector.values()) <= 1
               for sector in f.values())
    assert all(x >= 0 for x in t.values()) and sum(t.values()) <= 1
    assert sum(p.values())+sum(map(lambda s: sum(s.values()), f.values()))+sum(t.values()) == 16
    one = two = 0
    for S in FOURS:
        for matching in M4[S]:
            for e in matching:
                other = next(edge for edge in matching if edge != e)
                assert p[e]+noncap(f, e, other) <= 1
                one += 1
    for matching in M6:
        compatible = sum(t[other] for other in M6 if set(matching).isdisjoint(other))
        for e in matching:
            value = p[e]+compatible+sum(noncap(f, e, other) for other in matching if other != e)
            assert value <= 2
            two += 1
    target = M6[0]
    objective = sum(p.values())+sum(sum(s.values())-min(s.values()) for s in f.values())
    objective += sum(t[other] for other in M6 if set(target).isdisjoint(other))
    assert objective == 16
    return dict(status='exact feasible relaxation witness; no graph realization claimed',
                objective=16, one_edge_constraints=one, two_edge_constraints=two,
                path_sum=str(sum(p.values())),
                four_forest_sum=str(sum(sum(s.values()) for s in f.values())),
                six_forest_sum=str(sum(t.values())),
                path_counts_times_two=[int(2*p[e]) for e in PAIRS],
                four_counts_times_two=[[int(2*f[S][m]) for m in M4[S]] for S in FOURS],
                six_counts_times_two=[int(2*t[m]) for m in M6])


def main():
    folder = Path(__file__).resolve().parent
    graphs = [
        (6, [(i, (i+1)%6) for i in range(6)], list(range(6))),
        (8, [(i, (i+1)%8) for i in range(8)]+[(0, 4)], [1, 2, 3, 5, 6, 7]),
        (8, [(i, (i+1)%4) for i in range(4)]+[(4+i, 4+(i+1)%4) for i in range(4)]+[(3, 4)],
         [0, 1, 2, 5, 6, 7]),
        (10, [(i, (i+1)%10) for i in range(10)]+[(0, 4), (5, 9)], [1, 2, 3, 6, 7, 8]),
    ]
    permutations = tuple(itertools.permutations(V))[::12]
    states = {(i, p): state(g, p) for i, g in enumerate(graphs) for p in permutations}
    internal = [cycles(n, e) for n, e, _ in graphs]
    augmentations = gluings = 0
    for i, (n, edges, ports) in enumerate(graphs):
        p, f, t = states[i, V]
        for matching in M6:
            compatible = sum(t[other] for other in M6 if set(matching).isdisjoint(other))
            for terminal in matching:
                added = [edge for edge in matching if edge != terminal]
                prediction = p[terminal]+sum(noncap(f, terminal, edge) for edge in added)+compatible
                actual_edges = edges+[(ports[a], ports[b]) for a, b in added]
                assert paths(n, actual_edges, ports[terminal[0]], ports[terminal[1]]) == prediction
                augmentations += 1
        for j, (m, other, other_ports) in enumerate(graphs):
            for perm in permutations:
                q, g, u = states[j, perm]
                prediction = internal[i]+internal[j]+sum(p[e]*q[e] for e in PAIRS)
                prediction += sum(sum(f[S].values())*sum(g[S].values())
                                  -sum(f[S][a]*g[S][a] for a in M4[S]) for S in FOURS)
                prediction += sum(t[a]*u[b] for a in M6 for b in M6 if set(a).isdisjoint(b))
                joined = edges+[(a+n, b+n) for a, b in other]
                joined += [(ports[v], n+other_ports[perm[v]]) for v in V]
                assert cycles(n+m, joined) == prediction, (i, j, perm)
                gluings += 1
    result = dict(status='exact checks passed', shore_graphs=len(graphs),
                  gluing_checks=gluings, two_edge_augmentation_checks=augmentations,
                  relaxation_witness=check_relaxation(folder))
    destination = folder/'six-cut-state-checks.json'
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'relaxation_witness'}))


if __name__ == '__main__':
    main()
