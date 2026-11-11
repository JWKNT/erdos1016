"""Solver-free exact certificate for a cubic mean-cycle-length counterexample."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


POLE_EDGES = [(1, 5), (1, 7), (1, 8), (2, 6), (2, 8), (2, 11),
              (3, 7), (3, 9), (3, 11), (4, 8), (4, 9), (5, 10),
              (5, 11), (6, 9), (6, 10)]
PORTS = [4, 7, 10]
BASIS = [22568, 31104, 28165, 9752, 4419]


def adjacency(edges):
    result = {}
    for a, b in edges:
        result.setdefault(a, []).append(b)
        result.setdefault(b, []).append(a)
    return result


def paths(adj, start, end):
    def visit(route, seen):
        v = route[-1]
        if v == end:
            yield tuple(route)
            return
        for w in adj[v]:
            if w not in seen:
                yield from visit(route + [w], seen | {w})
    yield from visit([start], {start})


def cycles(adj):
    for start in sorted(adj):
        def visit(route, seen):
            v = route[-1]
            for w in adj[v]:
                if w == start and len(route) >= 3 and route[1] < route[-1]:
                    yield tuple(route)
                elif w > start and w not in seen:
                    yield from visit(route + [w], seen | {w})
        yield from visit([start], {start})


def edge_set(route, closed=False):
    if closed:
        route = route + (route[0],)
    return {tuple(sorted(e)) for e in zip(route, route[1:])}


def connected_after(edges, deleted):
    adj = adjacency(e for e in edges if e not in deleted)
    if len(adj) != 66:
        return False
    seen, stack = set(), [next(iter(adj))]
    while stack:
        v = stack.pop()
        if v not in seen:
            seen.add(v)
            stack.extend(adj[v])
    return len(seen) == 66


def girth(adj):
    best = len(adj) + 1
    for start in adj:
        distance = {start: 0}
        parent = {start: None}
        queue = [start]
        for v in queue:
            for w in adj[v]:
                if w not in distance:
                    distance[w], parent[w] = distance[v] + 1, v
                    queue.append(w)
                elif parent[v] != w:
                    best = min(best, distance[v] + distance[w] + 1)
    return best


def main():
    pole_adj = adjacency(POLE_EDGES)
    pole_cycles = list(cycles(pole_adj))
    pole_paths = {pair: list(paths(pole_adj, *pair)) for pair in combinations(PORTS, 2)}
    p = {pair: len(routes) for pair, routes in pole_paths.items()}
    lengths = {pair: sum(len(route) - 1 for route in routes)
               for pair, routes in pole_paths.items()}
    assert len(pole_cycles) == 29
    assert sum(map(len, pole_cycles)) == 219
    assert list(p.values()) == [26, 27, 27]
    assert list(lengths.values()) == [190, 197, 197]
    assert girth(pole_adj) == 5

    # Independent affine-space verification of the five-vector certificate.
    states = {0}
    for vector in BASIS:
        states |= {state ^ vector for state in list(states)}
    assert len(states) == 32
    index = {edge: i for i, edge in enumerate(POLE_EDGES)}
    for state in states:
        degrees = Counter()
        for i, (a, b) in enumerate(POLE_EDGES):
            if state >> i & 1:
                degrees[a] += 1
                degrees[b] += 1
        assert all(degree % 2 == 0 for degree in degrees.values())
    for cycle in pole_cycles:
        mask = sum(1 << index[edge] for edge in edge_set(cycle, True))
        assert mask in states
    for pair, routes in pole_paths.items():
        masks = [sum(1 << index[edge] for edge in edge_set(route)) for route in routes]
        assert all(mask ^ masks[0] in states for mask in masks)

    base_edges = [(a, b) for a in range(3) for b in range(3, 6)]
    base_adj = adjacency(base_edges)
    port_at = {v: {w: PORTS[i] for i, w in enumerate(sorted(base_adj[v]))}
               for v in base_adj}
    full_edges = [tuple(sorted(((v, a), (v, b))))
                  for v in base_adj for a, b in POLE_EDGES]
    full_edges += [tuple(sorted(((v, port_at[v][w]), (w, port_at[w][v]))))
                   for v, w in base_edges]
    full_adj = adjacency(full_edges)
    assert len(full_adj) == 66 and len(full_edges) == 99
    assert len(set(full_edges)) == 99
    assert all(len(neighbors) == 3 for neighbors in full_adj.values())
    assert girth(full_adj) == 5
    connectivity_checks = 0
    for deleted in combinations(full_edges, 2):
        assert connected_after(full_edges, set(deleted))
        connectivity_checks += 1

    count = 6 * len(pole_cycles)
    total_length = 6 * sum(map(len, pole_cycles))
    edge_frequency = Counter()
    for v in base_adj:
        for cycle in pole_cycles:
            for a, b in edge_set(cycle, True):
                edge_frequency[tuple(sorted(((v, a), (v, b))))] += 1
    for cycle in cycles(base_adj):
        local_pairs = {}
        for i, v in enumerate(cycle):
            previous, following = cycle[i - 1], cycle[(i + 1) % len(cycle)]
            local_pairs[v] = tuple(sorted((port_at[v][previous], port_at[v][following])))
        multiplicity = 1
        for pair in local_pairs.values():
            multiplicity *= p[pair]
        count += multiplicity
        total_length += len(cycle) * multiplicity
        for v, pair in local_pairs.items():
            cofactor = multiplicity // p[pair]
            total_length += cofactor * lengths[pair]
            for route in pole_paths[pair]:
                for a, b in edge_set(route):
                    edge_frequency[tuple(sorted(((v, a), (v, b))))] += cofactor
        for v, w in edge_set(cycle, True):
            edge_frequency[tuple(sorted(((v, port_at[v][w]), (w, port_at[w][v]))))] += multiplicity
    assert count == 2160078826
    assert total_length == 107497549026
    assert sum(edge_frequency.values()) == total_length
    assert 4 * total_length - 3 * 66 * count == 2294588556
    minimum_edge = min(edge_frequency, key=edge_frequency.get)
    assert 2 * edge_frequency[minimum_edge] <= count
    result = {
        "status": "PASS", "pole_edges": POLE_EDGES, "ports": PORTS,
        "cycle_basis_masks": BASIS,
        "pole_cycle_polynomial": dict(sorted(Counter(map(len, pole_cycles)).items())),
        "pole_path_polynomials": [
            {"pair": pair, "polynomial": dict(sorted(Counter(len(route)-1 for route in routes).items())),
             "count": p[pair], "length_sum": lengths[pair]}
            for pair, routes in pole_paths.items()],
        "vertices": 66, "edges": full_edges, "girth": 5,
        "edge_connectivity": 3, "two_edge_deletion_checks": connectivity_checks,
        "cycle_count": count, "cycle_length_sum": total_length,
        "mean_cycle_length": str(Fraction(total_length, count)),
        "fourfold_mean_excess": 4 * total_length - 3 * 66 * count,
        "edge_half_witness": {"edge": minimum_edge, "cycle_frequency": edge_frequency[minimum_edge]},
    }
    target = Path(__file__).with_suffix(".json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "vertices", "girth", "edge_connectivity",
                     "two_edge_deletion_checks", "cycle_count", "cycle_length_sum",
                     "fourfold_mean_excess", "edge_half_witness"]}, indent=2))


if __name__ == "__main__":
    main()
