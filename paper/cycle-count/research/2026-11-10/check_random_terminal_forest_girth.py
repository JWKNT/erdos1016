#!/usr/bin/env python3
"""Exact checks of the translation and saturation identities; no packages."""
import itertools
import json
import random
from collections import deque
from pathlib import Path


def components(n, edges, deleted=frozenset()):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        if u not in deleted and v not in deleted:
            adj[u].append(v)
            adj[v].append(u)
    unseen = set(range(n)) - set(deleted)
    result = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        part = {root}
        queue = [root]
        for u in queue:
            for v in adj[u]:
                if v in unseen:
                    unseen.remove(v)
                    part.add(v)
                    queue.append(v)
        result.append(part)
    return result


def is_forest(n, edges):
    parent = list(range(n))
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for u, v in edges:
        a, b = find(u), find(v)
        if a == b:
            return False
        parent[a] = b
    return True


def audit(n, edges, ports):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    paths = {0: 0}
    tree = set()
    queue = [0]
    for u in queue:
        for v, i in adj[u]:
            if v not in paths:
                paths[v] = paths[u] ^ (1 << i)
                tree.add(i)
                queue.append(v)
    assert len(paths) == n
    basis = [paths[u] ^ paths[v] ^ (1 << i)
             for i, (u, v) in enumerate(edges) if i not in tree]
    states = [0]
    for cycle in basis:
        states += [s ^ cycle for s in states]
    particular = 0
    for t in ports:
        particular ^= paths[t]
    joins = [particular ^ s for s in states]
    minimum = min(joins, key=lambda s: (s.bit_count(), s))
    def chosen(s):
        return [e for i, e in enumerate(edges) if s >> i & 1]
    f0 = chosen(minimum)
    marked = set(itertools.chain.from_iterable(f0))
    assert set(ports) <= marked and is_forest(n, f0)
    selected_parts = [part for part in components(n, f0) if len(part) > 1]
    assert len(selected_parts) == len(ports) // 2
    assert all(len(part & set(ports)) == 2 for part in selected_parts)
    induced = [e for e in edges if set(e) <= marked]
    marker_components = sum(bool(part & marked)
                            for part in components(n, induced))
    assert marker_components <= len(ports) // 2
    maximum_distance = 0
    for t in ports:
        distance = {t: 0}
        todo = deque([t])
        while todo:
            u = todo.popleft()
            for v, _ in adj[u]:
                if v not in distance:
                    distance[v] = distance[u] + 1
                    todo.append(v)
        maximum_distance = max(maximum_distance,
                               max(distance[v] for v in ports))
    assert len(marked) <= len(ports) * (maximum_distance + 1) // 2
    forest_count = outside_count = 0
    cycle_obstruction = False
    for s in states:
        z_edges = chosen(s)
        j_edges = chosen(s ^ minimum)
        outside_z = [e for e in z_edges if not (set(e) & marked)]
        outside_j = [e for e in j_edges if not (set(e) & marked)]
        assert outside_z == outside_j
        jf = is_forest(n, j_edges)
        outside = is_forest(n, outside_z)
        assert not jf or outside
        forest_count += jf
        outside_count += outside
        if not z_edges:
            continue
        vertices = set(itertools.chain.from_iterable(z_edges))
        degree = {v: 0 for v in vertices}
        for u, v in z_edges:
            degree[u] += 1
            degree[v] += 1
        nontrivial_parts = [part for part in components(n, z_edges)
                            if len(part) > 1]
        if (set(ports) & vertices or len(nontrivial_parts) != 1
                or any(d != 2 for d in degree.values())):
            continue
        if all(len(part & set(ports)) % 2 == 0
               for part in components(n, edges, vertices)):
            cycle_obstruction = True
    assert forest_count <= outside_count
    assert (forest_count == len(states)) == (not cycle_obstruction)
    # One geodesic-tree marker must work for every even port subset.
    root = ports[0]
    geodesics = {root: 0}
    todo = [root]
    for u in todo:
        for v, i in adj[u]:
            if v not in geodesics:
                geodesics[v] = geodesics[u] ^ (1 << i)
                todo.append(v)
    tree_mask = 0
    for t in ports:
        tree_mask |= geodesics[t]
    connected_marker = set(itertools.chain.from_iterable(chosen(tree_mask)))
    assert set(ports) <= connected_marker
    assert is_forest(n, chosen(tree_mask))
    assert len(connected_marker) <= (len(ports) - 1) * maximum_distance + 1
    outside_flags = [
        is_forest(n, [e for e in chosen(s)
                      if not (set(e) & connected_marker)])
        for s in states
    ]
    sector_checks = 0
    for subset in range(1 << len(ports)):
        if subset.bit_count() % 2:
            continue
        seed = 0
        for i, t in enumerate(ports):
            if subset >> i & 1:
                seed ^= geodesics[t]
        assert seed & ~tree_mask == 0
        for s, outside in zip(states, outside_flags):
            assert outside or not is_forest(n, chosen(s ^ seed))
        sector_checks += 1
    return dict(rank=len(basis), ports=len(ports), states=len(states),
                forests=forest_count, outside_forests=outside_count,
                marker_vertices=len(marked), full=not cycle_obstruction,
                all_even_sectors_checked=sector_checks)


def main():
    bases = []
    bases.append((4, list(itertools.combinations(range(4), 2))))
    bases.append((6, [(i, (i + 1) % 3) for i in range(3)]
                  + [(i + 3, (i + 1) % 3 + 3) for i in range(3)]
                  + [(i, i + 3) for i in range(3)]))
    bases.append((8, [(v, v ^ (1 << b)) for v in range(8)
                       for b in range(3) if v < (v ^ (1 << b))]))
    bases.append((10, [(i, (i + 1) % 5) for i in range(5)]
                   + [(i, i + 5) for i in range(5)]
                   + [(i + 5, (i + 2) % 5 + 5) for i in range(5)]))
    rng = random.Random(1016)
    results = []
    for n0, base in bases:
        for k in (2, 4, 6):
            choices = list(itertools.combinations(range(len(base)), k))
            rng.shuffle(choices)
            for selection in choices[:24]:
                selected = set(selection)
                edges = []
                ports = []
                n = n0
                for i, (u, v) in enumerate(base):
                    if i in selected:
                        edges.extend([(u, n), (n, v)])
                        ports.append(n)
                        n += 1
                    else:
                        edges.append((u, v))
                results.append(audit(n, edges, ports))
    output = dict(fixtures=len(results),
                  affine_states=sum(row["states"] for row in results),
                  saturated_fixtures=sum(row["full"] for row in results),
                  even_sector_checks=sum(row["all_even_sectors_checked"]
                                         for row in results),
                  maximum_rank=max(row["rank"] for row in results),
                  all_checks_pass=True, details=results)
    destination = Path(__file__).with_name("random-terminal-forest-girth-checks.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: v for k, v in output.items() if k != "details"}))


if __name__ == "__main__":
    main()
