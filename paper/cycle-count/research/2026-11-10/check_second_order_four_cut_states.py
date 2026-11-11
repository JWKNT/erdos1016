#!/usr/bin/env python3
"""Check four-cut gluing against independent full cycle-space enumeration."""
import itertools
import json
from pathlib import Path
from check_second_order_saturated_blocks import paths, cycles

PAIRINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


def pairing_key(pairs):
    return tuple(sorted(tuple(sorted(p)) for p in pairs))


def forest_states(n, edges, ports, return_masks=False):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    parent = {0: (-1, -1)}
    order = [0]
    roots = [0]*n
    for u in order:
        for v, e in adj[u]:
            if v not in parent:
                parent[v] = (u, e)
                roots[v] = roots[u] ^ (1 << e)
                order.append(v)
    tree = {e for _, e in parent.values()}
    basis = [roots[u] ^ roots[v] ^ (1 << i)
             for i, (u, v) in enumerate(edges) if i not in tree]
    base = 0
    for p in ports:
        base ^= roots[p]
    result = {pairing_key(p): 0 for p in PAIRINGS}
    forest_masks = set()
    for word in range(1 << len(basis)):
        selected = base
        for i, mask in enumerate(basis):
            if word >> i & 1:
                selected ^= mask
        uf = list(range(n))

        def find(v):
            while uf[v] != v:
                uf[v] = uf[uf[v]]
                v = uf[v]
            return v

        cyclic = False
        for i, (u, v) in enumerate(edges):
            if selected >> i & 1:
                a, b = find(u), find(v)
                if a == b:
                    cyclic = True
                    break
                uf[a] = b
        if cyclic:
            continue
        components = {}
        for i, p in enumerate(ports):
            components.setdefault(find(p), []).append(i)
        assert len(components) == 2
        assert all(len(p) == 2 for p in components.values())
        result[pairing_key(components.values())] += 1
        forest_masks.add(selected)
    counts = [result[pairing_key(p)] for p in PAIRINGS]
    return (counts, forest_masks) if return_masks else counts


def cycle_masks(n, edges):
    """Independent simple-cycle DFS, retaining parallel-edge identities."""
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    result = set()
    for start in range(n):
        def visit(u, vertices, selected):
            for v, e in adj[u]:
                if selected >> e & 1:
                    continue
                if v == start and u != start:
                    result.add(selected | (1 << e))
                elif v > start and not (vertices >> v & 1):
                    visit(v, vertices | (1 << v), selected | (1 << e))
        visit(start, 1 << start, 0)
    return result


def state(graph, order):
    n, edges, ports = graph
    ports = [ports[i] for i in order]
    return ([paths(n, edges, ports[i], ports[j])
             for i in range(4) for j in range(i+1, 4)],
            forest_states(n, edges, ports))


def main():
    folder = Path(__file__).resolve().parent
    graphs = [
        (4, [(i, (i+1) % 4) for i in range(4)], [0, 1, 2, 3]),
        (6, [(i, (i+1) % 6) for i in range(6)]+[(1, 4)], [0, 2, 3, 5]),
        (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)],
         [0, 1, 4, 5]),
    ]
    witnesses = list(map(json.loads, (folder/'second-order-four-terminal-extension-wide-search.jsonl').read_text().splitlines()))
    for witness in witnesses[:2]:
        graphs.append((witness['vertices'], [tuple(e) for e in witness['edges']],
                       witness['terminals']))
    permutations = list(itertools.permutations(range(4)))
    states = {(i, p): state(g, p) for i, g in enumerate(graphs) for p in permutations}
    internal = [cycles(n, e) for n, e, _ in graphs]
    attachment_checks = 0
    forest_maps = 0
    for i, (n, edges, ports) in enumerate(graphs):
        for perm in permutations:
            ordered = [ports[t] for t in perm]
            p, f = states[i, perm]
            added = edges + [(ordered[2], ordered[3])]
            assert paths(n, added, ordered[0], ordered[1]) == p[0]+sum(f)-f[0]
            assert len(cycle_masks(n, added)) == internal[i]+p[5]
            capped = edges + [(n, ordered[0]), (n, ordered[1]),
                              (n+1, ordered[2]), (n+1, ordered[3])]
            assert paths(n+2, capped, n, n+1) == sum(p[t] for t in (1, 2, 3, 4))
            cm = cycle_masks(n+2, capped)
            vertex_masks = {}
            for mask in cm:
                vertices = 0
                for e, (u, v) in enumerate(capped):
                    if mask >> e & 1:
                        vertices |= (1 << u) | (1 << v)
                vertex_masks[mask] = vertices
            z_cycles = [m for m in cm if vertex_masks[m] >> n & 1]
            w_cycles = [m for m in cm if vertex_masks[m] >> (n+1) & 1]
            internal_mask = (1 << len(edges))-1
            restored = {m & internal_mask for m in z_cycles
                        if vertex_masks[m] >> (n+1) & 1}
            for left in z_cycles:
                for right in w_cycles:
                    if not (vertex_masks[left] & vertex_masks[right]):
                        restored.add((left | right) & internal_mask)
            _, expected = forest_states(n, edges, ordered, return_masks=True)
            assert restored == expected
            attachment_checks += 1
            forest_maps += len(expected)
    checks = []
    for i, (n, edges, ports) in enumerate(graphs):
        p, f = states[i, (0, 1, 2, 3)]
        for j, (m, other, other_ports) in enumerate(graphs):
            for perm in permutations:
                q, g = states[j, perm]
                joined = edges + [(u+n, v+n) for u, v in other]
                joined += [(ports[t], n+other_ports[perm[t]]) for t in range(4)]
                exact = cycles(n+m, joined)
                predicted = (internal[i]+internal[j]
                             +sum(a*b for a, b in zip(p, q))
                             +sum(f)*sum(g)-sum(a*b for a, b in zip(f, g)))
                assert exact == predicted, (i, j, perm, exact, predicted)
            checks.append(dict(left=i, right=j, permutations=24,
                               total_rank=len(edges)-n+1+len(other)-m+1+3))
    print(json.dumps(dict(shore_graphs=len(graphs), gluing_checks=24*len(checks),
                          added_edge_and_capping_checks=attachment_checks,
                          individual_forest_maps=forest_maps,
                          cases=checks), indent=2))


if __name__ == '__main__':
    main()
