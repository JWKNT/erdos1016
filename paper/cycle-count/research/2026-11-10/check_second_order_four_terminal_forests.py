#!/usr/bin/env python3
"""Independent affine-basis audit of the four-terminal forest witnesses."""
import json
from pathlib import Path


def enumerate_joins(n, edges, terminals):
    adjacency = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adjacency[u].append((v, i))
        adjacency[v].append((u, i))
    parent = {0: (-1, -1)}
    order = [0]
    root_paths = [0] * n
    for u in order:
        for v, e in adjacency[u]:
            if v not in parent:
                parent[v] = (u, e)
                root_paths[v] = root_paths[u] ^ (1 << e)
                order.append(v)
    assert len(parent) == n
    tree = {e for _, e in parent.values()}
    basis = [root_paths[u] ^ root_paths[v] ^ (1 << i)
             for i, (u, v) in enumerate(edges) if i not in tree]
    assert len(basis) == len(edges) - n + 1
    particular = 0
    for t in terminals:
        particular ^= root_paths[t]
    forests = 0
    bad_examples = []
    for word in range(1 << len(basis)):
        selected = particular
        for i, cycle in enumerate(basis):
            if word >> i & 1:
                selected ^= cycle
        uf = list(range(n))
        degree = [0] * n
        cyclic = False
        chosen = []

        def find(v):
            while uf[v] != v:
                uf[v] = uf[uf[v]]
                v = uf[v]
            return v

        for i, (u, v) in enumerate(edges):
            if selected >> i & 1:
                chosen.append((u, v))
                degree[u] += 1
                degree[v] += 1
                x, y = find(u), find(v)
                if x == y:
                    cyclic = True
                uf[x] = y
        assert {v for v in range(n) if degree[v] % 2} == set(terminals)
        if cyclic:
            if len(bad_examples) < 2:
                bad_examples.append(chosen)
        else:
            forests += 1
    return forests, bad_examples


def attach_diamond(n, edges, terminals):
    """Move one terminal through a bridge and a full rank-two two-pole."""
    old = terminals[0]
    a, b, c, d = range(n, n + 4)
    new_edges = edges + [(old, a), (a, c), (a, d), (b, c), (b, d), (c, d)]
    return n + 4, new_edges, [b] + terminals[1:]


def main():
    folder = Path(__file__).resolve().parent
    rows = []
    source = folder / 'second-order-four-terminal-extension-wide-search.jsonl'
    for witness in map(json.loads, source.read_text().splitlines()):
        n = witness['vertices']
        edges = [tuple(e) for e in witness['edges']]
        terminals = witness['terminals']
        h = len(edges) - n + 1
        assert len(set(tuple(sorted(e)) for e in edges)) == len(edges)
        degree = [0] * n
        for u, v in edges:
            assert u != v
            degree[u] += 1
            degree[v] += 1
        assert all(degree[v] == (2 if v in terminals else 3) for v in range(n))
        forests, bad = enumerate_joins(n, edges, terminals)
        assert forests == 2**h - 1
        rows.append(dict(rank=h, forests=forests, total=2**h,
                         unique_cyclic_join=bad[0]))
    assert h == 7
    extensions = []
    for _ in range(3):
        n, edges, terminals = attach_diamond(n, edges, terminals)
        h = len(edges) - n + 1
        forests, _ = enumerate_joins(n, edges, terminals)
        assert 128 * forests == 127 * 2**h
        extensions.append(dict(rank=h, forests=forests, total=2**h))
    print(json.dumps(dict(exact_witness_checks=rows,
                          constant_density_extensions=extensions), indent=2))


if __name__ == '__main__':
    main()
