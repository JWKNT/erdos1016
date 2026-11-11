"""Exact affine-state checks for the four attached ladder counterexample."""
import itertools
import json
from pathlib import Path


def graph(b):
    edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
    ports = []
    n = 4
    for root in range(4):
        a, t = n, n + 1
        n += 2
        top, bottom = [], []
        for _ in range(b - 1):
            top.append(n)
            bottom.append(n + 1)
            n += 2
        edges.extend([(root, a), (a, top[0]), (a, bottom[0]),
                      (t, top[-1]), (t, bottom[-1])])
        edges.extend(zip(top, bottom))
        edges.extend(zip(top, top[1:]))
        edges.extend(zip(bottom, bottom[1:]))
        ports.append(t)
    return n, edges, ports


def cycle_basis(n, edges):
    adj = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        adj[u].append((v, e))
        adj[v].append((u, e))
    parent = [-1] * n
    parent[0] = 0
    root_path = [0] * n
    order = [0]
    tree = set()
    for u in order:
        for v, e in adj[u]:
            if parent[v] == -1:
                parent[v] = u
                root_path[v] = root_path[u] ^ (1 << e)
                tree.add(e)
                order.append(v)
    assert len(order) == n
    basis = [root_path[u] ^ root_path[v] ^ (1 << e)
             for e, (u, v) in enumerate(edges) if e not in tree]
    return adj, root_path, basis


def count_paths(adj, source, target):
    def visit(u, used):
        if u == target:
            return 1
        return sum(visit(v, used | (1 << v)) for v, _ in adj[u]
                   if not (used >> v) & 1)
    return visit(source, 1 << source)


def main():
    results = []
    for b in (2, 3, 4):
        n, edges, ports = graph(b)
        adj, root_path, basis = cycle_basis(n, edges)
        h = len(basis)
        assert h == 4 * b + 1
        assert all(len(adj[v]) == (2 if v in ports else 3)
                   for v in range(n))
        state = 0
        for v in ports:
            state ^= root_path[v]
        totals = {}
        for j in range(1 << h):
            if j:
                changed = (j & -j).bit_length() - 1
                state ^= basis[changed]
            parent = list(range(n))
            degree = [0] * n
            def find(v):
                while parent[v] != v:
                    parent[v] = parent[parent[v]]
                    v = parent[v]
                return v
            mask = state
            forest = True
            while mask:
                bit = mask & -mask
                mask ^= bit
                u, v = edges[bit.bit_length() - 1]
                degree[u] += 1
                degree[v] += 1
                ru, rv = find(u), find(v)
                if ru == rv:
                    forest = False
                    break
                parent[ru] = rv
            assert forest
            assert all((degree[v] & 1) == (v in ports) for v in range(n))
            components = {}
            for i, v in enumerate(ports):
                components.setdefault(find(v), []).append(i)
            pairing = tuple(sorted(tuple(x) for x in components.values()))
            assert all(len(pair) == 2 for pair in pairing)
            totals[pairing] = totals.get(pairing, 0) + 1
        assert totals == {
            ((0, 1), (2, 3)): 1 << (h - 1),
            ((0, 3), (1, 2)): 1 << (h - 1),
        }
        paths = [count_paths(adj, ports[i], ports[j])
                 for i, j in itertools.combinations(range(4), 2)]
        assert paths == [1 << (2 * b + 1)] * 6
        results.append({"block_rank": b, "rank": h, "vertices": n,
                        "forest_states": 1 << h,
                        "pairing_counts": [1 << (h - 1)] * 2,
                        "pair_path_counts": paths})
    output = {"status": "PASS", "cases": results,
              "total_affine_states": sum(x["forest_states"] for x in results)}
    path = Path(__file__).with_name("random-seven-concentration-checks.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output))


if __name__ == "__main__":
    main()
