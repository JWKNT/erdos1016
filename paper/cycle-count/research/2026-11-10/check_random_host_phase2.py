"""Finite checks for the coefficient-one lower bound.

Exhaust all simple graphs on at most five vertices and their spanning
pseudoforests. This verifies the decisive counting inequality for every
cycle subfamily, using its worst-case reformulation 2*n_0+n_1 <= 2*beta.
The checks do not verify the asymptotic random-host estimate.
"""

from itertools import combinations, permutations
import json


def graph_stats(n, edges, mask):
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for index, (u, v) in enumerate(edges):
        if mask >> index & 1:
            parent[root(u)] = root(v)
    roots = [root(v) for v in range(n)]
    vertices = {}
    counts = {}
    for v in roots:
        vertices[v] = vertices.get(v, 0) + 1
    for index, (u, _) in enumerate(edges):
        if mask >> index & 1:
            v = roots[u]
            counts[v] = counts.get(v, 0) + 1
    pseudo = all(counts.get(v, 0) <= size for v, size in vertices.items())
    cyclic = sum(counts.get(v, 0) == size for v, size in vertices.items())
    rank = mask.bit_count() - n + len(vertices)
    return rank, pseudo, cyclic, roots


def complete_cycles(n, edges):
    indices = {pair: i for i, pair in enumerate(edges)}
    cycles = set()
    for length in range(3, n + 1):
        for vertices in combinations(range(n), length):
            first = vertices[0]
            for order in permutations(vertices[1:]):
                if order[0] > order[-1]:
                    continue
                path = (first,) + order
                mask = 0
                for u, v in zip(path, path[1:] + path[:1]):
                    mask |= 1 << indices[tuple(sorted((u, v)))]
                cycles.add(mask)
    return sorted(cycles)


def theta_checks():
    def edge(u, v):
        return tuple(sorted((u, v)))

    def check_block(s, x, y, depth, require_long_path=True):
        assert (s + x + y) % 2 == 0
        alpha = (s + x - y) // 2
        z = (x + y - s) // 2
        assert 1 <= alpha < s
        assert z >= 1
        if require_long_path:
            assert z >= depth + 2
        base = {edge(i, (i + 1) % s) for i in range(s)}
        vertices = [0] + list(range(s, s + z - 1)) + [alpha]
        added = {edge(u, v) for u, v in zip(vertices, vertices[1:])}
        assert base.isdisjoint(added)
        graph = base | added
        assert len(graph) - (s + z - 1) + 1 == 2
        assert sorted((s, alpha + z, s - alpha + z)) == sorted((s, x, y))
        path = graph - {edge(0, 1), edge(alpha, alpha + 1)}
        adjacency = {v: [] for v in range(s + z - 1)}
        for u, v in path:
            adjacency[u].append(v)
            adjacency[v].append(u)
        endpoints = {v for v, neighbors in adjacency.items() if len(neighbors) == 1}
        assert endpoints == {1, alpha + 1}
        assert all(len(neighbors) in (1, 2) for neighbors in adjacency.values())
        seen = set()
        todo = [1]
        while todo:
            v = todo.pop()
            if v not in seen:
                seen.add(v)
                todo.extend(adjacency[v])
        assert len(seen) == len(adjacency)

    parameters = 0
    blocks = 0
    whole_blocks = 0
    for depth in (32, 64, 128, 256, 512):
        for base in range(2, min(16, depth // 4) + 1):
            cutoff = 2 * (depth + base + 1)
            first_high = depth + 5
            groups = (cutoff - first_high + 1) // 8
            covered = set()
            for j in range(groups):
                h = first_high + 8 * j
                triples = ((4*j+3, h+4, h+5), (4*j+4, h, h+2),
                           (4*j+5, h+6, h+7), (4*j+6, h+1, h+3))
                for triple in triples:
                    assert covered.isdisjoint(triple)
                    covered.update(triple)
                    check_block(*triple, depth)
                    blocks += 1
            all_lengths = set(range(3, cutoff + 1))
            assert covered <= all_lengths
            singles = all_lengths - covered
            rank = 8 * groups + len(singles)
            assert rank == cutoff - 2 - 4 * groups
            assert rank <= 1.5 * depth + base + 5
            whole_groups = (cutoff - 2) // 12
            total_thetas = 4 * whole_groups
            whole_covered = set()
            shortest = set()
            for j in range(whole_groups):
                q = whole_groups - j - 1
                h = total_thetas + 3 + 8 * j
                triples = ((4*q+3, h+4, h+5), (4*q+4, h, h+2),
                           (4*q+5, h+6, h+7), (4*q+6, h+1, h+3))
                for triple in triples:
                    assert whole_covered.isdisjoint(triple)
                    whole_covered.update(triple)
                    shortest.add(min(triple))
                    assert sum(triple) // 2 >= depth
                    check_block(*triple, depth, require_long_path=False)
                    whole_blocks += 1
            assert whole_covered == set(range(3, 3 * total_thetas + 3))
            assert shortest == set(range(3, total_thetas + 3))
            whole_rank = 2 * total_thetas + len(all_lengths - whole_covered)
            assert whole_rank == cutoff - 2 - total_thetas
            assert 3 * whole_rank <= 4 * depth + 4 * base + 12
            parameters += 1
    return parameters, blocks, whole_blocks


def main():
    graph_count = 0
    pair_count = 0
    strict_examples = 0
    for n in range(1, 6):
        edges = list(combinations(range(n), 2))
        universe = 1 << len(edges)
        stats = [graph_stats(n, edges, mask) for mask in range(universe)]
        all_cycles = complete_cycles(n, edges)
        for graph in range(universe):
            rank = stats[graph][0]
            cycles = [cycle for cycle in all_cycles if cycle & graph == cycle]
            pseudo = graph
            while True:
                _, is_pseudo, cyclic, roots = stats[pseudo]
                if is_pseudo:
                    omitted = graph ^ pseudo
                    internal = sum(
                        (omitted >> index & 1) and roots[u] == roots[v]
                        for index, (u, v) in enumerate(edges)
                    )
                    assert rank >= cyclic + internal
                    n0 = sum((cycle & omitted).bit_count() == 0 for cycle in cycles)
                    n1 = sum((cycle & omitted).bit_count() == 1 for cycle in cycles)
                    assert n0 <= cyclic
                    assert n1 <= 2 * internal
                    assert 2 * n0 + n1 <= 2 * rank
                    assert sum((cycle & omitted).bit_count() for cycle in cycles) >= 2 * (len(cycles) - rank)
                    pair_count += 1
                    strict_examples += int(2 * n0 + n1 < 2 * rank)
                if pseudo == 0:
                    break
                pseudo = (pseudo - 1) & graph
            graph_count += 1
    theta_parameters, theta_blocks, whole_blocks = theta_checks()
    print(json.dumps({
        "status": "pass",
        "graphs_checked": graph_count,
        "graph_pseudoforest_pairs_checked": pair_count,
        "strict_pairs": strict_examples,
        "theta_interval_parameter_pairs": theta_parameters,
        "theta_blocks_with_spanning_paths_checked": theta_blocks,
        "whole_theta_blocks_with_spanning_paths_checked": whole_blocks,
        "scope": "all simple graphs through five vertices and all spanning pseudoforests; all cycle subfamilies via the worst-case inequality; explicit theta cycles, spanning paths, and interval coverage",
    }, indent=2))


if __name__ == "__main__":
    main()
