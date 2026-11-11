"""Exact cycle counts for unions of two Hamilton cycles.

Fix one Hamilton cycle. Enumerate the second up to reversal, so every
Hamilton-decomposable loopless 4-regular multigraph is represented.
Parallel edges are distinct. A pair of parallel edges is a cycle.
"""

import argparse
import itertools
import json
import time
from collections import Counter
from pathlib import Path


def count_cycles(n, edges):
    mult = [[0] * n for _ in range(n)]
    for u, v in edges:
        assert u != v
        mult[u][v] += 1
        mult[v][u] += 1
    total = sum(mult[u][v] * (mult[u][v] - 1) // 2
                for u in range(n) for v in range(u + 1, n))
    long_total = 0
    for start in range(n):
        def extend(last, seen, weight, length):
            nonlocal long_total
            if length >= 3:
                long_total += weight * mult[last][start]
            for nxt in range(start + 1, n):
                if not (seen >> nxt & 1) and mult[last][nxt]:
                    extend(nxt, seen | (1 << nxt),
                           weight * mult[last][nxt], length + 1)
        extend(start, 1 << start, 1, 1)
    assert long_total % 2 == 0
    return total + long_total // 2


def necklace(n):
    return [(i, (i + 1) % n) for i in range(n)]


def count_cycles_by_cycle_space(n, edges):
    """Independent count from a fundamental binary cycle basis."""
    parent = list(range(n))
    def root(u):
        while parent[u] != u:
            u = parent[u]
        return u
    tree = [[] for _ in range(n)]
    chords = []
    for i, (u, v) in enumerate(edges):
        ru, rv = root(u), root(v)
        if ru != rv:
            parent[ru] = rv
            tree[u].append((v, i))
            tree[v].append((u, i))
        else:
            chords.append((i, u, v))
    def tree_path(u, v, previous=-1):
        if u == v:
            return 0
        for nxt, edge in tree[u]:
            if nxt == previous:
                continue
            result = tree_path(nxt, v, u)
            if result is not None:
                return result | (1 << edge)
        return None
    basis = [(1 << i) | tree_path(u, v) for i, u, v in chords]
    masks = [0]
    for vector in basis:
        masks += [mask ^ vector for mask in masks]
    incidents = [0] * n
    for i, (u, v) in enumerate(edges):
        incidents[u] |= 1 << i
        incidents[v] |= 1 << i
    total = 0
    for mask in masks[1:]:
        active = [v for v in range(n) if incidents[v] & mask]
        if any((incidents[v] & mask).bit_count() != 2 for v in active):
            continue
        seen = {active[0]}
        todo = list(seen)
        while todo:
            u = todo.pop()
            remaining = incidents[u] & mask
            while remaining:
                bit = remaining & -remaining
                remaining -= bit
                a, b = edges[bit.bit_length() - 1]
                v = b if a == u else a
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        if len(seen) == len(active):
            total += 1
    return total


def double_contract(n, edges, uv):
    u, v = uv
    vertices = [i for i in range(n) if i != v]
    label = {old: new for new, old in enumerate(vertices)}
    def replace(x):
        return label[u if x == v else x]
    return [(replace(a), replace(b)) for a, b in edges
            if tuple(sorted((a, b))) != uv]


def run(max_n):
    report = []
    for n in range(3, max_n + 1):
        started = time.monotonic()
        red = necklace(n)
        maximum = 0
        maximizers = 0
        checked = 0
        contract_checked = 0
        expansion_checked = 0
        contract_max_surplus = None
        contract_counterexample = None
        cycle_distribution = Counter()
        for tail in itertools.permutations(range(1, n)):
            if tail[0] > tail[-1]:
                continue
            blue_order = (0,) + tail
            blue = [(blue_order[i], blue_order[(i + 1) % n])
                    for i in range(n)]
            edges = red + blue
            count = count_cycles(n, edges)
            if n <= 8:
                assert count == count_cycles_by_cycle_space(n, edges)
            checked += 1
            cycle_distribution[count] += 1
            if count > maximum:
                maximum, maximizers = count, 1
            elif count == maximum:
                maximizers += 1
            assert count <= 2 ** n + n, (n, edges, count)
            multiplicities = Counter(tuple(sorted(e)) for e in edges)
            for uv, multiplicity in multiplicities.items():
                if multiplicity != 2:
                    continue
                if n <= 7:
                    u, v = uv
                    rest = [e for e in edges if tuple(sorted(e)) != uv]
                    avoiding = count_cycles(n, rest)
                    through_one = count - avoiding - 1
                    assert through_one <= 2 ** n
                    doubled_cycle = (len(multiplicities) == n and
                                     all(x == 2 for x in multiplicities.values()))
                    assert (through_one == 2 ** n) == doubled_cycle
                    for added in (1, 2):
                        sequence = [u] + list(range(n, n + added)) + [v]
                        expanded = rest + [
                            (sequence[i], sequence[i + 1])
                            for i in range(added + 1) for j in range(2)]
                        assert count_cycles(n + added, expanded) == (
                            2 ** added * through_one + avoiding + added + 1)
                        expansion_checked += 1
                reduced = double_contract(n, edges, uv)
                reduced_count = count_cycles(n - 1, reduced)
                surplus = count - reduced_count - 2 ** (n - 1) - 1
                contract_checked += 1
                if (contract_max_surplus is None or
                        surplus > contract_max_surplus):
                    contract_max_surplus = surplus
                if surplus > 0 and contract_counterexample is None:
                    contract_counterexample = {
                        'edges': edges, 'double_edge': uv,
                        'cycles': count, 'contracted_cycles': reduced_count,
                        'surplus': surplus,
                    }
        result = {
            'n': n,
            'second_hamilton_cycles': checked,
            'independent_cycle_space_check': n <= 8,
            'maximum_cycles': maximum,
            'maximizing_second_cycles': maximizers,
            'conjectured_maximum': 2 ** n + n,
            'double_contractions_checked': contract_checked,
            'double_chain_expansions_checked': expansion_checked,
            'double_contraction_max_surplus': contract_max_surplus,
            'double_contraction_counterexample': contract_counterexample,
            'cycle_count_distribution': dict(sorted(cycle_distribution.items())),
            'seconds': round(time.monotonic() - started, 3),
        }
        report.append(result)
        print(json.dumps({k: v for k, v in result.items()
                          if k != 'cycle_count_distribution'}), flush=True)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = run(args.max_n)
    if args.output:
        args.output.write_text(json.dumps(results, indent=2) + '\n')
