"""Exact F2 checks for common-functional splits and terminal-forest classes.

This checks the structural statements and conditional product law. The large
constant in the final exponential bound is deliberately not the test target.
"""

import argparse
import collections
from fractions import Fraction
import itertools
import json
import subprocess
from pathlib import Path


def graph6_edges(line):
    data = line.strip()
    n = data[0] - 63
    assert n < 63
    bits = [(char - 63) >> shift & 1 for char in data[1:]
            for shift in range(5, -1, -1)]
    return n, [(u, v) for bit, (u, v) in zip(
        bits, ((u, v) for v in range(1, n) for u in range(v))) if bit]


def components(n, edges):
    labels = list(range(n))
    for u, v in edges:
        if labels[u] != labels[v]:
            old, new = labels[v], labels[u]
            labels = [new if x == old else x for x in labels]
    relabel = {x: i for i, x in enumerate(sorted(set(labels)))}
    return [relabel[x] for x in labels]


def cycle_data(n, edges):
    labels = list(range(n))
    tree = [[] for _ in range(n)]
    chords = []
    incidents = [0] * n
    for i, (u, v) in enumerate(edges):
        incidents[u] |= 1 << i
        incidents[v] |= 1 << i
        if labels[u] == labels[v]:
            chords.append((i, u, v))
        else:
            old, new = labels[v], labels[u]
            labels = [new if x == old else x for x in labels]
            tree[u].append((v, i))
            tree[v].append((u, i))

    def path(u, target, previous=-1):
        if u == target:
            return 0
        for v, i in tree[u]:
            if v != previous:
                tail = path(v, target, u)
                if tail is not None:
                    return tail | (1 << i)
        return None

    basis = [(1 << i) | path(u, v) for i, u, v in chords]
    states = [0]
    for vector in basis:
        states += [mask ^ vector for mask in states]
    forms = [sum(1 << j for j, vector in enumerate(basis) if vector >> i & 1)
             for i in range(len(edges))]
    representations = []
    for star in incidents:
        reps = {0: 0}
        for i, form in enumerate(forms):
            if star >> i & 1:
                reps.update({a ^ form: mask | (1 << i)
                             for a, mask in list(reps.items())})
        representations.append(reps)
    return states, forms, incidents, representations


def check_common_functional(n, edges, data, functional, vertices, stats):
    states, forms, incidents, reps = data
    ell = len(vertices)
    if not ell:
        return
    d = max(incidents[v].bit_count() for v in vertices)
    assert d >= 2
    position = {v: i for i, v in enumerate(vertices)}
    parts = {v: reps[v][functional] for v in vertices}
    assert all(parts[v] and parts[v] != incidents[v] for v in vertices)

    def split_endpoint(v, i):
        if v not in position or parts[v] >> i & 1:
            return v
        return n + position[v]

    split_edges = [(split_endpoint(u, i), split_endpoint(v, i))
                   for i, (u, v) in enumerate(edges)]
    new_edges = [(v, n + position[v]) for v in vertices]
    m = len(edges)
    split_states, _, _, _ = cycle_data(n + ell, split_edges + new_edges)
    assert len(split_states) == len(states)
    original_index = {mask: i for i, mask in enumerate(states)}
    zero_states = []
    for mask in split_states:
        projection = mask & ((1 << m) - 1)
        index = original_index[projection]
        common_bit = (index & functional).bit_count() % 2
        assert mask >> m == (((1 << ell) - 1) if common_bit else 0)
        if not common_bit:
            zero_states.append(mask)
    assert 2 * len(zero_states) == len(states)

    labels = components(n + ell, split_edges)
    assert len(set(labels)) == ell
    quotient_edges = [(labels[u], labels[v]) for u, v in new_edges]
    quotient_degrees = collections.Counter(x for edge in quotient_edges for x in edge)
    assert len(quotient_degrees) == ell
    assert set(quotient_degrees.values()) == {2}
    assert len(set(components(ell, quotient_edges))) == 1

    component_masks = [0] * ell
    for i, (u, v) in enumerate(split_edges):
        assert labels[u] == labels[v]
        component_masks[labels[u]] |= 1 << i
    local_patterns = [{mask & cmask for mask in zero_states}
                      for cmask in component_masks]
    product_size = 1
    for patterns in local_patterns:
        product_size *= len(patterns)
    # Every state is one tuple; equality proves the complete Cartesian product.
    assert product_size == len(zero_states)
    assert len({tuple(mask & cmask for cmask in component_masks)
                for mask in zero_states}) == product_size
    stats['conditional_cartesian_product_checks'] += 1

    matching = []
    if ell >= 2:
        for size in range(ell // 2, -1, -1):
            found = None
            for candidate in itertools.combinations(range(ell), size):
                endpoints = [x for i in candidate for x in quotient_edges[i]]
                if len(set(endpoints)) == 2 * size:
                    found = list(candidate)
                    break
            if found is not None:
                matching = found
                break
        assert len(matching) == ell // 2
    joint = collections.Counter()
    for mask in zero_states:
        pattern = sum(1 << j for j, i in enumerate(matching)
                      if not mask & incidents[vertices[i]])
        joint[pattern] += 1
    total = len(zero_states)
    margins = [sum(count for pattern, count in joint.items() if pattern >> j & 1)
               for j in range(len(matching))]
    for numerator in margins:
        assert numerator * (1 << (d - 2)) >= total
    if matching:
        for pattern in range(1 << len(matching)):
            product = 1
            for j, numerator in enumerate(margins):
                product *= numerator if pattern >> j & 1 else total - numerator
            assert joint[pattern] * total ** (len(matching) - 1) == product
    stats['matching_product_law_checks'] += 1

    moment = sum(Fraction(1, 1 << sum(not mask & incidents[v] for v in vertices))
                 for mask in states) / len(states)
    q = 1 - Fraction(1, 1 << (d - 1))
    assert moment <= Fraction(1, 2) + Fraction(1, 2) * q ** (ell // 2)
    stats['common_functional_inequalities'] += 1
    stats['largest_common_family'] = max(stats['largest_common_family'], ell)


def check_terminal_forest(n, edges, data, selected, stats):
    states, forms, incidents, reps = data
    U = {0}
    for v in selected:
        U = {a ^ b for a in U for b in reps[v]}
    eligible = {v for v in range(n) if v not in selected
                and (set(reps[v]) & U) - {0}}
    boundary = [(i, v if u in selected else u) for i, (u, v) in enumerate(edges)
                if (u in selected) != (v in selected)]
    B = len(boundary)
    assert B >= 1
    adjacent = {v for _, v in boundary}
    labels = list(range(n))
    adjacency = {v: set() for v in range(n) if v not in selected}
    for u, v in edges:
        if u in selected or v in selected or labels[u] == labels[v]:
            continue
        old, new = labels[v], labels[u]
        labels = [new if x == old else x for x in labels]
        adjacency[u].add(v)
        adjacency[v].add(u)
    terminal_forms = {}
    for j, (i, v) in enumerate(boundary):
        leaf = n + j
        terminal_forms[leaf] = forms[i]
        adjacency[leaf] = {v}
        adjacency[v].add(leaf)
    pending = [v for v in adjacency if v < n and len(adjacency[v]) <= 1]
    while pending:
        v = pending.pop()
        if v not in adjacency or v >= n or len(adjacency[v]) > 1:
            continue
        for u in list(adjacency[v]):
            adjacency[u].remove(v)
            if u < n and len(adjacency[u]) <= 1:
                pending.append(u)
        del adjacency[v]
    branches = {v for v in adjacency if len(adjacency[v]) >= 3}
    assert len(branches) <= B
    exceptions = eligible & (adjacent | branches)
    assert len(exceptions) <= 2 * B
    remaining = eligible - exceptions
    assert all(v in adjacency and len(adjacency[v]) == 2 for v in remaining)
    visited = set()
    classes = []
    covered = set()
    for start in adjacency:
        if len(adjacency[start]) == 2:
            continue
        for neighbour in adjacency[start]:
            first_edge = frozenset((start, neighbour))
            if first_edge in visited:
                continue
            visited.add(first_edge)
            path = [start, neighbour]
            while len(adjacency[path[-1]]) == 2:
                u = next(v for v in adjacency[path[-1]] if v != path[-2])
                visited.add(frozenset((path[-1], u)))
                path.append(u)
            group = remaining & set(path[1:-1])
            if not group:
                continue
            # Compute the exact terminal-side functional on this chain.
            reached = {start}
            stack = [start]
            while stack:
                v = stack.pop()
                for u in adjacency[v]:
                    if frozenset((v, u)) == first_edge or u in reached:
                        continue
                    reached.add(u)
                    stack.append(u)
            functional = 0
            for leaf in reached:
                functional ^= terminal_forms.get(leaf, 0)
            assert functional != 0
            assert all(functional in reps[v] for v in group)
            assert not covered & group
            covered |= group
            classes.append(group)
    assert covered == remaining
    assert len(classes) <= 2 * B
    stats['terminal_forest_subsets'] += 1
    stats['nonempty_terminal_classes'] += len(classes)


def block_decomposition(n, edges, selected):
    adjacency = {v: [] for v in range(n) if v not in selected}
    for i, (u, v) in enumerate(edges):
        if u not in selected and v not in selected:
            adjacency[u].append((v, i))
            adjacency[v].append((u, i))
    discovery = {}
    low = {}
    stack = []
    blocks = []

    def visit(v, parent_edge=-1):
        discovery[v] = low[v] = len(discovery)
        for u, i in adjacency[v]:
            if i == parent_edge:
                continue
            if u not in discovery:
                stack.append(i)
                visit(u, i)
                low[v] = min(low[v], low[u])
                if low[u] >= discovery[v]:
                    block = []
                    while True:
                        j = stack.pop()
                        block.append(j)
                        if j == i:
                            break
                    blocks.append(set(x for j in block for x in edges[j]))
            elif discovery[u] < discovery[v]:
                stack.append(i)
                low[v] = min(low[v], discovery[u])

    for v in adjacency:
        if v not in discovery:
            if not adjacency[v]:
                blocks.append({v})
            visit(v)
    assert not stack
    incidences = {v: [] for v in adjacency}
    for i, block in enumerate(blocks):
        for v in block:
            incidences[v].append(i)
    return blocks, incidences


def check_conditional_blocks(n, edges, data, selected, stats):
    states, forms, incidents, reps = data
    U = {0}
    for v in selected:
        U = {a ^ b for a in U for b in reps[v]}
    eligible = {v for v in range(n) if v not in selected
                and (set(reps[v]) & U) - {0}}
    boundary = [(i, v if u in selected else u) for i, (u, v) in enumerate(edges)
                if (u in selected) != (v in selected)]
    B = len(boundary)
    neighbours = {v for _, v in boundary}
    blocks, incidences = block_decomposition(n, edges, selected)
    adjacency = {('b', i): set() for i in range(len(blocks))}
    for v, indices in incidences.items():
        if len(indices) > 1:
            node = ('v', v)
            adjacency[node] = {('b', i) for i in indices}
            for i in indices:
                adjacency[('b', i)].add(node)
    for j, (_, v) in enumerate(boundary):
        leaf = ('t', j)
        node = ('v', v) if len(incidences[v]) > 1 else ('b', incidences[v][0])
        adjacency[leaf] = {node}
        adjacency[node].add(leaf)
    pending = [v for v in adjacency if v[0] != 't' and len(adjacency[v]) <= 1]
    while pending:
        v = pending.pop()
        if v not in adjacency or v[0] == 't' or len(adjacency[v]) > 1:
            continue
        for u in list(adjacency[v]):
            adjacency[u].remove(v)
            if u[0] != 't' and len(adjacency[u]) <= 1:
                pending.append(u)
        del adjacency[v]
    exceptional = set()
    for v in eligible:
        node = ('v', v)
        if v in neighbours:
            exceptional.add(v)
        elif node in adjacency and (len(adjacency[node]) >= 3 or any(
                u[0] == 'b' and len(adjacency[u]) >= 3 for u in adjacency[node])):
            exceptional.add(v)
    assert len(exceptional) <= 5 * B
    good = eligible - exceptional
    common = {}
    for v in good:
        assert ('v', v) in adjacency and len(adjacency[('v', v)]) == 2
        intersection = (set(reps[v]) & U) - {0}
        assert len(intersection) == 1
        common[v] = next(iter(intersection))
    conflict = {v: set() for v in good}
    for block in blocks:
        vertices = block & good
        assert len(vertices) <= 2
        if len(vertices) == 2:
            u, v = vertices
            conflict[u].add(v)
            conflict[v].add(u)
    assert all(len(neighbours) <= 2 for neighbours in conflict.values())
    colors = {}
    for start in good:
        if start in colors:
            continue
        colors[start] = 0
        stack = [(start, -1)]
        while stack:
            v, parent = stack.pop()
            for u in conflict[v]:
                if u == parent:
                    continue
                assert u not in colors  # The conflict graph is a forest.
                colors[u] = 1 - colors[v]
                stack.append((u, v))
    masses = [sum((Fraction(1, len(reps[v])) for v in good if colors[v] == color),
                  Fraction(0)) for color in (0, 1)]
    color = 0 if masses[0] >= masses[1] else 1
    chosen = [v for v in good if colors[v] == color]
    assert 2 * masses[color] >= sum(masses)
    all_blocks = [i for v in chosen for i in incidences[v]]
    assert len(set(all_blocks)) == len(all_blocks)
    if not chosen:
        stats['block_selection_cases'] += 1
        return
    incident_selected = 0
    for v in selected:
        incident_selected |= incidents[v]
    fibres = collections.defaultdict(list)
    for index, mask in enumerate(states):
        fibres[mask & incident_selected].append((index, mask))
    assert len(fibres) == len(U)
    for fibre in fibres.values():
        total = len(fibre)
        joint = collections.Counter(sum(1 << j for j, v in enumerate(chosen)
                                        if not mask & incidents[v])
                                    for _, mask in fibre)
        margins = [sum(count for pattern, count in joint.items() if pattern >> j & 1)
                   for j in range(len(chosen))]
        for j, v in enumerate(chosen):
            bits = {(index & common[v]).bit_count() % 2 for index, _ in fibre}
            assert len(bits) == 1
            bit = bits.pop()
            assert margins[j] * len(reps[v]) == (0 if bit else 2 * total)
        for pattern in range(1 << len(chosen)):
            product = 1
            for j, numerator in enumerate(margins):
                product *= numerator if pattern >> j & 1 else total - numerator
            assert joint[pattern] * total ** (len(chosen) - 1) == product
        stats['full_U_conditional_product_checks'] += 1
    stats['block_selection_cases'] += 1
    stats['block_selected_vertices'] += len(chosen)


def check_graph(n, edges, stats, all_subsets=True):
    data = cycle_data(n, edges)
    reps = data[3]
    functionals = set().union(*(set(local) for local in reps)) - {0}
    for functional in functionals:
        vertices = [v for v in range(n) if functional in reps[v]]
        check_common_functional(n, edges, data, functional, vertices, stats)
    selections = range(1, (1 << n) - 1) if all_subsets else (
        list(1 << v for v in range(n)) + [sum(1 << v for v in range(0, n, 2))])
    for mask in selections:
        selected = {v for v in range(n) if mask >> v & 1}
        if selected and len(selected) < n:
            check_terminal_forest(n, edges, data, selected, stats)
            check_conditional_blocks(n, edges, data, selected, stats)
    stats['graphs'] += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geng', default='/tmp/nauty2_8_9/geng')
    parser.add_argument('--maximum-order', type=int, default=6)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name(
        'exponential-small-cuts-results.json'))
    args = parser.parse_args()
    stats = collections.Counter()
    classes = []
    for n in range(2, args.maximum_order + 1):
        before = stats['graphs']
        process = subprocess.Popen([args.geng, '-cq', '-D4', str(n)],
                                   stdout=subprocess.PIPE)
        for line in process.stdout:
            order, edges = graph6_edges(line)
            assert order == n
            check_graph(n, edges, stats)
        assert process.wait() == 0
        classes.append({'order': n, 'connected_simple_graphs': stats['graphs'] - before})
    structured = 0
    for n in range(3, 9):
        cycle = [(i, (i + 1) % n) for i in range(n)]
        check_graph(n, cycle, stats, False)
        check_graph(n, cycle + cycle, stats, False)
        structured += 2
    for k in range(3, 7):
        edges = [(2 * i, 2 * i + 1) for i in range(k)] * 2
        edges += [(2 * i + 1, (2 * i + 2) % (2 * k)) for i in range(k)]
        check_graph(2 * k, edges, stats, False)
        structured += 1
    result = {'status': 'all exact F2 and rational checks passed',
              'simple_graph_classes': classes,
              'additional_cycle_doubled_cycle_and_cubic_necklace_cases': structured,
              'counts': dict(stats),
              'checks': ['simultaneous split cycle-space bijection',
                         'equal new coordinates and exact component count',
                         'two-regular connected series quotient',
                         'conditional Cartesian-product cycle spaces',
                         'matched closed-star product law',
                         'exact rational common-functional inequality',
                         'terminal-forest classes and their nonzero functional',
                         'block-cut exclusions and weighted path coloring',
                         'exact conditional closure probability given full U',
                         'full-U conditional block product law']}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
