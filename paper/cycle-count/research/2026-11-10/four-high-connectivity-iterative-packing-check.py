"""Exact checks of the new separation and conditional-fiber assertions.

The very large analytic girth threshold is not a numerical test target.
This checks actual terminal bipartitions, all middle interval components,
core pruning, and the full Cartesian product of two affine internal spaces.
Only the Python standard library and the existing nauty geng binary are used.
"""

from collections import Counter, defaultdict
from fractions import Fraction
import itertools
import json
from pathlib import Path
import subprocess

from check_exponential_small_cuts import cycle_data, graph6_edges


HERE = Path(__file__).resolve().parent
GENG = '/tmp/nauty2_8_9/geng'
STATS = Counter()


def adjacency(n, edges):
    out = [set() for _ in range(n)]
    for u, v in edges:
        out[u].add(v)
        out[v].add(u)
    return out


def component(adj, start, allowed):
    seen = {start}
    pending = [start]
    while pending:
        v = pending.pop()
        for u in adj[v] & allowed - seen:
            seen.add(u)
            pending.append(u)
    return seen


def terminal_classes(n, edges, selected):
    _, forms, _, reps = cycle_data(n, edges)
    U = {0}
    for v in selected:
        U = {a ^ b for a in U for b in reps[v]}
    eligible = {v for v in range(n) if v not in selected
                and (set(reps[v]) & U) - {0}}
    boundary = [(i, v if u in selected else u)
                for i, (u, v) in enumerate(edges)
                if (u in selected) != (v in selected)]
    B = len(boundary)
    near = {v for _, v in boundary}
    tree = {v: set() for v in range(n) if v not in selected}
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for u, v in edges:
        if u in selected or v in selected or find(u) == find(v):
            continue
        parent[find(u)] = find(v)
        tree[u].add(v)
        tree[v].add(u)
    for j, (_, v) in enumerate(boundary):
        tree[n + j] = {v}
        tree[v].add(n + j)
    pending = [v for v in tree if v < n and len(tree[v]) <= 1]
    while pending:
        v = pending.pop()
        if v not in tree or v >= n or len(tree[v]) > 1:
            continue
        for u in tuple(tree[v]):
            tree[u].remove(v)
            if u < n and len(tree[u]) <= 1:
                pending.append(u)
        del tree[v]
    branches = {v for v in tree if len(tree[v]) >= 3}
    remaining = eligible - near - branches
    assert len(eligible - remaining) <= 2 * B
    assert all(v in tree and len(tree[v]) == 2 for v in remaining)
    used = set()
    classes = []
    for start in tree:
        if len(tree[start]) == 2:
            continue
        for nxt in tree[start]:
            if frozenset((start, nxt)) in used:
                continue
            path = [start, nxt]
            used.add(frozenset((start, nxt)))
            while len(tree[path[-1]]) == 2:
                nxt = next(v for v in tree[path[-1]] if v != path[-2])
                used.add(frozenset((path[-1], nxt)))
                path.append(nxt)
            group = [v for v in path[1:-1] if v in remaining]
            if group:
                classes.append(group)
    assert set(itertools.chain.from_iterable(classes)) == remaining
    assert len(classes) <= 2 * B
    return classes, boundary


def check_intervals(n, edges, selected):
    classes, boundary = terminal_classes(n, edges, selected)
    adj = adjacency(n, edges)
    outside = set(range(n)) - selected
    for group in classes:
        partitions = []
        for v in group:
            whole = component(adj, v, outside)
            unseen = whole - {v}
            terminal_parts = []
            while unseen:
                part = component(adj, next(iter(unseen)), unseen)
                unseen -= part
                terms = frozenset(j for j, (_, endpoint) in enumerate(boundary)
                                  if endpoint in part)
                if terms:
                    terminal_parts.append(terms)
            assert len(terminal_parts) == 2
            partitions.append(frozenset(terminal_parts))
            STATS['actual_articulation_partitions'] += 1
        assert len(set(partitions)) <= 1
        STATS['terminal_classes'] += 1
        STATS['largest_terminal_class'] = max(STATS['largest_terminal_class'], len(group))
        intervals = {}
        for i in range(len(group)):
            for j in range(i + 2, len(group)):
                allowed = outside - {group[i], group[j]}
                region = component(adj, group[i + 1], allowed)
                assert set(group[i + 1:j]) <= region
                assert not set(group[:i] + group[j + 1:]) & region
                assert not any(adj[v] & selected for v in region)
                endpoints = {u for v in region for u in adj[v] - region}
                assert endpoints <= {group[i], group[j]}
                intervals[i, j] = region
                STATS['middle_interval_separations'] += 1
        for H in (1, 2, 3):
            pieces = [intervals[i, i + H + 1]
                      for i in range(0, len(group) - H - 1, H + 2)]
            for a, b in itertools.combinations(pieces, 2):
                assert not a & b
                STATS['disjoint_segment_pairs'] += 1
    STATS['selected_vertex_sets'] += 1


def rank_and_mask(vertices, edges):
    mask = sum(1 << i for i, (u, v) in enumerate(edges)
               if u in vertices and v in vertices)
    return mask.bit_count() - len(vertices) + 1, mask


def forest(mask, edges):
    parent = {}

    def find(v):
        parent.setdefault(v, v)
        while parent[v] != v:
            v = parent[v]
        return v

    for i, (u, v) in enumerate(edges):
        if mask >> i & 1:
            a, b = find(u), find(v)
            if a == b:
                return False
            parent[a] = b
    return True


def check_cubic_fibers(n, edges):
    adj = adjacency(n, edges)
    allv = set(range(n))
    states = cycle_data(n, edges)[0]
    cores = {}
    for mask in range(1, (1 << n) - 1):
        vertices = {v for v in range(n) if mask >> v & 1}
        if component(adj, next(iter(vertices)), vertices) != vertices:
            continue
        h, _ = rank_and_mask(vertices, edges)
        if h < 1:
            continue
        old_boundary = sum((u in vertices) != (v in vertices) for u, v in edges)
        core = set(vertices)
        while True:
            leaves = [v for v in core
                      if sum(u in core for e in edges for u in
                             ([e[1]] if e[0] == v else [e[0]] if e[1] == v else [])) == 1]
            if not leaves:
                break
            core.remove(leaves[0])
        hc, emask = rank_and_mask(core, edges)
        new_boundary = sum((u in core) != (v in core) for u, v in edges)
        assert hc == h and new_boundary <= old_boundary
        degrees = {v: sum((u == v and w in core) or (w == v and u in core)
                          for u, w in edges) for v in core}
        assert all(degree in (2, 3) for degree in degrees.values())
        assert sum(degree == 2 for degree in degrees.values()) == new_boundary
        cores[frozenset(core)] = (hc, emask)
        STATS['core_prunings'] += 1
    for av, bv in itertools.combinations(cores, 2):
        if av & bv:
            continue
        ha, a = cores[av]
        hb, b = cores[bv]
        outside = ((1 << len(edges)) - 1) ^ (a | b)
        fibers = defaultdict(set)
        for state in states:
            fibers[state & outside].add((state & a, state & b))
        for points in fibers.values():
            ap = {x for x, _ in points}
            bp = {y for _, y in points}
            assert len(ap) == 1 << ha and len(bp) == 1 << hb
            assert len(points) == len(ap) * len(bp)
            assert points == set(itertools.product(ap, bp))
            fa = sum(forest(x, edges) for x in ap)
            fb = sum(forest(y, edges) for y in bp)
            both = sum(forest(x, edges) and forest(y, edges) for x, y in points)
            assert Fraction(both, len(points)) == Fraction(fa, len(ap)) * Fraction(fb, len(bp))
            STATS['affine_product_fibers'] += 1
        STATS['disjoint_core_pairs'] += 1
    STATS['cubic_graphs'] += 1


def geng_graphs(arguments):
    proc = subprocess.Popen([GENG, '-cq', *arguments], stdout=subprocess.PIPE)
    for line in proc.stdout:
        yield graph6_edges(line)
    assert proc.wait() == 0


def main():
    for n in range(2, 7):
        for order, edges in geng_graphs(['-D4', str(n)]):
            for mask in range(1, (1 << n) - 1):
                check_intervals(order, edges, {v for v in range(n) if mask >> v & 1})
            STATS['small_quotient_graphs'] += 1
    # Long chains make the interval and disjoint-segment assertions nonvacuous.
    for n in (8, 12, 18, 24):
        edges = [(v, (v + 1) % n) for v in range(n)]
        for copies in (1, 2):
            check_intervals(n, edges * copies, {0})
            STATS['long_quotient_fixtures'] += 1
    for n in (4, 6, 8, 10):
        for order, edges in geng_graphs(['-d3', '-D3', str(n)]):
            check_cubic_fibers(order, edges)
    for m in (3, 4, 5):
        edges = [(2 * i, 2 * i + 1) for i in range(m)] * 2
        edges += [(2 * i + 1, (2 * i + 2) % (2 * m)) for i in range(m)]
        check_cubic_fibers(2 * m, edges)
    result = {'status': 'all exact checks passed', 'counts': dict(STATS),
              'scope': ['actual terminal bipartitions and articulation components',
                        'terminal-free interval boundaries and disjoint segments',
                        'rank preservation and boundary decrease under core pruning',
                        'complete conditional Cartesian products of affine states',
                        'exact rational conditional forest product law'],
              'limitation': 'The analytic high-girth forest threshold is not numerically tested.'}
    out = HERE / 'four-high-connectivity-iterative-packing-checks.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
