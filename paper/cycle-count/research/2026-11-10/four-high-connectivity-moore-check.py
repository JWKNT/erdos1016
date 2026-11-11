#!/usr/bin/env python3
"""Exact finite checks of Moore-ball geometry, not a proof of the lemma."""
from collections import deque
from itertools import combinations
import json
from pathlib import Path


def edge(u, v):
    return min(u, v), max(u, v)


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    return adj


def bfs(adj, source, omitted=None):
    distance = [-1] * len(adj)
    parent = [-1] * len(adj)
    distance[source] = 0
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in sorted(adj[u]):
            if omitted == edge(u, v) or distance[v] >= 0:
                continue
            distance[v] = distance[u] + 1
            parent[v] = u
            queue.append(v)
    return distance, parent


def girth(adj, edges):
    cycles = []
    for u, v in edges:
        distance, _ = bfs(adj, u, edge(u, v))
        if distance[v] >= 0:
            cycles.append(distance[v] + 1)
    assert cycles
    return min(cycles)


def bases():
    result = [('K4', 4, set(combinations(range(4), 2)))]
    result.append(('cube', 8, {edge(u, u ^ (1 << j)) for u in range(8) for j in range(3)}))
    petersen = {edge(i, (i + 1) % 5) for i in range(5)}
    petersen |= {edge(i, i + 5) for i in range(5)}
    petersen |= {edge(i + 5, (i + 2) % 5 + 5) for i in range(5)}
    result.append(('Petersen', 10, petersen))
    # Incidence graph of the seven cyclic Fano-plane lines {i,i+1,i+3}.
    heawood = {edge(i, 7 + j) for j in range(7) for i in (j, (j + 1) % 7, (j + 3) % 7)}
    result.append(('Heawood', 14, heawood))
    L, width = 8, 4
    vertex = lambda x, y, s: 2 * (width * (x % L) + y % width) + s
    honeycomb = {edge(vertex(x, y, 0), vertex(x + dx, y + dy, 1))
                 for x in range(L) for y in range(width)
                 for dx, dy in ((0, 0), (1, 0), (0, 1))}
    result.append(('honeycomb8x4', 2 * L * width, honeycomb))
    return result


def subdivide(n, edges, indices):
    result = set(edges)
    ordered = sorted(edges)
    for index in indices:
        u, v = ordered[index]
        result.remove((u, v))
        result.update((edge(u, n), edge(v, n)))
        n += 1
    return n, result


def check(name, n, edges):
    adj = adjacency(n, edges)
    ports = {u for u in range(n) if len(adj[u]) == 2}
    assert all(len(adj[u]) in (2, 3) for u in range(n))
    assert min(bfs(adj, 0)[0]) >= 0
    k = len(ports)
    g = girth(adj, edges)
    h = len(edges) - n + 1
    assert n == 2 * h + k - 2
    t = (g - 1) // 2
    B = 3 * (1 << t) - 2
    assert B * B >= 1 << g
    all_bfs = [bfs(adj, u) for u in range(n)]
    balls = [{v for v in range(n) if all_bfs[u][0][v] <= t} for u in range(n)]
    for u in range(n):
        if not balls[u] & ports:
            assert len(balls[u]) >= B
    checked = packed_balls = good_balls = 0
    for source in range(n):
        distances, parent = all_bfs[source]
        for target in range(source + 1, n):
            path = [target]
            while path[-1] != source:
                path.append(parent[path[-1]])
            path.reverse()
            ell = distances[target]
            assert len(path) == ell + 1
            centers = [path[j] for j in range(t, ell - t + 1, 2 * t + 1)]
            assert len(centers) == (ell + 1) // (2 * t + 1)
            union = set()
            bad = 0
            good = 0
            for center in centers:
                ball = balls[center]
                assert not union & ball
                union |= ball
                if ball & ports:
                    bad += 1
                else:
                    good += 1
                    assert len(ball) >= B
            assert bad <= k
            assert good * B <= n
            assert (ell + 1) * B < (2 * t + 1) * ((k + 1) * B + n)
            checked += 1
            packed_balls += len(centers)
            good_balls += good
    if k == 2:
        for u in ports:
            sphere = sum(distance == t for distance in all_bfs[u][0])
            assert sphere >= 1 << (t - 1)
    entropy_checked = False
    exponential_shore_checked = False
    if h >= 2:
        # Count non-backtracking walks exactly. Entropy is tested by an
        # integer-power comparison, with no floating logarithms.
        directed = {(u, v): 1 for u in range(n) for v in adj[u]}
        for _ in range(t - 1):
            incoming = [0] * n
            for (u, v), count in directed.items():
                incoming[v] += count
            directed = {(u, v): incoming[u] - directed[(v, u)]
                        for u in range(n) for v in adj[u]}
        walks = sum(directed.values())
        numerator = 3 * (h - 1)
        denominator = 3 * h + k - 3
        assert walks <= n * n
        assert walks ** denominator >= (2 * len(edges)) ** denominator * (1 << ((t - 1) * numerator))
        if g >= 4:
            assert 1 << ((g - 4) * numerator) <= n ** (2 * denominator)
        entropy_checked = True
        if g >= k:
            assert k <= 6 * (h - 1)
            if g >= 22:
                assert (h - 1) ** 6 >= 1 << (g - 22)
            exponential_shore_checked = True
    return dict(name=name, order=n, rank=h, ports=k, girth=g,
                geodesics=checked, packed_balls=packed_balls, port_free_balls=good_balls,
                terminal_sphere_checks=2 if k == 2 else 0,
                entropy_walk_check=entropy_checked,
                exponential_shore_check=exponential_shore_checked)


def main():
    results = []
    for name, n, edges in bases():
        results.append(check(name, n, edges))
        ordered = sorted(edges)
        for k in sorted({1, 2, 3, 5, min(8, len(edges)), len(edges)}):
            indices = sorted({j * len(edges) // k for j in range(k)})
            new_n, new_edges = subdivide(n, edges, indices)
            results.append(check(f'{name}-subdivide{k}', new_n, new_edges))
        # Removing one edge gives a different normalized-two-pole mechanism.
        for j in sorted({0, len(edges) // 2, len(edges) - 1}):
            results.append(check(f'{name}-delete-edge{j}', n, edges - {ordered[j]}))
    output = dict(status='all_checks_passed', fixture_count=len(results),
                  total_geodesics=sum(row['geodesics'] for row in results),
                  total_packed_balls=sum(row['packed_balls'] for row in results),
                  total_port_free_balls=sum(row['port_free_balls'] for row in results),
                  total_terminal_sphere_checks=sum(row['terminal_sphere_checks'] for row in results),
                  total_entropy_walk_checks=sum(row['entropy_walk_check'] for row in results),
                  total_exponential_shore_checks=sum(row['exponential_shore_check'] for row in results),
                  fixtures=results)
    destination = Path(__file__).with_name('four-high-connectivity-moore-checks.json')
    destination.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({key: value for key, value in output.items() if key != 'fixtures'}, indent=2))


if __name__ == '__main__':
    main()
