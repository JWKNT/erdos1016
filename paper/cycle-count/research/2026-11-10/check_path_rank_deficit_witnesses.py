#!/usr/bin/env python3
"""Independent DFS verification of saved rank-distance catalogue witnesses."""
from collections import deque
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parent

def decode(text):
    n = ord(text[0]) - 63
    edges = []
    bit = 0
    for j in range(1, n):
        for i in range(j):
            if (ord(text[1 + bit // 6]) - 63) >> (5 - bit % 6) & 1:
                edges.append((i, j))
            bit += 1
    return n, edges

def verify(record):
    n, edges = decode(record['graph6'])
    removed = record['edge']
    source, target = edges[removed]
    adj = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        if e != removed:
            adj[u].append(v)
            adj[v].append(u)
    distance = [-1] * n
    distance[source] = 0
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if distance[v] == -1:
                distance[v] = distance[u] + 1
                queue.append(v)
    def count(u, visited):
        if u == target:
            return 1
        return sum(count(v, visited | (1 << v))
                   for v in adj[u] if not (visited >> v & 1))
    paths = count(source, 1 << source)
    b = len(edges) - n
    assert b == record['b']
    assert paths == record['paths']
    assert distance[target] == record['ell']
    assert paths - 2**(b - 1) == record['excess_count']
    return n, b, paths, distance[target]

def main():
    catalogue = json.loads((ROOT / 'path-rank-deficit-catalog-results.json').read_text())
    witnesses = {}
    for row in catalogue:
        records = [row['maximum_scaled_excess'],
                   row['maximum_scaled_excess_per_rank'],
                   *row['by_rank_distance_deficit'].values()]
        for record in records:
            witnesses[(record['graph6'], record['edge'])] = record
    results = [verify(record) for record in witnesses.values()]
    summary = {
        'status': 'PASS',
        'catalogue_graphs': sum(row['graphs'] for row in catalogue),
        'independently_checked_witnesses': len(results),
        'max_order': max(row[0] for row in results),
        'max_rank': max(row[1] for row in results),
        'method': 'direct vertex-simple DFS, independent of cycle-space enumeration',
    }
    (ROOT / 'path-rank-deficit-witness-checks.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))

if __name__ == '__main__':
    main()
