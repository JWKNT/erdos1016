#!/usr/bin/env python3
"""Check the constructive cyclic-cut certificate after arbitrary port restorations."""

import collections
import json
import random
from pathlib import Path

from check_four_regular_positive_port_localization import piece
from check_second_order_path_gap import compositions


def candidates(blocks, offset):
    b = sum(blocks) + 1
    n = 2 * b
    if b <= 4:
        return [set(range(offset, offset + n))]
    w = b - 1
    answer = []
    p = 0
    pending = None
    for size in blocks:
        if size == 2:
            answer.append({offset + p, offset + p + 1,
                           offset + w + p, offset + w + p + 1})
            pending = None
        elif pending is None:
            pending = p
        else:
            answer.append({offset + pending, offset + p,
                           offset + w + pending, offset + w + p})
            pending = None
        p += size
    assert 5 * len(answer) >= b
    return answer


def chain_with_candidates(pieces):
    total = 0
    edges = []
    sets = []
    first = previous = None
    for blocks in pieces:
        n, local, a, c = piece(blocks)
        edges.extend((u + total, v + total) for u, v in local)
        sets.extend(candidates(blocks, total))
        if previous is None:
            first = a + total
        else:
            edges.append((previous, a + total))
        previous = c + total
        total += n
    return total, edges, first, previous, sets


def cyclic(edges, vertices):
    parent = {v: v for v in vertices}
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for u, v in edges:
        if u not in vertices or v not in vertices:
            continue
        a, b = find(u), find(v)
        if a == b:
            return True
        parent[a] = b
    return False


def restore_and_complete(n, edges, a, c, marked):
    ports = [a, c]
    restored = []
    for i, (u, v) in enumerate(edges):
        previous = u
        for _ in range(marked[i]):
            restored.append((previous, n))
            ports.append(n)
            previous = n
            n += 1
        restored.append((previous, v))
    k = len(ports)
    if k == 2:
        restored.append(tuple(ports))
        return n, restored
    internal = list(range(n, n + k - 2))
    n += k - 2
    restored.extend(zip(internal, internal[1:]))
    free = iter(ports)
    for j, v in enumerate(internal):
        degree = 3 - (j > 0) - (j + 1 < len(internal))
        restored.extend((v, next(free)) for _ in range(degree))
    return n, restored


def random_blocks(rng, positions):
    result = []
    while positions:
        size = rng.randint(1, min(2, positions))
        result.append(size)
        positions -= size
    return tuple(result)


def main():
    stats = collections.Counter()
    for w in range(14):
        for blocks in compositions(w):
            local = candidates(blocks, 0)
            n, edges, _, _ = piece(blocks)
            assert all(cyclic(edges, v) for v in local)
            assert all(not (x & y) for i, x in enumerate(local) for y in local[i + 1:])
            stats['exact_piece_candidate_checks'] += 1

    rng = random.Random(20261111)
    for k in range(2, 10):
        for trial in range(100):
            if trial % 2:
                pieces = [random_blocks(rng, 5 * k + rng.randrange(1, 50))]
            else:
                pieces = [random_blocks(rng, rng.randrange(12))
                          for _ in range(5 * k)]
            n, edges, a, c, sets = chain_with_candidates(pieces)
            rank = len(edges) - n + 1
            assert rank > 5 * k
            assert 5 * len(sets) >= rank
            assert all(not (x & y) for i, x in enumerate(sets) for y in sets[i + 1:])
            marked = collections.Counter(rng.randrange(len(edges)) for _ in range(k - 2))
            spoiled = [v for v in sets
                       if any(count and edges[e][0] in v and edges[e][1] in v
                              for e, count in marked.items())]
            good = [v for v in sets if v not in spoiled]
            assert len(spoiled) <= k - 2
            assert len(good) >= 2
            order, completed = restore_and_complete(n, edges, a, c, marked)
            degree = collections.Counter(v for e in completed for v in e)
            assert all(degree[v] == 3 for v in range(order))
            for selected in good:
                cut = [(u, v) for u, v in completed if (u in selected) != (v in selected)]
                assert 1 <= len(cut) <= 4
                assert cyclic(completed, selected)
                assert cyclic(completed, set(range(order)) - selected)
                stats['exact_cyclic_cut_certificates'] += 1
            stats['completed_cubic_graphs'] += 1
            stats['restored_ports'] += k - 2
    result = {
        'status': 'all candidate, restoration, and cyclic-cut certificates passed',
        'checks': dict(stats),
        'scope': 'Structured saturated pieces and deterministic random port placements; exact cut certificates, not a numerical bound test.'
    }
    Path(__file__).with_name('four-regular-saturated-small-cut-checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
