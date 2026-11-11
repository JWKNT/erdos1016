"""Exact checks of mixed-ring counts, cap counts, and the four-port high graph.

No floating-point optimization is used. The graph checks enumerate binary
cycle spaces independently of the new closed formulas.
"""

from collections import Counter, defaultdict
from fractions import Fraction
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / '2026-11-10'))
from check_cubic_edge_frequency import cycle_space_cycles


def words(weight):
    if weight == 0:
        yield ()
    if weight >= 1:
        for tail in words(weight - 1):
            yield (1,) + tail
    if weight >= 2:
        for tail in words(weight - 2):
            yield (2,) + tail


def graph(word, closed, twist=False):
    n = 0
    edges = []
    left = []
    right = []
    for tile in word:
        left.append((n, n + 1))
        if tile == 1:
            right.append((n, n + 1))
            edges.append((n, n + 1))
            n += 2
        else:
            right.append((n + 2, n + 3))
            edges.extend((u, v) for u in (n, n + 1) for v in (n + 2, n + 3))
            n += 4
    for i in range(len(word) - 1):
        edges.extend(zip(right[i], left[i + 1]))
    if closed:
        end = left[0][::-1] if twist else left[0]
        edges.extend(zip(right[-1], end))
    return n, list(edges), left[0], right[-1]


def exact_formula(word, twist):
    a = word.count(2)
    s = word.count(1)
    W = 2 * a + s
    if a == 0:
        return 2 ** W + W * (W - 1) + int(twist)
    Q = Fraction(0)
    for i in range(len(word)):
        factor = Fraction(1)
        for length in range(len(word)):
            Q += factor
            factor /= word[(i + length) % len(word)]
    return 2 ** W + 2 ** a * (Q + Fraction(1, 2)) - len(word)


def max_formula(a, s):
    return (2 ** a * (2 * a + 4 * s + s * (s - 1) // 2)
            + 2 ** (a - 1) - 3 * a - 4 * s + s * (s - 1) // 2)


def hk_excess(W):
    return max_formula(W // 2, W % 2)


def paths(n, edges, source, target):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    out = []

    def visit(v, seen, chosen):
        if v == target:
            out.append((seen, chosen))
            return
        for u, i in adj[v]:
            if not (seen >> u & 1):
                visit(u, seen | 1 << u, chosen | 1 << i)
    visit(source, 1 << source, 0)
    return out


def check_high_profiles():
    pairs = list(itertools.combinations(range(4), 2))
    idx = {e: i for i, e in enumerate(pairs)}
    record = []
    maximum_nonexception = Fraction(0)
    cases = 0
    for mask in range(64):
        H = {e for i, e in enumerate(pairs) if mask >> i & 1}
        if any(all(tuple(sorted(e)) in H for e in itertools.combinations(T, 2))
               for T in itertools.combinations(range(4), 3)):
            continue
        high = [i for i in range(6) if mask >> i & 1]
        low = [i for i in range(6) if not (mask >> i & 1)]
        forced = set()
        for v in range(4):
            neighbors = [u for u in range(4) if u != v and tuple(sorted((u, v))) in H]
            for u, w in itertools.combinations(neighbors, 2):
                forced.add(idx[tuple(sorted((u, w)))])
        for fullbits in range(1 << len(high)):
            full = {i for j, i in enumerate(high) if fullbits >> j & 1}
            for smallbits in range(1 << len(low)):
                small = {i for j, i in enumerate(low) if smallbits >> j & 1}
                if not forced <= small:
                    continue
                valid = True
                for i in full:
                    u, v = pairs[i]
                    for w in range(4):
                        if w not in (u, v):
                            if not ({idx[tuple(sorted((u, w)))], idx[tuple(sorted((v, w)))]} & small):
                                valid = False
                if not valid:
                    continue
                values = [Fraction(1) if i in full else Fraction(15, 16) if i in high
                          else Fraction(1, 100) if i in small else Fraction(51, 100)
                          for i in range(6)]
                total = sum(values)
                exception = len(H) == 4 and len(full) == 4
                if not exception:
                    maximum_nonexception = max(maximum_nonexception, total)
                    assert total < Fraction(398, 100)
                cases += 1
    return {'feasible_endpoint_profiles': cases,
            'maximum_path_sum_outside_full_K22': str(maximum_nonexception)}


def main():
    stats = Counter()
    grouped = defaultdict(list)
    rank_maxima = []
    for W in range(3, 11):
        best = -1
        best_word = None
        for word in words(W):
            for twist in (False, True):
                n, edges, _, _ = graph(word, True, twist)
                cycles, _ = cycle_space_cycles(n, edges)
                actual = len(cycles)
                assert actual == exact_formula(word, twist), (word, twist, actual)
                stats['closed_graphs'] += 1
                stats['even_states'] += 2 ** (W + 1)
                if actual > best:
                    best, best_word = actual, word
                if word.count(2):
                    grouped[word.count(2), word.count(1)].append(actual - 2 ** W)
        if W >= 7:
            assert best == 2 ** W + hk_excess(W)
        rank_maxima.append({'rank': W + 1, 'max_cycles': best,
                            'witness_word': list(best_word),
                            'HK_cycles': 2 ** W + hk_excess(W)})
    for (a, s), counts in grouped.items():
        assert max(counts) == max_formula(a, s)
    for W in range(2, 9):
        for word in words(W):
            n, edges, left, right = graph(word, False)
            if len(set(left + right)) < 4:
                continue
            L = paths(n, edges, *left)
            R = paths(n, edges, *right)
            C = sum(not (a & b) for a, _ in L for b, _ in R)
            expected = sum(2 ** (word.count(2) - word[i + 1:j].count(2))
                           for i in range(len(word)) for j in range(i + 1, len(word)))
            assert C == expected
            through = 0
            for pairing in (right, right[::-1]):
                p = paths(n, edges, left[0], pairing[0])
                q = paths(n, edges, left[1], pairing[1])
                through += sum(not (a & b) for a, _ in p for b, _ in q)
            assert through == 2 ** word.count(2)
            for u in left:
                for v in right:
                    assert len(paths(n, edges, u, v)) == 2 ** (W - 1)
            stats['open_chains'] += 1
    for W in range(7, 501):
        target = hk_excess(W)
        assert target > W * (W - 1) + 1
        for a in range(1, W // 2 + 1):
            s = W - 2 * a
            assert max_formula(a, s) <= target
            stats['integer_optimization_cases'] += 1
    result = {'status': 'all exact checks passed', 'counts': dict(stats),
              'small_rank_ring_maxima': rank_maxima,
              'four_port_endpoint_profiles': check_high_profiles(),
              'scope': 'Cycle spaces, path pairs, and integer profile bounds; no asymptotic inference from enumeration.'}
    target = HERE / 'four-coefficient-checks.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
