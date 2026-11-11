"""Reproduce the finite 4-regular check with nauty and an exact C++ verifier.

Nauty geng 2.8.9 supplies every connected simple underlying graph once.
The verifier tries every existing-edge matching of the degree-three vertices.
It counts short cycles exactly and applies certified integer inequalities.
An independent binary-cycle-space implementation checks all small instances.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent


def graph6(line):
    n = ord(line[0]) - 63
    edges, bit = [], 0
    for v in range(1, n):
        for u in range(v):
            if (ord(line[1 + bit // 6]) - 63) >> (5 - bit % 6) & 1:
                edges.append((u, v))
            bit += 1
    return n, edges


def matchings(n, edges):
    degree = [0] * n
    for u, v in edges:
        degree[u] += 1
        degree[v] += 1
    odd = [v for v in range(n) if degree[v] == 3]
    present = set(edges)
    def has(u, v):
        return tuple(sorted((u, v))) in present
    if not odd:
        return [[]]
    if len(odd) == 2:
        return [[tuple(odd)]] if has(*odd) else []
    out = []
    for j in range(1, 4):
        rem = [odd[z] for z in range(1, 4) if z != j]
        if has(odd[0], odd[j]) and has(*rem):
            out.append([(odd[0], odd[j]), tuple(rem)])
    return out


def cycle_space_histogram(n, edges):
    """Fundamental binary cycle space; retain connected 2-regular sets."""
    parent = list(range(n))
    tree = [[] for _ in range(n)]
    chords = []
    def root(u):
        while parent[u] != u:
            u = parent[u]
        return u
    for i, (u, v) in enumerate(edges):
        ru, rv = root(u), root(v)
        if ru == rv:
            chords.append((i, u, v))
        else:
            parent[ru] = rv
            tree[u].append((v, i))
            tree[v].append((u, i))
    def path(u, v, prev=-1):
        if u == v:
            return 0
        for w, i in tree[u]:
            if w != prev:
                p = path(w, v, u)
                if p is not None:
                    return p | (1 << i)
        return None
    basis = [(1 << i) | path(u, v) for i, u, v in chords]
    masks = [0]
    for b in basis:
        masks += [x ^ b for x in masks]
    inc = [0] * n
    for i, (u, v) in enumerate(edges):
        inc[u] |= 1 << i
        inc[v] |= 1 << i
    hist = [0] * (n + 1)
    for mask in masks[1:]:
        active = [u for u in range(n) if mask & inc[u]]
        if any((mask & inc[u]).bit_count() != 2 for u in active):
            continue
        seen, stack = {active[0]}, [active[0]]
        while stack:
            u = stack.pop()
            rem = inc[u] & mask
            while rem:
                bit = rem & -rem
                rem -= bit
                a, b = edges[bit.bit_length() - 1]
                v = b if a == u else a
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        if len(seen) == len(active):
            hist[mask.bit_count()] += 1
    return hist[2:]


def small_checks(geng, checker, max_n):
    cases = 0
    for n in range(4, max_n + 1):
        for k in range(3):
            if 2*n-k > n*(n-1)//2:
                continue
            p = subprocess.run([geng, '-q', '-c', '-d3', '-D4', str(n), str(2*n-k)],
                               capture_output=True, check=True, text=True)
            q = subprocess.run([checker, '-', '--emit'], input=p.stdout,
                               capture_output=True, check=True, text=True)
            for line in q.stderr.splitlines():
                assert line.startswith('CHECK '), line
                _, g6, mi, *counts = line.split()
                nn, edges = graph6(g6)
                pairs = matchings(nn, edges)[int(mi)]
                expected = cycle_space_histogram(nn, edges + pairs)
                assert expected == list(map(int, counts)), (g6, pairs, expected, counts)
                cases += 1
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--geng', default='/tmp/nauty2_8_9/geng')
    ap.add_argument('--checker', default='/tmp/check_four_regular_finite')
    ap.add_argument('--small-max-n', type=int, default=8)
    ap.add_argument('--classes', default='11,0;12,0;13,0;11,1;12,1;13,1;14,1;11,2;12,2;13,2;14,2')
    ap.add_argument('--output', type=Path, default=HERE/'four-regular-finite-results.json')
    args = ap.parse_args()
    certificates = json.loads((HERE/'four-regular-enumeration-bounds.json').read_text())
    text_path = HERE/'four-regular-enumeration-bounds.txt'
    with text_path.open('w') as f:
        for r in certificates['rows']:
            for g in r['cutoffs']:
                print(r['n'], r['k'], r['length_sum_upper'], g,
                      *[r['short_cycle_upper'][str(l)] for l in range(3, g)], file=f)
    started = time.time()
    report = {'status': 'in progress', 'nauty_version': '2.8.9',
              'independent_small_checks': small_checks(args.geng, args.checker, args.small_max_n),
              'independent_small_max_n': args.small_max_n,
              'source_sha256': {}, 'classes': []}
    for p in [Path(args.geng), Path(args.checker), Path(__file__),
              HERE/'check_four_regular_finite.cpp', HERE/'four-regular-enumeration-bounds.json']:
        report['source_sha256'][str(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    for pair in args.classes.split(';'):
        if not pair:
            continue
        n, k = map(int, pair.split(','))
        cmd = [args.geng, '-c', '-d3', '-D4', str(n), str(2*n-k)]
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        q = subprocess.Popen([args.checker, str(text_path)], stdin=p.stdout,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        p.stdout.close()
        out, err = q.communicate()
        generation = p.stderr.read().decode()
        assert p.wait() == 0, generation
        assert q.returncode == 0, err.decode()
        r = json.loads(out)
        assert (r['n'], r['k']) == (n, k), r
        assert r['multigraph_instances'] == r['full_cycle_counts'] + sum(r['passed_after_length'].values())
        r['generator_command'] = cmd
        r['generator_report'] = generation
        report['classes'].append(r)
        args.output.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(r), flush=True)
    report['status'] = 'all requested classes passed'
    report['total_seconds'] = time.time()-started
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
