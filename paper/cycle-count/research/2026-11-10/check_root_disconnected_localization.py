#!/usr/bin/env python3
"""Exact restriction-law checks; these do not test asymptotic estimates."""
from collections import Counter
from pathlib import Path
import json
import random


def components(V, E):
    adj = {v: [] for v in V}
    for u, v in E:
        adj[u].append(v); adj[v].append(u)
    unseen = set(V); result = []
    while unseen:
        part = {next(iter(unseen))}; queue = list(part)
        for u in queue:
            for v in adj[u]:
                if v not in part:
                    part.add(v); queue.append(v)
        unseen -= part; result.append(part)
    return result


def basis(V, E):
    adj = {v: [] for v in V}
    for i, (u, v) in enumerate(E):
        adj[u].append((v, i)); adj[v].append((u, i))
    masks = {}; tree = set()
    for root in V:
        if root in masks: continue
        masks[root] = 0; queue = [root]
        for u in queue:
            for v, i in adj[u]:
                if v not in masks:
                    masks[v] = masks[u] ^ (1 << i)
                    tree.add(i); queue.append(v)
    return [masks[u] ^ masks[v] ^ (1 << i)
            for i, (u, v) in enumerate(E) if i not in tree]


def histogram(V, E, selected):
    B = basis(V, E); masks = [0]
    for vector in B: masks += [x ^ vector for x in masks]
    out = Counter()
    for word in masks:
        projected = sum(((word >> i) & 1) << j for j, i in enumerate(selected))
        out[projected] += 1
    return out, len(masks), len(B)


def check(V, E, R):
    S = V-R
    assert R and S and len(components(S, [e for e in E if set(e) <= S])) == 1
    ids = [i for i, e in enumerate(E) if set(e) <= R]
    internal = [E[i] for i in ids]
    boundary = [(u if u in R else v) for u, v in E if (u in R) != (v in R)]
    d = len(boundary); assert d
    cap = list(range(max(V)+1, max(V)+1+max(d, 3)))
    Er = internal + list(zip(boundary, cap))
    Er += [(cap[i], cap[(i+1) % len(cap)]) for i in range(len(cap))]
    Vr = R | set(cap)
    assert len(components(Vr, Er)) == 1
    h1, total1, rank1 = histogram(V, E, ids)
    h2, total2, rank2 = histogram(Vr, Er, range(len(internal)))
    assert h1.keys() == h2.keys()
    assert all(h1[x]*total2 == h2[x]*total1 for x in h1)
    c = len(components(R, internal))
    rankR = len(internal)-len(R)+c
    assert rank2 == rankR+d-c+1
    deg = Counter(v for e in E for v in e)
    cubic = all(deg[v] == 3 for v in R)
    if cubic: assert 2*rank2 == len(R)+d+2
    return dict(components=c, boundary=d, cubic=cubic,
                graph_rank=rank1, localized_rank=rank2,
                enumerated_states=total1+total2)


def main():
    rows = []
    # d=1 padding, d=2 padding, and disconnected retained regions.
    fixtures = [({0,1}, [(0,1)], {0}),
                (set(range(3)), [(0,1),(1,2),(2,0)], {0}),
                (set(range(4)), [(0,2),(1,2),(2,3)], {0,1}),
                (set(range(6)), [(0,1),(0,1),(1,2),(2,3),(3,4),(4,5),(5,3)], {0,1,4,5})]
    for fixture in fixtures: rows.append(check(*fixture))
    rng = random.Random(10162026111104)
    graphs = 0
    for n in range(4, 13, 2):
        accepted = 0
        while accepted < 30:
            stubs = list(range(n))*3; rng.shuffle(stubs)
            E = [tuple(stubs[i:i+2]) for i in range(0, len(stubs), 2)]
            V = set(range(n))
            if any(u == v for u,v in E) or len(components(V,E)) != 1: continue
            accepted += 1; graphs += 1
            for _ in range(16):
                R = {v for v in V if rng.randrange(2)}; S = V-R
                if not R or not S: continue
                if len(components(S, [e for e in E if set(e) <= S])) != 1: continue
                rows.append(check(V,E,R))
    report = dict(status='PASS', random_graphs=graphs, checks=len(rows),
                  disconnected_checks=sum(x['components'] > 1 for x in rows),
                  padded_checks=sum(x['boundary'] < 3 for x in rows),
                  cubic_rank_checks=sum(x['cubic'] for x in rows),
                  enumerated_states=sum(x['enumerated_states'] for x in rows),
                  max_localized_rank=max(x['localized_rank'] for x in rows),
                  scope='Exact full restriction distributions and rank formulas; no asymptotic theorem is inferred from testing.')
    Path(__file__).with_name('root-disconnected-localization-checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__': main()
