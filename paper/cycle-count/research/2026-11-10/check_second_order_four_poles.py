#!/usr/bin/env python3
"""Independent finite checks; no claim about unexamined graph classes."""
import itertools
import json
from pathlib import Path
from check_second_order_constructions import paths


def block_form(pi):
    i = swaps = 0
    while i < len(pi):
        if pi[i] == i:
            i += 1
        elif i+1 < len(pi) and pi[i:i+2] == (i+1,i):
            i += 2
            swaps += 1
        else:
            return None
    return swaps


def count_through(k, edges):
    adj = [0]*(2*k)
    for a,b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    def second(v,t,seen):
        if v == t:
            return 1
        rest = adj[v] & ~seen
        ans = 0
        while rest:
            bit = rest & -rest
            rest -= bit
            ans += second(bit.bit_length()-1,t,seen|bit)
        return ans
    def first(v,t,s2,t2,seen):
        if v == t:
            return second(s2,t2,seen|(1 << s2))
        rest = adj[v] & ~seen & ~(1 << s2) & ~(1 << t2)
        ans = 0
        while rest:
            bit = rest & -rest
            rest -= bit
            ans += first(bit.bit_length()-1,t,s2,t2,seen|bit)
        return ans
    return first(0,k-1,k,2*k-1,1)+first(0,2*k-1,k,k-1,1)


def main():
    rows = []
    for k in range(2,8):
        good = tested = 0
        for pi in itertools.permutations(range(k)):
            edges = ([(i,i+1) for i in range(k-1)]
                     + [(k+i,k+i+1) for i in range(k-1)]
                     + [(i,k+pi[i]) for i in range(k)])
            saturated = all(paths(2*k,edges,s,t) == 2**(k-1)
                            for s in (0,k) for t in (k-1,2*k-1))
            swaps = block_form(pi)
            assert saturated == (swaps is not None), (k,pi)
            if saturated:
                assert count_through(k,edges) == 2**swaps, (k,pi)
                good += 1
            tested += 1
        rows.append(dict(ladder_order=k,tested=tested,saturated=good))
    root = Path(__file__).resolve().parent
    checks = []
    for row in map(json.loads,(root/'second-order-four-pole-search.jsonl').read_text().splitlines()):
        b = row['rank']
        n = 2*b-1
        s,t,w = n-3,n-2,n-1
        edges = row['K_edges'] + [[s,w],[t,w],[s,0],[t,1],[w,2],[w,3]]
        value = paths(n,edges,s,t)
        assert value == row['paths'], (b,value,row['paths'])
        checks.append(dict(rank=b,paths=value,excess=value-2**(b-1)))
    print(json.dumps(dict(permutation_checks=rows,independent_search_checks=checks),indent=2))


if __name__ == '__main__':
    main()
