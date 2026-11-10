"""The examples of the paper, checked by direct enumeration.

  * Example 2.2 and Figure 1: a triangle W and a chain N of two four-cycles.
    Eight outside parts, five of them forests; nine cycles use an edge of W.
  * Section 3.1: the ring of j four-cycles has rank j + 1 and 2^j + j cycles.
  * Section 7, condition (ii): K5 minus an edge, with W the triangle on the
    three vertices of degree four. Sixteen outside parts: the empty set,
    twelve paths and three four-cycles. No outside part is wasted, and
    thirteen are forests.
  * Section 7.2: a cycle W with a path of length two between consecutive
    vertices. No outside part is wasted, and rank(G) - rank(W) = |V(W)|.
All arithmetic is exact. Run:  python3 check_examples.py
"""
from lib import *


def outside_parts(n, E, W):
    """Map each outside part to the list of even subgraphs that have it."""
    parts = {}
    for z in span(cyc_basis(n, E)):
        parts.setdefault(z & ~W, []).append(z)
    return parts


def edge_mask(E, edges):
    index = {e: i for i, e in enumerate(E)}
    return sum(1 << index[(min(a, b), max(a, b))] for a, b in edges)


# Example 2.2 with k = 2: vertices u=0, v=1, w=2 (triangle W); chain 0-3-4-1 and 0-5-4-1...
# The chain N: four-cycle 0,3,6,4 and four-cycle 6,5,1,7 joined at vertex 6.
E = sorted({(0, 1), (0, 2), (1, 2), (0, 3), (3, 6), (0, 4), (4, 6), (5, 6), (1, 5), (6, 7), (1, 7)})
n = 8
W = edge_mask(E, [(0, 1), (0, 2), (1, 2)])
parts = outside_parts(n, E, W)
assert len(cyc_basis(n, E)) == 4
assert len(parts) == 8
assert sum(1 for x in parts if is_forest(n, E, x)) == 5
cycles = [z for z in span(cyc_basis(n, E)) if is_cycle(n, E, z)]
assert sum(1 for c in cycles if c & W) == 9
print("Example 2.2 (k = 2): 8 outside parts, 5 forests, 9 cycles through W")

# Section 3.1: the ring of j four-cycles.
for j in range(2, 8):
    E = []
    for i in range(j):
        u, u2, x, y = i, (i + 1) % j, j + 2 * i, j + 2 * i + 1
        E += [(min(u, x), max(u, x)), (min(u2, x), max(u2, x)),
              (min(u, y), max(u, y)), (min(u2, y), max(u2, y))]
    E = sorted(set(E))
    n = 3 * j
    assert len(E) == 4 * j
    basis = cyc_basis(n, E)
    assert len(basis) == j + 1
    assert sum(1 for z in span(basis) if is_cycle(n, E, z)) == 2 ** j + j
print("ring of j four-cycles, j = 2..7: rank j + 1 and 2^j + j cycles")

# K5 minus the edge (3,4); W is the triangle on 0, 1, 2.
n = 5
E = sorted({(a, b) for a in range(5) for b in range(a + 1, 5)} - {(3, 4)})
W = edge_mask(E, [(0, 1), (0, 2), (1, 2)])
parts = outside_parts(n, E, W)
assert len(parts) == 16
kinds = {"empty": 0, "path": 0, "four-cycle": 0}
for x in parts:
    if x == 0:
        kinds["empty"] += 1
    elif is_forest(n, E, x):
        kinds["path"] += 1
    else:
        assert is_cycle(n, E, x) and bin(x).count("1") == 4
        kinds["four-cycle"] += 1
assert kinds == {"empty": 1, "path": 12, "four-cycle": 3}
assert all(any(is_cycle(n, E, z) for z in cls) for cls in parts.values())
print("K5 minus an edge: 16 outside parts =", kinds, "- none wasted, 13 forests")

# A cycle W of length m with a path of length two between consecutive vertices.
for m in range(3, 7):
    E = []
    for i in range(m):
        a, b, x = i, (i + 1) % m, m + i
        E += [(min(a, b), max(a, b)), (min(a, x), max(a, x)), (min(b, x), max(b, x))]
    E = sorted(set(E))
    n = 2 * m
    W = edge_mask(E, [(i, (i + 1) % m) for i in range(m)])
    parts = outside_parts(n, E, W)
    assert all(any(is_cycle(n, E, z) for z in cls) for cls in parts.values())
    assert len(cyc_basis(n, E)) - 1 == m
print("cycle with ears, m = 3..6: no outside part wasted, rank(G) - rank(W) = m")
print("all assertions passed")
