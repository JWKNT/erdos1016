"""Exact checks for the statements in fable-notes.md (Fable 5.2, 10 November 2026).

  1. Edge bound and recursion: for an edge e of a cycle W of G,
       c_e(G) <= p(G, W) * 2^(r-1)   and   c(G) = c(G - e) + c_e(G).
  2. Product formula: for connected W,
       p(G, W) = product over the components K of G - E(W) of phi(K, V(K) & V(W)),
     and the same product over the bridges of W is an upper bound.
  3. Localisation: for a connected vertex set R that avoids V(W), with G - R connected,
       P(xi & E(G[R]) is a forest) = p(G_R, W_R) >= p(G, W),
     where G_R is G[R] plus one pendant edge per boundary edge and a cycle W_R
     through the new pendant vertices.
  4. Vertex splitting: the cubic expansion that keeps a shortest terminal path
     does not lower the number of terminal paths, keeps the rank, and keeps
     the terminal distance.
  5. Layers: in the split graph, a window of distance layers outside the
     shortest path satisfies the boundary inequality (4.1) of the notes.
All probabilities are exact fractions. Run:  python3 fable_check_tools.py
"""
import os
import random
import sys
from collections import deque
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "paper-checks"))
from lib import comps, cyc_basis, span, bits, is_cycle, is_forest, rand_connected  # noqa: E402


def forest_prob(n, E, wmask):
    """p(G, W): proportion of even subgraphs whose part outside W is a forest."""
    Z = span(cyc_basis(n, E))
    return Fraction(sum(1 for z in Z if is_forest(n, E, z & ~wmask)), len(Z))


def shortest_path(n, E, s, t, banned=()):
    """Edge indices of a shortest s-t path that avoids the banned edge indices."""
    prev = {s: None}
    dq = deque([s])
    while dq:
        x = dq.popleft()
        if x == t:
            break
        for i, (a, b) in enumerate(E):
            if i in banned or x not in (a, b):
                continue
            y = b if x == a else a
            if y not in prev:
                prev[y] = (x, i)
                dq.append(y)
    if t not in prev:
        return None
    out, x = [], t
    while prev[x] is not None:
        out.append(prev[x][1])
        x = prev[x][0]
    return out


def count_paths(n, E, s, t):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    seen = [False] * n

    def go(x):
        if x == t:
            return 1
        seen[x] = True
        total = sum(go(y) for y in adj[x] if not seen[y])
        seen[x] = False
        return total
    return go(s)


def check_edge_bound(rng, trials=300):
    done = 0
    while done < trials:
        n = rng.randrange(5, 9)
        E = rand_connected(n, rng.randrange(n + 1, n + 6), rng)
        e = rng.randrange(len(E))
        path = shortest_path(n, E, E[e][0], E[e][1], banned=(e,))
        if path is None:
            continue
        wmask = (1 << e) | sum(1 << i for i in path)
        Z = span(cyc_basis(n, E))
        r = len(Z).bit_length() - 1
        cycles = [z for z in Z if is_cycle(n, E, z)]
        c_e = sum(1 for z in cycles if (z >> e) & 1)
        p = forest_prob(n, E, wmask)
        assert c_e <= p * 2 ** (r - 1)
        E2 = E[:e] + E[e + 1:]
        c2 = sum(1 for z in span(cyc_basis(n, E2)) if is_cycle(n, E2, z))
        assert len(cycles) == c2 + c_e
        done += 1
    print("1. edge bound c_e <= p 2^(r-1) and recursion:", trials, "graphs")


def phi(n, E, K, S):
    """Forest probability of a uniform even subgraph of K / S, read in K."""
    rep = min(S)
    EK = [E[i] for i in K]
    Ec = [(rep if a in S else a, rep if b in S else b) for a, b in EK]
    Z = span(cyc_basis(n, Ec))
    return Fraction(sum(1 for z in Z if is_forest(n, EK, z)), len(Z))


def check_product(rng, trials=300):
    done = 0
    while done < trials:
        n = rng.randrange(5, 9)
        E = rand_connected(n, rng.randrange(n + 1, n + 6), rng)
        e = rng.randrange(len(E))
        path = shortest_path(n, E, E[e][0], E[e][1], banned=(e,))
        if path is None:
            continue
        wedges = {e, *path}
        wmask = sum(1 << i for i in wedges)
        wverts = {x for i in wedges for x in E[i]}
        rest = [i for i in range(len(E)) if i not in wedges]
        prods = []
        # exact: components of G - E(W); upper bound: bridges of W
        for through_w in (True, False):
            cls = {i: i for i in rest}

            def find(i):
                while cls[i] != i:
                    i = cls[i]
                return i
            for i in rest:
                for j in rest:
                    shared = set(E[i]) & set(E[j])
                    if i < j and (shared if through_w else shared - wverts):
                        cls[find(i)] = find(j)
            prod = Fraction(1)
            for root in {find(i) for i in rest}:
                K = [i for i in rest if find(i) == root]
                S = {x for i in K for x in E[i]} & wverts
                prod *= phi(n, E, K, S)
            prods.append(prod)
        p = forest_prob(n, E, wmask)
        assert prods[0] == p <= prods[1]
        done += 1
    print("2. product formula over components of G - E(W), and bridge bound:", trials, "graphs")


def check_localisation(rng, trials=300):
    done = 0
    while done < trials:
        n = rng.randrange(6, 10)
        E = rand_connected(n, rng.randrange(n + 2, n + 6), rng)
        e = rng.randrange(len(E))
        path = shortest_path(n, E, E[e][0], E[e][1], banned=(e,))
        if path is None:
            continue
        wedges = {e, *path}
        wmask = sum(1 << i for i in wedges)
        wverts = {x for i in wedges for x in E[i]}
        free = [x for x in range(n) if x not in wverts]
        if not free:
            continue
        # grow a connected set R outside W, then close it: keep G - R connected
        R = {rng.choice(free)}
        for _ in range(rng.randrange(0, 4)):
            nb = {y for a, b in E for x, y in ((a, b), (b, a)) if x in R and y in free}
            if nb - R:
                R.add(rng.choice(sorted(nb - R)))
        outside = [x for x in range(n) if x not in R]
        lab = {x: x for x in outside}

        def find(x):
            while lab[x] != x:
                x = lab[x]
            return x
        for a, b in E:
            if a not in R and b not in R:
                lab[find(a)] = find(b)
        wroot = find(next(iter(wverts)))
        R = {x for x in range(n) if x in R or find(x) != wroot}
        inner = [i for i, (a, b) in enumerate(E) if a in R and b in R]
        cut = [i for i, (a, b) in enumerate(E) if (a in R) != (b in R)]
        imask = sum(1 << i for i in inner)
        Z = span(cyc_basis(n, E))
        lhs = Fraction(sum(1 for z in Z if is_forest(n, E, z & imask)), len(Z))
        # build G_R
        idx = {x: k for k, x in enumerate(sorted(R))}
        m = len(idx)
        ER = [(idx[E[i][0]], idx[E[i][1]]) for i in inner]
        k = max(len(cut), 3)
        for t, i in enumerate(cut):
            a, b = E[i]
            ER.append((idx[a if a in R else b], m + t))
        first_cycle_edge = len(ER)
        ER += [(m + t, m + (t + 1) % k) for t in range(k)]
        wr = sum(1 << i for i in range(first_cycle_edge, len(ER)))
        rhs = forest_prob(m + k, ER, wr)
        assert lhs == rhs and lhs >= forest_prob(n, E, wmask)
        if len(cut) >= 3:
            beta_inner = len(inner) - len(R) + comps(n, E, imask) - (n - len(R))
            assert len(cyc_basis(m + k, ER)) == beta_inner + len(cut)
        done += 1
    print("3. localisation identity and inequality:", trials, "graphs")


def split(n, E, A):
    """Cubic expansion that keeps the path A (a list of edge indices in order)."""
    onpath = set(A)
    incid = [[] for _ in range(n)]
    for i, (a, b) in enumerate(E):
        incid[a].append((i, 0))
        incid[b].append((i, 1))
    end = {}
    newE = []
    count = 0

    def fresh():
        nonlocal count
        count += 1
        return count - 1

    def hang(parent, sides):
        """Attach the given edge sides below parent through a cubic caterpillar."""
        if len(sides) == 1:
            end[sides[0]] = parent
            return
        q = fresh()
        newE.append((parent, q))
        for s in sides[:-2]:
            end[s] = q
            q2 = fresh()
            newE.append((q, q2))
            q = q2
        end[sides[-2]] = q
        end[sides[-1]] = q
    image = {}
    for z in range(n):
        sides = incid[z][:]
        random.shuffle(sides)
        psides = [s for s in sides if s[0] in onpath]
        others = [s for s in sides if s[0] not in onpath]
        z2 = fresh()
        image[z] = z2
        if psides:
            for s in psides:
                end[s] = z2
            if others:
                hang(z2, others)
        elif len(sides) <= 3:
            for s in sides:
                end[s] = z2
        else:
            end[sides[0]] = z2
            end[sides[1]] = z2
            hang(z2, sides[2:])
    for i in range(len(E)):
        newE.append((end[(i, 0)], end[(i, 1)]))
    return count, newE, image


def check_split(rng, trials=300):
    random.seed(7)
    done = 0
    while done < trials:
        n = rng.randrange(5, 8)
        E = rand_connected(n, rng.randrange(n + 1, n + 6), rng)
        u, v = rng.sample(range(n), 2)
        A = shortest_path(n, E, u, v)
        n2, E2, image = split(n, E, A)
        deg = [0] * n2
        for a, b in E2:
            deg[a] += 1
            deg[b] += 1
        assert max(deg) <= 3
        assert len(cyc_basis(n2, E2)) == len(cyc_basis(n, E))
        assert count_paths(n2, E2, image[u], image[v]) >= count_paths(n, E, u, v)
        assert len(shortest_path(n2, E2, image[u], image[v])) == len(A)
        done += 1
    print("4. vertex splitting keeps rank and distance, does not lose paths:", trials, "graphs")


def check_layers(rng, trials=300):
    """Inequality (4.1) of the notes: the boundary of a window of layers."""
    random.seed(11)
    done = 0
    while done < trials:
        n = rng.randrange(6, 11)
        E = rand_connected(n, rng.randrange(n + 2, n + 8), rng)
        u, v = rng.sample(range(n), 2)
        A = shortest_path(n, E, u, v)
        n2, E2, image = split(n, E, A)
        s, t = image[u], image[v]
        dist = {s: 0}
        dq = deque([s])
        while dq:
            x = dq.popleft()
            for a, b in E2:
                if x in (a, b):
                    y = b if x == a else a
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        dq.append(y)
        onpath = {x for i in shortest_path(n2, E2, s, t) for x in E2[i]}
        depth = max(dist.values())
        layer = [[x for x in range(n2) if dist[x] == j and x not in onpath]
                 for j in range(depth + 1)]
        size = lambda j: len(layer[j]) if 0 <= j <= depth else 0  # noqa: E731
        for i in range(depth + 1):
            for i2 in range(i, depth + 1):
                R = {x for j in range(i, i2 + 1) for x in layer[j]}
                cut = sum(1 for a, b in E2 if (a in R) != (b in R))
                assert cut <= 3 * size(i - 1) + 3 * size(i2 + 1) + (i2 - i + 3)
        done += 1
    print("5. boundary of a window of layers, inequality (4.1):", trials, "graphs")


if __name__ == "__main__":
    rng = random.Random(2026)
    check_edge_bound(rng)
    check_product(rng)
    check_localisation(rng)
    check_split(rng)
    check_layers(rng)
    print("all assertions passed")
