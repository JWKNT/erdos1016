# The one-cycle forest estimate stops at size r / log r

Date: 10 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

Status: **[PROVED]** below, by an elementary probabilistic construction. Audited by Astra: two independent line-level audits passed (`codex-audit-fable.txt`, 20:14 EST), with one wording correction in Section 8, now applied. Not Lean. The counting identities are **[CHECKED]** by `fable_check_sharpness.py` over all pairings at five small sizes.

This note answers the scope correction in `codex-audit-fable.txt`. Section 5 of `fable-notes.md` gives a marked cycle with three quarters of the rank. This note gives a marked cycle with an arbitrarily small fraction of the rank, and with only `C r / log r` edges.

Notation: `log` has base two. `p(G, W)` is the probability that the part outside `W` of a uniform even subgraph of `G` is a forest. Multigraphs are allowed, as in Section 6 of the manuscript. A loop adds two to a degree and is a cycle of length one. Two parallel edges form a cycle of length two.

## 1. Result

**Theorem S.** Let `0 < delta < 1` and put `C_delta = 123 max{2, ln(4/delta)}`. For every sufficiently large `r` there are a connected simple cubic graph `G` of rank `r` and a cycle `W` of `G` with

    |E(W)| <= C_delta r / log r     and     p(G, W) >= 1 - delta.

**Corollary S1.** For every `c > 0` and every `delta > 0`, and for every sufficiently large `r`, there are `G` and `W` as above with `|E(W)| <= c r` and `p(G, W) >= 1 - delta`. So no forest estimate holds for one marked cycle of linear size, for any positive coefficient.

**Corollary S2 (the threshold is `r / log r`).** Astra's Theorem `research-marked-size` gives `p(G, W) <= 1/2 + delta` for one cycle with `|E(W)| <= a_delta r / log r`, where `a_delta = exp(-16/delta)/72`. Theorem S shows that this fails for `|E(W)| <= C r / log r` when `C` is large. So the range of the one-cycle forest estimate is `r / log r`, up to the constant. The two constants are far apart, and I do not know the value of the largest forest probability when `|E(W)| = a r / log r` for a fixed `a` between them.

The numerical constants are not optimised.

## 2. The random graph

Let `n0` be even and let `m >= 3`. The fixed part of the graph is a cycle `W = w_0 w_1 ... w_(m-1)` and `m` further vertices `s_0, ..., s_(m-1)`, with the edges `s_i w_i`. Call these edges *spokes* and put `S = {s_i}`. There are `n0` further vertices; call them the *cubic vertices*. Each `s_i` has two *free points* and each cubic vertex has three. There are `M = 3 n0 + 2m` free points.

A *pairing* is a perfect matching of the free points. A pairing `pi` gives a cubic multigraph `G = G(pi)`: each pair becomes an edge between the two vertices that own its points. Put `J = G - V(W)`. Its vertices are `S` and the cubic vertices, and its edges are the pairs. Let `pi` be uniform over all pairings.

`G` has `2m + n0` vertices and `3m + 3n0/2` edges, so `beta(G) = beta0 + comp(G) - 1` with `beta0 = m + n0/2 + 1`.

In a cubic multigraph every even subgraph has all degrees zero or two. So it is a union of vertex-disjoint cycles.

**Lemma 1 (first moment).** For every pairing,

    1 - p(G, W) <= sum over the cycles C of J of P(E(C) is in xi),     P(E(C) is in xi) = 2^(beta(G - V(C)) - beta(G)).

*Proof.* A vertex of `W` has degree one in `G - E(W)`, so every cycle of `G - E(W)` is a cycle of `J`. If `E(C)` is in `xi`, then `xi` already has degree two on `V(C)`, so `xi` is `C` plus an even subgraph of `G - V(C)`. ∎

## 3. The pairs model

Let `Omega` be the set of all pairs `(pi, x)`, where `pi` is a pairing and `x` is an even subgraph of `G(pi)`. Let `nu` be the uniform distribution on `Omega`.

For `(pi, x)` call a free point *used* if the pair at this point is an edge of `x`. Put

- `T` = the set of `i` such that the spoke `s_i w_i` is in `x`, and `tau = |T|`;
- `K_S` = the set of `i` not in `T` such that `x` has degree two at `s_i`;
- `K_3` = the set of cubic vertices at which `x` has degree two; `k = |K_S| + |K_3|`.

Then `tau` is even. A vertex `s_i` with `i` in `T` has one used point. A vertex of `K_S` or `K_3` has two used points. No other point is used. A pair joins two used points or two unused points.

**Lemma 2 (structure of the pairs).** [PROVED, CHECKED] The pairs `(pi, x)` correspond one to one to the following data: an even set `T`; one of the two `T`-joins of the cycle `W`; a set `K_S` disjoint from `T`; a set `K_3`; the used point at each `s_i` with `i` in `T`; the unused point at each vertex of `K_3`; a perfect matching `sigma_1` of the used points; a perfect matching `sigma_2` of the unused points. Hence

    |Omega| = sum over tau, k_s, k_3 of  2 C(m, tau) 2^tau C(m - tau, k_s) C(n0, k_3) 3^(k_3) (U - 1)!! (M - U - 1)!!,   U = tau + 2 k_s + 2 k_3,

and, under `nu`, conditionally on all the other data, `sigma_1` is a uniform perfect matching of the used points.

*Proof.* Given the data, `x` consists of the spokes of `T`, the chosen `T`-join of `W`, and the pairs of `sigma_1`. Its degrees are zero or two, so it is an even subgraph of `G(sigma_1 + sigma_2)`. Conversely the data are read off from `(pi, x)`. A cycle has exactly two `T`-joins when `|T|` is even. ∎

A cycle `C` of `J` with `E(C)` in `x` has all its vertices in `K_S` and `K_3`, and its edges are pairs of `sigma_1`. So the number `N_t(pi, x)` of such cycles of length `t` is the number of cycles of length `t` in the matching `sigma_1`.

**Lemma 3 (cycles of a random matching).** Take `k` vertices with two points each and `tau` further single points, `tau` even. Let `sigma` be a uniform perfect matching of the `2k + tau` points, and let `N_t` be the number of cycles on `t` of the two-point vertices. Then, for `1 <= t <= k`,

    E N_t = (1 / 2t) * product over i = 0, ..., t-1 of (2k - 2i) / (2k + tau - 2i - 1).

Consequently `E N_t <= (1/2t) (2k / (2k + tau - 1))^t` if `tau >= 1`, and `E N_t <= sqrt(k) / t` always.

*Proof.* There are `k (k-1) ... (k-t+1) 2^t / (2t)` possible cycles, as sets of `t` pairs. Each is present with probability `1 / ((2k + tau - 1)(2k + tau - 3) ... (2k + tau - 2t + 1))`. For the first bound, `a / (a + c)` increases with `a`. For the second, the product is largest when `tau = 0`, and then it is at most `4^k / C(2k, k) <= 2 sqrt(k)`. ∎

There are no terms for chords or for components that a cycle cuts off. The matching `sigma_2` of the unused points absorbs them. This is the reason for the pairs model.

**Lemma 4 (transfer).** Put `1 + eta = E_pi 2^(comp(G) - 1)`. For every function `f >= 0` on `Omega`,

    E_pi E_xi f(pi, xi) <= (1 + eta) E_nu f,

where `xi` is a uniform even subgraph of `G(pi)`. For every event `A`, `nu(A) <= E_pi [ 2^(comp(G) - 1) P_xi(A | pi) ]`.

*Proof.* The pair `(pi, xi)` has probability `1 / (#pairings * 2^(beta(G(pi))))`, and `beta(G(pi)) >= beta0`. Also `|Omega| = #pairings * 2^(beta0) * (1 + eta)`. Both statements follow. ∎

**Lemma 5 (components).** Let `n0 >= 8`. Then `eta <= 3 / (n0/2 + m)` and `E_pi 2^(comp(J)) <= 3 (m + 1)`.

*Proof.* Call a set `X` of vertices of `J` *closed* if no pair joins `X` to its complement. The closed sets are the unions of components of `J`, so `2^(comp(J))` is the number of closed sets. A component of `G` other than the component of `W` is a component of `J` without a vertex of `S`. So `2^(comp(G) - 1)` is the number of closed sets of cubic vertices.

Let `X` have `y` cubic vertices and `s` vertices of `S`, so that it owns `2u = 3y + 2s` points. If `y` is odd, `X` is not closed. Otherwise

    P(X is closed) = (2u - 1)!! (M - 2u - 1)!! / (M - 1)!! = C(M/2, u) / C(M, 2u) <= 1 / C(M/2, u),

because `C(M, 2u) >= C(M/2, u)^2`. Here `M/2 = n0 + m + n0/2` and `u = y + s + y/2`, so `C(M/2, u) >= C(n0, y) C(m, s) C(n0/2, y/2)` and also `C(M/2, u) >= C(n0, y) C(n0/2 + m, y/2)` when `s = 0`.

For the second claim, sum over all `X`: the result is at most `(m + 1)` times the sum of `1 / C(n0/2, j)` over `0 <= j <= n0/2`, and this sum is at most 3. For the first claim, sum over the nonempty `X` with `s = 0`: the result is at most the sum of `1 / C(N, j)` over `1 <= j <= n0/2`, with `N = n0/2 + m`. Here `j <= N - 3`, so the term for `j = 1` is `1/N` and every other term is at most `2 / (N (N - 1))`. The sum is at most `3/N`. ∎

**Lemma 6 (used spokes).** For every pairing, `P_xi(tau < m/8 | pi) <= exp(-m/16) + 1[q > m/2]`, where `q` is the number of components of `J` that contain a vertex of `S`. Hence

    nu(tau < m/8) <= (1 + eta) exp(-m/16) + 3 (m + 1) 2^(-m/2).

*Proof.* The map from `xi` to `T` is linear, so `T` is uniform on its image. Let `S_1, ..., S_q` be the nonempty sets `S ∩ V(J_j)`, where `J_j` runs over the components of `J`. The spokes at `S_j` are an edge cut of `G`, so `|T ∩ S_j|` is even. Conversely, if all `|T ∩ S_j|` are even, choose a join in each `J_j` and a `T`-join in `W`. So `T ∩ S_j` is a uniform even subset of `S_j`, independently for the different `j`. A uniform even subset of a set of size `a` contains `a - 1` independent fair bits. So `tau` is at least a binomial variable with `m - q` trials. If `q <= m/2`, Hoeffding's inequality gives `P(tau < m/8) <= exp(-m/16)`.

For the second statement use Lemma 4. The number of components of `J` is `comp(G) - 1 + q`, so `2^(comp(G) - 1) 1[q > m/2] <= 2^(comp(J) - m/2)`. Then use Lemma 5. ∎

## 4. Long cycles and short cycles

Fix an integer `g >= 3` with `4 g^2 <= M`. Call a cycle of `J` *short* if its length is less than `g`, and *long* otherwise. Put `n' = n0 + m`.

**Lemma 7 (long cycles).** Let `m >= 16` and `kappa = (m/8 - 1) / (2 n')`. Put `X(pi)` = the sum of `P(E(C) is in xi)` over the long cycles `C` of `J`. Then

    E_pi X <= (1 + eta) [ exp(-kappa g) / (2 g kappa) + sqrt(n') (1 + ln n') ( (1 + eta) exp(-m/16) + 3 (m + 1) 2^(-m/2) ) ].

*Proof.* `E_pi X = E_pi E_xi (N_g + N_(g+1) + ...)`, and Lemma 4 bounds it by `(1 + eta)` times the same expectation under `nu`. Condition on the data of Lemma 2 other than `sigma_1`. If `tau >= m/8`, Lemma 3 gives `E N_t <= (1/2t)(1 - kappa)^t`, because `2k + tau - 1 < 2n'`. The sum over `t >= g` is at most `exp(-kappa g) / (2 g kappa)`. If `tau < m/8`, Lemma 3 gives the sum over all `t` of `E N_t <= sqrt(n') (1 + ln n')`, and Lemma 6 bounds the probability of this case. ∎

**Lemma 8 (short cycles).** Let `Y(pi)` be the sum of the lengths of the short cycles of `J`. Then `E_pi Y <= 2^(g+1)`.

*Proof.* The expected number of cycles of length `t` in `J` is at most `(1/2t) (6 n0 + 2m)^t / (M - 2t)^t <= (2^t / 2t) (1 - 2t/M)^(-t) <= e 2^t / (2t)` for `t < g`, because `4 t^2 <= M`. Multiply by `t` and sum. ∎

**Lemma 9 (a cycle that meets many spokes).** Let `G` be connected, and let `C` be a cycle of `J` that contains `a` vertices of `S`. Then `P(E(C) is in xi) <= 2^(1 - a)`.

*Proof.* If `E(C)` is in `xi`, then `xi` avoids the set `F` of the `a` spokes at `C`. The even subgraphs that avoid `F` are the even subgraphs of `G - F`, so this event has probability `2^(-a + comp(G - F) - 1)`. A component of `G - F` that does not contain `W` contains an end of a spoke of `F`, so it contains `C`. Hence `comp(G - F) <= 2`. ∎

**Lemma 10 (one more attachment).** Take an edge `e` of `J`. Subdivide `e` by a new vertex `z`, subdivide an edge of `W` by a new vertex `w_z`, and add the edge `z w_z`. Call the result `(G', W')`. The cycles of `J' = G' - V(W')` are the images `C'` of the cycles `C` of `J`, and

    P(E(C') is in xi') <= P(E(C) is in xi)     for every cycle C of J.

The operation raises the rank and the length of the marked cycle by one, and it keeps `G` cubic and connected.

*Proof.* By Lemma 1 it is enough to show `beta(G' - V(C')) <= beta(G - V(C)) + 1`, because `beta(G') = beta(G) + 1`. If `e` is an edge of `C`, then `z` is on `C'`, and `G' - V(C')` is `G - V(C)` with one edge of `W` subdivided: equality of ranks. If `e` has no end on `C`, then `G' - V(C')` is `G - V(C)` with two edges subdivided and one edge added: the rank grows by at most one. If `e` has exactly one end on `C`, then `G' - V(C')` is `G - V(C)` with one edge of `W` subdivided and a path of two edges added between two of its vertices: at most one. If `e` is a chord of `C`, then `z` is a vertex of degree one in `G' - V(C')`: the rank does not change. ∎

## 5. Proof of Theorem S

Let `n0` be large and even. Put

    g = ceil( (1/2) log n0 ),    m = ceil( C0 n0 / log n0 ),    K = g + 4 + ceil( log(4/delta) ),    C0 = 41 max{2, ln(4/delta)}.

*Step 1: a good pairing.* By Lemma 5, `G` is disconnected with probability at most `eta <= 6/n0`. By Markov's inequality and Lemmas 7 and 8, there is a pairing with `G` connected, `X <= 4 E X` and `Y <= 2^(g+3)`. Fix it.

*Step 2: more attachments.* Let `E_short` be the set of edges of `J` that lie on short cycles; `|E_short| <= Y <= 2^(g+3)`. Apply the operation of Lemma 10 `K` times to each edge of `E_short`, always to a part of the original edge. Call the result `(G*, W*)`. Every loop and every pair of parallel edges of `J` is in `E_short`, and `K >= 2`, so `G*` is a simple cubic graph. It is connected.

*Step 3: the forest probability.* By Lemma 1, `1 - p(G*, W*)` is at most the sum over the cycles of `J*`. A short cycle of `J` has all its edges in `E_short`, so its image contains at least `K` vertices that are joined to `W*`. By Lemma 9 it contributes at most `2^(1 - K)`. There are at most `Y` short cycles. By Lemma 10 the long cycles contribute at most `X` in total. So

    1 - p(G*, W*) <= 2^(g + 4 - K) + 4 E X <= delta/4 + 4 E X.

*Step 4: the numbers.* For large `n0` we have `m/8 - 1 >= m/9` and `2n' <= 2.25 n0`, so `kappa >= m / (20.25 n0) >= C0 / (20.25 log n0)` and `kappa g >= C0 / 40.5`. Hence

    exp(-kappa g) / (2 g kappa) <= (20.25 / C0) exp(-C0 / 40.5).

The other term in Lemma 7 tends to zero, because `m / log n0` tends to infinity. Since `C0 >= 82` and `C0 / 40.5 >= ln(4/delta)`, we get `4 (1 + eta) (20.25 / C0) exp(-C0/40.5) <= (82 / C0)(delta / 4)(1 + eta) <= (1 + eta) delta / 4`. So `1 - p(G*, W*) <= delta` for large `n0`.

*Step 5: sizes.* `|E(W*)| = m + K |E_short|` and `beta(G*) = m + n0/2 + 1 + K |E_short|`. Here `K |E_short| <= K 2^(g+3) = O(sqrt(n0) log n0)`, which is `o(m)`. So `beta(G*) = (1/2 + o(1)) n0` and `|E(W*)| <= (2 + o(1)) C0 beta(G*) / log beta(G*) <= 3 C0 beta(G*) / log beta(G*)`.

*Step 6: every large rank.* Let `r` be large. Choose the largest even `n0` such that `m + n0/2 + 1 + K 2^(g+3) <= r`. The graph `G*` for this `n0` has rank at most `r`, and the difference is `o(m)`. Apply the operation of Lemma 10 to arbitrary edges until the rank is `r`. By Lemma 10 the bound of Step 3 remains valid, and the length of the marked cycle grows by `o(m)`. A subdivision of an edge keeps the graph simple. ∎

## 6. Checks

`python3 fable_check_sharpness.py` (about 30 seconds). All assertions pass. The two rows for the Tutte-Coxeter graph in the table below come from a separate run of the same functions (`first_moment` over 10 random attachment sets, then `exact_forest_probability`; attached edges `[8, 15, 23, 34, 37]` and `[1, 14, 17, 21, 26, 37]`; about 20 minutes).

- **Lemma 2 and Lemma 3, exact.** For `(n0, m)` = `(0, 3)`, `(0, 4)`, `(0, 5)`, `(2, 3)`, `(2, 4)` the script runs over all pairings (up to 135,135). It checks that the number of pairs `(pi, x)` equals the formula of Lemma 2, and that for every length `t` the sum of `2^(beta(G - V(C)))` over all pairings and all cycles `C` of `J` of length `t` equals the value from Lemmas 2 and 3. These are equalities of integers.
- **Lemma 5, exact.** The same runs check both moment bounds.
- **Random pairings.** For `n0 = 12`, `m = 6` and 4,000 random pairings, the weighted mean of the first-moment sum agrees with the formula within 0.01 for the lengths 1 to 8.
- **Explicit small examples.** These are cages with `W` attached to a few edges only. They are not part of the proof. They show the effect at ranks where exact computation is possible.

| graph | `|E(W)|` | rank | `|E(W)|/r` | `p(G, W)` exact |
|---|---|---|---|---|
| Petersen | 3 | 9 | 0.333 | 0.5977 |
| Heawood | 3 | 11 | 0.273 | 0.5459 |
| Heawood | 4 | 12 | 0.333 | 0.6602 |
| McGee | 4 | 17 | 0.235 | 0.5647 |
| McGee | 5 | 18 | 0.278 | 0.6429 |
| Tutte-Coxeter | 5 | 21 | 0.238 | 0.6085 |
| Tutte-Coxeter | 6 | 22 | 0.273 | 0.6637 |

## 7. What to audit

1. Lemma 2: the bijection, in particular loops at the vertices `s_i` and at cubic vertices.
2. Lemma 4: the direction of both inequalities. `nu` gives more weight to disconnected graphs than the true model does.
3. Lemma 5: the three uses of Vandermonde's inequality `C(a + b, c + d) >= C(a, c) C(b, d)`.
4. Lemma 6: the description of the image of `xi -> T`.
5. Lemma 10: the four cases, and the claim that no new cycle of `J'` arises.
6. Step 2: the graph `G*` is simple.

## 8. Remarks

- For a fixed constant `C_delta` the theorem gives `p(G, W) >= 1 - delta`. It gives `p(G, W) -> 1` only if `delta` tends to zero and `C_delta` grows accordingly. (Wording corrected after Astra's audit.) In both cases the marked cycle blocks almost every cycle outside it.
- These graphs do not have many cycles. In `G*` almost every outside part is a forest, but the cycle theorem still gives `c(G*) <= (1/2 + o(1)) 2^r`. A forest outside part gives a cycle only if it has a completion inside `W`, and most do not, because `W` is long.
- The lower threshold `a_delta r / log r` and the upper threshold `C_delta r / log r` come from the same quantity: the weight `sum 2^(-|C|)` of the cycles outside `W` with lengths between about `log r` and `r / |E(W)|`. In Astra's proof this weight is at least `(1/8) ln(A_delta / 6)`, which is large. In the random graph the corresponding expected number of cycles inside `xi` is at most `exp(-kappa g) / (2 g kappa)`, which is small when `C` is large.
