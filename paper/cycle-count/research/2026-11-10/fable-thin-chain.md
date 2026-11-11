# Two links force a chain of nested separating cycles

Date: 10 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

Status: **[PROVED]** below, given the estimates of Section 6 of the manuscript and Astra's exponential cut theorem (`second-order-block-conditioning.tex`). The three combinatorial lemmas are **[CHECKED]** on random graphs by `fable_check_thin_chain.py`. Not audited by Astra. Not Lean.

Purpose. `second-order-path-notes.txt`, Section 3, names a missing step: most weighted pairs of moderate cycles have two links, but "two links need not immediately give a balanced rank separation; one link could be a small tree or a short connecting path". This note controls that possibility with weights. The result is a structure theorem for every graph whose forest probability exceeds `1/2 + r^(-kappa0)`. It does not prove a new upper bound for all graphs. It proves one for graphs of small diameter (Corollary T2), and it reduces the polynomial error bound to graphs with a specific thin structure.

## 1. Setting and parameters

As in Section 6 of the manuscript: `Gamma` is a connected multigraph of rank `r` with all degrees at most three; `P` is a set of vertices; every vertex outside `P` has degree three; `Gamma[P]` is connected; `|P| <= r / log^2 r`. `xi` is a uniform even subgraph, and `F` is the event that `xi ∩ E(Gamma - P)` is a forest. For a cubic graph `G` and a cycle `W` take `Gamma = G` and `P = V(W)`; then `P(F) = p(G, W)`.

Put `x = log r` and fix the absolute constants

    A = 6 exp(168),   L = floor(A x),   D = floor(x/10),   s = floor((D-1)/2),   t0 = 200 A,   kappa0 = 1 / (600 t0 2^(t0)).

**Assumption.** `P(F) > 1/2 + eps` with `eps >= r^(-kappa0)`, and `r` is large.

## 2. The estimates of Section 6 hold for this small `eps`

The only places where the proof of the forest estimate uses the size of `eps` are two counts of disjoint cyclic regions. Astra's theorem bounds `k` such regions with boundaries at most `d` by `k < 8 d 2^d ln(2/eps)`. This replaces `(d + 1) 2^(d-1) / eps`.

(a) *Short cycles.* A maximal family `Q` of disjoint cycles of length at most `D` in `Gamma - P` has fewer than `8 D 2^D ln(2/eps) = O(x^2 r^(1/10))` members. So their union `S` has `O(x^3 r^(1/10))` vertices. `J = Gamma - P - S` is simple, has girth greater than `D`, and its deficit is `o(r / L)`.

(b) *Supply.* Let `C*` be the set of cycles of `J` of length at most `L`, `a_C = 2^(-|C|)`, and `mu` the sum of the `a_C`. As in Lemma 6.8, `mu >= (1/8 - o(1)) ln(A/6) >= 20`. As in Lemma 6.6, for every vertex `w` the cycles of `C*` through `w` have total weight at most `L 2^(-s)`, and `2^(-s) <= 8 r^(-1/20)`.

(c) *Links.* For disjoint `C, C'` in `C*`, the proof of Lemma 6.9 gives

    l(C, C') <= 1 + 2L/t0 + 8 t0 2^(t0) ln(2/eps) + (8L/D)^2 <= 1 + x/100 + x/100 + (80 A)^2 <= x/40.

The third term uses the choice of `kappa0`. The proof needs `2 t0 + D/2 <= D`, which holds for large `x`.

(d) *Exceptional pairs.* For each `C`, the pairs with at least three links contribute at most `a_C 2^(x/40) L^3 2^(-s) = o(a_C)` to the second moment.

(e) *The one-link term.* Let `Z` be the sum of the variables `X_C` of the manuscript. For disjoint cycles, `E X_C X_C' = a_C a_C' 2^(l(C,C') - 1)`. Let `Lambda_1` be the sum of `a_C a_C'` over the ordered disjoint pairs with exactly one link. Then

    E Z^2 <= 2 mu^2 - Lambda_1 + (1 + o(1)) mu.

On `F` we have `Z = 0`, so `P(Z > 0) < 1/2` and `mu^2 <= E Z^2 P(Z > 0) < E Z^2 / 2`. Hence

    Lambda_1 < (1 + o(1)) mu.                                   (2.1)

This is the inverse second moment of `link-stability.tex`, for the cycle family and with a weak hypothesis.

## 3. Three lemmas about separating cycles

In this section `H` is a connected graph, `P` is a connected set of vertices, and cycles are vertex sets. [CHECKED: `fable_check_thin_chain.py`, 6,916 + 10,204 + 10,204 cases.]

**Lemma T1 (the second link is a region behind `C'`).** Let `C, C'` be disjoint cycles that avoid `P`, with no edge between them and with `l(C, C') >= 2`. Then some component `Y` of `H - C - C'` avoids `P` and is adjacent to both `C` and `C'`. In `H - C`, the cycle `C'` separates `Y` from `P`.

*Proof.* There are at least two components adjacent to both cycles, and the connected set `P` lies in one component. ∎

**Lemma T4 (disjoint separators are nested).** Let `u` be a vertex that is joined to `P` in `H`. Let `C_1, C_2` be disjoint cycles that avoid `u` and `P`, such that `u` and `P` lie in different components of `H - C_i` for `i = 1, 2`. Then exactly one of the following holds: `C_2` lies in the component of `P` in `H - C_1`; or `C_1` lies in the component of `P` in `H - C_2`.

*Proof.* Let `K_u` and `K_P` be the components of `u` and of `P` in `H - C_1`. Take a path from `u` to `P`. Replace its part between its first and its last vertex on `C_1` by an arc of `C_1`. The new path lies in `K_u ∪ C_1 ∪ K_P`. The cycle `C_2` meets it, and `C_2` is connected and disjoint from `C_1`. So `C_2` lies in `K_u` or in `K_P`. The same holds with the roles exchanged. If `C_2` is in the component of `u` in `H - C_1` and `C_1` is in the component of `u` in `H - C_2`, then a path from `u` to `C_1` avoids `C_2`, and it continues to `P` through `C_1 ∪ K_P`, which avoids `C_2`. This contradicts the separation by `C_2`. The two alternatives cannot both hold, by the same argument with `P` in place of `u`. ∎

So a family of pairwise disjoint cycles that separate `u` from `P` is linearly ordered: `C_1 < C_2 < ... < C_T`, where the component `K_i` of `u` in `H - C_i` grows with `i`.

**Lemma T5 (slabs).** In this situation put `S_i = K_(i+1) \ (K_i ∪ C_i)` for `1 <= i < T`. The sets `S_i` are pairwise disjoint and avoid `P` and all the cycles `C_j`. Every edge of `H` that leaves `S_i` ends in `C_i` or in `C_(i+1)`.

*Proof.* `S_i` is a union of components of `H - C_i - C_(i+1)`: it is the part of `K_(i+1)`, a component of `H - C_(i+1)`, that lies outside the component `K_i` of `H - C_i` and outside `C_i`. ∎

## 4. The structure theorem

For `C` in `C*` put `Gamma_C = Gamma - V(C)`. The component of `Gamma_C` that contains `P` is the *main* component; the others are *far* components. Let `N(C)` be the set of vertices of `Gamma_C` with a neighbour on `C`; `|N(C)| <= L`.

Sort the cycles `C'` of `C*` that are disjoint from `C` into four classes, with total weights

- `W_1(C)`: exactly one link with `C`;
- `W_e(C)`: an edge joins `C'` to `C`; then `C'` meets `N(C)`, so `W_e(C) <= L^2 2^(-s) < 1`;
- `W_far(C)`: `C'` lies in a far component of `Gamma_C`, and it is not in the first two classes;
- `W_ch(C)`: the remaining cycles. They lie in the main component, no edge joins them to `C`, and they have at least two links with `C`.

The cycles that meet `C` have weight at most `L^2 2^(-s) < 1`. So the four weights add up to more than `mu - 1`.

Call `C` *good* if `W_1(C) <= 5`. By (2.1) and Markov's inequality the good cycles have total weight at least `0.78 mu`. For a good cycle, `W_far(C) + W_ch(C) >= mu - 7 >= 13`.

**Theorem T.** [PROVED] Under the assumption of Section 1, every good cycle `C` satisfies (A) or (B).

(A) *`C` is a separator.* The far components of `Gamma - V(C)` contain cycles of `C*` of total weight at least 6. These components avoid `P`, all their boundary edges end on `C`, so the total boundary is at most `L`; and they contain at least `6 * 2^s / L` vertices.

(B) *Chain.* There are a vertex `u` in `N(C)` in the main component and `T >= 6 * 2^s / L^3` pairwise disjoint cycles `C_1 < C_2 < ... < C_T` of `C*`, disjoint from `C`, each of which separates `u` from `P` in `Gamma - V(C)`. Consequently:

- the distance from `u` to `P` in `Gamma - V(C)` is at least `T`;
- there are at least `T - 1 - L` pairwise disjoint sets `S_i` (the slabs of Lemma T5 without a vertex of `N(C)`) that avoid `P` and `C`, such that every edge of `Gamma` leaving `S_i` ends in `C_i ∪ C_(i+1)`; in particular `|delta S_i| <= 2L`.

Here `2^s >= r^(1/20) / 4`, so `T >= r^(1/20) / L^3`.

*Proof.* If `W_far(C) >= 6`, then (A) holds: a set `X` of vertices contains cycles of total weight at most `|X| L 2^(-s)`.

Otherwise `W_ch(C) >= 7`. Let `C'` be in this class. By Lemma T1 there is a component `Y` of `Gamma - C - C'` that avoids `P` and is adjacent to `C` and to `C'`. Since `C'` is in the main component, so is `Y`. Choose `u` in `Y ∩ N(C)`. In `Gamma_C` the vertex `u` is joined to `P`, and `C'` separates `u` from `P`. For `u` in `N(C)` let `S_u` be the set of cycles of `C*`, disjoint from `C` and not through `u`, that separate `u` from `P` in `Gamma_C`. We have shown that every cycle of the class is in some `S_u` with `u` in the main component. So some `u` has weight at least `7/L` in `S_u`.

Let `T*` be a maximal subfamily of pairwise disjoint cycles in `S_u`, with `T` members. Every cycle of `S_u` meets a cycle of `T*`, so the weight of `S_u` is at most `T L * L 2^(-s)`. Hence `T >= 7 * 2^s / L^3`. By Lemma T4 the members of `T*` are nested. Every path from `u` to `P` in `Gamma_C` meets each of them, which gives the distance. Lemma T5 gives the slabs in `Gamma_C`; in `Gamma` a slab can also have edges to `C`, and at most `|N(C)| <= L` slabs contain a vertex of `N(C)`. ∎

**Corollary T2 (polynomial error for robust small diameter).** [PROVED] Let `G` be a connected cubic graph of rank `r >= r_0` and let `W` be a cycle of `G` with at most `r / log^2 r` edges. Suppose that, for every cycle `C` of `G - V(W)` of length at most `A log r`, the graph `G - V(C)` is connected and each of its vertices is at distance less than `r^(1/20) / (A log r)^3` from `W`. Then

    p(G, W) <= 1/2 + r^(-kappa0).

*Proof.* Otherwise the assumption of Section 1 holds, and a good cycle exists. (A) fails because `G - V(C)` is connected. (B) fails because of the distance. ∎

The hypothesis has two parts, and expansion alone gives only the second. (Correction after Astra's audit: an earlier version said that every expander satisfies the hypothesis. That is too broad, because the deletion of a cycle can isolate a small pocket even in an expander. Astra's `second-order-detour-obstruction.tex` treats that case by allowing all components and bounding the diameter of each.) The point of the corollary is only that the second-moment method reaches a polynomial error when thin structures are excluded. The constant `kappa0` is extremely small.

## 5. What this reduces the problem to

Let `E*(r)` be the largest value of `p(G, W) - 1/2` over cubic graphs `G` of rank `r` and cycles `W` with at most `r / log^2 r` edges. The known bound is `E*(r) = O(1 / log log log r)`. Theorem T says: if `E*(r) > r^(-kappa0)`, then every witness `(G, W)` is *thin*: for cycles `C` that carry 78 percent of the weight of all moderate cycles, either `C` cuts off a part of the graph of at least `r^(1/20) / L^2` vertices from `W`, or behind one of the at most `L` neighbours of `C` there are at least `r^(1/20) / L^3` nested disjoint cycles of length at most `L`.

So a polynomial error bound for all graphs would follow from a bound for thin graphs.

What is missing, in my view:

1. *The interfaces are too wide for the cut theorem.* The slabs have boundaries of size up to `2L = 2A log r`. The exponential cut theorem needs more than `2^(2L)` such regions, which is more than `r`. The cycles of `C*` are long because the trace bound starts at length `6 log r`. A thin graph must contain much shorter cycles (a slab of size `m` with boundary at most `2L` contains a cycle of length `O(log m)` when `m` is much larger than `L`), and by (a) there are few disjoint ones of length at most `D`. I did not find a way to turn these into small cuts.
2. *Recursion into a slab loses rank.* Localisation at a union of slabs gives `p(G, W) <= p(G_R, W_R)` with a marked cycle of length at most `2L`, but the rank of `G_R` is smaller than `r`, so an induction with a decreasing error function does not close.
3. *A transfer formulation.* Along the chain the forest event is a product of slab factors that depend on the patterns on the interfaces and on how the forest joins the interface vertices. A proof for thin graphs probably needs a contraction estimate for this product. The state space has size about `L! 2^L`, which is more than polynomial in `r`.

## 5a. A second constraint: few nearly closed pieces

The same assumption limits the number of pieces of `J` with a small boundary. This is a different use of the non-backtracking matrix: many separated pieces give many eigenvalues near 2, not only one.

**Lemma T6 (test pieces).** [PROVED, given Lemmas 6.6 to 6.8 of the manuscript] Let `V_1, ..., V_m` be pairwise disjoint, pairwise non-adjacent sets of vertices of `J`. For each `i` let `b_i` be the number of edges of `J` that leave `V_i`, and `delta_i` the sum of `3 - deg_J(w)` over `w` in `V_i`. Let `0 < theta <= 1/2` and suppose `delta_i + 3 b_i <= theta |V_i|` for all `i`. Then the non-backtracking matrix `B` of `J` has at least `m` real eigenvalues in `[2 - theta, 2]`, and for even `l`

    tr B^l >= m (2 - theta)^l - 3 v 2^(l/2).

With `theta = 1/(12x)` this gives `mu >= m/16 - 1`.

*Proof.* Let `M(lambda) = lambda^2 I - lambda A + Delta - I` as in Lemma 6.7. For the indicator vector of `V_i`,

    1^T M(lambda) 1 = lambda^2 |V_i| - lambda (3|V_i| - delta_i - b_i) + 2|V_i| - delta_i,

and at `lambda = 2 - theta` this equals `-theta (1 - theta) |V_i| + (1 - theta) delta_i + (2 - theta) b_i <= 0`. The sets are non-adjacent, so `M(2 - theta)` is negative semidefinite on the span of the `m` indicator vectors. So it has at least `m` eigenvalues that are at most zero. `M(2)` is positive semidefinite. The sorted eigenvalues of `M(lambda)` are continuous in `lambda`. So for each `k <= m` the `k`-th eigenvalue vanishes at some `lambda_k` in `[2 - theta, 2]`, and coincident values come with the corresponding dimension of the kernel. By step (1) of the proof of Lemma 6.7, the kernel of `M(lambda)` embeds in the eigenspace of `B` for `lambda`. The trace bound follows as in Lemma 6.7. For the last claim, sum `tr B^l / (2 l 2^l)` over the even `l` between `6x` and `24x` as in Lemma 6.8: each term is at least `(m/e - o(1)) / (2l)`. ∎

**Consequence.** Under the assumption of Section 1 the second moment gives `mu <= (1 + o(1)) / (4 eps)`. So `J` contains at most `5/eps` pairwise non-adjacent sets with `delta_i + 3 b_i <= |V_i| / (12x)`.

**Combination with Theorem T.** In case (B), group the nested cycles into blocks of `20000 A x` consecutive cycles with the slabs between them, and leave one cycle between consecutive blocks. Let `V_i` be the set of vertices of `J` in the `i`-th block. Then `|V_i| >= 2000 A x^2`, because every cycle of `C*` has more than `x/10 - 1` vertices. The sets `V_i` are pairwise non-adjacent. No vertex of a block is adjacent to `P`, because the block lies on the side of `u` of a later separating cycle. At most `2L` edges of `Gamma` leave a block, apart from the at most `L` blocks that touch `C`; so `b_i <= 2L`, and `delta_i` is at most `2L` plus the number of edges from `V_i` to deleted short cycles inside the block. There are more than `r^(1/20) / L^5` blocks, and at most `5/eps` of them satisfy the condition of Lemma T6. So, if `eps >= r^(-kappa0)`, almost every block fails it. Since `3 b_i + 2L <= 8 A x` and `|V_i| / (12x) - 8 A x >= |V_i| / (13x)`, such a block has more than `|V_i| / (13x) >= 150 A x` edges to deleted short cycles inside it. A short cycle has at most `D <= x/10` such edges. So **almost every block of a chain contains at least `1500 A` of the deleted short cycles.**

So the remaining case is precise: chains of about `2^(D/2)` nested moderate cycles in which the slabs contain, on average, a deleted short cycle for every `13 x` separating cycles or more often. The count of deleted short cycles allows this: the cut theorem permits up to about `2^l` disjoint cycles of length `l`, and the chain has only about `2^(D/2)` blocks. The short cycles that can do this have length between about `D/2` and `D`. I did not find a way to exclude this case. If it can be excluded, the forest estimate holds with a polynomial error, and by the recurrence `psi(r) <= 2^(r-1) + O(2^r / r^kappa)` for some `kappa > 0`.

## 5b. Where the saturation gap could enter [HEURISTIC, not proved]

This section is a sketch. I did not check it.

*Small blocks give very short cycles.* A set of `m` vertices of degree three with at most `2L` boundary edges, `m` much larger than `L`, contains a cycle of length at most about `2 log m`. If many blocks of a chain have at most `r^c` vertices with `c < 1/80`, these very short cycles are disjoint cyclic regions with closure probability at least `r^(-2c)`, and their number is about `r^(1/20)`. Then the closure-mass form of the cut theorem contradicts `p > 1/2 + r^(-kappa0)`. So most blocks contain a slab with at least `r^c` vertices.

*Large slabs and a common functional.* Contract each large slab to a vertex, as in the proof of the cut theorem. If many of the local spaces are in direct sum, the slabs are independent, each has forest probability at most `1/2 + o(1)` by localisation, and the product is tiny. Otherwise the block-conditioning lemma gives a class of slabs with one common functional `a`. Given the data of `U`, the slabs of a colour class are independent, and each contributes its conditional forest probability `phi_v(a)`, where `(phi_v(0) + phi_v(1))/2 <= 1/2 + o(1)`. The total is about `(1/2) prod phi_v(0) + (1/2) prod phi_v(1)`. So `p > 1/2 + eps` needs `prod phi_v(1) >= 2 eps`: all but about `log(1/eps)` slabs have a conditional forest probability within a small constant of 1. They are almost saturated.

*The gap.* For slabs with two boundary edges, `phi_v(1)` is the path density of a two-terminal network, and Astra's theorem (`second-order-path-gap.tex`) says that it is 1 or at most `15/16`. Then almost every slab is exactly saturated, hence a series of capped ladders, which contains many disjoint cyclic regions with boundary at most four, and the cut theorem finishes the proof. For slabs with wider boundaries the same plan needs a gap theorem for regions with many boundary edges, conditional on one functional of the boundary pattern, with a gap that does not decay like `2^(-d)` in the boundary size `d`. The interfaces in Theorem T have size up to `2 A log r`. This is the obstacle in its sharpest form that I can state.

Remark (larger girth). With the closure-mass form of the cut theorem, step (a) can delete all cycles up to length `(1 - 2 kappa0) log r`. Then `2^s` is about `r^(1/2 - kappa0)` and the chain in (B) has about `r^(1/2 - kappa0)` nested cycles.

## 6. What to audit

1. Section 2(c): the count of cyclic components with small cut under `eps = r^(-kappa0)`, and the condition `2 t0 + D/2 <= D` in the tree-link argument.
2. Section 2(e): the inequality with `- Lambda_1`. It uses `l >= 1` for every disjoint pair and `E X_C X_C' = a_C a_C'` when `l = 1`.
3. Lemma T4, in particular the use of an arc of `C_1`.
4. Theorem T: the pigeonhole over `N(C)`, and the claim that a cycle of the class `W_ch` separates some `u` of the main component from `P`.
5. Lemma T6: the quadratic form at `2 - theta`, and the count of roots with multiplicity.
