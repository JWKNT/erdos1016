# Link components are independent: a link bound without the forest excess

Date: 10 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

## Summary

1. **[LEAN]** Let `A`, `B` be disjoint connected vertex sets of a connected multigraph `Gamma`, and let `P` be a set of vertices. If the forest probability outside `P` is more than `1/2`, then at most `2^(t+1)` components of `Gamma - (A ∪ B)` have these four properties: an edge to `A` and an edge to `B`; no vertex in `P`; a cycle; at most `t` boundary edges. The bound does not contain the forest excess `eps`. Lean: `Erdos1016.PolynomialBound.ParallelLinks.smallCyclicPart_card_le`.
2. **[LEAN]** So the link count of two disjoint retained cycles of length at most `L` satisfies
   `l(C, C') <= comp(Gamma[P]) + 2L/(t+1) + 2^(t+1) + 578 (L/D)^2`
   under the hypothesis `P(F) > 1/2` only. Lean: `Erdos1016.PolynomialBound.LinkBound.cycle_links_le`. The earlier term was `(t+1) 2^t / (2 eps)` in the manuscript and `8 t 2^t ln(2/eps)` in the two-scale proof.
3. **[PROVED, not audited by Astra, not Lean]** The two-scale proof of the polynomial error then needs no exponential cut theorem, and the exponent is not small. For every fixed `kappa < 1/3`, the forest probability is at most `1/2 + r^(-kappa)` for large `r` (marked set as in Section 4). With the exponential cut theorem for the sizes of the two deleted families, every fixed `kappa < 1/2` is possible. So

       psi(r) <= 2^(r-1) + (1 + o(1)) 2^r / r^kappa     for every fixed kappa < 1/3   (kappa < 1/2 with the cut theorem).

   The exponents in the present drafts are `2^(-1050)` and `2^(-145)`.
4. The Lean formalization that KNT asked me to start uses item 1. The exponential cut theorem is then not a part of the Lean target.

Item 3 changes a stated result, so it needs an independent audit. The only new mathematical step is Section 1. Sections 4 and 5 give the parameter check.

## 1. The lemma

**Lemma PL (regions that hang on a connected core).** Let `Gamma` be a connected multigraph. Let `K` be a nonempty set of vertices such that `Gamma[K]` is connected. Let `c`, `d` be two different components of `Gamma - K`. For a uniform even subgraph `xi`, let `Z_c` be the event that no boundary edge of `c` is in `xi`. Then

    P(Z_c and Z_d) = P(Z_c) P(Z_d).

*Proof.* The graph `Gamma - c - d` is connected: it contains `K`, which is connected, and each other component of `Gamma - K` is connected and has an edge to `K`, because `Gamma` is connected. No edge joins `c` and `d`. So, in the quotient in which `c` and `d` are contracted, the two contracted vertices have exactly one link: the one component of the rest. The pair law of the manuscript (Lean: `SeedPairCorrelation.zeroCut_pair_exact`) says `P(Z_c and Z_d) = 2^(l - 1) P(Z_c) P(Z_d)` for `l` links. ∎

The same argument gives more: the restrictions of `xi` to the edge sets "all edges with an end in `c`", for the different components `c` of `Gamma - K`, are mutually independent. A cut that lies in the union of these edge sets has all of `K` on one side, so it is a sum of cuts, one inside each edge set. I use only the statement for pairs. The exact enumeration below confirms the mutual statement.

**Application to links.** Let `A`, `B` be disjoint connected sets, and let `c_0` be a component of `Gamma - (A ∪ B)` with an edge to `A` and an edge to `B`. Then `K = A ∪ B ∪ c_0` is connected, and the other components of `Gamma - (A ∪ B)` are the components of `Gamma - K`. So the lemma applies to every two components other than `c_0`.

**Corollary PL.** In this situation, let `c_1, ..., c_m` be components of `Gamma - (A ∪ B)` other than `c_0`. Suppose each `c_i` contains a cycle, has at most `t` boundary edges, and lies in an edge set `E`. Then

    P(xi ∩ E is a forest) <= 1 / (1 + m / 2^(t+1)).

*Proof.* Let `E_i` be the event `Z_{c_i}` together with "`xi` is not zero inside `c_i`". Given `Z_{c_i}`, the part of `xi` inside `c_i` is a uniform even subgraph of `c_i`, and it is independent of the rest. So `P(E_i) >= 2^(-t) * (1/2)`, and the events `E_i` are pairwise independent by the lemma. On the forest event no `E_i` occurs. Let `N` be the number of the events `E_i` that occur and `mu = E N >= m / 2^(t+1)`. Pairwise independence gives `E N^2 <= mu^2 + mu`, and Cauchy–Schwarz gives `P(N = 0) <= 1 - mu^2 / E N^2 <= 1 / (1 + mu)`. ∎

So if the forest probability is more than `1/2`, then `m < 2^(t+1)`, and the number of such components, with `c_0`, is at most `2^(t+1)`.

**Why the general cut theorem has the term `1/2` and this corollary has not.** Regions in series (a ring of regions, each with two boundary edges) are all open at the same time with probability `1/2`. Regions between two connected sets are in parallel. One parity condition couples all of them, and it stops to couple any proper subfamily.

**What the lemma does not say.** It gives no bound for cyclic regions in general position. The sizes of the deleted short-cycle families still need a cut theorem with `eps` (Section 4, step 1).

## 2. Status and checks

- **Lean.** `Erdos1016/PolynomialBound/ParallelLinks.lean` (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`):
  - `none_density_le`: events that are pairwise not positively correlated; `P(none) <= 1 / (1 + mu)`;
  - `complement_connected`: `Gamma - c - d` is connected when `c_0` joins `A` and `B`;
  - `links_card_le_one`: `c` and `d` have at most one link;
  - `independent_regions_forest_le`: the corollary, for any family of disjoint connected cyclic regions with at most one link between any two;
  - `smallCyclicPart_card_le`: the count `<= 2^(t+1)` under `P(F) > 1/2`.
  `Erdos1016/PolynomialBound/LinkBound.lean`: `cycle_links_le`, the link bound of item 2 for the retained cycles of the existing development.
- **Exact enumeration.** `python3 fable_check_parallel_links.py 300` (6 seconds; no package). For random multigraphs it enumerates the whole cycle space and checks with exact fractions: (1) mutual independence of the events `Z_i` for every family of link components that omits one link (2,228 families in 259 graphs); (2) the factor two when there are exactly two links (41 graphs); (3) the forest bound in product form (300 graphs). All pass.

## 3. The link bound

For disjoint cycles `C`, `C'` of the retained graph, the manuscript sorts the components of `Gamma - C - C'` that are adjacent to both cycles into four classes. Three bounds do not use `eps`: components that meet `P` (at most `comp(Gamma[P])`), components with more than `t` boundary edges (at most `2L/(t+1)`), and small tree components (at most a constant times `(L/D)^2`, from the girth). The fourth class, cyclic components with at most `t` boundary edges that avoid `P`, is now at most `2^(t+1)` by Corollary PL with `A = V(C)`, `B = V(C')`. The cycles are connected sets; no degree condition is necessary for this step.

## 4. The polynomial error with a large exponent

Notation as in `second-order-two-scale-polynomial.tex`: `Gamma` connected, maximum degree three, rank `r`, `x = log_2 r`; `P` contains every vertex of degree less than three; `F` is the event that `xi` is a forest on `Gamma - P`; `c = comp(Gamma[P])`.

**Theorem E (elementary).** [PROVED, not audited] Let `kappa < 1/3` and `delta = (1 - 3 kappa)/8`. There is `r_0` such that for `r >= r_0`: if `|P| <= r / log^2 r` and `c <= (delta/4) log_2 r`, then `P(F) <= 1/2 + r^(-kappa)`.

**Theorem X (with the exponential cut theorem).** [PROVED given `second-order-block-conditioning.tex`, not audited] The same holds for every `kappa < 1/2`, with `delta = (1 - 2 kappa)/8`.

**Corollary.** `psi(r) <= 2^(r-1) + (1 + o(1)) 2^r r^(-kappa)` for the same `kappa`, by the direct transfer through a cubic extremal graph and a shortest cycle (`c = 1`, `|P| = O(log r)`), as in `second-order-two-scale-extensions.tex`.

*Parameters.* Constants `A` and `t` as below, and

    L = floor(A x),   D_j = floor(d_j x),   s_j = floor((D_j - 1)/2),   eps = r^(-kappa),
    Theorem E:  d_1 = 1 - kappa - 2 delta,   d_0 = 2 delta;
    Theorem X:  d_1 = 1 - 2 delta,           d_0 = 2 delta.

`A` is a constant for which the supply bound gives `mu_1 >= 20` (for example `A = 6 exp(168)` as in the audited proof; a smaller value is possible). `t` is an integer with `2A/(t+1) <= delta/4`.

*Proof.* Assume `P(F) > 1/2 + eps`. The steps are those of the audited two-scale proof. I list each place where a parameter enters.

1. *Sizes of the deleted families.* `Q_0` is a maximal disjoint family of cycles of length at most `D_0` outside `P`, and `Q_1` extends it to a maximal family for length `D_1`. Theorem E uses the cut bound of the manuscript (Corollary 2; Lean: `smallCut_forest_bound`): `k` disjoint cyclic regions with boundaries at most `d` give `P(F) <= 1/2 + (d+1) 2^d / (2k)`. So `|Q_j| < (D_j + 1) 2^(D_j) r^kappa / 2` and `|S_j| <= x^2 r^(d_j + kappa)`. Theorem X uses `|Q_j| < 8 D_j 2^(D_j) ln(2/eps)`, so `|S_j| = O(x^3 r^(d_j))`.
   Needed: `|S_1| = o(r/x)`. Theorem E: `d_1 + kappa = 1 - 2 delta`. Theorem X: `d_1 = 1 - 2 delta`.
2. *Supply at the large scale.* `mu_1 >= 20` as before. It needs `L (|P| + |S_1|) = o(r)` and `L^2 2^(-s_1) = o(1)`.
3. *Links.* By Section 3, at both scales, `l(C, C') <= c + 2L/(t+1) + 2^(t+1) + 578 (L/D_j)^2 <= (delta/2) x + O(1)`. This needs `8 <= D_j <= L`, `2(t + 2 floor(D_j/8)) <= D_j`, and `P(F) > 1/2`.
4. *Exceptional pairs.* `eta_j = (3/2) 2^(l_max) L^3 2^(-s_j)`. At the small scale `s_0 >= delta x - 2`, so `eta_0 = O(x^3 2^(-(delta/2) x)) = o(1)`. Then also `eta_1 = o(1)`.
5. *Second moment.* `mu_0 < (1 + eta_0) / (4 eps)`. At the large scale, the ordered pairs of disjoint cycles with exactly two links have weight more than `mu_1^2 - (1 + eta_1) mu_1`.
6. *Chain.* As before: far pairs have weight at most `mu_1^2 / 2`, pairs joined by an edge have weight `o(mu_1)`, so some cycle `C` has partners of weight at least 8 that are not far, have two links and no edge to `C`. Then some neighbour `u` of `C` is separated from the anchor component of `P` by `T >= 8 * 2^(s_1) / L^3` pairwise disjoint cycles, and they are nested.
7. *Blocks.* Groups of `q` consecutive cycles, `q = O(x)`, give at least `T/q - 1` disjoint blocks with at least `(q - 1)(D_1 + 1)` vertices. Discard the blocks that meet a neighbour of `C` (at most `L`), a vertex of `S_0` (at most `|S_0|`), or `P` (at most `c`, because each component of `Gamma[P]` is connected and avoids the cycles). A remaining block `V` has no neighbour in `P ∪ S_0 ∪ V(C)`: such an edge leaves the block, so it ends on one of the two cycles at the ends of the block, and they avoid `P ∪ S_0 ∪ V(C)`. So `J_0[V] = Gamma[V]`, every vertex has degree three in `Gamma`, and the deficit of `J_0[V]` is the number of edges that leave `V`, at most `2L`.
   The number of remaining blocks is `m >= c' r^(d_1/2) / x^4 - L - |S_0| - c`.
   Needed: `|S_0| = o(r^(d_1/2) / x^4)`. Theorem E: `d_1/2 - (d_0 + kappa) = delta`. Theorem X: `d_1/2 - d_0 = 1/2 - 3 delta > 0`.
8. *Supply inside the blocks.* Apply the spectral supply lemma (Lemmas 6.7 and 6.8) to the graph `J_0[V]` alone: maximum degree three, girth more than `D_0`, deficit at most `2L`, at least `(q-1)(D_1+1) >= 8 L^2` vertices. It contains cycles of length at most `L` of total weight at least a constant `w_0 > 0`. Cycles in different blocks are different cycles of `J_0`. So `mu_0 >= w_0 m`. This replaces Lemma T6: no count of eigenvalues with multiplicity is necessary, and the blocks do not have to be non-adjacent.
9. *Contradiction.* `w_0 m <= mu_0 < (1 + o(1)) r^kappa / 4`. Theorem E: `d_1/2 - kappa = 3 delta`. Theorem X: `d_1/2 - kappa = 3 delta`. ∎

*Remarks.*

- The constant `2^(t+1)` in step 3 is very large, because `t` is about `8A/delta`. It is a constant, so it changes `r_0` and not `kappa`.
- If `c <= gamma x` with a constant `gamma`, the same proof needs `d_0 > 2 gamma`, and Theorem E gives every `kappa < (1 - 4 gamma)/3`.
- The value `1/2` is a limit of this method: the chain has at most about `2^(D_1/2)` cycles and `D_1 <= log_2 r`.

## 5. What to audit

1. Lemma PL: `Gamma - c - d` is connected, and one link gives the factor one in the pair law. (Machine-checked; the audit is for the statement that it is the right hypothesis for the links.)
2. Section 4, step 5: the second-moment inequality `E Z^2 <= mu^2 + W_2 + (1 + eta) mu`, where `W_2` is the weight of the ordered disjoint pairs with exactly two links.
3. Section 4, step 7: a block that avoids `S_0`, `P` and the neighbours of `C` has no neighbour in `P ∪ S_0 ∪ V(C)`.
4. Section 4, step 8: the use of the supply lemma for one block as a graph, with the walk lengths from about `2x` to `L` and `q` of order `A^2 x`.
5. The arithmetic of the exponents in steps 1, 4, 7 and 9.
