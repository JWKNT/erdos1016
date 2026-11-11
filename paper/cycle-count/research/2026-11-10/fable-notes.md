# Notes from Fable 5.2 on items 1 and 2

Date: 10 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

These notes are partial. Each result has a status tag.
I read `RESEARCH-HANDOFF-CODEX-2026-11-10.txt`, `path-stability.tex`, `path-stability-phase2.tex` and `link-stability.tex` before I wrote them.
I did not change any file of Astra.
My files in this folder have the prefix `fable`.
Nothing here is formalized in Lean. Nothing here is committed.

Status tags:

- **[PROVED]** A complete elementary proof is written below.
- **[CONDITIONAL]** The proof is complete, but it uses a forest estimate in a range that is not formalized.
- **[CHECKED]** A script in this folder tests the statement with exact arithmetic.
- **[HEURISTIC]** There is an argument, but not a proof.
- **[OPEN]** I do not know the answer.

Notation follows the manuscript. `log` has base two. `p(G,W)` is the probability that the part outside `W` of a uniform even subgraph of `G` is a forest. `c(G)` is the number of cycles. `c_e(G)` is the number of cycles through the edge `e`. `P_uv(N)` is the number of `u`-`v` paths. `psi(r)` is the largest number of cycles at rank `r`.

## 0. Summary

1. **The cycle theorem needs no chords.** [PROVED from the formalized forest estimate] The Entringer-Slater identity `c(G) = c(G-e) + c_e(G)` and the bound `c_e(G) <= p(G,W) 2^(r-1)` for an edge `e` of a short cycle `W` give `psi(r) <= psi(r-1) + (1/4 + o(1)) 2^r`. This is Theorem 1.1 with the same error term. The proof uses the forest estimate for one cycle only. Section 1.
2. **The second-order term is an edge problem.** [PROVED] Put `X_r = psi(r) - 2^(r-1)`. Then `X_r - X_(r-1) <= g(r)`, where `g(r)` is the largest value, over graphs of rank `r`, of the smallest excess `c_e(G) - 2^(r-2)` over the edges `e`. There is no `2^(-k)` barrier in this form. Section 2.
3. **Localisation.** [PROVED, CHECKED] If `R` is a connected vertex set that avoids `V(W)`, then `p(G,W) <= p(G_R, W_R)`. Here `W_R` is one cycle with `|delta R|` edges, and `G_R` has rank `beta(G[R]) + |delta R|`. So a forest estimate for one cycle applies to every region with a small boundary, whatever the size of `W`. Section 3.
4. **General linear path stability.** [PROVED, given Astra's Theorem `research-marked-size`; audited by Astra in `codex-audit-fable.txt`; not Lean] For each `eps > 0` there are `theta` and `C` such that `P_uv(N) >= (1/2 + eps) 2^b` implies `l >= (2b - C)/(theta + 1)` for every `u`-`v` path of length `l`. The proof uses Astra's forest estimate at size `r / log r`, Astra's splitting lemma, the small-cut lemma, and item 3. Section 4. Astra then proved the additive form `l >= b - C_eps` in `general-additive-path-stability.tex`. I checked that proof (Section 8).
5. **A marked cycle with three quarters of the rank can block every cycle.** [PROVED, CHECKED] There are cubic graphs `G` of rank `r` with a cycle `W` of `3(r-1)/4` edges and `p(G,W) -> 1`. By itself this rules out a one-cycle forest estimate only for coefficients `c >= 3/4`. (Correction after Astra's audit: my first summary claimed more than Section 5 proves.) The case of every `c > 0`, and of size `C r / log r`, is in Section 7 and in `fable-sharpness.md`. Section 5.
6. **A conjecture that would fix the second-order term.** [OPEN] If `P_uv(N) <= 2^(b-1) + C 2^((b+l)/2)` held, then `psi(r) = 2^(r-1) + Theta(r 2^(r/2))`. The order `r 2^(r/2)` is the Horak-Kim lower bound. A search at ranks up to seven shows that `C >= 0.84` is necessary. It cannot show more: finitely many ranks do not refute an unspecified constant. (Correction after Astra's audit.) Section 6.

Added in the second session (10 November, evening):

7. **The one-cycle forest range is `r / log r`.** [PROVED; audited by Astra] For every `c > 0` there are cubic graphs with a marked cycle of at most `c r` edges, even `C r / log r` edges, and forest probability near 1. Section 7 and `fable-sharpness.md`.
8. **Audit log.** I checked nine of Astra's proofs line by line; all pass. Section 8.
9. **Census of cubic graphs up to 22 vertices.** [COMPUTED] `psi(9..12) = 401, 783, 1484, 2876`, in agreement with Markström's published table. The vertex form of the edge-half conjecture of Entringer and Slater is false (I do not know whether this is in the literature). Section 9 and `fable-census.md`.
10. **Two links force a chain of nested separating cycles.** [PROVED; not audited] A structure theorem for every graph whose forest probability exceeds `1/2 + r^(-kappa0)`, and a polynomial error bound for graphs of robust small diameter. Section 10 and `fable-thin-chain.md`.

11. **A polynomial error bound for the number of cycles.** [PROOF WRITTEN by Astra; audited by Astra's agents and by me, no gap found; not Lean] `psi(r) <= 2^(r-1) + (1 + o(1)) 2^r / r^kappa` for an absolute constant `kappa > 0` (extremely small). Astra's two-scale argument closes the remaining case of item 10. Section 11, `second-order-two-scale-polynomial.tex` and `fable-audit-two-scale.md`.

## 1. The cycle theorem from the Entringer-Slater recursion

**Lemma 1.1 (edge bound).** [PROVED, CHECKED] Let `G` be a connected multigraph of rank `r`. Let `W` be a cycle of `G` and let `e` be an edge of `W`. Then `c_e(G) <= p(G,W) 2^(r-1)`.

*Proof.* Let `C` be a cycle through `e`. Its outside part `C \ E(W)` is a proper subset of a cycle, so it is a forest. Let `C'` be a second cycle through `e` with the same outside part. Then `C + C'` is an even subgraph inside `W - e`, which is a path. So `C = C'`. There are `2^(r-1)` outside parts, and the proportion `p(G,W)` of them are forests. ∎

Astra states this bound in item 4 of the outline. The next step is the point.

**Lemma 1.2 (Entringer-Slater).** For every edge `e`, `c(G) = c(G-e) + c_e(G)`.

**Proposition 1.3.** [PROVED from Theorem 1.2 of the manuscript] Suppose that `p(G,W) <= 1/2 + d(r)` for every connected simple graph `G` of rank `r >= r0` and every cycle `W` of `G` with at most `sqrt(r)` edges. Then, for all large `r`,

    psi(r) <= psi(r-1) + (1/4 + d(r)/2) 2^r,
    psi(r) <= (1/2 + max{ d(s) : r/2 <= s <= r } + 2^(-r/2)) 2^r.

With `d(r) = 20 / log log log r` the second line is Theorem 1.1, with the constant 21.

*Proof.* Let `G` have rank `r`. We may assume that `G` is connected, because `psi` is superadditive. Delete vertices of degree one and suppress vertices of degree two. This does not change the cycles. The result `K` is a multigraph with minimum degree at least three and at most `2r - 2` vertices. Its girth is at most `2 log(2r) + 1`. Let `W` be a shortest cycle of `K` and let `e` be an edge of `W`. Subdivide every edge of `K` twice. The result `K'` is simple, and `W` becomes a cycle `W'` with at most `6 log(2r) + 3 <= sqrt(r)` edges. Subdivision changes neither `p` nor the cycle counts. Lemma 1.1 and the hypothesis give `c_e(K) <= (1/2 + d(r)) 2^(r-1)`. Lemma 1.2 gives `c(G) = c(K) <= psi(r-1) + (1/4 + d(r)/2) 2^r`, because `K - e` has rank `r - 1`. This is the first line. Divide by `2^r` and iterate from `r` down to `r/2` for the second line. ∎

Consequences.

- The chord construction, Lemma 3.1 and Lemma 3.2 of the manuscript are not necessary for Theorem 1.1. The Lean proof in the repository uses them, and it is correct. The recursion is a shorter route, and it is closer to the source paper of Entringer and Slater.
- The proof uses a witness with one component. The condition on the number of components of `W` is not necessary for the cycle theorem.
- The error term of the cycle theorem is the error term of the forest estimate for one short cycle. The term `2^(-k)` of the chord proof does not occur.
- Proposal for the manuscript: replace Section 3.2 by Proposition 1.3, and keep the chord proof as the description of the formal proof. KNT decides.

## 2. The second-order term as a problem about one edge

Put `X_r = psi(r) - 2^(r-1)`. For a graph `G` of rank `r` put `m(G) = min c_e(G)` over the edges `e` that lie on a cycle. Put

    g(r) = max{ m(G) : beta(G) = r } - 2^(r-2).

**Proposition 2.1.** [PROVED] `X_r - X_(r-1) <= g(r)` for every `r >= 2`. Hence `X_r <= X_s + g(s+1) + ... + g(r)`.

*Proof.* Let `c(G) = psi(r)` and let `e` attain `m(G)`. Then `psi(r) = c(G-e) + m(G) <= psi(r-1) + 2^(r-2) + g(r)`. ∎

For `e = uv`, `c_e(G) = P_uv(G-e)`, and `G - e` has rank `r - 1`. So `g(r)` is a statement about terminal paths:

    g(r) = max over G of min over edges uv of ( P_uv(G - uv) - 2^(r-2) ).

The table of Entringer and Slater gives `psi(3..8) = 7, 15, 29, 57, 109, 213`. So `X_3..X_8 = 3, 7, 13, 25, 45, 85`, and `g(r) >= 4, 6, 12, 20, 40` for `r = 4..8`.

What this changes in the outline.

- Target (i), a polynomial error: it is enough to find, in every graph of rank `r`, one edge `e` on a cycle with `c_e(G) <= (1/4 + r^(-a)) 2^r`. The bound on the number of components of `W` is no longer an obstacle.
- Target (ii), Problem 8.1: it is enough to prove `P_uv(N) <= 2^(b-1) + 2^((1-k)b)` for one suitable pair of adjacent vertices of `G`, with `N = G - uv`. The pair can be chosen. An edge of a shortest cycle has `dist_N(u,v) <= 2 log(2r)`.
- The link to item 1: every quantitative form of path stability that is uniform in `b - l` gives an upper bound for `X_r`. Section 6 states the form that would be sharp.
- An exact bound `m(G) <= 2^(r-2)` is false for the extremal graphs, because `X_r` grows. So Conjecture 2 of Entringer and Slater, `min c_e(G) <= c(G)/2`, does not follow from a bound on `m(G)` alone. For near-extremal graphs the forest estimate gives it up to `o(1)`.

## 3. Localisation and the product formula

**Lemma 3.1 (localisation).** [PROVED, CHECKED] Let `G` be a connected multigraph and let `W` be a subgraph. Let `R` be a nonempty connected vertex set with `R` disjoint from `V(W)`, and suppose that `G - R` is connected. Build `G_R` from `G[R]` as follows. For every edge `f` of `delta R`, with end `z` in `R`, add a new vertex `t_f` and the edge `z t_f`. Add a cycle `W_R` through all the vertices `t_f`. If `|delta R| < 3`, put extra vertices on this cycle. Then

    P( xi_G ∩ E(G[R]) is a forest ) = p(G_R, W_R),      p(G, W) <= p(G_R, W_R),

and `beta(G_R) = beta(G[R]) + |delta R|` when `|delta R| >= 3`.

*Proof.* For an edge set `T`, the map `xi -> xi \ T` sends `Z(G)` onto `Z(G/T)`, and a linear map sends the uniform law to the uniform law on its image. Take `T = E(G - R)`. Then `G/T` is `G[R]` together with one new vertex `c` that receives the edges of `delta R`. Take `T = E(W_R)` in `G_R`. The contraction `G_R / E(W_R)` is the same multigraph. So `xi_G \ E(G-R)` and `xi_(G_R) \ E(W_R)` have the same law. The second set is a forest in `G_R` exactly if its part in `E(G[R])` is a forest, because the edges `z t_f` end in distinct vertices of degree one. This is the equality. The inequality holds because `E(G[R])` is disjoint from `E(W)`. The rank is a count of edges and vertices. ∎

The hypothesis that `G - R` is connected costs nothing when `W` is connected. Replace `R` by the complement `R+` of the component of `G - R` that contains `W`. Then `R+` contains `R`, it is connected, it avoids `V(W)`, and `delta R+` is a subset of `delta R`.

**Corollary 3.2 (localised forest estimate).** [PROVED from the forest estimate] Let `W` be connected and let `R` be as above. Put `rho = beta(G[R]) + |delta R|`. If the forest estimate holds for one cycle with at most `f(rho)` edges at rank `rho`, and `|delta R| <= f(rho)`, then `p(G, W)` is at most the bound of that estimate at rank `rho`. The size of `W` plays no role.

With the formalized estimate, `f(rho) = sqrt(rho)`. With Remark 6.10, `f(rho) = rho / log^2 rho`. With Astra's Theorem `research-marked-size`, `f(rho) = a_delta rho / log rho`.

**Lemma 3.3 (product formula).** [PROVED, CHECKED] Let `W` be connected. Let `K_1, ..., K_q` be the connected components of `G - E(W)`, and put `S_j = V(K_j) ∩ V(W)`. Let `phi(K, S)` be the probability that a uniform even subgraph of `K/S` is a forest in `K`. Then

    p(G, W) = phi(K_1, S_1) ... phi(K_q, S_q).

The same product over the bridges of `W` is an upper bound for `p(G, W)`. It is not an equality: two bridges with two common attachment vertices can form a cycle together.

*Proof.* `G/W` is a one-point union of the graphs `K_j / S_j`, so `Z(G/W)` is their direct sum. The components `K_j` are vertex-disjoint in `G - E(W)`. ∎

Example 2.2 of the manuscript is the case `q = 1`, `|S_1| = 2`: `phi(K, {a,b}) = (1 + P_ab(K)) / 2^(beta(K)+1)`. For three attachment vertices, `phi(K, {a,b,c}) = (1 + P_ab + P_ac + P_bc) / 2^(beta(K)+2)`.

## 4. General linear path stability

**Theorem 4.1.** [PROVED, given Astra's Theorem `research-marked-size`, which supplies (FE2) below; audited by Astra; I audited that theorem in Section 8] For every `eps` in `(0, 1/2]` there is `theta = theta(eps)` such that the following holds. Let `N` be a connected graph of rank `b` with two vertices `u != v`. If `P_uv(N) > (1/2 + eps) 2^b`, then every `u`-`v` path has length

    l > 2b / (theta + 1) - (theta + 1).

In particular `l >= b / (theta + 1)^2` for every `b >= 1`. This answers Problem 8.2 with `c(eps) = (theta(eps) + 1)^(-2)`.

The constant `theta` is not explicit, because the threshold of the forest estimate is not explicit. Astra's planar theorem in `path-stability-phase2.tex` is unconditional and explicit. Theorem 4.1 has no hypothesis on the graph, but it depends on the larger range.

The hypothesis that the proof uses is this.

> (FE2) There are `rho0(eps)` such that `p(G, W) <= 1/2 + eps` for every connected simple graph `G` of rank `rho >= rho0(eps)` and every cycle `W` of `G` with at most `rho / log^2 rho` edges.

Remark 6.10 of the manuscript asserts (FE2). Astra's Theorem `research-marked-size` implies it.

### 4.1 Reduction to a cubic graph with a shortest path

Step a. If a block of `N` outside the terminal route contains a cycle, then `P_uv(N) <= 2^(b-1)` by Astra's Proposition `research-offroute`. So assume that there is no such block. Delete vertices of degree one other than `u, v`.

Step b. Suppress the vertices of degree two other than `u, v`. The result `N1` is a multigraph without loops. `P_uv` and `b` do not change. Path lengths do not increase. Every vertex other than `u, v` has degree at least three. Let `A1` be a shortest `u`-`v` path of `N1`, of length `l1 <= l`.

Step c. Split vertices as in Astra's Lemma `path-planar-split`, without the planarity condition. At an internal vertex `z` of `A1`, keep one vertex with the two path edges, and attach the other edges at `z` through a tree of cubic vertices below it. At a terminal, keep one vertex with the path edge, and attach the other edges in the same way. Replace every other vertex of degree at least four by a tree of cubic vertices. Call the result `Gamma` and the image of `A1` again `A'`.

Then `beta(Gamma) = b`, and `P_u'v'(Gamma) >= P_uv(N)`. Every vertex outside `A'` has degree three. Every internal vertex of `A'` has degree three, and exactly one of its edges is not on `A'`. The terminals have degree at most two. Finally `A'` is a shortest `u'`-`v'` path of `Gamma`: the contraction of the new tree edges maps walks of `Gamma` to walks of `N1` that are not longer, and `A'` has length `l1`. [CHECKED: test 4 of `fable_check_tools.py`]

Why the kernel matters: subdivision of edges outside `A` changes neither `P_uv`, nor `b`, nor `p(H, W)`. So every path of every graph can be made the unique shortest path. The words "shortest path" carry information only after Step b.

Count vertices: `2(|V| + b - 1) = 3(|V| - 2) + deg u' + deg v'`, so `|V(Gamma)| >= 2b`. Put `U = V(Gamma) \ V(A')`. Then `|U| >= 2b - l1 - 1`.

### 4.2 Layers

Write `A' = w_0 w_1 ... w_l1`. Let `L_j` be the set of vertices at distance `j` from `u' = w_0`. Then `w_j` is in `L_j`. Put `U_j = L_j ∩ U` and `m_j = |U_j|`. Put `m_j = 0` if there is no layer `j`.

- Every edge joins two vertices in the same layer or in consecutive layers.
- At most one edge joins `w_i` to `U`, and its other end is in `U_(i-1)`, `U_i` or `U_(i+1)`.

For `i <= i'` put `R(i, i') = U_i ∪ ... ∪ U_i'`. Its mass is `m(i, i') = m_i + ... + m_i'`. The two facts give

    |delta R(i, i')| <= 3 m_(i-1) + 3 m_(i'+1) + (i' - i + 3).        (4.1)

### 4.3 A window with a small boundary

Put `Phi(x) = x / log^2 x`. It increases for `x >= 8`. Call a set `R` inside `U` *good* if `|R| >= theta` and `|delta R| <= Phi(|R|) / 4`.

**Lemma 4.2 (window).** [PROVED] Let `theta >= 2^36`. If `m_j >= theta` for some `j`, then some `R(i, i')` is good.

*Proof.* Start with `i = i' = j`. While `m_(i-1) > Phi(m(i,i')) / 48`, replace `i` by `i - 1`. Otherwise, while `m_(i'+1) > Phi(m(i,i')) / 48`, replace `i'` by `i' + 1`. Repeat until neither rule applies. The process stops, because there are finitely many layers. Let `mu` be the final mass and `L = log mu >= 36`. Each step multiplies the mass by more than `1 + 1/(48 L^2)`. So the number `s` of steps is at most `ln(mu) / ln(1 + 1/(48 L^2)) <= 96 L^2 ln(mu) < 67 L^3`. At the end `m_(i-1)` and `m_(i'+1)` are at most `Phi(mu) / 48`. Then (4.1) gives

    |delta R| <= Phi(mu)/8 + 67 L^3 + 3 <= Phi(mu)/4,

because `2^L >= 8 L^2 (67 L^3 + 3)` for `L >= 36`. ∎

**Lemma 4.3 (pigeonhole).** [PROVED] Let `theta >= 2^36`. If no subset of `U` is good, then `l1 > 2b/(theta + 1) - (theta + 1)`.

*Proof.* By Lemma 4.2 every layer has `m_j < theta`. Let `R` be the union of the `U_j` with `j >= l1 + 2`. No vertex of `A'` has a neighbour in `R`, so `|delta R| <= 3 m_(l1+1) < 3 theta`. If `|R| >= theta^2`, then `R` is good, because `Phi(theta^2)/4 >= 3 theta`. So `|R| < theta^2`. Hence `2b - l1 - 1 <= |U| < (l1 + 2) theta + theta^2`. ∎

### 4.4 From a good set to the forest bound

Let `H` be `Gamma` with a new vertex `x` and the edges `u'x`, `x v'`. Let `W = A' + u'x + x v'`. Astra's Lemma `research-path-injection` gives `P_u'v'(Gamma) <= p(H, W) 2^b`. It holds for multigraphs.

**Lemma 4.4.** [CONDITIONAL on (FE2)] Let `M0 = 2 max(rho0(eps), 2^100)` and `theta = max(2^36, (M0 + 1) M0 2^(M0+1) / eps)`. If some subset of `U` is good, then `p(H, W) <= 1/2 + eps`.

*Proof.* (Repair from Astra's audit: if the boundary of the localised region has one or two edges, the marked cycle `W_R+` is a triangle, so its length is `max(3, |delta R+|)`. This is still at most `Phi(rho)`, because `rho >= 2^100`. For the hypothesis `P >= (1/2 + eps) 2^b` with equality allowed, apply the proof with `eps/2`.)

Let `R` be good, with `m = |R|` and `d = |delta R| <= m / (4 log^2 m)`. Let `R_1, ..., R_q` be the vertex sets of the components of `Gamma[R]`. They are regions of `H` that avoid `V(W)`. Their sizes add up to `m`, and their boundaries are disjoint and add up to `d`. Every vertex of `R` has degree three, so `beta(Gamma[R_s]) = (|R_s| - |delta R_s|)/2 + 1`. Sort the components into four classes.

1. `|R_s| >= M0` and `|delta R_s| <= Phi(|R_s|) / 2`.
2. `|R_s| >= M0` and `|delta R_s| > Phi(|R_s|) / 2`. Then `|R_s| < 2 |delta R_s| log^2 m`. The total size of this class is less than `2 d log^2 m <= m/2`.
3. `|R_s| < M0` and `Gamma[R_s]` is a tree. Then `|R_s| < |delta R_s|`. The total size of this class is less than `d <= m/4`.
4. `|R_s| < M0` and `Gamma[R_s]` contains a cycle. Then `|delta R_s| <= |R_s| < M0`.

*Case A: class 1 is empty.* Then class 4 has total size more than `m/4`, so it has more than `m / (4 M0)` members. They are disjoint cyclic regions with boundaries of size less than `M0`. The small-cut lemma gives `p(H, W) <= 1/2 + (M0 + 1) 2^(M0 - 1) 4 M0 / m <= 1/2 + eps`, because `m >= theta`.

*Case B: class 1 contains `R_s`.* Let `R+` be the complement of the component of `H - R_s` that contains `W`. It is a subset of `U`. Put `rho = beta(Gamma[R+]) + |delta R+| = (|R+| + |delta R+|)/2 + 1`. Then `rho >= |R_s| / 2 >= rho0(eps)`, and

    |delta R+| <= |delta R_s| <= Phi(|R_s|)/2 <= Phi(|R_s|/2) <= Phi(rho).

Subdivide parallel edges inside `Gamma[R+]`, so that the graph `G_R+` of Lemma 3.1 is simple. Lemma 3.1 and (FE2) give `p(H, W) <= p(G_R+, W_R+) <= 1/2 + eps`. ∎

### 4.5 Proof of Theorem 4.1

Suppose that `P_uv(N) > (1/2 + eps) 2^b`. Then Step a applies, and `P_u'v'(Gamma) > (1/2 + eps) 2^b`, so `p(H, W) > 1/2 + eps`. By Lemma 4.4 no subset of `U` is good. By Lemma 4.3, `l >= l1 > 2b/(theta+1) - (theta+1)`. If `b >= (theta+1)^2` this is at least `b/(theta+1)`. If `b < (theta+1)^2` then `l >= 1 > b/(theta+1)^2`. ∎

### 4.6 What to audit

1. Lemma 3.1, and the closure step that makes `H - R` connected.
2. Inequality (4.1). It uses that `A'` is a shortest path of `Gamma`, and that each path vertex has at most one edge to `U`.
3. The arithmetic of Lemma 4.2.
4. Step b: no loops arise, and a shortest path of the kernel exists with the stated degrees after Step c.
5. (FE2). The proof of Theorem 4.1 uses it once, in Case B. Astra's Theorem `research-marked-size` would replace Remark 6.10 there.
6. The small-cut lemma for the multigraph `H`. The manuscript states it for multigraphs.

Why the formalized range `sqrt(rho)` is not enough for this proof: in a graph of constant width `w`, a window of `t` layers has `t` attachment edges and about `6w` layer edges, and its rank is about `tw/2`. The condition `6w + t <= sqrt(tw/2)` has no solution.

### 4.7 Remarks

- For a path of length `l` in the cubic graph `Gamma`, the proof shows more: a good set exists as soon as one layer has `theta` vertices. So a counterexample to linear stability, if (FE2) holds, has bounded width in every layer.
- The value of `c(eps)` is far from the truth. In the series-parallel case Astra has `l >= b - log(1/(2 eps))`. For planar graphs Astra has `l >= b/(2 + eta) - O(1)`. I expect `l >= b - C(eps)` in general. [OPEN]
- A proof with small-cut regions only, in the style of the planar proof, fails for cubic graphs of bounded width and large girth inside each window. Case B is the replacement for the face count.

## 5. One marked cycle of linear size can block every cycle

Astra's outline proposes a forest estimate for one marked cycle `W` with `|E(W)| <= c(eps) r`. The examples of this section show that `c(eps) < 3/4` is necessary. They do not show more. Section 7 treats every `c > 0`. The examples also show why the proof of Section 4 needs the kernel and a shortest path.

**Lemma 5.1.** [PROVED, CHECKED] Let `G` be a cubic multigraph of rank `r` and let `C` be a cycle of `G` with `j` chords. Exactly `2^(beta(G - V(C)))` even subgraphs contain `C`, and

    beta(G - V(C)) = r - |C| + j + comp(G - V(C)) - 1.

*Proof.* An even subgraph that contains `C` has degree two at every vertex of `C`. So it is the disjoint union of `C` and an even subgraph of `G - V(C)`. The deletion of `V(C)` removes `|C|` vertices and `2|C| - j` edges. ∎

**Construction.** Let `J0` be a cubic graph with `n0` vertices and girth `g0`. Subdivide every edge once. Add a cycle `W` on `3 n0 / 2` new vertices, and join its `k`-th vertex to the `k`-th subdivision vertex. The result `G` is cubic. It has `4 n0` vertices, rank `r = 2 n0 + 1`, and `|E(W)| = 3 n0 / 2 = 3 (r - 1) / 4`.

**Proposition 5.2.** [PROVED] `p(G, W) >= 1 - 2 n0 2^(-g0)`.

*Proof.* A cycle of `G` that avoids `E(W)` avoids `V(W)`, because a vertex of `W` has only one edge outside `W`. So the outside part of `xi` is a forest unless `xi` contains a cycle `C` of `G - V(W)`. Such a cycle is a subdivided cycle of `J0` of length `t >= g0`, and `|C| = 2t`. It has no chord, and `G - V(C)` is connected: every remaining vertex is a subdivision vertex, a vertex of `W`, or a vertex of `J0` next to a remaining subdivision vertex. Lemma 5.1 gives `P(C ⊆ xi) = 4^(-t)`. A cubic graph has at most `n0 2^t` cycles of length `t`. Sum over `t >= g0`. ∎

Cubic graphs with `g0 >= (4/3 - o(1)) log n0` exist. I recall this for the sextet graphs of Biggs and Hoare, with the girth bound due to Weiss. I did not read these sources again. For such graphs `p(G, W) -> 1`, with `|E(W)| < 3r/4`.

Exact values from `fable_check_blocking.py` [CHECKED]. The script uses Lemma 5.1 and inclusion-exclusion. It agrees with direct enumeration for `K4` and `K33`.

| `J0` | girth | `r` | `|E(W)|` | `p(G, W)` |
|---|---|---|---|---|
| `K4` | 3 | 9 | 6 | 237/256 = 0.9258 |
| `K33` | 4 | 13 | 9 | 1973/2048 = 0.9634 |
| Petersen | 5 | 21 | 15 | 0.985540 |
| Heawood | 6 | 29 | 21 | 0.992763 |
| McGee | 7 | 49 | 36 | 0.997391 |
| Tutte-Coxeter | 8 | 61 | 45 | 0.998536 |

**Smaller marked cycles.** [HEURISTIC] Attach `W` to a subset `D` of the edges of `J0` only, with `|D| = t0 |E(J0)|`. Then `|E(W)|/r` is about `3 t0 / (1 + 3 t0)`. A cycle of `J0` of length `t` with `i` edges in `D` has probability about `2^(-t-i)`. If `J0` has about `2^t / (2t)` cycles of each length `t >= g0`, as a random cubic graph does, and `D` is spread evenly, then the expected number of cycles of `G - V(W)` inside `xi` is about

    sum over t >= g0 of (1 - t0/2)^t / (2t).

This tends to zero when `g0 t0 -> infinity`. With `g0` of order `log r` this allows `t0` of order `1/log r`. So I expect that the forest estimate for one cycle fails at `|E(W)| = C r / log r` for a large constant `C`. Astra's Theorem `research-marked-size` covers `|E(W)| <= a r / log r`. If the heuristic is right, the range `r / log r` is sharp up to the constant. A proof needs cycle counts in random cubic graphs or random lifts for all lengths above the girth. I did not write one.

Consequences.

- A forest estimate that uses only `|E(W)|` and the number of components of `W` cannot reach size `3r/4`. Section 7 lowers this to `C r / log r`.
- The injection `P_uv(N) <= p(H, W) 2^b` with `W = A + (new path)` does not prove linear stability for an arbitrary short path `A`. In the examples above, delete one edge of `W`. The rest of `W` is a path `A` with `p` near one. This is consistent with Theorem 4.1: `A` is not a shortest path of the kernel. In the graphs of the table a shortest path between the ends of `A` has at most ten edges.
- The marked vertices block cycles only when they are spread through the whole graph. Lemma 3.1 states the correct local condition: a region with a small boundary.

## 6. Conjectures, and what I would do next

**Conjecture A (additive stability with exponent one half).** [OPEN] There is a constant `C` such that every connected graph `N` of rank `b` with terminals at distance `l` has

    P_uv(N) <= 2^(b-1) + C 2^((b + l)/2).

Checks against known examples.

- Two-terminal series-parallel networks: Astra's bound `2^(b-1) + 2^(l-1)` implies it with `C = 1/2` when `l <= b`.
- Networks with all joins paths: `l >= b`, so `C = 1/2` is enough.
- The wheel example with seven paths, `b = 3`, `l = 2`: needs `C >= 0.53`.
- Astra's example with thirteen paths, `b = 4`, `l = 2`: needs `C >= 0.625`.
- Astra's family with `2^(b-1) + b` paths at `l = 2`: consistent.

**Proposition 6.1.** [PROVED] Conjecture A implies `psi(r) <= 2^(r-1) + 5 C r 2^(r/2)` for large `r`.

*Proof.* Let `G` have rank `r` and let `K` be its kernel, as in Proposition 1.3. An edge `e = uv` of a shortest cycle has `dist_(K-e)(u, v) <= 2 log(2r)`. Conjecture A for `K - e`, with `b = r - 1`, gives `c_e(K) - 2^(r-2) <= C 2^((r-1)/2) 2r`. So `g(r) <= 2 C r 2^((r-1)/2)` in Proposition 2.1, and the sum over the ranks up to `r` is at most `5 C r 2^(r/2)`. ∎

Horak and Kim proved `psi(r) >= 2^(r-1) + c r 2^(r/2)`. So Conjecture A would give the order of the second term: `psi(r) = 2^(r-1) + Theta(r 2^(r/2))`. The factor `r` on both sides has the same source, the girth bound `2 log r`. I take this agreement as evidence that the exponent `(b + l)/2` is the right one. It is not a proof of anything.

**Conjecture B (weaker).** [OPEN] `P_uv(N) <= 2^(b-1) + 2^(b - k (b - l))` for some `k > 0`. By the same argument this implies `psi(r) <= 2^(r-1) + 2^((1 - k) r + O(log r))`, which is Problem 8.1.

**A corollary of the forest estimate for three attachment vertices.** [PROVED from the forest estimate] If `K` is connected of large rank `beta` and `a, b, c` are vertices, then `P_ab + P_ac + P_bc <= (2 + o(1)) 2^beta`. Proof: attach a triangle `W` at `a, b, c` and use Lemma 3.3. The two-terminal bound alone gives only `3 * 2^beta`.

**Search data.** [CHECKED as lower bounds only] `fable_search_excess.py` looks for graphs of rank `b` that contain a terminal path of length `l` and have many terminal paths. The search is random and it is not exhaustive. The table gives the best excess `P_uv - 2^(b-1)` that it found. Series composition with two parallel paths doubles the count and adds one to `b` and to `l`, so each entry is at least twice the entry up and to the left. The entries in brackets come from this rule, because the search found less.

| `b` | `l = 2` | `l = 3` | `l = 4` | `l = 5` | `l = 6` |
|---|---|---|---|---|---|
| 2 | 2 | | | | |
| 3 | 3 | 4 | | | |
| 4 | 5 | 7 | 8 | | |
| 5 | 7 | 11 | 14 | 16 | |
| 6 | 11 | 19 | 24 | 28 | 32 |
| 7 | 18 | 27 | [38] | [48] | 56 |

The witnesses are in `fable-search-excess-results.json`. I counted their paths again with separate code. The table comes from `python3 fable_search_excess.py 7 6000 1016`, except the entry `(7,2)`, which a second run with seed 7 improved from 16 to 18. The file records this.

The entries with `l = b` are the networks in which all joins are paths. The entries `(3,2)` and `(4,2)` are the examples with seven and thirteen paths in Astra's notes.

What the data say about Conjecture A. In the column `l = 2` the excess is `2, 3, 5, 7, 11, 18`. The quotient of the excess by `2^((b+l)/2)` rises from `0.50` to `0.84` in the table. So Conjecture A needs `C >= 0.84`. The data say nothing more: finitely many ranks cannot refute an unspecified constant `C`, and the ranks are small. At these ranks `psi(r) / 2^r` is still above `0.8`. The extremal graphs for `r <= 8` are cages, in which the terminal distance of every edge is the girth minus one, not two. So the column `l = 2` is also not the column that matters for `psi(r)`.

Suggested next steps, in my order of preference.

1. Astra audits Section 4, in particular Lemma 3.1 and Lemma 4.4. If it holds, Problem 8.2 is solved up to the status of (FE2).
2. Decide whether the manuscript should use Proposition 1.3 for Theorem 1.1. The formal proof can stay as it is.
3. Replace the random search by an exhaustive one. The quantity is `M(b, l) = max P_uv` over kernels of rank `b` with terminal distance at most `l`. The growth rate of `M(b, 2) - 2^(b-1)` decides between Conjecture A and Conjecture B.
4. Try to prove Conjecture B for cubic kernels by induction on the identity `2^b = sum over terminal paths P of 2^(beta(N - V(P)))`, which holds when all vertices other than the terminals have degree three. The density is the reciprocal of the average of `2^(beta(N - V(P)))` over the terminal paths.
5. Write a proof for the heuristic of Section 5, if the sharpness of `r / log r` is wanted for a paper.

What I did not do: I did not check Astra's proof of Theorem `research-marked-size` line by line. I did not work on items 3 to 7 of the outline.

## 7. The one-cycle forest range is `r / log r` (added in the second session)

Full proof: `fable-sharpness.md`. Checks: `fable_check_sharpness.py`.

**Theorem S.** [PROVED; counting identities CHECKED over all pairings at five sizes; audited by Astra, two independent passes] For every `delta` in `(0, 1)` there is `C_delta = 123 max{2, ln(4/delta)}` such that, for every sufficiently large `r`, some connected simple cubic graph `G` of rank `r` has a cycle `W` with `|E(W)| <= C_delta r / log r` and `p(G, W) >= 1 - delta`.

Consequences.

- For every `c > 0` the statement "one marked cycle with at most `c r` edges has `p <= 1/2 + eps`" is false for large `r`. This is the claim that my first summary made without proof.
- With Astra's Theorem `research-marked-size`, the one-cycle forest estimate holds up to `a r / log r` and fails at `C r / log r`. The threshold is `r / log r` up to the constant.

Method in one paragraph. Take `n0` vertices with three free points and `m` vertices with two free points, each of the latter joined to its own vertex of a cycle `W`. Pair the free points at random. Count pairs (pairing, even subgraph) instead of even subgraphs of a fixed graph. In a pair, the even subgraph outside `W` is a uniform perfect matching of the points that it uses. Its paths end at the used spokes, and about half of the spokes are used. So the expected number of its cycles of length `t` is at most `(1/2t)(1 - kappa)^t` with `kappa` about `m / (16 n0)`, exactly, with no correction for chords. The cycles shorter than `(1/2) log n0` are few. Subdivide their edges about `log n0` times and attach the new vertices to `W`. Then every short cycle meets many spokes and has probability at most `2/n0`.

## 8. Audit log: Astra's results that I checked line by line (second session)

I read each proof against the manuscript's Section 6 and recomputed each estimate. "PASS" means that I found no gap. These are my audits, not formal proofs.

1. **Theorem `research-marked-size`** (`path-stability.tex`: for fixed `delta`, `p <= 1/2 + delta` when `|E(W)| <= a_delta r / log r` and `comp(W) <= (log r)/100`). **PASS.** Points checked: the reduction lemma does not use `m <= sqrt(r)`; `|S| = O(x^2 r^(1/10) / delta) = o(r/x)`; `L d_J / (2v) <= (3/2) A a + o(1) = 1/8 + o(1)`; the trace bound for even `j` in `[6x, L]`; the walk error `(3/2) L^2 2^(-s) mu`; the weight `(1 + o(1)) mu >= (1/8) ln(A/6) = 2/delta`; the link bound with `t0 = floor(y/2)`: the four terms are `x/100`, `O(x/y)`, `O(y sqrt(x))` and `(80 A)^2`; the exceptional pairs `2^(x/100 + o(x)) L^3 2^(-s) = o(1)`; the final `1/2 + (1 + o(1))/(4 mu) <= 1/2 + delta/2`. So Theorem 4.1 above and the two theorems in `general-path-stability.tex` and `general-additive-path-stability.tex` do not depend on Remark 6.10.
   Remark: the same computation gives the explicit form `p <= 1/2 + (2 + o(1)) / ln(1/(18 a))` for `|E(W)| <= a r / log r`, if one takes `A = 1/(3a)`.
2. **Additive path stability** (`general-additive-path-stability.tex`). **PASS.** Points checked: a cycle of minimum layer span meets its first layer, so the window minus that layer is a forest; `beta <= 2 |U_a| <= 2B`; the identity `m = 2 beta + d - 2c` for cubic sets; `d <= 6B + s + 3`; a cycle of span `s` has length at least `2s`; the greedy deletion of whole windows keeps intervals apart; `beta(J) <= 2 L k`; the small-cut bound on `k`; `beta(J) >= b - l0`.
3. **Sharp no-waste bound** (`no-waste-phase2.tex`: `beta(G) - beta(W) <= |V(W)| + 1`). **PASS.** This answers Problem 8.3 of the manuscript. Points checked: the unique cyclic block has maximum degree three; the kernel has at most six vertices by the Erdős-Pósa lemma; no loops, digons or triangles when the rank is three or four; the path obstruction (`P ∪ Q ∪ C` is even and its outside part properly contains `C`); the identity `beta(G) - beta(W) = m + k - s - c + 1`; the covering counts (each vertex in at least two of four stars for `K4`, at least five of nine trees for `K33`).
4. **Polynomial error in minor-closed classes** (`planar-cycle-error.tex`, with the separator lemma in `path-stability-phase2.tex`). **PASS**, given the separator theorem of Alon, Seymour and Thomas in the form "at most `h^(3/2) n^(1/2)` vertices, components of order at most `n/2`". I did not read that source again.
5. **Recurrence write-up** (`cycle-recursion.tex`). **PASS.** It states Section 1 and Section 2 above correctly.
6. **Conjecture A.** Astra reports an exact count in the Horak-Kim family: rank `2q`, terminal distance three, `P = 2^(2q-1) + (q - 3/4) 2^q + 1`. So Conjecture A is false with an absolute constant. I have not checked this count yet. Conjecture B is open.

7. **Exponential small-cut theorem** (`second-order-structural-notes.tex` and `second-order-terminal-forest.tex`: for `k` disjoint cyclic regions with boundaries at most `d >= 2`, the forest probability is at most `1/2 + 2 exp(-k / (2 d 4^d))`). **PASS.** Points checked. Common-functional lemma: the split graph `Q'`, the identity `beta(Q' - H) = beta(Q') - 1`, exactly `l` components, the quotient is a cycle (connected, `l` vertices, `l` edges, all degrees even), independence of the components given `a = 0`, the matching of `floor(l/2)` quotient edges, closed with probability at least `2^(2-d)`. First theorem: `dim L_i <= d - 1`; `2^d` spaces in direct sum give `(1 - 2^(-d))^(2^d) <= 1/e`; otherwise the pigeonhole on at most `2^(D_d) - 1` functionals. Terminal-forest lemma: the two representations of `a` differ by a cut; the edge set `A` goes to a union of components of `H - v`; at least two components carry terminals; a vertex of degree two in the terminal forest has exactly two such components, and the functional is the terminal sum on one side of its suppressed edge. Final theorem: `B <= d t`, `l >= k / (2 d 2^d) - 2`, and the trivial range `k <= (1 + 2d) 2^d`. The transfer to regions (contract each region; a closed region has forest probability at most one half) is correct.

8. **Weighted block-conditioning lemma and the constant `8 d 2^d`** (`second-order-block-conditioning.tex`), and the **closure-mass form** `1/2 + 2 exp(-mu / (16 d (d-1)))` (`second-order-weighted-cuts.tex`). **PASS.** Points checked: the exceptional set has at most `B + B + 3B` vertices; a remaining vertex is an articulation of degree two in the terminal forest and `L_v ∩ U = {0, a_v}`; two remaining vertices that share a block are joined through a block node of degree two, so the conflict graph is a forest of paths; given all functionals of `U` the blocks of `Q - S` are independent; `P(closed | U) = 2 p_v 1[a_v = 0]`; the chord bound `E exp(-2W) <= 1/2 + (1/2) exp(-2A)` needs only `E W = A/2`. The chord bound is better than the Chebyshev argument that I suggested in the handoff file.
9. **Exponential error in minor-closed classes** (`second-order-minor-exponential.tex`, the transfer lemma, the planar theorem with `774144 = 252 * 48 * 64`, and the fixed-minor theorem). **PASS**, given the separator theorem. Points checked: `alpha = 2 exp(-1/A) >= 3/2` and the induction `3/alpha + 1 <= 3`; `m <= r/72` for `r >= 2048`; `k >= (r - 36m)/126 >= r/252` regions with boundary at most six; in the fixed-minor case `k >= r/(8K)` regions with boundary at most `3K` and exponent `r / (192 K^2 2^(3K))`.

Remark for the forest estimate (not checked in detail): with the closure-mass bound, a maximal family of disjoint cycles of length at most `D1` in `Gamma - P` has `sum 2^(-|Q|) < 8 D1^2 ln(2/eps)`. So one can delete all cycles up to length `D1 = log r - 7 log log r` and still lose only `o(r / log^3 r)` vertices. The remaining graph `J` then has girth about `log r` instead of `(log r)/10`. This improves `2^(-s)` from `r^(-1/20)` to about `r^(-1/2)`. It does not remove the term `2L/t0` in the link count, which is the term that limits `L`.

Not audited by me: the four-regular theorem, the random-host results, the Horak-Kim edge count, `second-order-path-constant.tex`.

## 9. Census of cubic graphs (second session)

See `fable-census.md`. Exhaustive exact counts for all connected cubic graphs up to 22 vertices: `psi(9) = 401`, `psi(10) = 783`, `psi(11) = 1484`, `psi(12) = 2876`. These four values are not new: they agree with Table 1 of Markström's paper (Congr. Numer. 171, 2004), which I read after the census. The census is an independent confirmation. The recurrence `X_r - X_(r-1) <= g(r)` of Section 2 is exact or within 8 percent for every rank from 4 to 11. The edge-half conjecture of Entringer and Slater holds in this range. Their vertex form (Conjecture 3) is false: `K4` with three vertices replaced by triangles has 47 cycles, and each edge at the fourth vertex lies on 24 of them.

## 10. Two links force a chain of nested separating cycles (second session)

See `fable-thin-chain.md`. Checks: `fable_check_thin_chain.py`.

**Theorem T.** [PROVED given Section 6 of the manuscript and Astra's exponential cut theorem; lemmas CHECKED; not audited] Let `Gamma, P` be as in Section 6 with `Gamma[P]` connected, and suppose that the forest probability exceeds `1/2 + r^(-kappa0)` for a certain absolute constant `kappa0 > 0`. Then, for cycles `C` of length at most `A log r` that carry at least 78 percent of the weight `sum 2^(-|C|)`, one of two things holds. Either `C` cuts off from `P` a part of the graph that contains moderate cycles of weight at least 6. Or some neighbour `u` of `C` is separated from `P`, in `Gamma - V(C)`, by at least `r^(1/20) / (A log r)^3` pairwise disjoint nested cycles of length at most `A log r`; between consecutive cycles there are disjoint slabs with boundary at most `2 A log r`.

Why the hypothesis can be so weak: the exponential cut theorem bounds the number of small-cut cyclic regions by a multiple of `ln(2/eps)`, not of `1/eps`. So all estimates of Section 6 survive with `eps = r^(-kappa0)`.

**Corollary T2.** [PROVED, same status] If `G` is cubic, `W` is a cycle with at most `r / log^2 r` edges, and for every cycle `C` of length at most `A log r` outside `W` the graph `G - V(C)` is connected and has all vertices within distance `r^(1/20) / (A log r)^3` of `W`, then `p(G, W) <= 1/2 + r^(-kappa0)`.

This is the step that `second-order-path-notes.txt`, Section 3, lists as missing: it shows with weights that the second link between two typical cycles is a region behind one of them, not a short path. It does not give a new bound for all graphs. Section 5 of the note lists what is still missing.

## 11. A polynomial error bound (second session, late)

Proof: `second-order-two-scale-polynomial.tex` (Astra). My audit: `fable-audit-two-scale.md`. Numerical check of the spectral lemma: `fable_check_test_pieces.py`.

**Theorem.** [PROOF WRITTEN; audited by Astra's agents and by me; not Lean] There is an absolute constant `kappa > 0` such that, for all large `r`: if `Gamma` and `P` are as in Section 6 of the manuscript with `Gamma[P]` connected and `|P| <= 2r / log^2 r`, then the forest probability is at most `1/2 + r^(-kappa)`. Consequently `psi(r) <= 2^(r-1) + (1 + o(1)) 2^r / r^kappa`.

The earlier bound was `2^(r-1) + O(2^r / log log log r)`. The constant `kappa` is about `10^(-1.6 * 10^77)` as written, so the theorem is a statement about the order of the error term only.

How the proof goes, in terms of the notes above.

1. Assume the forest probability exceeds `1/2 + r^(-kappa)`. The exponential cut theorem keeps all estimates of Section 6 valid (Section 10).
2. Delete short cycles at two scales: up to length `(log r)/100`, and then, extending the same family, up to length `(log r)/10`.
3. In the graph of the larger scale, the chain theorem (Section 10) gives a cycle `C`, a neighbour `u` of `C`, and about `r^(1/20)` nested disjoint cycles that separate `u` from `P`. Astra's antisymmetry step shows that the other alternative of the chain theorem cannot hold for every cycle.
4. Group the nested cycles into blocks. A block is a full region of the graph, so it contains the medium cycles that were deleted at the larger scale. Only the few vertices deleted at the smaller scale can spoil a block. So about `r^(1/20)` blocks are regions in which every vertex has degree three in the graph of the smaller scale, with a boundary of at most `2 A log r` edges.
5. The test-piece lemma (T6 in `fable-thin-chain.md`) gives one eigenvalue of the non-backtracking matrix near 2 for each block. So the weight of the moderate cycles at the smaller scale is about `r^(1/20)`.
6. The second moment at the smaller scale bounds this weight by `r^kappa`. Contradiction.
7. The recurrence of Section 1 transfers the bound to `psi(r)`.

My part: the recurrence (Section 1), the chain theorem and the test-piece lemma (Section 10), and the audit. Astra's part: the exponential cut theorem, the antisymmetry step, and the two scales, which is the idea that I did not find (I had stated the remaining case in `fable-thin-chain.md`, Section 5a, with one scale only).

Before anyone relies on this theorem: it is a long argument on top of three other new results of today, and none of it is formalised. A Lean formalisation is the proper check.
