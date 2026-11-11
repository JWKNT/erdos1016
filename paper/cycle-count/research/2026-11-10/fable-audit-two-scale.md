# Audit of the two-scale proof of a polynomial error

Date: 10 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

Subject: `second-order-two-scale-polynomial.tex` (Astra), as saved at 21:04 EST.

## Verdict

**PASS. I found no gap.** I read every line of the proof and recomputed every estimate. I tried in particular to break the two steps that Astra named: the antisymmetry of the far relation, and the restoration of the medium cycles. Both hold.

The statements that pass:

- **Theorem (polynomial forest error).** Let `Gamma` be connected, of rank `r`, with all degrees at most three; let `P` be a nonempty set with `Gamma[P]` connected, `|P| <= 2r / log^2 r`, and every vertex outside `P` of degree three. Then, for all sufficiently large `r`, the forest probability is at most `1/2 + r^(-kappa)`, with the absolute constant `kappa = 1 / (10^6 t 2^t)`, `t = ceil(10000 A)`, `A = 6 e^168`.
- **Corollary.** `psi(r) <= 2^(r-1) + (1 + o(1)) 2^r / r^kappa`.

This is a mathematical audit. It is not a formal proof, and the result is not in Lean. The proof depends on the following, none of which I re-derived here beyond what is listed:

1. the lemmas of Section 6 of the manuscript (link formula, exceptional partners, walk bound, spectrum lemma, reduction). The repository formalises them inside the proof of the forest estimate, for the parameters of the manuscript. Their use here with other parameters and at two scales is not formalised;
2. Astra's exponential cut theorem (`second-order-block-conditioning.tex`), which I audited earlier today (`fable-notes.md`, Section 8);
3. Theorem T and Lemma T6 of `fable-thin-chain.md` (mine; Astra audited them).

## What I checked, in the order of the proof

1. **Sizes of the two deleted families.** `|Q_j| < 8 D_j 2^(D_j) ln(2/eps)` from the cut theorem, since a cycle of length at most `D_j` outside `P` is a cyclic region with boundary at most `D_j`. With `eps = r^(-kappa)` this gives `|S_0| = O(x^3 r^(1/100))` and `|S_1| = O(x^3 r^(1/10))`. Girth of `J_j` greater than `D_j` by maximality; `Q_1` is maximal because it is a maximal extension of `Q_0`.
2. **Deficit.** `d_j <= 3(|P| + |S_j|)` and `L d_j = O(r / x) = o(v_j)`. This uses `|P| <= 2r / log^2 r`.
3. **Supply at the large scale.** `mu_1 >= (1/4 - o(1)) ln(A/6)`, so the stated `mu_1 > 20` holds with room.
4. **Link bound at both scales.** `l(C, C') <= 1 + 2L/t + 8 t 2^t ln(2/eps) + (8L/D_j)^2`. The four terms are: the component of `P` (one, because `Gamma[P]` is connected); components with more than `t` boundary edges; cyclic components with at most `t` boundary edges (cut theorem); tree components and direct edges (girth). With the constants: `x/5000`, about `5.5 * 10^(-6) x`, and a constant. The tree argument needs `2t + D_j/2 <= D_j`; this holds for large `r` at both scales. So `l <= x/1000`.
5. **Exceptional pairs.** At most `a_C 2^(x/1000) L^3 2^(-s_j)`; at the small scale `s_0 = x/200 + O(1)`, so this is `a_C r^(-0.004 + o(1))`. This bound does not depend on the size of `mu_j`.
6. **The two consequences of the second moment.** `Lambda_j < (1 + eta) mu_j` and `mu_j <= (1 + eta) / (4 eps)`. I recomputed both from `mu^2 <= E Z^2 (1/2 - eps)`.
7. **Antisymmetry of "far".** If `C'` lies in a component of `Gamma - V(C)` that avoids `P`, take a path from `P` to its first vertex on `C`. It stays in the component of `P`, so it avoids `C'`, and `C` is connected and disjoint from `C'`. So `C` is in the component of `P` in `Gamma - V(C')`, and the reverse pair is not far. Hence the ordered far pairs have weight at most `mu_1^2 / 2`.
8. **A cycle with heavy chain partners.** Ordered weights: all pairs `mu_1^2`; far at most `mu_1^2/2`; intersecting or joined by an edge `o(mu_1)`; one link at most `(1 + o(1)) mu_1`. The rest is at least `mu_1^2/2 - (1 + o(1)) mu_1`, so some `C` has partners of weight at least `mu_1/2 - 1 - o(1) > 8`. For these partners: no edge to `C`, at least two links, and `C'` in the component of `P`.
9. **Chain.** Pigeonhole over the at most `L` neighbours of `C`; a maximal disjoint subfamily of the cycles that separate `u` from `P`; `T >= 8 * 2^(s_1) / L^3`. Nestedness and the linear order (I also checked transitivity: if `C_a < C_b` then the side of `u` of `C_a` is inside the side of `u` of `C_b`).
10. **Blocks.** `V(a, b) = U_b \\ (U_a ∪ V(C_a))` contains the `q - 1` cycles strictly between; it has at least `(q - 1)(D_1 + 1) >= 2000 A x^2` vertices; edges that leave it end on `C_a` or `C_b`, so at most `2L` of them; different blocks are non-adjacent because `U_b` is a component of `H - V(C_b)`; no vertex of a block is adjacent to `P`.
11. **Restoration.** A block is a vertex set of `Gamma - V(C)`, so it contains the vertices of `S_1 \\ S_0` between its two cycles. After discarding at most `L + 4|S_0|` blocks, each remaining block avoids `S_0`, has no neighbour in `P ∪ S_0 ∪ C`, and all its vertices have degree three in `J_0`. The number of remaining blocks is of order `r^(1/20) / x^4`, and `|S_0|` is of order `x^3 r^(1/100)`.
12. **Spectral count.** The quadratic form of `M(2 - theta)` on an indicator vector; `M(2)` positive semidefinite; `m` roots with multiplicity; the injection of the kernel into the eigenspace of `B`; the trace bound for even `l`.
13. **Cycle weight at the small scale.** With `theta = 1/(12x)` and even `l` in `[6x, 24x]`: `(1 - theta/2)^l >= 1/e - o(1)`, the sum of `1/(2l)` is `(ln 4)/4`, so the walk sum is at least `0.127 m`; the repeated-walk excess is `(3/2) L^2 2^(-s_0) mu_0 = o(mu_0)`. So `mu_0 >= m/16 - 1` holds with room.
14. **Contradiction.** `mu_0 >= c r^(1/20) / x^4` against `mu_0 <= (1 + o(1)) r^kappa / 4`.
15. **Corollary.** The kernel, a shortest cycle of length `O(log r)`, the reduction with a connected marked set, the edge bound `c_e <= p 2^(r-1)`, and the summation of the recurrence.

## Numerical check of the spectral lemma

`python3 fable_check_test_pieces.py` (needs numpy; 12 seconds). For 18 random graphs made of 3 to 8 cubic pieces of 40 to 100 vertices, joined in a ring through separator vertices, with up to two deleted vertices per piece, it checks in floating point: the formula for the quadratic form; `M(2)` positive semidefinite; at least `m` nonpositive eigenvalues of `M(2 - theta)`; at least `m` real eigenvalues of `B` in `[2 - theta, 2]`; every non-real eigenvalue of modulus at most `sqrt(2)`. All pass. In every case the number of eigenvalues in the interval is exactly `m`.

## Remarks

1. **The exponent is extremely small.** `kappa` is about `10^(-1.6 * 10^77)`. The only place that forces this is item 4: the number of cyclic components with at most `t` boundary edges is bounded by `8 t 2^t ln(2/eps)`, and this must stay below a small multiple of `log r`. So `kappa` is about `1 / (t 2^t)` with `t` at least a multiple of `A`.
2. **`A` can be much smaller.** Item 8 needs only `mu_1/2 - 1 - o(1) > 0`, that is, `mu_1 > 2`. Then the chain has `T >= c 2^(s_1) / L^3` for a small `c > 0`, which is enough. With the supply `(1/4) ln(A/6)` this allows `A` about `6 e^9`, and with the improved supply of `second-order-path-constant.tex` about `6 e^5`. The exponent stays tiny (`2^(-t)` with `t` in the thousands), but it is no longer of the order above.
3. **Where a better exponent would have to come from.** A bound for the links through small-cut cyclic components that does not count them one by one. I have no such bound.
4. **Scope.** The theorem is for a connected marked set. The cycle theorem needs only this case. The forest estimate for a witness with several components is not improved by this proof.
5. **Credit, as I understand the day's work.** The outside-part counting and the forest machinery: KNT and Astra. The recurrence, the chain theorem and the test-piece lemma: Fable. The exponential cut theorem, the antisymmetry step and the two girth scales, which close the argument: Astra.
