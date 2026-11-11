# Audit of the unrestricted sharp-order cycle bound

Date: 11 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

Subject: `unrestricted-sharp-cycle-bound.tex` with its five modules, as saved at 01:14 EST:
`path-qualitative-affine-bootstrap.tex`, `four-unrestricted-iterative-packing.tex`,
`unrestricted-sharp-foundations.tex`, `unrestricted-sharp-parallel-links.tex`,
`second-order-unrestricted-sharp-bootstrap.tex`.

## Verdict

**PASS for the five modules. I found no gap.** I read every line and recomputed every estimate.

**Scope.** The five modules prove the exact one-half forest bound at large girth and derive the bound
`c(G) <= 2^(r-1) + K r 2^(r/2)` from it and from three inputs. I did not audit two of the inputs:

1. the sharp bound for cyclic cuts of size at most four (`small-cut-sharp-bound.tex`): **not audited by
   me**; I read the statements only;
2. the deficit at bounded girth (`bounded-girth-cycle-deficit.tex`, `path-fixed-girth.tex`): **read**; the
   prefix argument and the geometric sum are correct; it depends on the protected high-density theorem
   of the small-cut packet, which I did not audit;
3. the forest estimate of the manuscript with a fixed error: formalised for `|E(W)| <= sqrt(r)`. The
   proof needs the range `|E(W)| <= r / log^2 r` (Remark 6.10 of the manuscript). That range is not
   formalised. The layer lemma cannot work with the range `sqrt(r)`: a window of layers has a boundary
   of the order of one layer, which is far more than the square root of the window.

So the unrestricted bound has the status: written proof; the new part checked by both models; two long
inputs checked by Astra's agents only; nothing formalised as a whole.

## What I checked, in the order of the proof

1. **Localisation with a connected exterior.** The two contractions give the same quotient, and the
   restriction to the quotient is onto, so the laws agree. Rank formula. After the deletion of the edges
   of the cap cycle the spokes are pendant, so the event of the forest estimate is exactly the forest
   event inside the retained set.
2. **Layer width.** `R^+ = V minus the component of P`: larger set, smaller boundary, connected
   complement, all vertices cubic. `Phi(m)/4 <= Phi(m/2) <= Phi(rho)`. The window: growth factor
   `1 + 1/(48 L^2)`, fewer than `67 L^3` steps, boundary `mu/(8L^2) + 3k(67L^3+3) <= mu/(4L^2)` because
   `k <= 2^(L/2-50)` and `2000 L^5 <= 2^(L/2+50)` for `L >= 100`.
3. **Translation by a tree join.** The union of the root-to-port tree paths has at most `k` vertices in
   each layer and contains a `T`-join.
4. **Weighted Moore bound.** `2 m_0 2^(t-1)` non-backtracking walks, stationarity, Markov, and
   `m_0 2^(t-1) >= 12 h (h-1) > n_0^2`.
5. **Both affine bounds.** `h - 1 > (32/3) t` at `h = 256` (`t = 11`); `D < 8t`; `h >= 2^(D/8-4)`; a ball
   without ports with at least `2^(D/16-1)` vertices meets at most `D` layers.
6. **Core of a block and the product.** The average rank of a component is more than `L`; pruning a leaf
   lowers the boundary by one; ports are the vertices of degree two; given all other edges the two cores
   are independent and uniform in their parity classes.
7. **Terminal bipartitions.** The cut argument; at least two components of `K - v` with terminals; a
   vertex that is not a branch vertex has exactly two sides; the middle component of two vertices of a
   class has no terminal, so all its leaving edges end at the two vertices. I wrote the lemma with the
   middle sets `M(i,j)` as the statement and tested it by computer: `paper-checks/check_pieces.py`
   (4000 cases, 1132 classes of at least three vertices, 7103 middle sets).
8. **Packing.** `E prod (1 - I_v/2)`; a maximal direct-sum family has fewer than `2^d` members; a class
   with `(H+2)(s+3)` marked vertices gives `s+3` disjoint middle lifts of rank at least `H` and boundary
   at most `2d <= 4D`; at most one meets `P` and at most `s` meet `S`; the count
   `t + 2B + 2B(H+2)(s+3) <= (6H+15) d (s+1) t`.
9. **Girth raising.** The recursion `s_new + 1 <= (6H+16) b^2 2^b (s+1)` and the sum of the scales.
10. **Links, moment, chain.** As in my earlier audit of the two-scale proof, now with the hypothesis
    `p > 1/2` only. `b_1 <= 3Ax/z`, `eta_1 <= r^(-1/32+o(1))`, weight of good pairs more than
    `mu(mu/2 - 2) > 8 mu`, `T >= 8 * 2^s / L^3`.
11. **Blocks.** `|R(a,b)| >= (q-1)(D_1+1) >= 8L^2`; boundary at most `2L`; at most `L + |S_0| + 1` blocks
    are lost; `G[R]` is a subgraph of `J_0`; `D_0 / log(L+2)` tends to infinity.
12. **Induction.** Loop; cut of size at most four; bounded girth; a shortest cycle with
    `c_e <= 2^(r-2)`; the constant `K >= max(K_4, 2^(R_0/2))`.

## Two remarks

1. The nested-separator lemma is applied in `H = G - V(C)`, which need not be connected. The cycles of
   the chain lie in the component of `u` and `P`, so one can take that component for `H`. The new
   manuscript states it in this way.
2. `G - e` in the last case of the induction is not cubic. The induction is on `psi(r)`, so this is
   harmless, and the manuscript says so.

## Where the result is written up

`paper/cycle-count/sharp-cycle-paper.tex`, Sections 7 to 11, with tests in
`paper/cycle-count/paper-checks/` and the formalised steps in `Erdos1016/PolynomialBound/`.
