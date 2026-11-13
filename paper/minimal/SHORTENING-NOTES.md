# Does the formal proof give a shorter proof of the exact maximum?

Notes of Fable 5.2, 12 November 2026. Shared with Astra and KNT. The question is from KNT:
after the Lean proof of Theorem 1.1 of `exact-maximum/` (the number of cycles is `H(r)` for all
large `r`), is there a shorter proof?

These notes compare each section of the text with what the Lean proof uses. Astra's notes are in
`paper/cycle-count/research/2026-11-12/proof-shortening/` (start with `SHORTER-PROOF.txt`) and in
`paper/cycle-count/research/2026-11-12/further-simplification/`. The text changed four times on
12 November 2026: at 03:20 UTC (Section 6 of these notes), at 03:50 UTC (Section 7), at
05:00 UTC (Section 9) and at 05:45 UTC (Section 10). The theorem files of commit `3a80aa9` did
not change; the second proof is in new files.

## 1. Answer

**Yes: the text is now 279 typeset lines shorter (14.7 per cent) and has 42 pages in the place of
49.** Most of the gain is in Section 8 (221 lines). There the lemma on strings is gone: the chain
of nested separators, which the section already had for long cycles, also proves the packing
bound for short cycles (Section 7 of these notes), and a piece is now a large connected part
with few boundary vertices, without a Moore bound and without a core (Section 9). The forest
estimate is stated in the form that the proof uses, for a cubic multigraph with a marked set, so
the reduction from simple graphs is gone from this paper (Section 9). One proposition has the
estimates for cycles at girth `log r` that Sections 3 and 8 both need (Section 10). The changes
of the first round (the cap in Theorem 6.8, Corollary 5.11, Case 5) remove cases, but they
shorten the proofs by 9 lines only. No main part of the proof can be removed; Section 5 of these
notes gives the reason for each main part.

Typeset lines (`pdftotext -layout`), first text (commit `91c6904`) against the present text:

| Part of the text | Before | Now |
|---|---|---|
| Section 1 (the account of the formal proofs is longer) | 153 | 175 |
| Section 2 (the edge recursion and the localisation are now inside the proofs that use them) | 133 | 89 |
| Section 3 (Theorem 3.1 for a marked multigraph; no reduction lemma; Proposition 3.5) | 294 | 265 |
| Section 4 (the proof of Lemma 4.1 has the localisation) | 59 | 72 |
| Section 5 (Lemmas 5.8 and 5.9 with shorter proofs; Corollary 5.11 for a pole without bridge) | 353 | 339 |
| Section 6 (Lemma 6.5 is the cap; Theorem 6.8 has two cases less) | 281 | 275 |
| Section 8 (one chain argument, used twice; no strings; pieces by their size; eight statements) | 492 | 271 |
| Sections 7, 9 | 82 | 82 |
| The paper | 1,903 lines, 49 pages | 1,624 lines, 42 pages |

The column "Now" is the text after the fourth round, measured on 12 November 2026. The fifth
round (Section 11) had 1,608 lines and 41 pages by changes of the layout; it is withdrawn.

The second paper (`pancyclic/`) has the reduction lemma now. It has 277 lines and 8 pages (245
lines and 7 pages before).

**Correction of the first estimate.** In the first form of these notes (02:45 UTC) I wrote that
the changes A to D make the proof about one page shorter. This was an estimate, and it was
wrong: measured, A to D give 9 lines. I had not counted that the cap needs a lemma and a proof of
its own. Since then I write a candidate text, build it, and count the lines before I give a
number.

| Change | Found by | Effect on the text | Status |
|---|---|---|---|
| A. A cap for a cut of size four | Astra | the first Lemma 6.5 (low states), Cases 1 and 2 of Theorem 6.8 and the special case of rank one go away | in the text; proved in Lean |
| B. Caps for a cut of size two or three | Fable | no Case A in Proposition 6.3, no bound `(9/16) 2^b` | **not in the text**: about five lines longer than the first proof. Proved in Lean |
| C. A set of eight vertices in Case 5 | Astra | no shortest cycle in Section 9 | in the text; proved in Lean |
| D. The sides of a smallest cyclic cut have no bridge | Astra | Corollary 5.11 has one conclusion | in the text; proved in Lean |
| E. In a graph without a cyclic cut of size three, a side of rank at least four has no three full pairs at one port | Fable | Lemma 6.7 and one case of Theorem 6.8 would change (estimate: about 5 lines after the note on the formal method; not measured) | **not in the text**: proof by hand and a complete search for ranks 3 to 6; no Lean proof |
| F. The packing bound from the chain | Fable | the lemma on strings, the parity spaces and the separate chain lemma go away; Section 8 loses 145 lines | in the text; proved in Lean by Astra (`Shortening.ChainPacking.exists_cutoff`, with the bound `150 d^3 (s+1) 2^d`) |
| G. One case in the lemma on forest proportions and in the proposition on pieces | Fable | the case with rank 256 goes away | in the text; proved in Lean by Astra (`Shortening.LargeOrderPieces`) |
| H. One lemma on links for Sections 3 and 8 | Fable | Lemma 3.7 (3.8 before the third round) has the two lemmas on links of Section 8 | in the text; the two parts are in Lean in other forms |
| I. A limit argument for Lemma 6.6 | Astra | no decimal numbers in Lemma 6.6 and Theorem 6.8 | **not in the text**: measured 3 lines longer. Proved in Lean |
| J. Pieces by their size | Fable | no Moore bound with ports, no core; 39 lines | in the text; the formal proof keeps the Moore bound and the core |
| K. Theorem 3.1 for a marked multigraph | Fable | no reduction lemma, no forest input, shorter Lemmas 2.1 and 2.6; 42 lines | in the text; this is the Lean theorem `eventually_marked_forest_bound_logSquared` |
| L. Lemma 5.8 by a count, Lemma 5.9 by a cycle that a path avoids, Lemma 8.6 by connected sets | Fable | 14 lines | in the text; the formal proofs of 5.8 and 5.9 use the first arguments |
| M. One second-moment lemma for four places | Fable | none | **not in the text**: measured 0 lines |
| N. One proposition for cycles at girth `log r` (Proposition 3.5) | Fable | the parameter checks of Sections 3.2 and 8.4 are done once; the two lemmas on links and the lemma on the second moment are steps of its proof; 38 lines with O | in the text; no change of a formal statement |
| O. Three lemmas of Section 8 that had one use (marker, blocks, pieces) are steps of the proofs that use them | Fable | Section 8 has the statements 8.1 to 8.8 | in the text |
| P. The lemma on two links takes the second-moment bound as hypothesis | Fable | 7 lines | in the text |
| Q. The edge recursion and the localisation are steps of the proofs that use them | Fable | 22 lines | in the text |

There are two formal proofs of the theorem in the library, and Astra has more in
`ExactMaximumSupport/Shortening/`:

- `Erdos1016.ExactMaximum.exactMaximum` (`Main.lean`), the first proof. It is at commit
  `3a80aa9`.
- `Erdos1016.ExactMaximum.exactMaximum_caps` (`MainCaps.lean`), the proof by the cases of the
  present text: `threeCutStatement`, Astra's `Shortening.FourCutTreeCap.fourCutStatement` (A),
  `shortCycleStatement`, Astra's `Shortening.ChainLargeGirth.largeGirthStatement` (C, F, G), the
  reduction and the lower bound. `lake build` passes (7,288 jobs,
  exit code 0, 12 November 2026, 05:00 UTC), and `audits/ExactMaximumCapsAudit.lean` passes
  (exit code 0): 15 axiom reports with the standard axioms only; the proof term of
  `exactMaximum_caps` uses 7,986 declarations of the project (the first proof: 8,380) and none
  of the first proof of Theorem 6.8, of Case 5, of the packing bound or of the theorem.
- Astra's own shortest assembly is `Shortening.ChainExactMaximum.exactMaximum` (compactness for
  the cut of size four, one mark per thread in the case of bounded girth); its proof closure has
  8,275 declarations of the project, against 8,730 for the first proof.
- The formal proof differs from the text in method in three places: Theorem 3.1 (the links are
  bounded with Lemma 2.5), Lemmas 5.8 and 5.9 (two disjoint paths and exact counts), and the
  lemma on forest proportions of Section 8.1 (core and Moore bound). Section 1.4 of the paper
  says so.

## 2. What the formal proof uses

Astra extracted the dependencies of `ExactMaximum.exactMaximum` from the proof terms
(`random-dependency-summary.txt`): 8,730 declarations of this project in 546 modules. The theorem
`Erdos1016.mainTheorem` on pancyclic graphs is not among them. All 63 proof modules of
`Erdos1016/ExactMaximum/` are used.

The last column has Astra's groups: the number of declarations that only the named group uses.

| Part | Text (source lines) | Astra's groups |
|---|---|---|
| Sections 2 and 3: tools, forest estimate, leading term | 628 | old forest estimate 187, leading term 323 |
| Section 4: layers | 78 | in the groups of Sections 5 and 8 |
| Section 5: poles, Theorem 5.4, gap | 535 | few cycles 278, Corollary 5.6 261, gap 597 |
| Section 6: rings, cuts | 383 | rings 537, lower bound 187 |
| Section 7: bounded girth | 62 | 468 |
| Section 8: large girth | 716 | large girth 1,203, its forest estimate 1,131 |
| Section 9 and the reduction to cubic multigraphs | 46 | 65 |

About 3,500 declarations are in no group, because several parts use them: the cycle space,
networks, links, the second moment, and the counts for the cuts. In Lean
the leading term (Corollary 3.11) comes from the older proof with chords and triangles. The text
has the shorter proof with a shortest cycle and a recursion. This is a possible cleanup of the
Lean files. It does not shorten the text.

## 3. The changes that are proved in Lean (Astra)

**A. Caps.** Let `Y` be a pole of rank `k` with four ports, and let `α = ij|kl` be a pairing.
Add two adjacent vertices `x`, `y`; join `x` to the ports `i`, `j` and `y` to the ports `k`, `l`.
The new multigraph has rank `k + 3`. Its cycles are: the cycles of `Y`; a path of `Y` between
two ports, closed through `x`, `y` or both; and two disjoint paths of `Y` with a pairing other
than `α`, closed through `x` and `y`. Corollary 3.11 for this multigraph gives, for large `k`,

    z + S + F - u_α ≤ 4.001,      z = c(Y) / 2^k.

In Theorem 6.8, `a_ij(X) ≤ 1` and `F(X) ≤ 1` give `B ≤ S(Y) + F(Y) - min_α u_α(Y)`. So
`z + B ≤ 4.001`. If `c(G) ≥ 2^(r-1)`, the gluing formula gives `4 ≤ 2^(-k) + z/2 + B`. Hence
`z ≤ 0.004` and `B ≥ 3.997`, so `S(Y) + F(Y) ≥ 3.997`, and Lemma 6.6 (rigidity) applies at once.
This works for every rank `h ≥ 1` of the other side.

Lean: `Shortening.TreeCapCycleBound.exists_thousandth_bound`,
`Shortening.FourCutTreeCap.fourCutStatement`.

**C. Eight vertices.** In Case 5 take a set `P` of eight vertices that induces a connected
subgraph. Then `|δP| = 24 - 2|E(G[P])|`, every component of `G - P` has two edges to `P`, and
`β(G - P) ≤ r - 5`. So `c(G) < (2/5 + 1/32) 2^r`. A path with five vertices is also sufficient
(`β(G - P) ≤ r - 4`). Theorem 8.1 is then necessary only for a set `P` of fixed size. Its proof
uses the size of `P` in two places only (the number of vertices and the deficit of `J`), so this
does not shorten Section 8.

Lean: `Shortening.FixedMarkerLargeGirth.largeGirthStatement`.

**D. No bridge.** If a side `S` of a smallest cyclic cut of size `d ≥ 3` had a bridge, the two
parts `A`, `B` of `S` would each contain a cycle, and `|δA| + |δB| = d + 2 < 2d`. So Corollary
5.11 is necessary only for a pole without bridge, and its case (ii) is not necessary.

Lean: `Shortening.MinimalCutBridgeless.four_cut_shore_bridgeless`.

## 4. The changes that I found

**B. Caps for a cut of size two or three.** The idea of A also removes the first case of
Proposition 6.3. Use the notation of that proof, with `z = c(T_2) / 2^(b_2)` and a small `δ`.

- `d = 2`: add an edge between the two ports of `T_2`. The rank is `b_2 + 1`, and the cycles are
  the cycles of `T_2` and its paths between the ports. So `z + a_1 ≤ 1 + 2δ`.
- `d = 3`: add a vertex and join it to the three ports. The rank is `b_2 + 2`, and
  `z + a_1 + a_2 + a_3 ≤ 2 + 4δ`.

Suppose that `c(G) ≥ 2^(r-1) = 2^(d-2) 2^(b_1+b_2)`. Formula (6.1) and `x_j ≤ 1` give

    2^(d-2) < 2^(-b_2) + z/2 + Σ x_j a_j ≤ 2^(-b_2) - z/2 + 2^(d-2) (1 + 2δ).

So `z` is small, and `Σ x_j a_j > 2^(d-2) - 0.001` for large `b_2`.

- `d = 2`: `x_1 a_1 > 0.999`, so both numbers exceed `0.501`. Lemma 5.7 (a) for both sides
  gives `c(G) ≤ 2^(r-1) + 2 K_0 2^(r/2)`.
- `d = 3`: let `a_1 ≥ a_2 ≥ a_3`. Then `a_1 + a_2 > 1.33`, so `a_3 ≤ κ(b_2)` by Lemma 5.7 (b).
  Then `x_1 a_1 + x_2 a_2 > 1.998`. So `x_1 + x_2 > 1.998`, and `x_1`, `a_1 > 0.998`. Lemma 5.7
  (b) gives `x_3 ≤ κ(b_1)`, and (a) gives `c(T_i) ≤ K_0 2^(b_i/2)` for both sides. The last
  display of the proof gives the bound.

Case A of the proof and the three sub-cases with a sum below `1.002` go away, and the bound
`c(T) ≤ (9/16) 2^b` is not used.

*Result.* I wrote this proof into the text and measured it. It is about five typeset lines
longer than the proof with the bound `(9/16) 2^b`, because the cap and the two inequalities need
more room than Case A. So the text keeps the first proof of Proposition 6.3. The proof with caps
is in Lean: `ExactMaximum.capStatement` (`CutCaps.lean`) and
`ExactMaximum.threeCutStatement_caps` (`SmallCutCaps.lean`, `MainCaps.lean`). The audit file
checks that it does not use `poleCycleBoundStatement`. The Lean arithmetic uses the cap in the
case in which the larger side has no pair of ports with many paths; it does not suppose
`c(G) ≥ 2^(r-1)`.

**E. Three full pairs at one port do not occur.**

*Addition to Lemma 5.9.* Let `T` be a pole with three ports `s`, `t`, `v`, without bridge, of
rank `h ≥ 2`, and let the pair `s,t` be full. By Lemma 5.8, `T` is a capped ladder with caps `s`,
`t` in which `v` subdivides an edge `e`. Then `P_vt(T) = 2^h` if and only if `e` is an edge at
the cap `s`, or `e` is the first tile and this tile is a single rung. This is in the proof of
Lemma 5.9: the three counts are `(1 + A) 2^q'`, `2 (1 + A) 2^q'` and `(4 + 3A) 2^q'`, and the
value `2^h` occurs only for `p = 0` in the first two.

*Lemma (no star).* Let `Y` be a pole with four ports, without bridge, of rank `h ≥ 4`, such that
the pairs `12`, `13`, `14` are full. Then there is a set `A` of vertices with `1 ∈ A` and
`2, 3, 4 ∉ A` such that exactly two edges of `Y` leave `A`, and `Y[A]` contains a cycle.

*Proof.* Replace the ports `3` and `4` by edges. The result is a pole with ports `1`, `2`,
without bridge, of rank `h`, and the pair is full. By Lemma 5.8 it is a capped ladder with tiles
`τ_1, …, τ_m` from the cap `2` to the cap `1`. Its weight is `h - 1 ≥ 3`, so `m ≥ 2`. The pole
`Y` arises when the ports `3` and `4` subdivide edges. The pairs `13` and `14` are full. By the
addition to Lemma 5.9, with `s = 2` and `t = 1`, each of the ports `3`, `4` subdivides an edge at
the cap `2` or the single rung `τ_1`. Let `A` consist of the cap `1` and the vertices of
`τ_2, …, τ_m`. The two edges between `τ_1` and `τ_2` are the edges that leave `A`. The cap `1`
and the tile `τ_m` contain a cycle. ∎

*Use.* Let `G` have a cyclic cut of size four and no smaller cyclic cut, and let `Y` be a side of
rank at least four. By D, `Y` has no bridge. If three pairs at the port `1` were full, the two
edges that leave `A` and the cut edge at the port `1` would be a cyclic cut of size three. So
Lemma 6.6 gives the four full pairs between two pairs of ports. Lemma 6.7 and the case of three
full pairs in Theorem 6.8 are then not necessary.

*Caution.* The poles of the lemma exist: a capped ladder from `1` to `2` whose tile next to `2`
is a single rung, with the ports `3` and `4` on this rung. The lemma says only that such a pole
is not a side of a cut in a graph without a cyclic cut of size three.

*Check.* `paper/minimal/checks/star_check.py` lists all poles with four ports of a given rank
and tests the lemma without Lemma 5.8. Output for the ranks 3 to 6:

| Rank | Multigraphs listed | With the three full pairs | Of these without bridge | Exceptions |
|---|---|---|---|---|
| 3 | 1,844 | 30 | 17 | 0 |
| 4 | 32,316 | 70 | 31 | 0 |
| 5 | 618,110 | 168 | 47 | 0 |
| 6 | 13,020,801 | 391 | 74 | 0 |

For rank 2 the lemma is false (6 exceptions). The lemma is not in Lean. The gain in the text is
small, because the lemma replaces a lemma of similar length. The gain is in the logic: Theorem
6.8 has one shape only.

**Smaller remarks.**

- Lemma 6.7 uses only two of the three full pairs. The Lean statement
  (`two_mul_numPathPairs_le_of_full`) has two.
- In Case 3 of Theorem 6.8 the bounds `a_ij(X) ≤ κ(h)` and `c(X) ≤ K_0 2^(h/2)` for the small
  side are not necessary: `a_ij(X) ≤ 1`, `a_ij(Y) ≤ κ(k)` and `c(X) < 2^h` are sufficient. The
  assumption `h ≤ k` is used only to make `k` large.
- Corollary 5.6 can be a statement about the pole alone: a pole with at most `g + 2` ports, a
  large rank and many paths has a cycle of length at most four among its vertices of degree
  three. The Lean statement (`CyclicShoreStatement`) has this form.
- Theorem 5.4 is used for arbitrary `ε` only in Corollary 5.6. The cuts use `ε_0 = 1/1000`.
- Theorem 3.1 is used with a fixed error only. A statement "for every `δ > 0` and large `r`,
  `p(G, W) ≤ 1/2 + δ`" has the same proof with `L = M log r` for a constant `M`, without the
  iterated logarithms. This is a matter of taste; the present statement is the theorem of [KNT].

## 5. What cannot be removed, and why

1. **Theorem 3.1 (forest estimate).** It gives Corollary 3.11 and Lemma 4.1. Theorem 8.1 uses
   Lemma 4.1 (through Lemma 8.2), so Theorem 8.1 cannot replace Theorem 3.1.
2. **Theorem 8.1 (large girth).** The general estimate gives `1/2 + o(1)`. A graph of large girth
   needs a bound below `1/2`. The count of Section 7 saves only `2^(-g)` for girth `g`, and it
   needs poles with at most `(1/2 + 2^(-g-2)) 2^b` paths. The constants of Proposition 5.3 for
   this margin are much larger than the rank when `g` is not bounded.
3. **Section 7 (bounded girth).** Theorem 8.1 starts from pieces in which every set of ports has
   a forest proportion of at most `3/5` (Lemma 8.4). The proof needs a ball that is a tree, so it
   needs large girth. For girth five we have this bound only for two ports (Corollary 5.6). A
   bound for every set of ports of a pole of girth five would join Cases 4 and 5. I found no
   proof. The argument of Lemma 8.2 does not help: when `N - P` is a forest, `q(N, P) = 1`.
4. **Theorem 5.4 (few cycles).** For a cut of size two, two capped ladders joined by two edges
   have `2^(r-1) + c(T_1) + c(T_2)` cycles. A ring has only a factor `r` more in the second term.
   So the bound `K 2^(b/2)` is necessary. For a cut of size four, the caps and the gap are not
   sufficient: the numbers `a_ij(Y) = 2/3`, `F(Y) = 0`, `c(Y) = 0`, with a cycle of length four
   as `X`, satisfy all cap inequalities and give `B = 4` (Astra, `four-cap-obstructions.txt`).
   Statement (T1) excludes these numbers, and (T1) is Theorem 5.4 with the margin `1/6`.
5. **Theorem 5.10 (gap) and Lemma 5.8 (ladders).** One missing path in a side of rank `h` costs
   `2^k` cycles. The terms without control are of order `2^((h+k)/2)`, which is larger when `h` is
   near `k`. So "almost full" must give "full". The ladders are necessary to find the ring.
6. **An induction on the rank.** It needs the theorem for the first rank. No proof by induction
   that starts from the trivial bound is known to us.

## 6. What is now in the text

1. Lemma 6.4 (gluing): the bound is `B ≤ S(Y) + F(Y) - min_α u_α(Y)`.
2. Lemma 6.5 is the cap for four ports: `z + S + F - u_α ≤ 4.001`. The lemma on low states is
   gone. The numbers of the other statements of Section 6 and the numbers of the equations did
   not change.
3. Theorem 6.8: the sides have no bridge (D, six lines in the proof); if `c(G) ≥ 2^(r-1)`, the
   cap gives `S(Y) + F(Y) > 3.997`; Lemma 6.6; three full pairs at one port are impossible by
   the gap theorem and Lemma 6.7; four full pairs in both sides give a ring.
4. Corollary 5.11 is for a pole without bridge and has one conclusion.
5. Section 9, Case 5: a connected set of eight vertices; the condition
   `2 log(2r) + 2 ≤ 3 log r` is gone.
6. Section 1.4: the table names the declarations of the second formal proof; the text says that
   commit `3a80aa9` has the first formal proof and that the files of the second proof are not in
   a commit yet. **When KNT asks for a commit, this sentence needs the new commit number.**

Proposition 6.3 has its first proof (see B). The first text is in git: commit `91c6904`.

## 7. The second round: one chain argument in Section 8 (F, G, H)

*The observation.* The first text had two tools in Section 8 for the same task. For long cycles
it used the second moment and a chain of nested separators (Lemmas 8.13 to 8.16). For short
cycles (the packing bound, Proposition 8.9) it used local parity spaces, a maximal direct sum,
and a lemma on strings (Lemma 8.8, 75 source lines). But the packing bound has the hypotheses of
the chain argument in a simpler form: the sets are pairwise disjoint.

*The new proof of the packing bound.* Let `X_1, …, X_n` be disjoint cyclic regions outside
`U = P ∪ S` with at most `d` boundary edges, and let `q(G, U) ≥ 2/5`. Let `E_i` be the event
that no edge of `δX_i` is in `ξ` and `ξ` has an edge in `G[X_i]`, with `p_i = P(E_i) ≥ 2^(-d-1)`
and `μ = Σ p_i`. As in Lemma 2.5, `P(E_i ∩ E_j) = 2^(ℓ-1) p_i p_j`, and each `i` has at most `d`
partners with three or more links. So `E Z^2 ≤ μ^2 + W_2 + (d+1) μ`, where `W_2` is the weight of
the pairs with exactly two links. No `E_i` occurs on the forest event, so `P(Z ≠ 0) ≤ 3/5`, and
`W_2 ≥ (2/3) μ^2 - (d+1) μ`. A pair with two links gives a separator: one of the two sets
separates a neighbour `u` of the other set from a vertex `p ∈ P`. So some set `X` and some `u`
have `T ≥ (μ/3 - 2d)/d` separators. These are nested. A block between every `(16d+1)`-th of them
has at least `8d^2` vertices and at most `2d` boundary edges, and it avoids `P`. Two blocks that
also avoid `S` and the neighbours of `X` give `q(G, U) ≤ 9/25`. So `T ≤ (d+s+2)(16d+1)`, and
`n ≤ 2^(d+1) μ ≤ 150 d^3 (s+1) 2^d`.

*The new structure of Section 8.*

1. Lemma 8.4 and Proposition 8.7 have one case (G): rank at least `Λ ≥ 4`, at most `2Λ` ports,
   girth at least `C_0 log(Λ+2)`. `D_*` is an integer with `D ≥ C_0 log(2D+2)` for `D ≥ D_*`.
2. Section 8.2 (separators): nested separators, blocks, and two new statements. Proposition 8.10
   (a long chain): many disjoint regions with small boundaries that separate `u` from `p` give
   `q(G, U) ≤ 9/25`. Lemma 8.11 (two links): a family of regions with weights, in which the pairs
   with two links have a large weight, has a set `A` and a vertex `u` with separators of large
   weight.
3. Section 8.3: the packing bound from 8.11 and 8.10; raising the girth with
   `log(|S_j|+1) ≤ 2 D_j + 7 log^2 D_j`.
4. Section 8.4, the proof of Theorem 8.1: it has the second moment for cycles and uses 8.11 and
   8.10 again. There is no separate lemma on two links for cycles, no chain lemma, and the
   paragraphs on blocks are gone.
5. Lemma 3.8 (H) has two parts: (a) the bound `5·2^t` for the components with a cycle that join
   two regions (the first Lemma 8.11); (b) the bound for the links of two cycles, with "at most
   `c` components of `Γ[P]`" (the first Lemmas 3.8 and 8.12). The proof of Theorem 3.1 uses (b)
   with `t = ⌊y/2⌋`.

*Check.* I checked each step of the new proofs against the lemmas that they use. Astra checks
them independently and writes a Lean proof (`Shortening/DisjointRegionChain.lean`,
`ChainPacking*.lean`); its first report confirms the separators.

*Not applied.* I wrote Astra's limit argument (I) into the text: Lemma 6.6 for limits of states,
with exact laws and a short classification, and Theorem 6.8 by a sequence of counterexamples.
Measured: Section 6 has 276 lines with it and 273 without. So the text keeps the explicit numbers.

## 8. Open candidates

- Astra: a pole of girth at least five with a bounded number of ports and a large rank has at
  most `(1/2 + ε) 2^b` paths between two ports. It can replace Corollary 5.6 in Section 7. The
  statement is cleaner. I expect that the proof in the text is not shorter, because it adds the
  gap theorem and the ladders to the thin layers; this is not measured. It is proved in Lean
  (`Shortening/BoundedPortShortCycle.lean`).
- Fable: change E, about 5 lines (estimate). With the new proof of Lemma 5.9 the positions of the
  third port are in the text already (the pair is full only if the edge is at the cap or is a
  first single rung).
- Open mathematics: a bound `3/5` for the forest proportion of every set of boundary vertices of
  a large piece of girth at least five in a graph without a cyclic cut of size at most four. It
  would let Theorem 8.1 start at girth five and remove Section 7, Lemma 5.5 and Corollary 5.6
  (about 95 lines). The examples to exclude are ladders and tubes; see Section 9.
- Open mathematics: a proof of the bound below `1/2` for bounded girth from Theorem 3.1 alone.
  One cycle `Z` of bounded length with a small set `U ⊇ V(Z)` such that two vertices of `Z` that
  are joined in `G - E(Z)` are joined in `G[U] - E(Z)` is sufficient (Section 9). A graph that is
  a long tube has no such cycle.

## 9. The third round: statements in the form that the proof uses (J, K, L)

*J. Pieces by their size.* Section 8.1 of the first text reduced a piece to its core (degrees two
and three) and used a Moore bound for multigraphs with ports to find a large layer. Now a piece
is a connected subcubic multigraph `N`; its vertices of degree less than three are its boundary
vertices. If `N` has at most `2Λ` boundary vertices, at least `C_1 Λ^4` vertices and girth at
least `C_0 log(Λ+2)`, then some vertex has distance more than `s` from the boundary, where `s`
is the least integer with `2^s > (2s+1) B (2Λ+1)^2`. The ball of radius `s` around it is a tree
with at least `2^s` vertices in at most `2s+1` layers, and the marker lemma with Lemma 4.1 gives
the bound `3/5` for every set of boundary vertices. The proposition on pieces asks for
`2 C_1 Λ^5` vertices, and the proposition on a long chain has a lower bound `m` for the size of
a separator. The constants are `C_2 = 44 C_1` in the packing bound `C_2 d^6 (s+1) 2^d` and
`C_3 = 7 + log(2 C_2)` in the theorem on raising the girth. Section 8 has the statements 8.1 to
8.11.

*K. The forest estimate for a marked multigraph.* The first text stated Theorem 3.1 for a union
of cycles `W` in a simple graph, reduced it to a multigraph with a marked set `P` (Lemma 3.2),
and then went back to multigraphs by subdivision (Proposition 3.9, Corollary 3.11) and to one
cycle by localisation (Lemma 2.6). The proof of the exact maximum needs none of this: Lemma 4.1
uses the localised multigraph `G_X` with `P = V(W_X)`, and the leading term uses a cubic
multigraph with `P` the vertex set of a shortest cycle. So Theorem 3.1 is now the statement for
`q(Γ, P)`: `Γ` connected and subcubic of rank `r`, at most `2r / log^2 r` vertices in `P`, every
vertex outside `P` of degree three, at most `(log r)/100` components of `Γ[P]`. This is the Lean
theorem `Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared`, word for word. Lemma
2.1 is `c_e(G) ≤ q(G, V(W)) 2^(r-1)` (a cycle `C` through `e` and `C + W` have the same edges
away from `W`). The number `R_δ` is defined in Section 4. The pancyclic paper needs the form for
a union of cycles; the reduction lemma is in that paper now.

New numbers in Section 3: 3.2 walks, 3.3 spectrum, 3.4 cycle weight, 3.5 second moment, 3.6 links
through trees, 3.7 few links, 3.8 cubic multigraphs, 3.9 leading term. The first text and the
Lean comments of commit `3a80aa9` use the numbers 3.3 to 3.11 for these.

*L. Three shorter proofs.*

- Lemma 5.8 (ladders). In a bridgeless pole with two ports and a full pair, `J = N - V(A)` is a
  forest. The count of Step 4 of Proposition 5.3 then gives `ℓ = b` with equality in each
  estimate. So every inner layer is `{w_j, y_j}`, `J` is the path `y_1 … y_(b-1)`, and the
  further edges of `A` are a permutation `π` with `|π(j) - j| ≤ 1`.
- Lemma 5.1 has one more sentence: if a cycle `Z` is disjoint from a path from `s` to `t` and
  `N - E(Z)` has `k` components, then `P_st ≤ 2^b - 2^(b-|Z|+k-1)`. With it, Lemma 5.9 (third
  port) has four short cases and no numbers `A_i`. Test: `checks/third_port_check.py 9` counts
  the paths for every position of the third port in every capped ladder of weight at most 9
  (3,482 positions) and compares with the four cases; exit code 0. The test covers the counts,
  not the reduction to a capped ladder.
- Lemma 8.6 (nested separators): if `C_2` is not in `U_1`, then `U_1 ∪ C_1` is connected,
  contains `u` and avoids `C_2`.

*Looked at and not usable.*

- A product with one piece: `q(G, P) ≤ max_T (forest proportion of T in G[U]) · q(G/U, P ∪ {u})`.
  With the second factor at most `1/2 + o(1)` by Theorem 3.1, one piece would be sufficient. But
  Theorem 3.1 needs a boundary of `U` that is small against the rank of `G/U`, and a graph that
  expands has no such set `U`.
- A cycle with a free neighbourhood: if two vertices of `Z` that are joined in `G - E(Z)` are
  joined in `G[U] - E(Z)`, then `Z ⊆ ξ` has probability at least `2^(-|Z|)` for every choice of
  `ξ` outside `G[U]`. Disjoint sets `U_i` would give the packing bound at once. But they do not
  exist in a long tube, and there the chain is necessary.
- Caps and the gap theorem without Theorem 5.4 for the cut of size four: the numbers
  `a_ij = 1/2`, `u = (1/2, 1/2, 0)` satisfy all cap inequalities and reach `B = 4`.

## 10. The fourth round: one proposition for Sections 3 and 8, and tools with one use (N to Q)

*N. Proposition 3.5 (logarithmic girth).* The proofs of Theorem 3.1 and of Theorem 8.1 both
delete a maximal family of short cycles, and then both check the same things for the graph `J`
of girth about `log r`: the number of links of two cycles, the error term of the second moment,
the deficit of `J`, and the weight of the cycles. They did this with different parameters. Now
one proposition does it: let `Γ`, `P` be as in Theorem 3.1 with `q(Γ,P) ≥ 2/5`, let
`x/16 ≤ D ≤ x/8` and `7x ≤ L ≤ x sqrt(y)` (`x = log r`, `y = log x`), and let `S` be the union
of a maximal family of disjoint cycles of length at most `D` outside `P` with `|S| ≤ r/x^2`.
Then `L^2 2^(-s) ≤ r^(-1/60)`, `μ ≥ (1/4) ln(L/(6x)) - 1/sqrt(x)` and
`E Z^2 ≤ μ^2 + W_2 + (1 + r^(-1/60)) μ`. The proof has four steps: parallel components with a
cycle (the first Lemma 3.8 (a)), the links of two cycles (the first Lemmas 3.7 and 3.8 (b),
with `t = floor(y/2)` and the bound `x/90`), the second moment (the first Lemma 3.6), and the
weight (Lemma 3.4). The proof of Theorem 3.1 is then: packing by Lemma 2.4, the proposition with
`L = floor(x sqrt(y))`, and Lemma 2.1. The proof of Theorem 8.1 uses the proposition with
`D = D+` and `L = floor(Ax)`.

*O, P, Q. Tools with one use.* A lemma that only one proof uses, as one step, is now a step of
that proof: the marker (in the lemma on forest proportions), the blocks and the pieces (in the
proposition on a long chain), the edge recursion (in the leading term) and the localisation (in
Lemma 4.1). The lemma on two links has the hypothesis `W_2 ≥ (2/3) μ^2 - K μ` and the conclusion
`(μ/3 - K/2 - e)/N`, so its two uses need no computation. I did not fold the statements that
carry an idea of their own (the cap, the full star, the product, the nested separators, the
packing bound, the third port, four thin layers, the spectrum, four ports).

*New numbers.* Section 2: 2.1 second moment inequality, 2.2 link formula, 2.3 exceptional
partners, 2.4 many small cuts. Section 3: 3.1 forest estimate, 3.2 walks, 3.3 spectrum, 3.4 cycle
weight, 3.5 logarithmic girth, 3.6 cubic multigraphs, 3.7 leading term. Section 8: 8.1 the
theorem, 8.2 forest proportions, 8.3 product, 8.4 nested separators, 8.5 long chain, 8.6 two
links, 8.7 packing, 8.8 raising the girth. Sections 4 to 7 keep their numbers.

*Looked at in this round and not usable.*

- A proof of the cut of size two or three, or four, without Theorem 5.4: the numbers
  `a = (2/3, 2/3, 2/3)` for three ports satisfy the cap inequality and the gap theorem, and with
  a triangle as the other side they give `2^(r-1) (1 + δ/4)` cycles. Only the statement
  "two pairs with sum above one exclude the third pair" removes them, and this is Theorem 5.4.
- The bound `3/5` for pieces of girth five (it would remove Section 7): for a set `T` with an
  odd number of vertices at each end of a long thin piece, every `T`-join crosses all separators.
  A marker with several long strands can have a forest as complement, so the marker lemma gives
  nothing; a proof needs cycles that do not separate the two ends, and these can be long.
- Folding all lemmas with one use would save about 50 more lines; the proofs would be long.

## 11. The fifth round (12 November 2026, 06:30 UTC): sixteen lines and one page, withdrawn

**Withdrawn.** The part "Applied" below changed the layout and no mathematics. KNT wrote that a
shorter layout is not wanted for its own sake: the aim is new mathematics. The text is the text
of the fourth round again (1,624 lines, 42 pages). The parts "Measured and not applied" and
"Looked at and not usable" stay valid. Section 12 has the result of the research task that
followed.

KNT asked to keep the nine statements of Section 10 and to look for more. Astra does not work on
the project any more, so nobody will formalise a new argument of the text unless Fable does it.
I read the changed sections again line by line (Sections 3 and 8 after the fourth round) and
found no error; one clause was missing in Step 1 of Proposition 3.5 and is added.

*Measured and not applied.*

- A proof of Lemma 6.6 (rigidity) by the number of pairs with `a_ij > κ` (three, four, five or
  six). It is more regular than the proof with cross sums. Typeset it has the same number of
  lines (Section 6: 275 and 275), so the first proof stays.

*Looked at and not usable.*

- **A recursion for the cut of size two.** Close each side `T_i` by an edge between its two
  ports. Then `c(T_i) + P_i ≤ ψ(b_i + 1)`, and
  `c(G) ≤ 2^(r-1) + A(b_1+1) + A(b_2+1)` with `A(ρ) = ψ(ρ) - 2^(ρ-1)`. With an induction on the
  rank this gives the cut of size two without Section 5. For the cut of size three the same
  idea gives a product `A(b_1+2) A(b_2+2)`, which is too large by a factor of order `r^2`. So
  Theorem 5.4 is necessary for three and four, and the recursion does not shorten Proposition 6.3.
- **A marker without layers.** If the boundary vertices of a piece `N` lie in a connected set
  `P'` of `N` with at most `2β(N)/log^2 β(N)` vertices, then every even set of boundary vertices
  has forest proportion at most `1/2 + o(1)`, by Theorem 3.1 alone, with no condition on the
  girth (the argument of the step "a marker" of Lemma 8.2). So the girth is necessary only for
  pieces that are long and thin: their boundary vertices are far from each other. The same
  observation gives the case of bounded girth in a few lines when the neighbours of a shortest
  cycle `C` are near to each other in `G - V(C)`: sort the cycles that meet `C` by their edges
  at `C`; each forest join of `G - V(C)` gives at most two cycles; the result is
  `c(G) ≤ 2^(r-1) - 2^(r-g-1) + o(2^r)`. A long tube that is closed through `C` has no such
  cycle, so Section 7 with Corollary 5.6 stays.
- **The bound `3/5` for long thin pieces of girth five.** With it, the packing bound would need
  one stage and no girth, and Theorem 8.8, the two girth scales, Section 7, Lemma 5.5 and
  Corollary 5.6 would go (about 200 lines). For a set `T` with an even number of vertices at
  each end, the separators themselves are cycles that every join can contain, independently,
  so the forest proportion is at most `(1 - 2^(1-d))^m` for `m` separators. For an odd number at
  each end, a proof needs short cycles that do not separate the two ends. I have no proof that
  they exist in every window of a thin piece.
- Change E (Section 4 of these notes) gives about 4 lines and a fifth place in which the formal
  proof has another method. Not applied.

*Applied.* The introduction told the plan three times (the eight sentences, the figure with the
five cases, and two passages in Sections 1.2 and 1.3). The two passages are shorter now, and
Section 8 does not recall the definition of `q`. Measured: 7 lines, and no page: white space
before Section 5 took up the gain. The last page then had nine lines of references. Four short
displays at the end of Section 8 and at the start of Section 9 are now in the text line, the
inequality for `W_2` is inside the paragraph on the chain, and one sentence of comment is gone.
Measured: 9 lines more, and the references fit on page 41.

*White space.* The pages lose about 650 points to white space, a little less than one page. I
made the boxes of the statements breakable as a test: the white space fell by 60 points only and
the number of pages did not change, so the design file is as before. The space is lost before
headings, displays and figures.

*What is left without new mathematics.* The nine statements with one use are about 50 lines.
Everything else that I measured in five rounds is in these notes.

## 12. The research task on Section 8 (12 November 2026): one family of short cycles

KNT set a research task: find a shorter mathematical proof of Theorem 8.1, without Theorem 8.8
if possible, and do not change the manuscript before a simplification is established. The result
is in `research/one-scale.pdf` (18 pages, with complete proofs). The manuscript is unchanged.

- *First proof.* The chain proposition discards the blocks that contain a short cycle, and it
  counts them by a packing number. It needs no deleted set. One proposition on a weighted family
  of regions ("heavy families") then gives the packing bound and the final contradiction. The
  packing bound for the length `d` follows from the bound for the length `C_0 log(d+2)`, by
  induction. Theorem 8.8, the nested sets `S_j`, the two girth scales and the set `U` of
  Proposition 8.5 are gone. Measured in a copy: Section 8 has 259 lines in the place of 271, and
  the paper keeps 42 pages.
- *Second proof.* A new lemma on pieces: at a fixed girth, every large connected subcubic
  multigraph with a small boundary has a forest proportion of less than 3/5. The proof is an
  induction on the number of boundary vertices: short cycles that are free give the bound by the
  second moment, and short cycles that are not free separate two boundary vertices, so they are
  nested. Then two large disjoint regions with small boundaries always give `q <= 9/25`, and the
  packing bound has no induction. Measured in a copy: Section 8 has 289 lines.
- *Negative results.* The hypotheses of Case 5 do not exclude pairs with two links (necklaces
  over a bipartite Hamiltonian cubic graph; `checks/tube_cyclic_cuts.py`). Each proof keeps an
  induction over about `log* r` scales, and the packing bound stays as the case of many short
  cycles. The note gives the reasons.
- *Open.* The lemma on pieces at girth five, for induced pieces of a graph without a cyclic cut
  of size at most four. With it, Section 7, Lemma 5.5 and Corollary 5.6 would not be necessary.
- *Status.* The new proofs are on paper only. There is no formal proof, and nobody else has read
  them. `research/apply_one_scale.py` and `research/apply_two_regions.py` apply a proof to a
  copy of the folder `exact-maximum/`; `research/trial-one-scale.pdf` and
  `research/trial-fixed-girth.pdf` are the two copies.

## 13. The second research task (12 November 2026): the case of bounded girth is not necessary

KNT asked: can Section 7 be removed by a stronger lemma on pieces? The result is in
`research/girth-five.pdf` (13 pages, with complete proofs). The manuscript is unchanged.

- *Audit.* Theorem 4.4 of the first note is correct. The induction step is written again with
  both regions and with each condition.
- *New theorem.* At girth five, a connected subcubic multigraph with at most `k` boundary
  vertices and at least `C_1 k^7` vertices has a forest proportion of less than 3/5 for every
  even set of boundary vertices. No hypothesis on cuts is necessary.
- *The proof.* Call a set of boundary vertices rigid if every join is a forest. (1) A connected
  subcubic multigraph of girth five with a full pair has fewer than `15 d` vertices, where `d` is
  its deficit: by Lemmas 5.2 and 5.8 it is a chain of capped ladders, and each cycle of length at
  most four of a ladder must contain a port. (2) A thin multigraph of girth five with a rigid set
  is small: a tree with the fewest edges that connects the terminals passes one time through a
  region far from the terminals; if both sides are even the region is a tree, and if both are
  odd it has a full pair. (3) A piece with forest proportion at least 3/5 is thin (the marker
  step), and a long thin piece has many stretches; none of them has a rigid set, so each loses a
  fixed factor. This gives the lemma for few boundary vertices, with a very large constant. The
  induction of Theorem 4.4 then gives the size `C_1 k^7`.
- *Consequence.* Theorem 8.1 holds for girth five. Theorem 7.1, Lemma 5.5 and Corollary 5.6 are
  used nowhere else, and the main theorem has four cases.
- *Measured.* Lean form (Lemma 8.2 stays; a second lemma for few boundary vertices): 1,617
  lines, 42 pages. Clean form (one lemma on pieces): 1,643 lines, 43 pages. Now: 1,624 lines,
  42 pages. So the removal of the case costs no length, and it does not make the paper shorter
  by much: the new statements have 87 lines, and Section 7 with its two dependencies has 90.
- *Tests.* `checks/girth5/`: forest proportions by complete enumeration in families of girth at
  least five (they decrease with the size; no rigid set above 30 vertices), a search for rigid
  sets (ladders at girth four, nothing large at girth five), and a check of the two cases of
  step (2) on 290 rigid sets.
- *Status.* On paper only. No formal proof; the Lean proof has the case of bounded girth.
  Nobody else has read the new proofs.

## 14. The third research task (12 November 2026): three cases

KNT asked: keep searching for more efficiencies. The result is in `research/fewer-cases.pdf`
(14 pages, with complete proofs). The manuscript is unchanged.

- *The gap theorem is a corollary.* The proof of Lemma 5.8 uses the full pair only to see that
  `J = N - V(A)` is a forest. So for a bridgeless 2-pole of rank at least two: full pair, `J` a
  forest, and capped ladder are equivalent. If `J` has a cycle and `P_st >= (3/4) 2^b`, Step 2 of
  the proof of Proposition 5.3 gives a cycle of `J` with at most `20 Theta` vertices, and
  Lemma 5.1 gives `P_st <= 2^b - 2^(b - 20 Theta)`. This removes Lemma 5.9 (four cases) and the
  induction of Theorem 5.10. Price: the gap is `gamma_0 = 2^(-20 Theta)` in the place of `1/16`,
  Section 6 has `eps_0 = gamma_0/20` in the place of `1/1000`, and the gap theorem now uses the
  forest estimate.
- *A cycle of length four.* With the last case in the form for girth five, a graph with a
  cyclic cut of size four and girth at least five belongs to the last case. So Theorem 6.8 is
  needed only when the graph has a cycle `C` of length four. With `Y = G - V(C)` of rank `k`:
  `c(G) 2^(-k) = 2^(-k) + z + (S + F - u_{12|34}) + (S + F - u_{14|23})`, and each bracket with
  `z` is at most `4 + eps_0` by the cap. No lemma on gluing, and no step for a second side.
- *Three cases.* A loop gives a cyclic cut of size one, so Case 1 is the case `d = 1` of
  Proposition 6.3.
- *One count.* `c(G) <= q(G,P) 2^r + 2^(r-1-p/2)` for a cubic multigraph without a bridge and a
  connected set `P` of `p` vertices. With `p = 8` it is the last case; with `p = 4 log r` and
  Theorem 3.1 it is Corollary 3.7. The edge recursion is not necessary. In lines this is
  neutral (Section 3 has 7 lines more, the final proof 9 lines less).
- *Measured.* Lean form of the second note with the four reductions: 1,587 lines, 41 pages,
  39 statements, three cases. With the clean form: 1,610 lines, 41 pages. Without the new gap
  theorem (`apply_fewer_cases.py <copy> keepgap`): 1,607 lines, 42 pages, 40 statements, three
  cases. Now: 1,624 lines, 42 pages, 40 statements, five cases.
- *Failed* (details in the note): no way to remove Proposition 6.3 (two capped ladders joined at
  their caps have more than `2^(r-1)` cycles, so the exponent `b/2` of Theorem 5.4 is needed); an
  induction on the rank has no start; (T1), (T2), (T3), the cap and the lemma on a full star are
  each necessary for the arithmetic (three explicit states); no elementary gap with a good
  constant; no polynomial bound for pieces at girth five without induction; no base without
  rigid sets; one lemma for the two marker steps saves no mathematics; nothing new for the chain
  and the packing bound.
- *Tests.* `checks/gap_and_square_check.py` (five tests, exit code 0): the ladder criterion on
  1,500 random 2-poles, the count for a cycle of length four and the cap identity
  `c(G) + c(Y) = 1 + c(cap 12|34) + c(cap 14|23)`, the count with a marked set, a local search
  for counterexamples to the arithmetic of the rigidity lemma, and the three states.
- *Status.* On paper only. No formal proof; the Lean proof has the gap `1/16` by induction, a
  cut of size four with two sides, and the edge recursion. Nobody else has read the new proofs.


## 15. Astra's notes (12 November 2026): audit and a combined copy

KNT gave me notes of Astra with eight proposals, written for the draft of 42 pages. The audit is
in `research/astra-audit.pdf`; the manuscript is unchanged.

- *Verdict.* All eight proposals are sound; I found no error. One step needs an exact reading:
  in the count of the cycles by their edges on a shortest path, "positions that cannot be
  consecutive" are the indices `i` for which the further edge of `w_(i-1)` points forward and
  that of `w_i` points backward (a property of the graph). Read as a property of the cycle the
  count would be false.
- *Same as my notes.* The marked set (note 3, reduction 4), the gap theorem as a corollary (note
  3, reduction 1; Astra bounds the short cycle by `4 Delta + 2`), the recursion `d -> log d`
  (note 1). Astra's notes do not mention my notes.
- *New, in the copy.* (1) Lemma on a shortest path `A` in a bridgeless 2-pole, `J = N - V(A)`,
  `Delta = b - l`, with no hypothesis on paths: `Delta <= beta(J)`; at most `2 Delta` layers are
  not thin and at most `4 Delta` vertices of `J` are outside thin layers; every cycle of `J` has
  at most `4 Delta + 2` vertices; `c(N) <= 10 * 2^(5 beta(J) + b/2)`. So Proposition 5.3 keeps
  one conclusion, and `K_eps = 20 * 2^(5 C_eps)`. (2) Rigidity by a limit: for a limit state
  with `S + F >= 4` only the cross and the star remain; the gadgets are stated for every margin.
  (3) Three full pairs at a port give a cyclic cut of size three (the first end piece of the
  capped ladder has no other port). (4) `W_2 <= 2 mu (e + N M)`. (5) Nesting in two cases; the
  window step with the threshold `m^(3/4)`.
- *With the cycle of length four.* One cap is sufficient, the bound for `z` is not used, and
  the lemma on a full star (6.7) is not necessary. Proposition 6.3 keeps the numbers of the
  manuscript, because the gap constant is used in the last step of the limit proof only.
- *Measured.* Copy `research/trial-combined.pdf` (`apply_girth_five.py <copy> lean`,
  `apply_fewer_cases.py <copy> keepgap`, `apply_combined.py <copy>`): 1,577 lines, 41 pages, 39
  statements, three cases. Against the copy of note 3 (1,587): Section 4 has 5 lines less,
  Section 5 has 1 less, Section 6 has 6 less, the last section 3 less, the introduction 5 more.
  Option `caps` (cuts of size two and three by caps, bound `2^(r-1) + 420 * 2^(r/2)`): 1,588
  lines. Option `blocks` (connected blocks): 1,578 lines. So these two are not in the main line.
- *Not built.* Astra's package on the manuscript with its Section 7 (without note 2). Proposals
  2, 3, 4, 7.2 do not depend on that choice; proposal 6 then needs its form with two sides.
- *Tests.* `checks/astra_audit_check.py`, six tests, exit code 0 (seeds 1 and 2).
- *Status.* On paper only. The Lean proof has other methods in these places: the edge
  recursion, matchings between ordinary layers, the gap `1/16` by induction, a cut of size four
  with two sides and fixed numbers, bounded girth and two girth scales.

## 16. Codified (12 November 2026)

KNT said: "Codify it. Also, your section 1.4 on authorship and the formal verification is WAY too
verbose. further you dont need to reference the other paper in section 3."

- The manuscript `exact-maximum/` now has the text of the combined copy (Section 15), written
  with the three scripts. Before that step the sources were identical to the draft of 42 pages,
  and after it they were identical to the proofread copy `research/trial-combined.pdf`.
- The draft of 42 pages is in `research/base-42-pages/` (sources and PDF). It was in no commit.
  The four notes and the scripts `research/apply_*.py` refer to it.
- `sections/girth.tex` (bounded girth) is removed from the manuscript; it is in the archive.
- Section 1.4: three short paragraphs, 16 typeset lines. It names the authors and their parts in
  four sentences, the formal statement `Erdos1016.ExactMaximum.exactMaximum` at the public commit
  `3a80aa9` with its axioms, and it says that the formal proof follows an earlier and longer form
  of the argument. The table of declarations and the list of differences are now in `README.md`.
- Section 3: the remark after Theorem 3.1 is "This paper uses the theorem only when `Gamma[P]`
  is connected. The proof is that of [KNT]." The reference to the second paper is removed. The
  statement of Theorem 3.1 is not changed, because the second paper cites it.
- Measured: 39 pages, 1,479 typeset lines, 39 numbered statements, three cases. Before the
  codification: 42 pages, 1,624 lines, 40 statements, five cases. The first text of
  11 November 2026 had 49 pages and 1,903 lines.
- The log has no overfull box and no undefined reference. All nine entries of the bibliography
  are cited.
- Not done: no commit, no formal proof of the new parts, no second reader for the lemmas at
  girth five.

## 17. The pass over the presentation (12 November 2026)

KNT said: "yes, also remove that reference to 8. We're mostly good on the shortening of the math.
now just do some checks over presentation. is a section too compressed? would it benefit from
splitting up/more exposition? is a figure here needed? is a figure here not needed? does this
sentence read well? etc.."

- The citation of the second paper in Section 1.4 and its entry in the bibliography are removed.
- I looked at every page (contact sheets) and read the whole text again. The list of changes is
  in `README.md`, section "The pass over the presentation".
- Findings that led to a change: Section 7.1 had five lemmas and a paragraph of eight definitions
  in a row; the three lemmas at girth five had no outline; the proofs of Lemma 7.5, Lemma 5.3(d),
  Lemma 5.9, Lemma 6.5, Case 1 of Theorem 6.6, Step 1 of Lemma 4.1, Step 2 of Proposition 3.5 and
  the count for rings describe a picture in words; Figure 3 and the figure of the chain used
  letters that the text does not use; one figure split a sentence over two pages; the heading of
  Section 7 was alone at the foot of a page; the constants of Section 6.2 were defined at the end
  of Section 5; "Theorem 3.1 through Corollary 3.8" read like a range; the number `e^124` had no
  reason in the present proof.
- Examined and left as it is: the diagram of the three cases (Figure 2) is small now, but it is
  the only place that shows the cases with their bounds at one look; Section 3 stays one section,
  because its two parts are the proof of one theorem; the proof of Proposition 6.3 keeps its
  decimal numbers; the statement boxes stay unbreakable (a broken box can lose its label).
- Measured: 42 pages, 1,586 typeset lines (figures count), 40 numbered statements, 16 figures.
  Before the pass: 39 pages, 1,479 lines, 39 statements, 8 figures. The log has no overfull box
  and no undefined reference; every figure is cited.
- A first form of `\needroom` (a stretch with a penalty) always broke the page, because the
  pages of this design have no stretch. The present form measures the room that is left.


## 18. Three papers (12 November 2026)

KNT said: "this is good." and then: "also from astra, and i agree - lets split this into three
papers, using their option B." Astra's plan: paper 1 is the forest estimate (the tools, the
cycles of moderate length, the proof, a short section on the two applications without their
proofs, its own introduction and the Lean statements); paper 2 is the pancyclic paper, which
cites paper 1 and loses its proof of the reduction; paper 3 is the maximum number of cycles,
which cites paper 1. Option B: the corollary `psi(r) ~ 2^(r-1)` stays in paper 3. Astra asked
that no application paper repeat the proof of the estimate.

- The single paper that KNT called good (42 pages) is in `research/single-paper-12-nov/`.
- Paper 1, `forest/forest.tex`: 13 pages, 10 numbered statements, 4 figures. Sections 2 to 4
  are the text of the single paper (Sections 2, 3.1, 3.2) with new numbers. Section 5 is the
  reduction from the pancyclic paper. New: Section 1 (the result with a figure, a ring that
  shows that `1/2` cannot be lowered, an outline, the place of each hypothesis, the two
  applications, authorship in three short paragraphs), an outline box in Section 3, a figure
  of the splitting step. Proposition 3.4 states its three conclusions as (i), (ii), (iii).
- Paper 3, `exact-maximum/`: 36 pages (it had 42), 37 numbered statements (40), 15 figures
  (16). Section 2 states the five results of paper 1 that the paper uses. Section 3 is the
  leading term. The packing proof in Section 7.4 now cites the link formula and the lemma on
  exceptional partners directly (it cited "the proof of Lemma 2.4"), and Section 7.5 cites the
  four parts of Proposition 2.5 (it cited the notation of Section 3.1 and equation (3.1)).
- Paper 2, `pancyclic/pancyclic.tex`: 7 pages (it had 8). Theorem 2.1 is quoted from paper 1,
  with five sentences on the method. The section on authorship has no table.
- No proof changed. All three logs: no overfull box, no undefined reference.
- Checked by reading: each number that one paper cites from another (Theorem 1.1, Corollary
  1.2, Lemmas 2.2 to 2.4 and Proposition 3.4 of paper 1) is the number in the built PDF.
- The fine print on the constant `1/2` is new mathematics of three lines: in a ring of `k`
  copies of `K_{2,2}` there are `2^(2k) = 2^(r-1)` cycles that go once around the ring, and each
  of them meets the four vertices of one copy.

- Later on 12 November 2026 KNT said: "the forest paper should not reference to either of the
  other two in any way." The subsection on the two applications, the sentence on companion
  papers in the lead, and the citations of the two papers are removed. I also removed the
  citation of the manuscript of September 2026, because its subject is the pancyclic problem;
  the section on authorship still says that KNT obtained the estimate in September 2026 with
  Astra. The bibliography has three entries. The paper has 12 pages, and the numbers of its
  statements did not change.

## 19. The Lean development and the present text (12 November 2026)

KNT said: "now work on fixing the lean formalization to match: and commit everything when done".

- New files, all without `sorry` and with the axioms `propext`, `Classical.choice`,
  `Quot.sound` only: `Erdos1016/ExactMaximum/ThreeCases.lean` (the three cases of the text as
  statements, and Section 8 as a theorem), `GirthFive.lean` (Lemma 3.2 of the text as
  `numCycles_le_marked`; Theorem 7.1 as the definition `GirthForestStatement 5`; Case 3 of
  Section 8 from it), `MainThreeCases.lean` (`exactMaximum_threeCases`, and
  `exactMaximumStatement_of_girthFiveForest`), and `audits/ExactMaximumThreeCasesAudit.lean`.
- The match is not complete. Case 3 of `exactMaximum_threeCases` uses the older route (a cyclic
  cut of size four, bounded girth, girth at least some `D >= 256`). Theorem 7.1 of the text at
  girth five, with Lemmas 7.4 to 7.6, has no formal proof. The audit shows in the proof terms
  that the proof from `GirthForestStatement 5` uses neither the case of bounded girth nor the
  case of large girth, so this one statement is what a formal proof along the text still
  needs.
- `Erdos1016/ExactMaximum/README.md`, section "The third proof", has the table of the text and
  the formal statements, with "same", "other" and "no formal proof" for each statement.
- The root file `Erdos1016.lean` imports the three new modules and four modules of Astra's
  folder `Shortening`, so that no module is outside the import closure
  (`scripts/project_inventory.py`: 672 modules, none outside).

## 20. Theorem 7.1 at girth five has a formal proof (12 November 2026, evening)

KNT said: "formalize 7.1 on girth. once done, upload and commit everything. try to reorganize
the lean files in github too to reflect what things are used where a bit more."

- `Erdos1016.ExactMaximum.girthForestStatement_five : GirthForestStatement 5` is proved
  (`Erdos1016/ExactMaximum/GirthFive/`, eleven files, about 3400 lines, no `sorry`, the axioms
  `propext`, `Classical.choice`, `Quot.sound` only). `exactMaximum_threeCases` now uses it, so
  the formal proof has the three cases of the text and nothing of the cases of bounded girth
  and of large girth. `audits/ExactMaximumThreeCasesAudit.lean` checks this in the proof terms.
- The formal proof of Lemma 7.6 (pieces at girth five) has a new inner step. The text shows
  with Lemmas 7.4 and 7.5 (full pairs, rigid sets, a tree through the set, capped ladders)
  that the region of a group of layers is not rigid. The formal proof takes slabs along a
  shortest path. A pigeonhole step gives a slab for which the word outside the slab can be
  chosen with zero or two terminals at the slab. With zero terminals a cycle of the slab is
  added. With two terminals the slab is small: the vertices outside a shortest path between
  the terminals form a forest, each of them has at most one neighbour on the path, and a path
  of seven such vertices would give seven positions `p_0, ..., p_6` with `p_k ≠ p_l`,
  `|p_k - p_l| ≤ (l - k) + 2` and `|p_k - p_{k+1}| ≥ 2`, which do not exist (the rail lemma).
  `Erdos1016/ExactMaximum/GirthFive/README.md` has the statements and the proofs.
- This step is new mathematics, and it is checked by the kernel. It may give a shorter text
  for Section 7.2 (no Lemma 7.4, no Lemma 7.5, no figure of the tree). I did not draft it and
  did not count lines. The manuscript is not changed, with one exception: the two paragraphs
  on the formal proof in Section 1.4 (the declaration `exactMaximum_threeCases`, the commit
  `b7f9fc9`, and one sentence on the steps that are not those of the text). The paper has 36
  pages as before.
- The end of the formal proof is not that of the text: it deletes short cyclic regions at the
  scales `D, 2D, 4D, ...` and uses Astra's last step for large girth. Only the bound for the
  first family is new (`GirthFive.exists_base_finset_packing`).
- The Lean files. Three entry modules, one for each text: `Erdos1016/ForestEstimate.lean`,
  `Erdos1016/Pancyclic.lean`, `Erdos1016/MaximumCycles.lean`. `audits/UsageMap.lean` computes,
  from the proof terms, which modules each endpoint theorem uses, and `Erdos1016/README.md`
  has the table by folder. No existing file was moved: Astra's files import most modules of
  `Erdos1016/ExactMaximum/`, and I do not edit Astra's files.

## 21. Pieces at girth five by slabs: draft and measurement (13 November 2026)

KNT clicked "Draft and measure" for the new inner step of the formal proof of Lemma 7.6.

- The note `research/slabs.pdf` (6 pages) has the text in two forms, with complete proofs, and
  `research/apply_slabs.py` applies a form to a copy of the paper.
- Measured (nonempty lines of `pdftotext -layout` without the running heads):

  | | Pages | Lines | Section 7 | Section 7.2 | Statements | Figures |
  |---|---|---|---|---|---|---|
  | The paper now | 36 | 1305 | 378 | 121 | 37 | 15 |
  | Form "slabs" | 36 | 1288 | 361 | 103 | 36 | 15 |
  | Form "slabs and rails" | 36 | 1308 | 377 | 120 | 36 | 15 |

- What I learned by the draft. The present proof of Lemma 7.5 (rigid sets) already ends with
  the two cases of the formal proof (a join outside `B` with a cycle of `B`; or a full pair in
  `B`). So the new step replaces only the way to find `B`: slabs across a shortest path and a
  count of side components, in the place of a smallest tree through the rigid set, its
  segments, a far point and an exchange step. This removes one lemma and 17 lines.
- The present Lemma 7.4 (full pairs at girth five) is the same statement as the formal lemma
  on two terminals, because an `{x,y}`-join that is a forest is a path. Its proof by ladders
  has 22 lines of TeX; the proof by a shortest path and seven integers has 36. So the second
  form is not shorter than the paper. Its gain is of another kind: Section 7 then refers to no
  statement of Sections 5 and 6, and Section 7.2 has the method of the formal proof.
- A human proof of the fact on seven integers is in the note: the steps are 2 or 3 in absolute
  value; two consecutive steps of the same sign are both 2 or both -2; alternating signs give
  a repeated position after five or six steps; a pair of equal steps forces its neighbours
  and gives a repeated position too. `checks/rail_check.py` enumerates all sequences (exit 0).
- In the text the count is a little stronger than in Lean: for some slab no vertex of `U` is
  in a side component at all (the formal proof asks only for an even number in each side
  component).
- My recommendation to KNT: the form "slabs" if the aim is fewer steps; the form "slabs and
  rails" if the aim is that the formal proof has the method of the text. The gain is small in
  both, and the manuscript is not changed.

## 22. The form "slabs" is in the paper (13 November 2026, 01:00 UTC)

KNT chose "Apply slabs". `research/apply_slabs.py` ran on `exact-maximum/`. The paper has 36
pages, 1288 typeset lines, 36 statements and 15 figures, and its text is equal to the text of
`research/trial-slabs.pdf` (compared with `pdftotext -layout`).

- Section 7.2 has two lemmas: 7.4 (full pairs at girth five, not changed) and 7.5 (pieces at
  girth five, with the steps "Slabs", "Side components" and "No rigid set"). The lemma on rigid
  sets and the figure of the tree are gone; Figure 14 shows the slabs. The statements after
  7.4 have a number that is smaller by one (7.5 to 7.11).
- Section 1.4 says: "Lemma 7.4 has a proof without ladders" in the place of "Lemma 7.6 has a
  proof without rigid sets". The cited commit `b7f9fc9` is the same; no Lean file changed.
- The tables text-to-Lean in `Erdos1016/ExactMaximum/README.md` and in
  `Erdos1016/ExactMaximum/GirthFive/README.md` have the new numbers. Lemma 7.5 is now "same";
  Lemma 7.4 is "other".
- Not done: the form "slabs and rails" (the proof of Lemma 7.4 by a shortest path). It stays in
  the note `research/slabs.pdf` and in the copy `research/trial-slabs-rails.pdf`.
