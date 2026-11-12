import Erdos1016.ExactMaximum.ThreeCases
import Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker
import Erdos1016.ExactMaximumSupport.LargeGirth.LargeGirthCycleCounting
import Erdos1016.ExactMaximumSupport.LargeGirth.MarkerRankLoss

set_option autoImplicit false

/-!
# The last case of the text: girth at least five

Case 3 in Section 8 of the paper "The maximum number of cycles in a graph of large rank" (draft
of 12 November 2026) has two inputs.

* **Theorem 7.1 of the text.** Let `G` be a connected cubic multigraph of large rank `r`, and let
  `P` be a nonempty set of at most `3 log r` vertices such that `G[P]` is connected. If `G - P`
  has girth at least five, then `q(G,P) < 2/5`. Here `q(G,P)` is the probability that the edges
  of a uniformly random even subgraph without an end in `P` form a forest.
* **Lemma 3.2 of the text (cycles and a marked set).** If `G` has no bridge, then
  `c(G) ≤ q(G,P) 2^r + 2^(r - 1 - |P|/2)`.

This file has:

* `GirthForestStatement D`: the statement of Theorem 7.1 with "girth at least `D`" in the place
  of "girth at least five". It is a definition. **`GirthForestStatement 5`, which is Theorem 7.1
  of the text, has no formal proof.** The formal development proves `GirthForestStatement D` for
  some `D ≥ 256` (`exists_girthForestStatement` in `MainThreeCases.lean`).
* `numCycles_le_marked`: Lemma 3.2 of the text, with `⌈|P|/2⌉` in the exponent.
* `three_le_cut_of_no_cyclic_cut`: without a cyclic cut of size at most three, every cut has at
  least three edges. The text needs only that there is no bridge.
* `girthCaseStatement_of_forest`: Case 3 of Section 8, by the method of the text. A connected
  set of eight vertices is marked, and `2/5 + 1/32 < 1/2`.
-/

noncomputable section

namespace Erdos1016.ExactMaximum
open FiniteMultiGraph ExactMaximumSupport.LargeGirth

/-- **Theorem 7.1 of the text, for girth at least `D`.** There is `R` such that, for a connected
cubic multigraph `G` of rank `r ≥ R` and a set `P` of at most `3 log r` vertices such that `G[P]`
is connected: if `G - P` has no cycle of length less than `D`, then `q(G,P) < 2/5`. -/
def GirthForestStatement (D : ℕ) : Prop :=
  ∃ R : ℕ, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex),
    G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) → R ≤ G.cycleRank →
    (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
    (P.card : ℝ) ≤ 3 * Real.logb 2 (G.cycleRank : ℝ) →
    ¬ (PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D →
    G.regionForestProbability Pᶜ < 2 / 5

/-- A larger girth is a stronger hypothesis. -/
theorem GirthForestStatement.mono {D D' : ℕ} (h : GirthForestStatement D) (hD : D ≤ D') :
    GirthForestStatement D' := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun G P hG hcubic hr hP hsize hshort => hR G P hG hcubic hr hP hsize ?_⟩
  rintro ⟨x, hx, hlen⟩
  exact hshort ⟨x, hx, lt_of_lt_of_le hlen hD⟩

/-- **Lemma 3.2 of the text (cycles and a marked set).** Let `G` be a connected cubic multigraph
without loops in which every cut has at least two edges, and let `P` be a nonempty set of `p`
vertices. Then `c(G) ≤ q(G,P) 2^r + 2^(r - 1 - ⌈p/2⌉)`. The text also supposes that `G[P]` is
connected and that `P` is not the set of all vertices; the proof does not need this. -/
theorem numCycles_le_marked (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hcubic : ∀ v, G.degree v = 3) (hloop : G.IsLoopless)
    (hP : P.Nonempty)
    (hcuts : ∀ U : Finset G.Vertex, U.Nonempty → U ≠ Finset.univ → 2 ≤ (G.cutEdges U).card) :
    (G.numCycles : ℝ) ≤ G.regionForestProbability Pᶜ * (2 : ℝ) ^ G.cycleRank +
      (2 : ℝ) ^ (G.cycleRank - 1 - (P.card + 1) / 2) := by
  have hloss := MarkerRankLoss.twice_exterior_rank_add_card_le G P hG hcubic hP hcuts
  have hc := CycleCounting.numCycles_le_probability_add_internal G hloop Pᶜ
  have hle : (PieceCore.Induced.graph G Pᶜ).cycleRank ≤
      G.cycleRank - 1 - (P.card + 1) / 2 := by omega
  have hpow : (2 : ℝ) ^ (PieceCore.Induced.graph G Pᶜ).cycleRank ≤
      (2 : ℝ) ^ (G.cycleRank - 1 - (P.card + 1) / 2) :=
    pow_le_pow_right₀ (by norm_num) hle
  linarith

/-- In a cubic multigraph without loops, a cut with at most two edges is cyclic. So without a
cyclic cut of size at most three, every cut has at least three edges. -/
theorem three_le_cut_of_no_cyclic_cut (G : FiniteMultiGraph) (hloop : ¬ G.HasLoop)
    (hcubic : ∀ v, G.degree v = 3) (hnocut : ¬ G.HasCyclicCutLE 3)
    (U : Finset G.Vertex) (hne : U.Nonempty) (hproper : U ≠ Finset.univ) :
    3 ≤ (G.cutEdges U).card := by
  by_contra hn
  have hcyc := MarkerRankLoss.cyclic_of_cut_card_le_two G
    (G.isLoopless_iff_not_hasLoop.mpr hloop) hcubic U hne hproper (by omega)
  exact hnocut ⟨U, hcyc, by omega⟩

/-- **Case 3 of Section 8, by the method of the text.** If the forest bound `q(G,P) < 2/5` holds
at girth `D ≥ 3`, then a connected cubic multigraph of large rank `r`, without a loop, without a
cyclic cut of size at most three and without a cycle of length less than `D`, has fewer than
`2^(r-1)` cycles. A connected set `P` of eight vertices is marked. By Lemma 3.2 the number of
cycles is less than `(2/5) 2^r + 2^(r-5)`. -/
theorem girthCaseStatement_of_forest {D : ℕ} (hD : 3 ≤ D) (h : GirthForestStatement D) :
    GirthCaseStatement D := by
  obtain ⟨R, hforest⟩ := h
  refine ⟨max R 8, fun G hG hcubic hloop hr hnocut hshort => ?_⟩
  have hrR : R ≤ G.cycleRank := (le_max_left R 8).trans hr
  have hr8 : 8 ≤ G.cycleRank := (le_max_right R 8).trans hr
  have hcuts : ∀ U : Finset G.Vertex, U.Nonempty → U ≠ Finset.univ →
      2 ≤ (G.cutEdges U).card := fun U hne hproper =>
    le_trans (by decide : 2 ≤ 3) (three_le_cut_of_no_cyclic_cut G hloop hcubic hnocut U hne hproper)
  obtain ⟨P, hP, hconn⟩ := ConnectedMarker.exists_eight G hG hcubic (by omega)
  have hsize : (P.card : ℝ) ≤ 3 * Real.logb 2 (G.cycleRank : ℝ) := by
    rw [hP]
    exact ConnectedMarker.eight_le_log_budget G.cycleRank hr8
  have hq := hforest G P hG hcubic hrR hconn hsize
    (CycleCounting.induced_no_short G Pᶜ D hD hshort)
  have hc := numCycles_le_marked G P hG hcubic (G.isLoopless_iff_not_hasLoop.mpr hloop)
    (Finset.card_pos.mp (by omega)) hcuts
  have hexp : G.cycleRank - 1 - (P.card + 1) / 2 = G.cycleRank - 5 := by omega
  rw [hexp] at hc
  have hp32 : (2 : ℝ) ^ (G.cycleRank - 5) * 32 = (2 : ℝ) ^ G.cycleRank := by
    conv_rhs => rw [show G.cycleRank = (G.cycleRank - 5) + 5 by omega]
    rw [pow_add]
    norm_num
  have hhalf : (2 : ℝ) ^ G.cycleRank = 2 * (2 : ℝ) ^ (G.cycleRank - 1) := by
    conv_lhs => rw [show G.cycleRank = (G.cycleRank - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hpos : (0 : ℝ) < 2 ^ G.cycleRank := by positivity
  have hstrict := mul_lt_mul_of_pos_right hq hpos
  have hlt : (G.numCycles : ℝ) < (2 : ℝ) ^ (G.cycleRank - 1) := by linarith
  exact_mod_cast hlt

end Erdos1016.ExactMaximum
