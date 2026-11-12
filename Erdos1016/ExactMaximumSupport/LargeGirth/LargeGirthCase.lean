import Erdos1016.ExactMaximum.Cases
import Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker
import Erdos1016.ExactMaximumSupport.LargeGirth.LargeGirthCycleCounting
import Erdos1016.ExactMaximumSupport.LargeGirth.MarkerRankLoss

set_option autoImplicit false

/-!
# The conditional large-girth counting case

This bridge assumes the actual uniform marked-forest theorem.
It then proves the large-girth statement used by the five-case reduction.
The eight-vertex marker avoids a separate shortest-cycle construction.
The forest theorem is an explicit hypothesis of the public implication.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.LargeGirth.LargeGirthCase
open FiniteMultiGraph

/-- The actual forest theorem needed by this counting bridge. -/
def ForestBoundStatement : Prop :=
  ∃ D R : ℕ, 256 ≤ D ∧ ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex),
    G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) → R ≤ G.cycleRank →
    (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
    (P.card : ℝ) ≤ 3 * Real.logb 2 (G.cycleRank : ℝ) →
    ¬ (PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D →
    G.regionForestProbability Pᶜ < (2 / 5 : ℝ)

/-- Case 5 follows from the marked-forest theorem on the original uniform cycle space. -/
theorem largeGirthStatement_of_forest_bound (hforest : ForestBoundStatement) :
    ExactMaximum.LargeGirthStatement := by
  obtain ⟨D, R, hD, hforest⟩ := hforest
  refine ⟨D, max R 8, ?_⟩
  intro G hG hcub hloop hr hnocut hshort
  have hrR : R ≤ G.cycleRank := (le_max_left R 8).trans hr
  have hr8 : 8 ≤ G.cycleRank := (le_max_right R 8).trans hr
  obtain ⟨P, hP, hconnP⟩ := ConnectedMarker.exists_eight G hG hcub (by omega)
  have hsize : (P.card : ℝ) ≤ 3 * Real.logb 2 (G.cycleRank : ℝ) := by
    rw [hP]
    exact ConnectedMarker.eight_le_log_budget G.cycleRank hr8
  have houtside := CycleCounting.induced_no_short G Pᶜ D (by omega) hshort
  have hq := hforest G P hG hcub hrR hconnP hsize houtside
  have hloss := MarkerRankLoss.eight_vertex_rank_loss G P hG hcub hloop hnocut hP
  exact CycleCounting.numCycles_lt_half_of_forest_rank_loss G
    (G.isLoopless_iff_not_hasLoop.mpr hloop) Pᶜ hq (by omega)

end Erdos1016.ExactMaximumSupport.LargeGirth.LargeGirthCase
