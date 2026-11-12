import Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker
import Erdos1016.ExactMaximumSupport.LargeGirth.ForestProbability
import Erdos1016.ExactMaximumSupport.LargeGirth.LargeGirthCycleCounting
import Erdos1016.ExactMaximumSupport.LargeGirth.MarkerRankLoss
import Erdos1016.ExactMaximum.Cases

set_option autoImplicit false

/-!
# The large-girth case from eight connected vertices

The fixed marker replaces the shortest cycle in the manuscript's final case.
The ambient hypothesis only rules out cuts of size zero or one.
The checked forest theorem and the cubic rank ledger give the explicit bound.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth
open FiniteMultiGraph LargeGirth

/-- Large loopless cubic graphs with no bridge satisfy the explicit fixed-marker bound. -/
theorem exists_bound :
    ∃ D R : ℕ, 256≤D ∧ ∀ G : FiniteMultiGraph,
      G.toSimpleGraph.Connected → (∀v,G.degree v=3) → G.IsLoopless →
      (∀ U : Finset G.Vertex,U.Nonempty → U≠Finset.univ →
        2≤(G.cutEdges U).card) →
      R≤G.cycleRank → ¬G.HasCycleShorterThan D →
      (G.numCycles : ℝ)<(69/160 : ℝ)*2^G.cycleRank := by
  obtain ⟨D,R,hD,hforest⟩ := ForestProbability.exists_cutoff
  refine ⟨D,max R 8,hD,?_⟩
  intro G hG hcubic hloop hcuts hr hshort
  have hrR : R≤G.cycleRank := (le_max_left R 8).trans hr
  have hr8 : 8≤G.cycleRank := (le_max_right R 8).trans hr
  obtain ⟨P,hP,hconn⟩ := ConnectedMarker.exists_eight G hG hcubic (by omega)
  have hsize : (P.card : ℝ)≤3*Real.logb 2 (G.cycleRank : ℝ) := by
    rw [hP]
    exact ConnectedMarker.eight_le_log_budget G.cycleRank hr8
  have hq := hforest G P hG hcubic hrR hconn hsize
    (CycleCounting.induced_no_short G Pᶜ D (by omega) hshort)
  have hloss := MarkerRankLoss.eight_vertex_rank_loss_of_cut_bound
    G P hG hcubic hP hcuts
  have hc := CycleCounting.numCycles_le_probability_add_internal G hloop Pᶜ
  have hp : (2 : ℝ)^(PieceCore.Induced.graph G Pᶜ).cycleRank*32≤
      (2 : ℝ)^G.cycleRank := by
    calc
      _=(2 : ℝ)^((PieceCore.Induced.graph G Pᶜ).cycleRank+5) := by
        rw [pow_add]
        norm_num
      _≤_ := pow_le_pow_right₀ (by norm_num) hloss
  have hstrict := mul_lt_mul_of_pos_right hq
    (by positivity : (0 : ℝ)<2^G.cycleRank)
  nlinarith

/-- The fixed marker supplies the original large-girth interface directly. -/
theorem largeGirthStatement : ExactMaximum.LargeGirthStatement := by
  obtain ⟨D,R,hD,hbound⟩ := exists_bound
  refine ⟨D,max R 1,?_⟩
  intro G hG hcubic hloop hr hnocut hshort
  have hrR : R≤G.cycleRank := (le_max_left R 1).trans hr
  have hr1 : 1≤G.cycleRank := (le_max_right R 1).trans hr
  have hcuts : ∀U : Finset G.Vertex,U.Nonempty → U≠Finset.univ →
      2≤(G.cutEdges U).card := by
    intro U hne hproper
    exact le_trans (by decide : 2≤3)
      (MarkerRankLoss.cut_card_ge_three G hloop hcubic hnocut U hne hproper)
  have hb := hbound G hG hcubic (G.isLoopless_iff_not_hasLoop.mpr hloop)
    hcuts hrR hshort
  have he : (2 : ℝ)^G.cycleRank=2*(2 : ℝ)^(G.cycleRank-1) := by
    conv_lhs => rw [show G.cycleRank=(G.cycleRank-1)+1 by omega]
    rw [pow_succ]
    ring
  have hp : (0 : ℝ)<2^G.cycleRank := by positivity
  have hlt : (G.numCycles : ℝ)<(2 : ℝ)^(G.cycleRank-1) := by nlinarith
  exact_mod_cast hlt

end Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth
