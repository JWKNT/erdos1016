import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct
import Erdos1016.ExactMaximumSupport.LargeGirth.PieceExtraction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Large pieces with small physical boundaries

Only the logarithmic, large-order regime is used. The local affine estimate
comes directly from the logarithmic Moore/ball budgets; it does not invoke
the older fixed-rank regime. Actual induced-core extraction and the internal
affine product law then give the two-piece forest bound.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.LargeOrderPieces
open FiniteMultiGraph LargeGirth LargeGirth.PieceCore
open Probability.PoleMarker

/-- The integer logarithmic regime, proved without the fixed-rank regime. -/
theorem exists_affine_integer_constant :
    ∃ C : ℕ, 64 ≤ C ∧
    ∀ (M : FiniteMultiGraph) (g l : ℕ), M.toSimpleGraph.Connected →
      (∀ v, 2 ≤ M.degree v) → (∀ v, M.degree v ≤ 3) →
      ¬ M.HasCycleShorterThan g → 4 ≤ l → l ≤ M.cycleRank →
      M.cubicDeficit ≤ 2*l → C*Nat.clog 2 (l+2) ≤ g →
      ∀ b : M.Demand, (∀ v, M.degree v = 3 → b v = 0) →
        affineForestProbability M b ≤ 3/5 := by
  obtain ⟨B, hB⟩ := exists_supported_demand_layer_bound
  obtain ⟨C, hC, hbudget⟩ := MooreGrowth.exists_logarithmic_budget B
  refine ⟨C, hC, ?_⟩
  intro M g l hconn hmin hmax hshort hl hlr hk hg b hb
  have hbud := hbudget g M.cubicDeficit l hl hk hg
  have hr : 4 ≤ M.cycleRank := hl.trans hlr
  have hg3 : 3 ≤ g := by omega
  have hm := multigraph_weighted_moore_integer M g hconn hmin hmax
    (by omega) hg3 hshort
  rw [AffinePole.edgeCount_eq M hconn hmax (by omega)] at hm
  have hlog := MooreGrowth.girth_lt_eight_clog_of_rank M.cycleRank M.cubicDeficit g hr
    (hk.trans (Nat.mul_le_mul_left 2 hlr)) hm
  exact (AffinePole.bound_of_budgets M B hB g hconn hmin hmax (by omega) hg3 hshort hlog
    hbud.2.1 hbud.2.2 b hb).le

/-- The large-order affine estimate with the paper's real scale parameter. -/
theorem exists_affine_constant :
    ∃ C : ℝ, 3 ≤ C ∧
    ∀ (M : FiniteMultiGraph) (g : ℕ) (l : ℝ), M.toSimpleGraph.Connected →
      (∀ v, 2 ≤ M.degree v) → (∀ v, M.degree v ≤ 3) →
      ¬ M.HasCycleShorterThan g → 4 ≤ l → l ≤ M.cycleRank →
      (M.cubicDeficit : ℝ) ≤ 2*l → C*Real.logb 2 (l+2) ≤ g →
      ∀ b : M.Demand, (∀ v, M.degree v = 3 → b v = 0) →
        affineForestProbability M b ≤ 3/5 := by
  obtain ⟨C, hC, hbound⟩ := exists_affine_integer_constant
  refine ⟨4*C, ?_, ?_⟩
  · have hc : (64 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  intro M g l hconn hmin hmax hshort hl hlr hk hg b hb
  apply hbound M g ⌈l⌉₊ hconn hmin hmax hshort ?_ ?_ ?_ ?_ b hb
  · have hh := Nat.le_ceil l
    exact_mod_cast (show (4 : ℝ) ≤ (⌈l⌉₊ : ℝ) by linarith)
  · exact Nat.ceil_le.mpr hlr
  · have hh := Nat.le_ceil l
    exact_mod_cast (show (M.cubicDeficit : ℝ) ≤ 2*(⌈l⌉₊ : ℝ) by linarith)
  · have hh := mul_le_mul_of_nonneg_left (AffinePole.ceil_clog_le_four_logb l hl)
      (by positivity : (0 : ℝ) ≤ C)
    have hlast : (C : ℝ)*(Nat.clog 2 (⌈l⌉₊+2) : ℝ) ≤ (g : ℝ) := by nlinarith
    exact_mod_cast hlast

/-- Two actual large regions with small boundaries force forest probability
at most nine twenty-fifths. The regions may be disconnected. -/
theorem exists_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex) (X : Fin 2 → Finset G.Vertex)
      (g : Fin 2 → ℕ), G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      Disjoint (X 0) (X 1) → (∀ i, X i ⊆ Pᶜ) →
      (∀ i, ¬ (Induced.graph G (X i)).HasCycleShorterThan (g i)) →
      (∀ i, ∃ l : ℝ, 4 ≤ l ∧ 8*l^2 ≤ ((X i).card : ℝ) ∧
        ((G.cutEdges (X i)).card : ℝ) ≤ 2*l ∧ C*Real.logb 2 (l+2) ≤ g i) →
      G.regionForestProbability Pᶜ ≤ 9/25 ∧ G.regionForestProbability Pᶜ < 2/5 := by
  classical
  obtain ⟨C, hC, hAffine⟩ := exists_affine_constant
  refine ⟨C, by linarith, ?_⟩
  intro G P X g hG hcubic hdisj hXP hshort hcase
  choose l hl hsize hcut hlog using hcase
  have hcores (i : Fin 2) : ∃ U : Finset G.Vertex, U ⊆ X i ∧
      (Induced.graph G U).toSimpleGraph.Connected ∧
      l i ≤ ((Induced.graph G U).cycleRank : ℝ) ∧
      (∀ v, 2 ≤ (Induced.graph G U).degree v ∧ (Induced.graph G U).degree v ≤ 3) ∧
      ¬ (Induced.graph G U).HasCycleShorterThan (g i) ∧
      ((Induced.graph G U).cubicDeficit : ℝ) ≤ 2*l i := by
    have hlogone : 1 ≤ Real.logb 2 (l i+2) := by
      have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
        (by norm_num : (0 : ℝ)<2) (by linarith [hl i] : (2 : ℝ)≤l i+2)
      simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
    have hg3 : 3 ≤ g i := by
      have hh := hlog i
      exact_mod_cast (show (3 : ℝ) ≤ (g i : ℝ) by nlinarith)
    exact PieceExtraction.exists_induced_core_real G (X i) hG (fun v _ => hcubic v)
      (l i) (hl i) (hsize i) (hcut i) (g i) hg3 (hshort i)
  choose U hUX hconnU hrU hdU hgU hkU using hcores
  have hlocal (i : Fin 2) : ∀ b : (Induced.graph G (U i)).Demand,
      (∀ v, (Induced.graph G (U i)).degree v = 3 → b v = 0) →
      affineForestProbability (Induced.graph G (U i)) b ≤ (3/5 : ℝ) :=
    hAffine (Induced.graph G (U i)) (g i) (l i) (hconnU i)
      (fun v => (hdU i v).1) (fun v => (hdU i v).2) (hgU i) (hl i) (hrU i) (hkU i) (hlog i)
  apply PoleProduct.region_product G (fun v => (hcubic v).le) P (U 0) (U 1) ?_
    ((hUX 0).trans (hXP 0)) ((hUX 1).trans (hXP 1)) (hlocal 0) (hlocal 1)
  exact Finset.disjoint_left.mpr (fun v hv0 hv1 =>
    Finset.disjoint_left.mp hdisj (hUX 0 hv0) (hUX 1 hv1))

end Erdos1016.ExactMaximumSupport.Shortening.LargeOrderPieces
