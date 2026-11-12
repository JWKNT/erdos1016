import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct
import Erdos1016.ExactMaximumSupport.LargeGirth.PieceExtraction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Two pieces with small physical boundaries

The pieces are actual vertex subsets of the ambient cubic multigraph.
Core extraction supplies the induced poles; no pole model is assumed.
The large-order case permits disconnected pieces and uses an actual component.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.SmallBoundaryPieces
open FiniteMultiGraph PieceCore PieceCore.Induced

local instance pieceProductDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The two-piece form of the small-boundary proposition. The logarithmic
scale parameter may be real, as in the paper. -/
theorem exists_constants :
    ∃ D : ℕ, ∃ C : ℝ, 256 ≤ D ∧ 0 < C ∧
    ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex) (X : Fin 2 → Finset G.Vertex)
      (g : Fin 2 → ℕ), G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      Disjoint (X 0) (X 1) → (∀ i, X i ⊆ Pᶜ) →
      (∀ i, ¬ (graph G (X i)).HasCycleShorterThan (g i)) →
      (∀ i,
        ((G.toSimpleGraph.induce (↑(X i) : Set G.Vertex)).Connected ∧
          256 ≤ (graph G (X i)).cycleRank ∧ (G.cutEdges (X i)).card ≤ 4*g i ∧ D ≤ g i) ∨
        ∃ l : ℝ, 4 ≤ l ∧ 8*l^2 ≤ ((X i).card : ℝ) ∧ ((G.cutEdges (X i)).card : ℝ) ≤ 2*l ∧
          C*Real.logb 2 (l+2) ≤ g i) →
      G.regionForestProbability Pᶜ ≤ 9/25 ∧ G.regionForestProbability Pᶜ < 2/5 := by
  classical
  obtain ⟨D, C, hD, hC, hproduct⟩ := PoleProduct.exists_two_pole_constants
  refine ⟨D, C+256, hD, by positivity, ?_⟩
  intro G P X g hG hcubic hdisj hXP hshort hcase
  have hcores (i : Fin 2) : ∃ U : Finset G.Vertex, U ⊆ X i ∧
      (graph G U).toSimpleGraph.Connected ∧ (∀ v, 2 ≤ (graph G U).degree v) ∧
      ¬ (graph G U).HasCycleShorterThan (g i) ∧
      ((256 ≤ (graph G U).cycleRank ∧ (graph G U).cubicDeficit ≤ 4*g i ∧ D ≤ g i) ∨
       ∃ l : ℝ, 4 ≤ l ∧ l ≤ (graph G U).cycleRank ∧
         ((graph G U).cubicDeficit : ℝ) ≤ 2*l ∧ C*Real.logb 2 (l+2) ≤ g i) := by
    rcases hcase i with ⟨hconn, hr, hk, hg⟩ | ⟨l, hl, hn, hk, hg⟩
    · obtain ⟨U, hUX, hconnU, hrU, hdU, hgU, hkU⟩ := exists_induced_core G (X i) hconn
        (fun v _ => hcubic v) (by omega) (g i) (by omega) (hshort i)
      exact ⟨U, hUX, hconnU, fun v => (hdU v).1, hgU,
        Or.inl ⟨by omega, hkU.trans hk, hg⟩⟩
    · have hlog : 1 ≤ Real.logb 2 (l+2) := by
        have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
          (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤l+2)
        simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using hh
      have hg3 : 3 ≤ g i := by
        have hh : (256:ℝ) ≤ (g i:ℝ) := by nlinarith
        exact_mod_cast (show (3:ℝ)≤(g i:ℝ) by linarith)
      have hgC : C*Real.logb 2 (l+2) ≤ g i := by nlinarith
      obtain ⟨U, hUX, hconnU, hrU, hdU, hgU, hkU⟩ :=
        PieceExtraction.exists_induced_core_real G (X i) hG (fun v _ => hcubic v)
          l hl hn hk (g i) hg3 (hshort i)
      exact ⟨U, hUX, hconnU, fun v => (hdU v).1, hgU,
        Or.inr ⟨l, hl, hrU, hkU, hgC⟩⟩
  choose U hUX hconnU hminU hshortU hregime using hcores
  apply hproduct G P U g (fun v => (hcubic v).le) ?_
    (fun i => (hUX i).trans (hXP i)) hconnU hminU hshortU hregime
  exact Finset.disjoint_left.mpr (fun v hv0 hv1 =>
    (Finset.disjoint_left.mp hdisj) (hUX 0 hv0) (hUX 1 hv1))

end Erdos1016.ExactMaximumSupport.LargeGirth.SmallBoundaryPieces
