import Erdos1016.Probability.Moments.SmallCutRegionBound

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph

/-- The contrapositive form of the small-cut bound counts any disjoint
cyclic regions when the ambient forest probability exceeds one half. -/
theorem smallCut_packing_card_le (G : FiniteMultiGraph)
    {ι : Type*} [Fintype ι] (U : ι → Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (s : Finset ι) (d : ℕ)
    (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ d)
    (hcyclic : ∀ i ∈ s, ∃ z : G.internalCycleSpace (U i), z ≠ 0)
    (E : Finset G.Edge) (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E)
    (ε : ℝ) (hε : 0 < ε)
    (hforest : (1 / 2 : ℝ) + ε <
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1))) :
    (s.card : ℝ) ≤ ((d : ℝ) + 1) * (2 : ℝ) ^ d / (2 * ε) := by
  classical
  by_cases hs : s.Nonempty
  · have h := G.smallCut_forest_bound U hG hdisj hconn s hs d hcut hcyclic E hE
    have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
    have hratio : ε < ((d : ℝ) + 1) * (2 : ℝ) ^ d / (2 * s.card) := by linarith
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < 2 * s.card by positivity)).mp hratio
    apply (le_div_iff₀ (show 0 < 2 * ε by positivity)).mpr
    nlinarith only [hmul]
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos1016.FiniteMultiGraph
