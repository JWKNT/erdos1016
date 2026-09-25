import Erdos1016.Probability.Avoidance.RegionPackingBound
import Erdos1016.Cycles.Geometry.ExteriorLinkClassification
import Erdos1016.Cycles.Selection.ShortRegionObstructions

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.ExteriorComponents

local instance exteriorCyclicDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Actual small cyclic exterior components form a disjoint family outside
the marked set, so their number follows directly from the small-cut bound. -/
theorem smallCyclicPart_card_le (G : FiniteMultiGraph) (U P : Finset G.Vertex)
    (t : ℕ) (S : Finset (Component G U)) (hG : G.toSimpleGraph.Connected)
    (ε : ℝ) (hε : 0 < ε)
    (hforest : (1 / 2 : ℝ) + ε < G.regionForestProbability Pᶜ) :
    ((smallCyclicPart G U P t S).card : ℝ) ≤
      ((t : ℝ) + 1) * (2 : ℝ) ^ t / (2 * ε) := by
  rw [G.regionForestProbability_eq_density] at hforest
  apply G.smallCut_packing_card_le (vertices G U) hG (vertices_disjoint G U)
    (vertices_connected G U) (smallCyclicPart G U P t S) t
    (E := G.internalEdges Pᶜ) (ε := ε)
  · intro c hc
    exact (Finset.mem_filter.mp hc).2.2.1
  · intro c hc
    exact G.internalCycleSpace_nontrivial_of_not_forest _ (Finset.mem_filter.mp hc).2.2.2
  · intro c hc e he
    have hP := (Finset.mem_filter.mp hc).2.1
    have hends := (Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_compl.mpr ?_, Finset.mem_compl.mpr ?_⟩
    · exact fun hs => hP ⟨G.src e, hs, hends.1⟩
    · exact fun ht => hP ⟨G.dst e, ht, hends.2⟩
  · exact hε
  · exact hforest

end Erdos1016.FiniteMultiGraph.ExteriorComponents
