import Erdos1016.Nonbacktracking.Walks.CycleWords
import Erdos1016.Decomposition.TwoCore.MaximalCore

set_option autoImplicit false
noncomputable section
namespace Erdos1016.Proof.CoreCycleSpace
open Nonbacktracking Nonbacktracking.FiniteTwoCore BoundaryDecay
local instance evenSupportDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The vertices used by an even word have minimum degree two in the
ambient induced graph. This includes disconnected words. -/
theorem usedVertices_minTwo (G : PhysicalGraph) (x : G.CycleSpace) :
    MinTwo G.toSimpleGraph (G.usedVertices x.1) := by
  intro v hv
  have hpos : 0 < G.selectedDegree x.1 v := by
    apply Finset.card_pos.mpr
    obtain ⟨e, he, hi⟩ := (mem_usedVertices x.1 _).mp hv
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hi⟩⟩
  have heven : 2 ∣ G.selectedDegree x.1 v := by
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [← boundary_eq_selectedDegree_cast]
    exact congrFun x.2 v
  have htwo : 2 ≤ G.selectedDegree x.1 v := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hsub : (G.selectedGraph x.1).neighborSet v ⊆
      (↑((G.usedVertices x.1).filter fun w => G.toSimpleGraph.Adj v w) : Set G.Vertex) := by
    intro w hw
    obtain ⟨e, he, hends⟩ := hw
    have hwused : w ∈ G.usedVertices x.1 := by
      apply (mem_usedVertices x.1 _).mpr
      refine ⟨e, he, ?_⟩
      rcases hends with h | h
      · exact Or.inr h.2
      · exact Or.inl h.1
    exact Finset.mem_filter.mpr ⟨hwused, ⟨e, one_ne_zero, hends⟩⟩
  have hcount := Set.ncard_le_ncard hsub
  rw [← selectedDegree_eq_neighbor_ncard, Set.ncard_coe_Finset] at hcount
  exact htwo.trans hcount

/-- Every even word is supported on the full two-core. -/
theorem usedVertices_subset_core (G : PhysicalGraph) (x : G.CycleSpace) :
    G.usedVertices x.1 ⊆ vertices G.toSimpleGraph Finset.univ :=
  maximal G.toSimpleGraph Finset.univ _ (Finset.subset_univ _) (usedVertices_minTwo G x)

end Erdos1016.Proof.CoreCycleSpace
