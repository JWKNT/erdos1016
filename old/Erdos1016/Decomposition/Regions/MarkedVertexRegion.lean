import Erdos1016.Decomposition.TwoCore.NormalizedExtraction

set_option autoImplicit false

/-!
# The starting region and the marked-vertex safe-core theorem

A largest component after deleting the marked vertex has at least (N-1)/3
vertices, cut at most three, and connected ORIGINAL exterior. This proves the
starting-region hypotheses rather than adding them to the theorem signature.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos1016.SafeCore
local instance instSafeCoreMarkedVertexPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)







/-- No component boundary has unpaid contacts to a different component. -/
theorem component_cut_le_removed_cut {R C : Finset G.Vertex}
    (hC : C ∈ components G Rᶜ) : cutSize G C ≤ cutSize G R := by
  apply Finset.card_le_card
  intro e he
  apply (mem_ownerCut G R e).2
  rcases (mem_ownerCut G C e).1 he with h | h
  · have hs : G.src e ∉ R := Finset.mem_compl.1 (component_subset G hC h.1)
    have hd : G.dst e ∈ R := by
      by_contra hn
      have hc := component_closed G hC (G.src e) h.1 (G.dst e)
        (Finset.mem_compl.2 hn) ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩
      exact h.2 hc
    exact Or.inr ⟨hs, hd⟩
  · have hd : G.dst e ∉ R := Finset.mem_compl.1 (component_subset G hC h.2)
    have hs : G.src e ∈ R := by
      by_contra hn
      have hc := component_closed G hC (G.dst e) h.2 (G.src e)
        (Finset.mem_compl.2 hn) ⟨e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩
      exact h.1 hc
    exact Or.inl ⟨hs, hd⟩





theorem components_union (U : Finset G.Vertex) : (components G U).biUnion id = U := by
  ext v
  constructor
  · intro hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.1 hv
    exact component_subset G hC hvC
  · intro hv
    obtain ⟨C, hC, hvC⟩ := components_cover G hv
    exact Finset.mem_biUnion.2 ⟨C, hC, hvC⟩





end Erdos1016.SafeCore
