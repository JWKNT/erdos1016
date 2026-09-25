import Erdos1016.Graph.ExteriorComponents

set_option autoImplicit false

/-! A forest exterior component cannot meet any connected cyclic region
 retained entirely in the exterior. This applies to packed short cycles,
 including loops and digons, and proves their vertex sets avoid every
 exterior tree used in the high-girth path count. -/
noncomputable section
namespace Erdos1016.FiniteMultiGraph.ExteriorComponents
open SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- Restricting the full internal graph to fewer vertices preserves the
 actual multigraph forest property. -/
theorem internal_forest_mono {A B : Finset G.Vertex} (hAB : A ⊆ B)
    (hB : G.IsForestWord (G.restrictEdges (G.internalEdges B) (fun _ => 1))) :
    G.IsForestWord (G.restrictEdges (G.internalEdges A) (fun _ => 1)) := by
  apply hB.mono
  intro e he
  have hAe : G.src e ∈ A ∧ G.dst e ∈ A := by
    simpa [restrictEdges, internalEdges] using he
  simp [restrictEdges, internalEdges, hAB hAe.1, hAB hAe.2]

/-- The labelled forest condition implies ordinary acyclicity of the
 induced underlying graph; the converse would fail on loops or digons. -/
theorem internal_forest_induced_acyclic (A : Finset G.Vertex)
    (hA : G.IsForestWord (G.restrictEdges (G.internalEdges A) (fun _ => 1))) :
    (G.toSimpleGraph.induce (↑A : Set G.Vertex)).IsAcyclic := by
  let x := G.restrictEdges (G.internalEdges A) (fun _ => 1)
  let f : G.toSimpleGraph.induce (↑A : Set G.Vertex) →g G.selectedGraph x := {
    toFun := Subtype.val
    map_rel' := by
      intro a b hab
      obtain ⟨hne, e, he⟩ := hab
      refine ⟨hne, e, ?_, he⟩
      have hends : G.src e ∈ A ∧ G.dst e ∈ A := by
        rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact ⟨hs.symm ▸ a.2, ht.symm ▸ b.2⟩
        · exact ⟨hs.symm ▸ b.2, ht.symm ▸ a.2⟩
      simp [x, restrictEdges, internalEdges, hends.1, hends.2] }
  intro v p hp
  exact hA.2.2 (p.map f) ((Walk.map_isCycle_iff_of_injective Subtype.val_injective).mpr hp)

/-- A connected region in U meeting one induced component lies entirely
 in that component. -/
theorem connected_region_subset_component (U R : Finset G.Vertex)
    (hRU : R ⊆ U) (hR : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected)
    (c : Component G U) (hmeet : ∃ x ∈ R, x ∈ vertices G U c) :
    R ⊆ vertices G U c := by
  obtain ⟨x, hxR, hxC⟩ := hmeet
  obtain ⟨hxU, hxc⟩ := (mem_vertices G U c x).mp hxC
  let inc : G.toSimpleGraph.induce (↑R : Set G.Vertex) →g graph G U :=
    (SimpleGraph.induceHomOfLE (G := G.toSimpleGraph)
      (show (↑R : Set G.Vertex) ⊆ ↑U from hRU)).toHom
  intro y hyR
  apply (mem_vertices G U c y).mpr
  refine ⟨hRU hyR, ?_⟩
  have heq := ConnectedComponent.sound ((hR.preconnected ⟨y, hyR⟩ ⟨x, hxR⟩).map inc)
  exact heq.trans hxc

/-- In particular an exterior forest component avoids each packed cyclic
 region that is disjoint from the deleted cycles. A cyclic region may be a
 loop or digon; no simple-cycle representation is used here. -/
theorem forest_component_disjoint_cyclic_region (U R : Finset G.Vertex)
    (hRU : R ⊆ U) (hR : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected)
    (hcyclic : ¬G.IsForestWord (G.restrictEdges (G.internalEdges R) (fun _ => 1)))
    (c : Component G U)
    (hforest : G.IsForestWord
      (G.restrictEdges (G.internalEdges (vertices G U c)) (fun _ => 1))) :
    Disjoint (vertices G U c) R := by
  apply Finset.disjoint_left.mpr
  intro x hxC hxR
  exact hcyclic (internal_forest_mono G
    (connected_region_subset_component G U R hRU hR c ⟨x, hxR, hxC⟩) hforest)

/-- Consequently it avoids the union of any finite packed family of such
 regions; disjointness among the packed regions is not needed for this step. -/
theorem forest_component_disjoint_cyclic_union
    {I : Type*} (U : Finset G.Vertex) (s : Finset I) (R : I → Finset G.Vertex)
    (hRU : ∀ i ∈ s, R i ⊆ U)
    (hconn : ∀ i ∈ s, (G.toSimpleGraph.induce (↑(R i) : Set G.Vertex)).Connected)
    (hcyclic : ∀ i ∈ s, ¬G.IsForestWord (G.restrictEdges (G.internalEdges (R i)) (fun _ => 1)))
    (c : Component G U)
    (hforest : G.IsForestWord
      (G.restrictEdges (G.internalEdges (vertices G U c)) (fun _ => 1))) :
    Disjoint (vertices G U c) (s.biUnion R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxC hxR
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxR
  exact Finset.disjoint_left.mp
    (forest_component_disjoint_cyclic_region G U (R i) (hRU i hi)
      (hconn i hi) (hcyclic i hi) c hforest) hxC hxi

end Erdos1016.FiniteMultiGraph.ExteriorComponents
