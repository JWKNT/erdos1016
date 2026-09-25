import Erdos1016.Cycles.Geometry.RetainedExteriorTreeCount
import Erdos1016.Cycles.Geometry.ExteriorLinkClassification
import Erdos1016.Cycles.Geometry.PackedForestRetention

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
open ExteriorComponents
open Erdos1016.Nonbacktracking.ShortWalks
local instance retainedExteriorLinksDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The four-way exterior-link estimate in the actual retained graph. Packed
regions are automatically avoided by forest components, and all path-count
hypotheses inside J follow from the multigraph geometry. Only the small-cyclic
count K remains for the small-cut probability estimate. -/
theorem exterior_links_le_marked_cut_cyclic_blocks
    (G : FiniteMultiGraph) (P U : Finset G.Vertex)
    (F : Finset (Finset G.Vertex)) (D t q K : ℕ)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ∀ f ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (S : Finset (Component G U))
    {a b : (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).Vertex}
    (C : (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).toSimpleGraph.Walk a a)
    (C' : (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).toSimpleGraph.Walk b b)
    (hC : C.IsCycle)
    (hdisjoint : Disjoint {x | x ∈ C.support} {x | x ∈ C'.support})
    (hmax : ∀ v, G.degree v ≤ 3) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (hPU : P ⊆ U) (hFU : F.biUnion id ⊆ U)
    (hF : ∀ A ∈ F, G.ShortCyclicRegion P D A)
    (hCU : ∀ v ∈ C.support, vertex G (P ∪ F.biUnion id)ᶜ hloop hsimple v ∉ U)
    (hC'U : ∀ v ∈ C'.support, vertex G (P ∪ F.biUnion id)ᶜ hloop hsimple v ∉ U)
    (hq : 0 < q)
    (hg : GirthGreater (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).toSimpleGraph D)
    (hbudget : 2 * (t + 2 * q) ≤ D)
    (hcyclic : (smallCyclicPart G U P t S).card ≤ K)
    (hattachC : ∀ c ∈ S, ∃ u ∈ C.support, ∃ x ∈ vertices G U c,
      G.toSimpleGraph.Adj (vertex G (P ∪ F.biUnion id)ᶜ hloop hsimple u) x)
    (hattachC' : ∀ c ∈ S, ∃ v ∈ C'.support, ∃ y ∈ vertices G U c,
      G.toSimpleGraph.Adj y (vertex G (P ∪ F.biUnion id)ᶜ hloop hsimple v)) :
    S.card ≤ Fintype.card (Component G P) + (G.cutEdges U).card / (t + 1) + K +
      (C.length / q + 1) * (C'.length / q + 1) := by
  have hforest (c) (hc : c ∈ smallForestPart G U P t S) :
      G.IsForestWord (G.restrictEdges (G.internalEdges (vertices G U c)) (fun _ => 1)) :=
    not_not.mp (Finset.mem_filter.mp hc).2.2.2
  have hret (c) (hc : c ∈ smallForestPart G U P t S) :
      vertices G U c ⊆ (P ∪ F.biUnion id)ᶜ :=
    G.forest_component_retained P U F D hF hFU c (hforest c hc)
      (smallForestPart_disjoint_marked G U P t S c hc)
  have hout : ∀ v, v ∉ U → v ∈ (P ∪ F.biUnion id)ᶜ := by
    intro v hv
    simp only [Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨fun h => hv (hPU h), fun h => hv (hFU h)⟩
  have hcub (c) (hc : c ∈ smallForestPart G U P t S) (v) (hv : v ∈ vertices G U c) :
      G.degree v = 3 := by
    apply hcubic v
    exact fun hp => Finset.disjoint_left.mp
      (smallForestPart_disjoint_marked G U P t S c hc) hv hp
  have htrees := card_retained_exterior_trees_le_length_blocks G (P ∪ F.biUnion id)ᶜ
    hloop hsimple U (smallForestPart G U P t S) C C' hC hdisjoint hmax hout hCU hC'U
    hret hforest hcub D t q hq hg hbudget
    (fun c hc => (Finset.mem_filter.mp hc).2.2.1)
    (fun c hc => hattachC c (Finset.mem_filter.mp hc).1)
    (fun c hc => hattachC' c (Finset.mem_filter.mp hc).1)
  have hclasses := card_le_marked_large_cyclic_forest G U P hPU t K S hcyclic
  omega

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
