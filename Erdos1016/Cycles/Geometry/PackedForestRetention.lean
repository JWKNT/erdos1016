import Erdos1016.Graph.ExteriorForestRegions
import Erdos1016.Cycles.Selection.ShortRegionPacking

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph
local instance packedForestRetentionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A nonzero internal cycle-space coordinate is a genuine labelled cycle
obstruction, also in the presence of loops and parallel labels. -/
theorem not_internal_forest_of_nonzero (G : FiniteMultiGraph) (A : Finset G.Vertex)
    (h : ∃ z : G.internalCycleSpace A, z ≠ 0) :
    ¬ G.IsForestWord (G.restrictEdges (G.internalEdges A) (fun _ => 1)) := by
  obtain ⟨z, hz⟩ := h
  apply G.not_isForestWord_of_even_support z.1
  · intro hzero
    apply hz
    apply Subtype.ext
    exact Subtype.ext hzero
  · intro e he
    have hm : e ∈ G.internalEdges A := by
      by_contra hn
      exact he (z.2 e hn)
    simp [restrictEdges, hm]

/-- A forest exterior component avoiding the marked set survives deletion
of the entire packed cyclic union. This is a consequence of actual graph
connectedness and foresthood, not an extra retainedness assumption. -/
theorem forest_component_retained (G : FiniteMultiGraph)
    (P U : Finset G.Vertex) (F : Finset (Finset G.Vertex)) (D : ℕ)
    (hF : ∀ A ∈ F, G.ShortCyclicRegion P D A)
    (hFU : F.biUnion id ⊆ U) (c : ExteriorComponents.Component G U)
    (hforest : G.IsForestWord (G.restrictEdges
      (G.internalEdges (ExteriorComponents.vertices G U c)) (fun _ => 1)))
    (hmarked : Disjoint (ExteriorComponents.vertices G U c) P) :
    ExteriorComponents.vertices G U c ⊆ (P ∪ F.biUnion id)ᶜ := by
  have hdis := ExteriorComponents.forest_component_disjoint_cyclic_union G U F id
    (fun A hA v hv => hFU (Finset.mem_biUnion.mpr ⟨A, hA, hv⟩))
    (fun A hA => (hF A hA).connected)
    (fun A hA => G.not_internal_forest_of_nonzero A (hF A hA).cyclic) c hforest
  intro v hv
  simp only [Finset.mem_compl, Finset.mem_union, not_or]
  exact ⟨fun hp => Finset.disjoint_left.mp hmarked hv hp,
    fun hs => Finset.disjoint_left.mp hdis hv hs⟩

end Erdos1016.FiniteMultiGraph
