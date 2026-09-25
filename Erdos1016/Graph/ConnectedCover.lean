import Erdos1016.Extremal.Capacity.WitnessSupport

set_option autoImplicit false
noncomputable section

namespace Erdos1016.ShortProof

/-- A finite cover by nonempty connected sets bounds the number of components.
Connectivity here is reachability in the actual target graph. -/
theorem component_count_le_connected_cover {V ι : Type*} [Finite V]
    (H : SimpleGraph V) (F : Finset ι) (U : ι → Set V)
    (hne : ∀ i ∈ F, (U i).Nonempty)
    (hreach : ∀ i ∈ F, ∀ u ∈ U i, ∀ v ∈ U i, H.Reachable u v)
    (hcover : ∀ v, ∃ i ∈ F, v ∈ U i) :
    Nat.card H.ConnectedComponent ≤ F.card := by
  classical
  let rep : {i // i ∈ F} → V := fun i => Classical.choose (hne i.1 i.2)
  have hrep (i : {i // i ∈ F}) : rep i ∈ U i.1 := Classical.choose_spec (hne i.1 i.2)
  let f : {i // i ∈ F} → H.ConnectedComponent := fun i => H.connectedComponentMk (rep i)
  have hf : Function.Surjective f := by
    intro c
    refine SimpleGraph.ConnectedComponent.ind ?_ c
    intro v
    obtain ⟨i, hi, hv⟩ := hcover v
    refine ⟨⟨i, hi⟩, ?_⟩
    exact SimpleGraph.ConnectedComponent.sound (hreach i hi _ (hrep ⟨i, hi⟩) v hv)
  simpa using Nat.card_le_card_of_surjective f hf

/-- The vertices of the actual cycle union, excluding isolated host vertices. -/
def cycleUnionVertices (G : PhysicalGraph) (F : Finset G.CycleWord) : Finset G.Vertex :=
  F.biUnion fun C => G.usedVertices C.1

/-- The edge-support graph, on exactly the vertices touched by selected cycles. -/
def cycleUnionGraph (G : PhysicalGraph) (F : Finset G.CycleWord) :=
  (witnessSupportGraph G F).toSimpleGraph.induce (↑(cycleUnionVertices G F) : Set G.Vertex)

lemma cycle_vertices_in_union (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) {v : G.Vertex} (hv : v ∈ G.usedVertices C.1) :
    v ∈ cycleUnionVertices G F := by
  classical
  exact Finset.mem_biUnion.mpr ⟨C, hC, hv⟩

/-- A union of at most `k` simple cycles has at most `k` edge-bearing
components, independently of how its cycles intersect. -/
theorem cycleUnion_component_count_le (G : PhysicalGraph) (F : Finset G.CycleWord) :
    Nat.card (cycleUnionGraph G F).ConnectedComponent ≤ F.card := by
  classical
  let S := cycleUnionVertices G F
  let H := cycleUnionGraph G F
  let U : G.CycleWord → Set {v : G.Vertex // v ∈ S} :=
    fun C => {v | v.1 ∈ G.usedVertices C.1}
  apply component_count_le_connected_cover H F U
  · intro C hC
    let v := Classical.choice C.2.2.2.1.nonempty
    exact ⟨⟨v.1, cycle_vertices_in_union G F hC v.2⟩, v.2⟩
  · intro C hC u hu v hv
    let f : (G.selectedGraph C.1).induce (↑(G.usedVertices C.1) : Set G.Vertex) →g H :=
      { toFun := fun a => ⟨a.1, cycle_vertices_in_union G F hC a.2⟩
        map_rel' := by
          intro a b hab
          change (witnessSupportGraph G F).toSimpleGraph.Adj a.1 b.1
          obtain ⟨e, he, hend⟩ := hab
          have hsupp : e ∈ witnessSupportEdges G F :=
            witnessSupport_edge_mem G F hC (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
          let q := Finset.equivFin (witnessSupportEdges G F) ⟨e, hsupp⟩
          refine ⟨q, one_ne_zero, ?_⟩
          simpa [witnessSupportGraph, q] using hend }
    exact (C.2.2.2.1 ⟨u.1, hu⟩ ⟨v.1, hv⟩).map f
  · intro v
    obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp v.2
    exact ⟨C, hC, hv⟩

end Erdos1016.ShortProof
