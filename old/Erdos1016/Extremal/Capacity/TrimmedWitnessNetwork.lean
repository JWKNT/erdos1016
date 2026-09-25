import Erdos1016.Extremal.Capacity.TrimmedWitnessComponents
import Erdos1016.Extremal.Capacity.TrimmedWitnessRank

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.TrimmedWitnessNetworkIso

open Erdos1016
open Erdos1016.Proof.VertexSupportedWitness
open Erdos1016.BoundaryTrace

private theorem support_src_mem (G : PhysicalGraph) (F : Finset G.CycleWord)
    {e : G.Edge} (he : e ∈ witnessSupportEdges G F) :
    G.src e ∈ witnessSupportVertices G F := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, e, he, Or.inl rfl⟩

private theorem support_dst_mem (G : PhysicalGraph) (F : Finset G.CycleWord)
    {e : G.Edge} (he : e ∈ witnessSupportEdges G F) :
    G.dst e ∈ witnessSupportVertices G F := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, e, he, Or.inr rfl⟩

/-- The endpoint-restricted network with the original witness support labels. -/
def endpointSupportNetwork (G : PhysicalGraph) (F : Finset G.CycleWord) :
    Network {v : G.Vertex // v ∈ witnessSupportVertices G F}
      {e : G.Edge // e ∈ witnessSupportEdges G F} where
  src e := ⟨G.src e.1, support_src_mem G F e.2⟩
  dst e := ⟨G.dst e.1, support_dst_mem G F e.2⟩
  noLoops e h := G.noLoops e.1 (congrArg Subtype.val h)

private theorem witnessSupport_adj_iff_raw
    (G : PhysicalGraph) (F : Finset G.CycleWord) (u v : G.Vertex) :
    (witnessSupportGraph G F).toSimpleGraph.Adj u v ↔
      ∃ e ∈ witnessSupportEdges G F,
        (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u) := by
  classical
  let W := witnessSupportGraph G F
  let E := witnessSupportEdges G F
  constructor
  · intro h
    change ∃ e : W.Edge, (1 : F₂) ≠ 0 ∧
      ((W.src e = u ∧ W.dst e = v) ∨ (W.src e = v ∧ W.dst e = u)) at h
    obtain ⟨e, _, h | h⟩ := h
    · let q := ((Finset.equivFin E).symm e).1
      refine ⟨q, ((Finset.equivFin E).symm e).2, Or.inl ?_⟩
      constructor
      · simpa [W, witnessSupportGraph, q] using h.1
      · simpa [W, witnessSupportGraph, q] using h.2
    · let q := ((Finset.equivFin E).symm e).1
      refine ⟨q, ((Finset.equivFin E).symm e).2, Or.inr ?_⟩
      constructor
      · simpa [W, witnessSupportGraph, q] using h.1
      · simpa [W, witnessSupportGraph, q] using h.2
  · rintro ⟨e, he, h | h⟩
    · let ew : W.Edge := Finset.equivFin E ⟨e, he⟩
      refine ⟨ew, one_ne_zero, Or.inl ?_⟩
      have hraw : ((Finset.equivFin E).symm ew).1 = e := by simp [ew]
      constructor
      · change G.src ((Finset.equivFin E).symm ew).1 = _
        rw [hraw]
        exact h.1
      · change G.dst ((Finset.equivFin E).symm ew).1 = _
        rw [hraw]
        exact h.2
    · let ew : W.Edge := Finset.equivFin E ⟨e, he⟩
      refine ⟨ew, one_ne_zero, Or.inr ?_⟩
      have hraw : ((Finset.equivFin E).symm ew).1 = e := by simp [ew]
      constructor
      · change G.src ((Finset.equivFin E).symm ew).1 = _
        rw [hraw]
        exact h.1
      · change G.dst ((Finset.equivFin E).symm ew).1 = _
        rw [hraw]
        exact h.2

private theorem supportNetwork_adj_iff_raw
    (G : PhysicalGraph) (F : Finset G.CycleWord)
    (u v : {x : G.Vertex // x ∈ witnessSupportVertices G F}) :
    (endpointSupportNetwork G F).graph.Adj u v ↔
      ∃ e ∈ witnessSupportEdges G F,
        (G.src e = u.1 ∧ G.dst e = v.1) ∨
        (G.src e = v.1 ∧ G.dst e = u.1) := by
  classical
  let N := endpointSupportNetwork G F
  constructor
  · rintro ⟨e, h | h⟩
    · refine ⟨e.1, e.2, Or.inl ?_⟩
      exact ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩
    · refine ⟨e.1, e.2, Or.inr ?_⟩
      exact ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩
  · rintro ⟨e, he, h | h⟩
    · refine ⟨⟨e, he⟩, Or.inl ?_⟩
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · refine ⟨⟨e, he⟩, Or.inr ?_⟩
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

private theorem supportGraph_induce_eq_networkGraph
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    (witnessSupportGraph G F).toSimpleGraph.induce
      (witnessSupportVertices G F : Set G.Vertex) =
      (endpointSupportNetwork G F).graph := by
  classical
  let W := witnessSupportGraph G F
  let N := endpointSupportNetwork G F
  ext u v
  change (witnessSupportGraph G F).toSimpleGraph.Adj u.1 v.1 ↔
    (endpointSupportNetwork G F).graph.Adj u v
  rw [witnessSupport_adj_iff_raw G F u.1 v.1]
  exact (supportNetwork_adj_iff_raw G F u v).symm

/-- The reindexing from support labels to the physical trimmed graph. -/
def endpointSupportReindex (G : PhysicalGraph) (F : Finset G.CycleWord) :
    Network.Reindex (endpointSupportNetwork G F)
      (trimmedWitnessGraph G F).traceNetwork where
  vertices := Finset.equivFin (witnessSupportVertices G F)
  edges := Finset.equivFin (witnessSupportEdges G F)
  endpoints := by
    intro e
    left
    constructor
    · apply congrArg (Finset.equivFin (witnessSupportVertices G F))
      apply Subtype.ext
      simp [endpointSupportNetwork, trimmedWitnessGraph,
        Equiv.symm_apply_apply]
    · apply congrArg (Finset.equivFin (witnessSupportVertices G F))
      apply Subtype.ext
      simp [endpointSupportNetwork, trimmedWitnessGraph,
        Equiv.symm_apply_apply]

/-- The physical graph of the endpoint-restricted network is the trimmed graph
up to the explicit vertex and edge reindexing. -/
def endpointSupport_networkGraphIso (G : PhysicalGraph) (F : Finset G.CycleWord) :
    (endpointSupportNetwork G F).graph ≃g
      (trimmedWitnessGraph G F).traceNetwork.graph where
  toEquiv := (endpointSupportReindex G F).vertices
  map_rel_iff' := by
    intro u v
    exact (endpointSupportReindex G F).graph_adj_iff u v

/-- The induced support graph is isomorphic to the graph underlying the
trimmed witness graph, as needed by the component-count split. -/
def witnessSupport_induced_trimmed_iso (G : PhysicalGraph)
    (F : Finset G.CycleWord) :
    ((witnessSupportGraph G F).toSimpleGraph.induce
      (witnessSupportVertices G F : Set G.Vertex)) ≃g
      (trimmedWitnessGraph G F).toSimpleGraph := by
  classical
  let e₁ : ((witnessSupportGraph G F).toSimpleGraph.induce
      (witnessSupportVertices G F : Set G.Vertex)) ≃g
      (endpointSupportNetwork G F).graph := by
    refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
    intro u v
    change (endpointSupportNetwork G F).graph.Adj u v ↔
      ((witnessSupportGraph G F).toSimpleGraph.induce
        (witnessSupportVertices G F : Set G.Vertex)).Adj u v
    rw [supportGraph_induce_eq_networkGraph G F]
  let e₂ := endpointSupport_networkGraphIso G F
  refine { toEquiv := e₁.toEquiv.trans e₂.toEquiv, map_rel_iff' := ?_ }
  intro u v
  change (trimmedWitnessGraph G F).toSimpleGraph.Adj
      ((e₁.toEquiv.trans e₂.toEquiv) u) ((e₁.toEquiv.trans e₂.toEquiv) v) ↔
    ((witnessSupportGraph G F).toSimpleGraph.induce
      (witnessSupportVertices G F : Set G.Vertex)).Adj u v
  rw [← (trimmedWitnessGraph G F).traceNetwork_graph]
  change (trimmedWitnessGraph G F).traceNetwork.graph.Adj
      (e₂ (e₁ u)) (e₂ (e₁ v)) ↔ _
  calc
    _ ↔ (endpointSupportNetwork G F).graph.Adj (e₁ u) (e₁ v) :=
      e₂.map_rel_iff'
    _ ↔ ((witnessSupportGraph G F).toSimpleGraph.induce
        (witnessSupportVertices G F : Set G.Vertex)).Adj u v := e₁.map_rel_iff'

/-- Component splitting for the literal support and its endpoint-trimmed graph.
The complement term counts precisely the host vertices removed by trimming. -/
theorem witnessSupport_componentCount_adjustment
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    Fintype.card (witnessSupportGraph G F).traceNetwork.Component =
      Fintype.card (trimmedWitnessGraph G F).traceNetwork.Component +
        Fintype.card {v : G.Vertex // v ∉
          (witnessSupportVertices G F : Set G.Vertex)} := by
  classical
  let V := witnessSupportVertices G F
  let W := witnessSupportGraph G F
  let T := trimmedWitnessGraph G F
  have hends : ∀ ⦃u v : W.Vertex⦄, W.traceNetwork.graph.Adj u v →
      u ∈ (V : Set G.Vertex) ∧ v ∈ (V : Set G.Vertex) := by
    intro u v h
    apply Erdos1016.Proof.TrimmedWitnessComponentBridge.witnessSupport_adj_endpoints G F
    simpa only [W.traceNetwork_graph] using h
  have hiso : (W.traceNetwork.graph.induce (V : Set G.Vertex)) ≃g
      T.traceNetwork.graph := by
    simpa only [W.traceNetwork_graph, T.traceNetwork_graph] using
      witnessSupport_induced_trimmed_iso G F
  exact Erdos1016.Proof.TrimmedWitnessComponentBridge.component_card_adjustment_of_induced_iso
    W.traceNetwork.graph (V : Set G.Vertex) hends T.traceNetwork.graph hiso

/-- The complement subtype cardinal is exactly the number of host vertices
removed from the support graph. -/
theorem removed_vertex_card_eq
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    Fintype.card {v : G.Vertex // v ∉
      (witnessSupportVertices G F : Set G.Vertex)} =
      G.vertexCount - (witnessSupportVertices G F).card := by
  classical
  let V := witnessSupportVertices G F
  have hsub : Fintype.card {v : G.Vertex // v ∈ (V : Set G.Vertex)} = V.card := by
    have e : {v : G.Vertex // v ∈ (V : Set G.Vertex)} ≃ Fin V.card := by
      simpa [PhysicalGraph.Vertex] using Finset.equivFin V
    have h := Fintype.card_congr e
    simpa [PhysicalGraph.Vertex, V] using h
  rw [Fintype.card_subtype_compl, hsub]
  simp [PhysicalGraph.Vertex, V]

/-- Numerical component-count adjustment consumed by the Euler rank bridge. -/
theorem witnessSupport_componentCount_adjustment_sub
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    Fintype.card (witnessSupportGraph G F).traceNetwork.Component =
      Fintype.card (trimmedWitnessGraph G F).traceNetwork.Component +
        (G.vertexCount - (witnessSupportVertices G F).card) := by
  have h := witnessSupport_componentCount_adjustment G F
  rw [removed_vertex_card_eq] at h
  exact h

/-- The trimmed graph has exactly the cycle rank of the literal witness
support graph. -/
theorem trimmedWitness_cycleRank_eq
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    (trimmedWitnessGraph G F).cycleRank = (witnessSupportGraph G F).cycleRank := by
  apply Erdos1016.Proof.TrimmedWitnessRankBridge.trimmedWitness_cycleRank_eq_of_componentCount_adjustment
  exact witnessSupport_componentCount_adjustment_sub G F


end Erdos1016.Proof.TrimmedWitnessNetworkIso
