import Erdos1016.CycleSpace.Support.ActiveComponents
import Erdos1016.Decomposition.TwoCore.PhysicalCore
import Erdos1016.Cleanup.Corridors.PhysicalPartition
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.RestrictedComponentGraph

open Erdos1016
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.BoundaryTrace
open Erdos1016.Proof.PhysicalPartition

local instance {V : Type*} (J : SimpleGraph V) : DecidableRel J.Adj := Classical.decRel _

/-- The finite set of vertices in a chosen active connected component. -/
def componentSupportFinset (G : PhysicalGraph) (c : ActiveComponent G) :
    Finset (activeSubgraph G).Vertex := by
  classical
  exact c.supp.toFinset

theorem mem_componentSupportFinset (G : PhysicalGraph) (c : ActiveComponent G)
    (v : (activeSubgraph G).Vertex) :
    v ∈ componentSupportFinset G c ↔ componentOf G v = c := by
  simp [componentSupportFinset, componentOf,
    SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- Any active edge incident to the component stays inside its vertex support. -/
theorem componentSupport_closed_adj (G : PhysicalGraph) (c : ActiveComponent G)
    {u v : (activeSubgraph G).Vertex}
    (hu : u ∈ componentSupportFinset G c)
    (h : (activeSubgraph G).toSimpleGraph.Adj u v) :
    v ∈ componentSupportFinset G c := by
  apply (mem_componentSupportFinset G c v).2
  rw [← (mem_componentSupportFinset G c u).1 hu]
  exact (SimpleGraph.ConnectedComponent.sound h.reachable).symm

/-- The physical graph obtained by inducing the active graph on the selected
component support. Its vertices are reindexed to `Fin`. -/
def componentSupportPhysical (G : PhysicalGraph) (c : ActiveComponent G) : PhysicalGraph :=
  Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical
    (activeSubgraph G) (componentSupportFinset G c)

theorem degreeWithin_componentSupport_eq (G : PhysicalGraph) (c : ActiveComponent G)
    (v : (activeSubgraph G).Vertex) (hv : v ∈ componentSupportFinset G c) :
    degreeWithin (activeSubgraph G).toSimpleGraph (componentSupportFinset G c) v =
      (activeSubgraph G).toSimpleGraph.degree v := by
  classical
  unfold degreeWithin SimpleGraph.degree
  have hfilter :
      (componentSupportFinset G c).filter
        (fun w => (activeSubgraph G).toSimpleGraph.Adj v w) =
      (activeSubgraph G).toSimpleGraph.neighborFinset v := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · exact fun h => h.2
    · intro hadj
      exact ⟨componentSupport_closed_adj G c hv hadj, hadj⟩
  rw [hfilter]

/-- The vertex-restricted physical graph is connected, as it is just the
induced graph on the support of one active connected component. -/
theorem componentSupportPhysical_connected (G : PhysicalGraph)
    (c : ActiveComponent G) :
    (componentSupportPhysical G c).toSimpleGraph.Connected := by
  classical
  let A := activeSubgraph G
  let S := componentSupportFinset G c
  let N := Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetwork A S
  have hind : N.graph = A.toSimpleGraph.induce (↑S : Set A.Vertex) := by
    change (Network.Shore.inside A.traceNetwork S).graph = _
    rw [Network.Shore.inside_graph_eq_induce, A.traceNetwork_graph]
  have hcomp : (A.toSimpleGraph.induce (↑S : Set A.Vertex)).Connected := by
    have hS : (↑S : Set A.Vertex) = c.supp := by
      ext v
      simp [S, componentSupportFinset, componentOf,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hS]
    exact c.connected_induce_supp
  have hN : N.graph.Connected := by simpa [hind] using hcomp
  have hphys : (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical A S).toSimpleGraph.Connected := by
    exact (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysicalGraphIso A S).connected_iff.1
      hN
  simpa [componentSupportPhysical, A, S] using hphys

/-- Degrees in the reindexed component graph agree with the active-subgraph
degrees at the corresponding original support vertices. -/
theorem componentSupportPhysical_degree_eq (G : PhysicalGraph)
    (c : ActiveComponent G) (v : Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
      (componentSupportFinset G c)) :
    (componentSupportPhysical G c).degree
    (Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
        (componentSupportFinset G c)) v) =
      (activeSubgraph G).toSimpleGraph.degree v.1 := by
  let A := activeSubgraph G
  let S := componentSupportFinset G c
  change (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical A S).degree
      (Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex S) v) = _
  rw [Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical_degree_eq]
  exact degreeWithin_componentSupport_eq G c v.1 v.2



/-- Actual active edge labels with both endpoints in the chosen component are
exactly the component edge labels. -/
def componentSupportEdgeLabelEquiv (G : PhysicalGraph) (c : ActiveComponent G) :
    Erdos1016.BoundaryTrace.Network.Shore.InsideEdge
        (activeSubgraph G).traceNetwork (componentSupportFinset G c) ≃
      {e : (activeSubgraph G).Edge // e ∈ componentEdges G c} := by
  classical
  refine {
    toFun := fun e => ?_
    invFun := fun e => ?_
    left_inv := ?_
    right_inv := ?_ }
  · have hs : componentOf G ((activeSubgraph G).src e.1) = c := by
      apply (mem_componentSupportFinset G c _).1
      simpa [PhysicalGraph.traceNetwork] using e.2.1
    refine ⟨e.1, ?_⟩
    simp [componentEdges, edgeComponent, hs]
  · have hs : componentOf G ((activeSubgraph G).src e.1) = c := by
      have he : edgeComponent G e.1 = c := (Finset.mem_filter.1 e.2).2
      change componentOf G ((activeSubgraph G).src e.1) = c at he
      exact he
    have ht : componentOf G ((activeSubgraph G).dst e.1) = c := by
      rw [← edgeComponent_eq_dst G e.1]
      exact hs
    refine ⟨e.1, ?_⟩
    constructor
    · apply (mem_componentSupportFinset G c _).2
      exact hs
    · apply (mem_componentSupportFinset G c _).2
      exact ht
  · intro e
    apply Subtype.ext
    rfl
  · intro e
    apply Subtype.ext
    rfl

/-- The edge labels of the vertex-restricted physical graph reindex to the
existing edge-restricted component physical graph. -/
def componentSupportEdgeEquiv (G : PhysicalGraph) (c : ActiveComponent G) :
    (componentSupportPhysical G c).Edge ≃
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge := by
  let S := componentSupportFinset G c
  let N := Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetwork
    (activeSubgraph G) S
  let I := Erdos1016.BoundaryTrace.Network.Shore.InsideEdge
    (activeSubgraph G).traceNetwork S
  let finI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let loc : I ≃ {e : (activeSubgraph G).Edge // e ∈ componentEdges G c} :=
    componentSupportEdgeLabelEquiv G c
  let old := (activeSubgraph G).restrictedEdgeEquiv (componentEdges G c)
  exact (by
    dsimp [componentSupportPhysical, Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical,
      Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetwork, S, N] at *
    exact finI.symm.trans (loc.trans old.symm))

/-- Vertex inclusion of the reindexed component graph into the ambient active
vertex labels. -/
def componentSupportVertexMap (G : PhysicalGraph) (c : ActiveComponent G) :
    (componentSupportPhysical G c).Vertex → (activeSubgraph G).Vertex :=
  fun v => ((Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
    (componentSupportFinset G c))).symm v).1

theorem componentSupportVertexMap_injective (G : PhysicalGraph) (c : ActiveComponent G) :
    Function.Injective (componentSupportVertexMap G c) := by
  intro u v h
  let e := Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
    (componentSupportFinset G c))
  have hsub : e.symm u = e.symm v := Subtype.ext h
  exact e.symm.injective hsub

theorem componentSupportVertexMap_mem_support (G : PhysicalGraph) (c : ActiveComponent G)
    (v : (componentSupportPhysical G c).Vertex) :
    componentSupportVertexMap G c v ∈ componentSupportFinset G c := by
  exact ((Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
    (componentSupportFinset G c))).symm v).2

theorem componentSupportVertexMap_surj_on_support (G : PhysicalGraph) (c : ActiveComponent G)
    {v : (activeSubgraph G).Vertex} (hv : v ∈ componentSupportFinset G c) :
    ∃ w : (componentSupportPhysical G c).Vertex, componentSupportVertexMap G c w = v := by
  let e := Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
    (componentSupportFinset G c))
  refine ⟨e ⟨v, hv⟩, ?_⟩
  simp [componentSupportVertexMap, e]





/-- Source and target endpoints agree under the local-to-component edge
equivalence and vertex inclusion. -/
theorem componentSupportEdgeEquiv_src (G : PhysicalGraph) (c : ActiveComponent G)
    (e : (componentSupportPhysical G c).Edge) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).src
        (componentSupportEdgeEquiv G c e) =
      componentSupportVertexMap G c ((componentSupportPhysical G c).src e) := by
  simp [componentSupportEdgeEquiv, componentSupportVertexMap,
    componentSupportPhysical,
    Erdos1016.PhysicalGraph.restrictPhysical,
    componentSupportEdgeLabelEquiv,
    Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical,
    Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetwork,
    Erdos1016.BoundaryDecay.physicalize,
    Erdos1016.BoundaryTrace.Network.Shore.inside,
    PhysicalGraph.traceNetwork, PhysicalGraph.restrictedEdgeEquiv,
    Finset.equivFin]

theorem componentSupportEdgeEquiv_dst (G : PhysicalGraph) (c : ActiveComponent G)
    (e : (componentSupportPhysical G c).Edge) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).dst
        (componentSupportEdgeEquiv G c e) =
      componentSupportVertexMap G c ((componentSupportPhysical G c).dst e) := by
  simp [componentSupportEdgeEquiv, componentSupportVertexMap,
    componentSupportPhysical,
    Erdos1016.PhysicalGraph.restrictPhysical,
    componentSupportEdgeLabelEquiv,
    Erdos1016.Nonbacktracking.FiniteTwoCore.inducedPhysical,
    Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetwork,
    Erdos1016.BoundaryDecay.physicalize,
    Erdos1016.BoundaryTrace.Network.Shore.inside,
    PhysicalGraph.traceNetwork, PhysicalGraph.restrictedEdgeEquiv,
    Finset.equivFin]

/-- Carry a local physical corridor to the old edge-restricted graph. -/
def componentSupportCorridorToRestricted (G : PhysicalGraph) (c : ActiveComponent G)
    (C : PhysicalCorridor (componentSupportPhysical G c)) :
    PhysicalCorridor ((activeSubgraph G).restrictPhysical (componentEdges G c)) where
  edges := C.edges.map (componentSupportEdgeEquiv G c)
  vertices := C.vertices.map (componentSupportVertexMap G c)
  vertices_length := by simpa using C.vertices_length
  edges_nodup := C.edges_nodup.map_on (fun e _ f _ hef => by
    apply (componentSupportEdgeEquiv G c).injective
    exact hef)
  step := by
    intro i
    let i' : Fin C.edges.length := ⟨i.val, by simpa using i.isLt⟩
    have hi := C.step i'
    simp only [List.get_eq_getElem, List.getElem_map]
    simp only [i'] at hi
    simp only [List.get_eq_getElem] at hi
    rcases hi with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
    · left
      constructor
      · rw [componentSupportEdgeEquiv_src]
        exact congrArg (componentSupportVertexMap G c) hsrc
      · rw [componentSupportEdgeEquiv_dst]
        exact congrArg (componentSupportVertexMap G c) hdst
    · right
      constructor
      · rw [componentSupportEdgeEquiv_dst]
        exact congrArg (componentSupportVertexMap G c) hdst
      · rw [componentSupportEdgeEquiv_src]
        exact congrArg (componentSupportVertexMap G c) hsrc

theorem componentSupportCorridorToRestricted_support (G : PhysicalGraph)
    (c : ActiveComponent G) (C : PhysicalCorridor (componentSupportPhysical G c)) :
    (componentSupportCorridorToRestricted G c C).support =
      C.support.image (componentSupportEdgeEquiv G c) := by
  classical
  ext e
  simp [PhysicalCorridor.support, componentSupportCorridorToRestricted,
    Finset.mem_image, List.mem_toFinset, List.mem_map]





theorem activeEdge_mem_componentEdges_of_endpoint (G : PhysicalGraph)
    (c : ActiveComponent G) (e : (activeSubgraph G).Edge)
    (h : (activeSubgraph G).src e ∈ componentSupportFinset G c ∨
      (activeSubgraph G).dst e ∈ componentSupportFinset G c) :
    e ∈ componentEdges G c := by
  classical
  have hs : componentOf G ((activeSubgraph G).src e) = c := by
    rcases h with h | h
    · exact (mem_componentSupportFinset G c _).1 h
    · exact (edgeComponent_eq_dst G e).trans
        ((mem_componentSupportFinset G c _).1 h)
  simp [componentEdges, edgeComponent, hs]







end Erdos1016.Proof.RestrictedComponentGraph
