import Erdos1016.Graph.Embeddings.ComponentCount
import Erdos1016.Cleanup.Protection.ParallelPairProtection

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.WitnessComponentProtection

open Erdos1016
open ActivePhysicalComponents
open CleanupSpecification PhysicalPartition
open CorridorPairedPathCertificates PhysicalDegreeTwoCoreComponents
open CompressedRouteDecomposition
open RestrictedComponentGraph
open ComponentWitnessCorridorGeometry
open CorridorParallelPairCount
open ComponentCorridorReindexing
open PartitionRouteDecomposition

variable {G : PhysicalGraph} (I : CleanupInput G) (c : ActiveComponent G)
variable (D : CorridorPartition (componentSupportPhysical G c)
  (componentWitnessBadProtected G c I) (componentLocalWitnessPullback G c I))
variable (hend : Endpoints D)

abbrev originalVertex (q : (compressedCorridorGraph D hend).Vertex) : G.Vertex :=
  componentSupportVertexMap G c (compressedCorridorVertexMap D hend q)

def witnessVertices : Finset (compressedCorridorGraph D hend).Vertex := by
  classical
  exact Finset.univ.filter fun q => originalVertex I c D hend q ∈ I.witnessVertices

def witnessCore : SimpleGraph (compressedCorridorGraph D hend).Vertex :=
  (witnessGraph G I.witnessVertices I.witnessEdges).comap (originalVertex I c D hend)

theorem originalVertex_injective : Function.Injective (originalVertex I c D hend) :=
  (componentSupportVertexMap_injective G c).comp (compressedCorridorVertexMap_injective D hend)

/-- All original witness vertices in this active component survive compression. -/
theorem originalVertex_surjective_on_witness
    (v : G.Vertex) (hv : v ∈ I.witnessVertices)
    (hc : v ∈ componentSupportFinset G c) :
    ∃ q, originalVertex I c D hend q = v ∧ q ∈ witnessVertices I c D hend := by
  classical
  obtain ⟨u, hu⟩ := componentSupportVertexMap_surj_on_support G c hc
  have huP : u ∈ componentWitnessBadProtected G c I := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, Finset.mem_union_left _ (hu.symm ▸ hv)⟩
  let Q := protectedOrBranch (componentSupportPhysical G c) (componentWitnessBadProtected G c I)
  have huQ : u ∈ Q := Finset.mem_union_left _ huP
  let q : (compressedCorridorGraph D hend).Vertex := Finset.equivFin Q ⟨u, huQ⟩
  have hq : compressedCorridorVertexMap D hend q = u := by
    simp [q, compressedCorridorVertexMap, retainedVertexEquiv, Q]
  have hmap : originalVertex I c D hend q = v := by
    change componentSupportVertexMap G c (compressedCorridorVertexMap D hend q) = v
    rw [hq, hu]
  exact ⟨q, hmap, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap.symm ▸ hv⟩⟩

/-- Witness adjacency is active adjacency, since every witness edge is active. -/
theorem witness_adj_active {u v : G.Vertex}
    (h : (witnessGraph G I.witnessVertices I.witnessEdges).Adj u v) :
    (activeSubgraph G).toSimpleGraph.Adj u v := by
  classical
  obtain ⟨_, _, _, e, he, hend⟩ := h
  obtain ⟨x, hx⟩ := I.witness_edges_active e he
  have hactive : e ∈ activeEdges G :=
    (mem_activeEdges_iff G e).mpr (active_of_cycle_coordinate_ne_zero G x e hx)
  let a := (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨e, hactive⟩
  have hs : (activeSubgraph G).src a = G.src e := by simp [a, activeSubgraph, PhysicalGraph.restrictPhysical]
  have ht : (activeSubgraph G).dst a = G.dst e := by simp [a, activeSubgraph, PhysicalGraph.restrictPhysical]
  refine ⟨a, one_ne_zero, ?_⟩
  rw [hs, ht]
  exact hend

/-- The compressed witness core has at most as many components as the full
original witness. This is a uniform component bound, independent of m. -/
theorem witness_core_component_count_le :
    Nat.card ((witnessCore I c D hend).induce
      (↑(witnessVertices I c D hend) : Set (compressedCorridorGraph D hend).Vertex)).ConnectedComponent ≤
        witnessComponentCount G I.witnessVertices I.witnessEdges := by
  classical
  let A := witnessVertices I c D hend
  let J := (witnessGraph G I.witnessVertices I.witnessEdges).induce
    (↑I.witnessVertices : Set G.Vertex)
  let f : {q : (compressedCorridorGraph D hend).Vertex // q ∈ A} →
      {v : G.Vertex // v ∈ I.witnessVertices} := fun q =>
    ⟨originalVertex I c D hend q.1, (Finset.mem_filter.mp q.2).2⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply originalVertex_injective I c D hend
    exact congrArg (fun z : {v : G.Vertex // v ∈ I.witnessVertices} => z.1) h
  have hclosed : ∀ a b, J.Adj (f a) b → ∃ a', f a' = b := by
    intro a b hab
    have hactive := witness_adj_active I hab
    have ha : originalVertex I c D hend a.1 ∈ componentSupportFinset G c :=
      componentSupportVertexMap_mem_support G c _
    have hb := componentSupport_closed_adj G c ha hactive
    obtain ⟨q, hq, hqA⟩ := originalVertex_surjective_on_witness I c D hend b.1 b.2 hb
    exact ⟨⟨q, hqA⟩, Subtype.ext hq⟩
  have h := ClosedEmbeddingComponentCount.component_count_le J f hinj hclosed
  change Nat.card ((witnessCore I c D hend).induce
    (↑A : Set (compressedCorridorGraph D hend).Vertex)).ConnectedComponent ≤ Nat.card J.ConnectedComponent at h
  simpa [J, witnessComponentCount, Nat.card_eq_fintype_card] using h

/-- A singleton physical corridor has exactly the endpoints of its sole edge,
up to orientation. -/
theorem singleton_endpoints {H : PhysicalGraph} (C : PhysicalCorridor H)
    (e : H.Edge) (hs : C.support = {e}) :
    (corridorStart C = H.src e ∧ corridorFinish C = H.dst e) ∨
      (corridorStart C = H.dst e ∧ corridorFinish C = H.src e) := by
  have hlen : C.edges.length = 1 := by
    have hc := C.support_card_eq_length
    rw [hs] at hc
    simpa using hc.symm
  have hvlen : C.vertices.length = 2 := by rw [C.vertices_length, hlen]
  have hedge : C.edges.get ⟨0, by omega⟩ = e := by
    have hm : e ∈ C.edges := List.mem_toFinset.mp (by change e ∈ C.support; rw [hs]; simp)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    have : i.val = 0 := by omega
    simpa [this] using hi
  have hstep := C.step ⟨0, by omega⟩
  simp only [hedge] at hstep
  rcases hstep with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
  · left
    constructor
    · simpa [corridorStart, List.head_eq_getElem_zero] using hsrc.symm
    · simpa [corridorFinish, List.getLast_eq_getElem, hvlen] using hdst.symm
  · right
    constructor
    · simpa [corridorStart, List.head_eq_getElem_zero] using hdst.symm
    · simpa [corridorFinish, List.getLast_eq_getElem, hvlen] using hsrc.symm

/-- A witness edge in the selected component is a physical support edge with
exactly the same original endpoints. -/
theorem witness_edge_lift (e : G.Edge) (he : e ∈ I.witnessEdges)
    (hc : G.src e ∈ componentSupportFinset G c ∨ G.dst e ∈ componentSupportFinset G c) :
    ∃ a ∈ componentLocalWitnessPullback G c I,
      componentSupportVertexMap G c ((componentSupportPhysical G c).src a) = G.src e ∧
      componentSupportVertexMap G c ((componentSupportPhysical G c).dst a) = G.dst e := by
  classical
  obtain ⟨x, hx⟩ := I.witness_edges_active e he
  have hactive : e ∈ activeEdges G :=
    (mem_activeEdges_iff G e).mpr (active_of_cycle_coordinate_ne_zero G x e hx)
  let A := activeSubgraph G
  let eA : A.Edge := (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨e, hactive⟩
  have hs : A.src eA = G.src e := by simp [eA, A, activeSubgraph, PhysicalGraph.restrictPhysical]
  have ht : A.dst eA = G.dst e := by simp [eA, A, activeSubgraph, PhysicalGraph.restrictPhysical]
  have heComp : eA ∈ componentEdges G c :=
    activeEdge_mem_componentEdges_of_endpoint G c eA (by change A.src eA ∈ _ ∨ A.dst eA ∈ _; rw [hs, ht]; exact hc)
  let eR := (A.restrictedEdgeEquiv (componentEdges G c)).symm ⟨eA, heComp⟩
  let a := (componentSupportEdgeEquiv G c).symm eR
  have hmap : componentCorridorEdgeToOriginal G c (componentSupportEdgeEquiv G c a) = e := by
    simp [a, eR, eA, A, componentCorridorEdgeToOriginal]
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap.symm ▸ he⟩, ?_, ?_⟩
  · rw [← componentSupportEdgeEquiv_src, ← src_componentCorridorEdgeToOriginal, hmap]
  · rw [← componentSupportEdgeEquiv_dst, ← dst_componentCorridorEdgeToOriginal, hmap]

/-- Singleton witness corridors embed the original witness core in the
compressed multigraph. Thus compression does not invent witness components. -/
theorem witness_core_adj {q r : (compressedCorridorGraph D hend).Vertex}
    (h : (witnessCore I c D hend).Adj q r) :
    (compressedCorridorGraph D hend).toSimpleGraph.Adj q r := by
  classical
  obtain ⟨_, _, hne, e, he, horient⟩ := h
  have hq : originalVertex I c D hend q ∈ componentSupportFinset G c :=
    componentSupportVertexMap_mem_support G c _
  have heComp : G.src e ∈ componentSupportFinset G c ∨
      G.dst e ∈ componentSupportFinset G c := by
    rcases horient with h | h
    · exact Or.inl (h.1.symm ▸ hq)
    · exact Or.inr (h.2.symm ▸ hq)
  obtain ⟨a, ha, hsrc, hdst⟩ := witness_edge_lift I c e he heComp
  obtain ⟨C, hC, hCa⟩ := D.witness_singleton a ha
  have hmem : C ∈ corridorFamily D := by
    simp only [corridorFamily, Finset.mem_toList, List.mem_toFinset]
    exact hC
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
  change corridorAt D k = C at hk
  have hs : originalVertex I c D hend ((compressedCorridorGraph D hend).src k) =
      componentSupportVertexMap G c (corridorStart C) := by
    simp [originalVertex, hk, SingleCorridorRoute.corridorStart,
      SingleCorridorRoute.corridorFinish, corridorStart, corridorFinish]
  have ht : originalVertex I c D hend ((compressedCorridorGraph D hend).dst k) =
      componentSupportVertexMap G c (corridorFinish C) := by
    simp [originalVertex, hk, SingleCorridorRoute.corridorStart,
      SingleCorridorRoute.corridorFinish, corridorStart, corridorFinish]
  have hends := singleton_endpoints C a hCa
  have hi := originalVertex_injective I c D hend
  have hne' : q ≠ r := fun hqr => hne (congrArg (originalVertex I c D hend) hqr)
  refine ⟨hne', k, ?_⟩
  rcases hends with hh | hh <;> rcases horient with ho | ho
  · left
    exact ⟨hi (hs.trans ((congrArg _ hh.1).trans (hsrc.trans ho.1))),
      hi (ht.trans ((congrArg _ hh.2).trans (hdst.trans ho.2)))⟩
  · right
    exact ⟨hi (hs.trans ((congrArg _ hh.1).trans (hsrc.trans ho.1))),
      hi (ht.trans ((congrArg _ hh.2).trans (hdst.trans ho.2)))⟩
  · right
    exact ⟨hi (hs.trans ((congrArg _ hh.1).trans (hdst.trans ho.2))),
      hi (ht.trans ((congrArg _ hh.2).trans (hsrc.trans ho.1)))⟩
  · left
    exact ⟨hi (hs.trans ((congrArg _ hh.1).trans (hdst.trans ho.2))),
      hi (ht.trans ((congrArg _ hh.2).trans (hsrc.trans ho.1)))⟩

/-- Bad vertices retained in the selected compressed component. -/
def badVertices : Finset (compressedCorridorGraph D hend).Vertex := by
  classical
  exact Finset.univ.filter fun q => originalVertex I c D hend q ∈
    BadVertexCardinalityBound.badVertexSet G I.witnessEdges

theorem initial_protection_eq :
    componentSupportCompressedProtectedVertices G c D hend =
      witnessVertices I c D hend ∪ badVertices I c D hend := by
  classical
  ext q
  simp [componentSupportCompressedProtectedVertices, componentWitnessBadProtected,
    witnessVertices, badVertices, originalVertex]

theorem badVertices_card_lt (hR : 5 ≤ I.R) :
    (badVertices I c D hend).card < 520 * I.R := by
  classical
  have hcard : (badVertices I c D hend).card ≤
      (BadVertexCardinalityBound.badVertexSet G I.witnessEdges).card := by
    apply Finset.card_le_card_of_injOn (originalVertex I c D hend)
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · exact fun _ _ _ _ h => originalVertex_injective I c D hend h
  exact hcard.trans_lt
    (HighActiveConnectedBridge.badVertexSet_card_lt_520_mul_of_connected
      G I.witnessEdges I.R hR I.outside_probability I.graph_connected)

end Erdos1016.Proof.WitnessComponentProtection

end
