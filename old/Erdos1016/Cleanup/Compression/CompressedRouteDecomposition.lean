import Erdos1016.Cleanup.Compression.PartitionRouteDecomposition
import Erdos1016.Cleanup.Transport.SelectedComponentRoutes

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CompressedRouteDecomposition

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.DegreeTwoCorridorRoutes
open Erdos1016.Proof.EndpointBoundary
open Erdos1016.Proof.PartitionRouteDecomposition
open Erdos1016.Proof.SelectedComponentRoutes
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents

variable {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}

local notation "Q" => protectedOrBranch G P₀

/-- Index the retained physical vertices by `Fin Q.card`. -/
def retainedVertexEquiv :
    Fin (protectedOrBranch G P₀).card ≃
      {v : G.Vertex // v ∈ protectedOrBranch G P₀} :=
  (Finset.equivFin (protectedOrBranch G P₀)).symm

/-- The auxiliary graph has one vertex per protected-or-branch vertex and
one edge per corridor. Degree-two corridor interiors are suppressed. -/
def compressedCorridorGraph (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) : FiniteMultiGraph where
  vertexCount := (protectedOrBranch G P₀).card
  edgeCount := (corridorFamily D).length
  src e := (Finset.equivFin (protectedOrBranch G P₀))
    ⟨corridorStart (corridorAt D e),
    hendpoints (corridorAt D e) (corridorAt_mem D e) |>.1⟩
  dst e := (Finset.equivFin (protectedOrBranch G P₀))
    ⟨corridorFinish (corridorAt D e),
    hendpoints (corridorAt D e) (corridorAt_mem D e) |>.2⟩

def compressedCorridorVertexMap (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) :
    (compressedCorridorGraph D hendpoints).Vertex → G.Vertex := fun v =>
  (retainedVertexEquiv (G := G) (P₀ := P₀)) v |>.1

theorem compressedCorridorVertexMap_injective (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) :
    Function.Injective (compressedCorridorVertexMap D hendpoints) := by
  intro v w hvw
  apply (retainedVertexEquiv (G := G) (P₀ := P₀)).injective
  exact Subtype.ext hvw

@[simp] theorem compressedCorridor_src_image (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q)
    (e : (compressedCorridorGraph D hendpoints).Edge) :
    compressedCorridorVertexMap D hendpoints
      ((compressedCorridorGraph D hendpoints).src e) =
        corridorStart (corridorAt D e) := by
  simp [compressedCorridorVertexMap, compressedCorridorGraph, retainedVertexEquiv]

@[simp] theorem compressedCorridor_dst_image (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q)
    (e : (compressedCorridorGraph D hendpoints).Edge) :
    compressedCorridorVertexMap D hendpoints
      ((compressedCorridorGraph D hendpoints).dst e) =
        corridorFinish (corridorAt D e) := by
  simp [compressedCorridorVertexMap, compressedCorridorGraph, retainedVertexEquiv]

/-- Install all partition corridors as routes in the suppressed graph. -/
def compressedCorridorRouteSystem (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) :
    EdgeDisjointRouteSystem (compressedCorridorGraph D hendpoints) (routeGraph G) := by
  classical
  refine {
    vertexMap := compressedCorridorVertexMap D hendpoints
    support := fun e => (corridorAt D e).support
    endpoint := ?_
    disjoint := ?_
    nonempty := ?_ }
  · intro e
    let C := corridorAt D e
    have hb := EndpointBoundary.corridorEndpointBoundary C
    have hdem :
        endpointDemand (compressedCorridorGraph D hendpoints) (routeGraph G)
          (compressedCorridorVertexMap D hendpoints) e =
        endpointDemand oneEdgeGraph (routeGraph G)
          (fun v => if v.val = 0 then corridorStart C else corridorFinish C)
          ⟨0, by decide⟩ := by
      ext v
      simp [FiniteMultiGraph.endpointDemand, oneEdgeGraph,
        compressedCorridorGraph, compressedCorridorVertexMap,
        retainedVertexEquiv, C]
    exact hb.trans hdem.symm
  · intro e f hef
    have hget : Function.Injective (corridorFamily D).get :=
      (List.nodup_iff_injective_get).mp (Finset.nodup_toList D.corridors.toFinset)
    have hCne : corridorAt D e ≠ corridorAt D f := by
      intro h
      exact hef (hget h)
    exact D.edge_disjoint (corridorAt D e) (corridorAt_mem D e)
      (corridorAt D f) (corridorAt_mem D f) hCne
  · intro e
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil (corridorAt D e).edges
      (hnonempty (corridorAt D e) (corridorAt_mem D e))
    exact ⟨p, by rw [PhysicalCorridor.support]; exact List.mem_toFinset.mpr hp⟩

private theorem corridorAt_internal_degree_two (D : CorridorPartition G P₀ W)
    (e : Fin (corridorFamily D).length) :
    InternalVerticesDegreeTwo (corridorAt D e) := by
  intro i
  have hC : corridorAt D e ∈ D.corridors := corridorAt_mem D e
  have hlen : (corridorAt D e).vertices.length - 2 =
      (corridorAt D e).edges.length - 1 := by
    have hverts := (corridorAt D e).vertices_length
    omega
  let j : Fin ((corridorAt D e).vertices.length - 2) := ⟨i.val, by
    rw [hlen]
    exact i.isLt⟩
  have hj := D.internal_unprotected_degree_two (corridorAt D e) hC j
  have hd : G.degree ((corridorAt D e).vertices.get ⟨j.val + 1, by
      have hh := (corridorAt D e).vertices_length
      omega⟩) = 2 := hj.2
  simpa [j] using hd

/-- The suppressed routes retain the explicit linked-step path witnesses. -/
def compressedCorridorPaths (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) :
    PathBearingRouteSystem (compressedCorridorRouteSystem D hnonempty hendpoints) := by
  classical
  refine {
    steps := fun e => corridorSteps (corridorAt D e)
    nonempty := ?_
    chain := ?_
    support_eq := ?_
    start := ?_
    finish := ?_ }
  · intro e
    exact corridorSteps_ne_nil (corridorAt D e)
      (hnonempty (corridorAt D e) (corridorAt_mem D e))
  · intro e
    exact corridorSteps_chain_of_internal_degree_two (corridorAt D e)
      (corridorAt_internal_degree_two D e)
  · intro e
    rw [corridorSteps_edges]
    rfl
  · intro e
    let C := corridorAt D e
    have hne := corridorSteps_ne_nil C (hnonempty C (corridorAt_mem D e))
    refine ⟨(corridorSteps C).head hne, ?_, ?_⟩
    · exact (List.head_eq_iff_head?_eq_some hne).1 rfl
    · change ((corridorSteps C).head hne).startVertex =
        compressedCorridorVertexMap D hendpoints
          ((compressedCorridorGraph D hendpoints).src e)
      rw [compressedCorridor_src_image]
      rw [corridorSteps_head_start C (hnonempty C (corridorAt_mem D e))]
  · intro e
    let C := corridorAt D e
    have hne := corridorSteps_ne_nil C (hnonempty C (corridorAt_mem D e))
    refine ⟨(corridorSteps C).getLast hne, ?_, ?_⟩
    · exact List.getLast?_eq_getLast_of_ne_nil hne
    · change ((corridorSteps C).getLast hne).endVertex =
        compressedCorridorVertexMap D hendpoints
          ((compressedCorridorGraph D hendpoints).dst e)
      rw [compressedCorridor_dst_image]
      rw [corridorSteps_last_end C (hnonempty C (corridorAt_mem D e))]

/-- Route partition data with an injective retained-vertex map. Its expansion
induces a cycle-space equivalence even though suppressed physical vertices
are absent from the auxiliary graph. -/
structure CompressedCorridorDecomposition (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) where
  paths : PathBearingRouteSystem (compressedCorridorRouteSystem D hnonempty hendpoints)
  edgeLabels_nodup : ∀ e,
    ((paths.steps e).map PathStep.edge).Nodup
  vertexMap_injective : Function.Injective
    (compressedCorridorVertexMap D hendpoints)
  physical_edge_coverage : ∀ p : (routeGraph G).Edge,
    ∃ e, p ∈ (compressedCorridorRouteSystem D hnonempty hendpoints).support e

noncomputable def compressedCorridorDecomposition
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) :
    CompressedCorridorDecomposition D hnonempty hendpoints := by
  classical
  refine ⟨compressedCorridorPaths D hnonempty hendpoints, ?_,
    compressedCorridorVertexMap_injective D hendpoints, ?_⟩
  · intro e
    change ((corridorSteps (corridorAt D e)).map PathStep.edge).Nodup
    rw [corridorSteps_edges]
    exact (corridorAt D e).edges_nodup
  · intro p
    obtain ⟨C, hC, hp⟩ := D.edge_cover p
    have hCfin : C ∈ D.corridors.toFinset := List.mem_toFinset.mpr hC
    have hCList : C ∈ corridorFamily D := Finset.mem_toList.mpr hCfin
    obtain ⟨e, he⟩ := List.mem_iff_get.mp hCList
    refine ⟨e, ?_⟩
    change p ∈ ((corridorFamily D).get e).support
    rw [he]
    exact hp

noncomputable def compressedCorridor_cycleEquiv (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) :
    (compressedCorridorGraph D hendpoints).CycleSpace ≃ₗ[ZMod 2]
      (routeGraph G).CycleSpace := by
  let T := compressedCorridorDecomposition D hnonempty hendpoints
  exact cycleExpandEquiv_of_injective
    (compressedCorridorRouteSystem D hnonempty hendpoints)
    T.vertexMap_injective T.physical_edge_coverage
    (PathBearingRouteSystem.cycle_word_constant_on_support
      (compressedCorridorRouteSystem D hnonempty hendpoints) T.paths)

end Erdos1016.Proof.CompressedRouteDecomposition

end
