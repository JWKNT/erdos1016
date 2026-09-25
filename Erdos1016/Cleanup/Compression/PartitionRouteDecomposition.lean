import Erdos1016.Cleanup.Corridors.EndpointBoundary

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PartitionRouteDecomposition

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.EndpointBoundary


variable {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}

/-- Deduplicate a corridor list before using its elements as auxiliary edges.
The certificate only requires pairwise disjointness for distinct corridor
values, so indexing the original list directly would be needlessly fragile. -/
noncomputable def corridorFamily (D : CorridorPartition G P₀ W) :
    List (PhysicalCorridor G) := by
  classical
  exact D.corridors.toFinset.toList

def corridorAt (D : CorridorPartition G P₀ W)
    (e : Fin (corridorFamily D).length) : PhysicalCorridor G :=
  (corridorFamily D).get e

theorem corridorAt_mem (D : CorridorPartition G P₀ W)
    (e : Fin (corridorFamily D).length) : corridorAt D e ∈ D.corridors := by
  classical
  have hmem := List.get_mem (corridorFamily D) e
  change (corridorAt D e) ∈ D.corridors.toFinset.toList at hmem
  have hfin : corridorAt D e ∈ D.corridors.toFinset :=
    Finset.mem_toList.mp hmem
  exact List.mem_toFinset.mp hfin

/-- The auxiliary graph has one edge per distinct corridor and keeps all
physical vertices. Degree-two interior vertices become isolated auxiliary
vertices, which preserves the identity vertex map used by route expansion. -/
def corridorAuxGraph (D : CorridorPartition G P₀ W) : FiniteMultiGraph where
  vertexCount := G.vertexCount
  edgeCount := (corridorFamily D).length
  src := fun e => corridorStart (corridorAt D e)
  dst := fun e => corridorFinish (corridorAt D e)

/-- The disjoint route system carried by a corridor partition. -/
def corridorRouteSystem (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ []) :
    EdgeDisjointRouteSystem (corridorAuxGraph D) (routeGraph G) := by
  classical
  refine {
    vertexMap := fun v => v
    support := fun e => (corridorAt D e).support
    endpoint := ?_
    disjoint := ?_
    nonempty := ?_ }
  · intro e
    let C := corridorAt D e
    have hboundary := EndpointBoundary.corridorEndpointBoundary C
    rw [hboundary]
    ext v
    simp [C, corridorAuxGraph, endpointDemand, oneEdgeGraph]
  · intro e f hef
    have hget : Function.Injective (corridorFamily D).get :=
      (List.nodup_iff_injective_get).mp (Finset.nodup_toList D.corridors.toFinset)
    have hCne : corridorAt D e ≠ corridorAt D f := by
      intro h
      exact hef (hget h)
    have hC := corridorAt_mem D e
    have hF := corridorAt_mem D f
    exact D.edge_disjoint (corridorAt D e) hC (corridorAt D f) hF hCne
  · intro e
    have hmem := corridorAt_mem D e
    have hne := hnonempty (corridorAt D e) hmem
    cases he : (corridorAt D e).edges with
    | nil => exact (hne he).elim
    | cons p ps =>
      refine ⟨p, ?_⟩
      rw [PhysicalCorridor.support]
      exact List.mem_toFinset.mpr (by simp [he])











end Erdos1016.Proof.PartitionRouteDecomposition

end
