import Erdos1016.Cleanup.Paths.SingleCorridorRoute
import Erdos1016.Cleanup.Compression.SingleSeriesRouteCompression

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.EndpointBoundary

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleSeriesRouteCompression

variable {G : PhysicalGraph}

private def corridorEdgeAt (C : PhysicalCorridor G) :
    Fin C.edges.length → (routeGraph G).Edge := fun i => C.edges.get i

private def corridorVertexAt (C : PhysicalCorridor G) :
    Fin (C.edges.length + 1) → (routeGraph G).Vertex := fun i =>
  C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩

private theorem corridorEdgeAt_injective (C : PhysicalCorridor G) :
    Function.Injective (corridorEdgeAt C) := by
  intro i j hij
  change C.edges.get i = C.edges.get j at hij
  exact (List.nodup_iff_injective_get.mp C.edges_nodup) hij

private theorem corridorEdgeAt_image (C : PhysicalCorridor G) :
    Finset.univ.image (corridorEdgeAt C) = C.support := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, -, hi⟩
    rw [← hi, PhysicalCorridor.support]
    exact List.mem_toFinset.mpr (List.get_mem C.edges i)
  · intro he
    have he' : e ∈ C.edges := List.mem_toFinset.mp he
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he'
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

private theorem corridorEdgeAt_endpointDemand_eq_pairDemand (C : PhysicalCorridor G)
    (i : Fin C.edges.length) :
    endpointDemand (routeGraph G) (routeGraph G) (fun x => x)
        (corridorEdgeAt C i) =
      PathBoundaryTelescoping.pairDemand (routeGraph G)
        (corridorVertexAt C i.castSucc) (corridorVertexAt C i.succ) := by
  classical
  ext v
  have hi := C.step i
  dsimp [corridorEdgeAt, corridorVertexAt] at hi ⊢
  rcases hi with hi | hi
  · simpa [routeGraph, endpointDemand, PathBoundaryTelescoping.pairDemand,
      hi.1, hi.2, Fin.succ, Nat.add_comm]
  · simp [routeGraph, endpointDemand, PathBoundaryTelescoping.pairDemand,
      hi.1, hi.2, Fin.succ, Nat.add_comm]
    ring

private theorem corridorEndpoints_are_start_finish (C : PhysicalCorridor G) :
    corridorVertexAt C 0 = corridorStart C ∧
    corridorVertexAt C (Fin.last C.edges.length) = corridorFinish C := by
  constructor
  · simp [corridorVertexAt, corridorStart, List.head_eq_getElem_zero,
      C.vertices_length]
  · simp [corridorVertexAt, corridorFinish, List.getLast_eq_getElem,
      C.vertices_length]

/-- The boundary of the indicator word of any recorded corridor is exactly
the two endpoint demands. The proof needs only the ordered corridor steps,
edge-label injectivity, and mod-two path telescoping. -/
theorem corridorEndpointBoundary
    (C : PhysicalCorridor G) :
    CorridorEndpointBoundary C (corridorStart C) (corridorFinish C) := by
  classical
  let pathVertex := corridorVertexAt C
  let pathEdge := corridorEdgeAt C
  have hinj := corridorEdgeAt_injective C
  have himage := corridorEdgeAt_image C
  unfold CorridorEndpointBoundary
  rw [← himage]
  rw [SingleSeriesRouteCompression.boundary_image_path_eq_endpoint_sum
    (routeGraph G) pathEdge hinj]
  rw [show (∑ i : Fin C.edges.length,
      endpointDemand (routeGraph G) (routeGraph G) (fun x => x) (pathEdge i)) =
      ∑ i : Fin C.edges.length,
        PathBoundaryTelescoping.pairDemand (routeGraph G)
          (pathVertex i.castSucc) (pathVertex i.succ) by
        apply Finset.sum_congr rfl
        intro i hi
        exact corridorEdgeAt_endpointDemand_eq_pairDemand C i]
  rw [PathBoundaryTelescoping.path_pairDemand_sum
    (routeGraph G) pathVertex]
  obtain ⟨hstart, hfinish⟩ := corridorEndpoints_are_start_finish C
  ext v
  simp [CorridorEndpointBoundary, endpointDemand,
    PathBoundaryTelescoping.pairDemand, oneEdgeGraph,
    corridorStart, corridorFinish, pathVertex, hstart, hfinish]

end Erdos1016.Proof.EndpointBoundary

end
