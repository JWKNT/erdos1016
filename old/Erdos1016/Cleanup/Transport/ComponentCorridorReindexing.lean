import Erdos1016.Cleanup.Compression.PartitionRouteDecomposition
import Erdos1016.Cleanup.Transport.ComponentMarginalData

set_option autoImplicit false

/-!
# Reindex selected-component corridors to the original physical graph

The selected component graph only reindexes edges. A corridor in that graph
therefore transports to the original physical graph by composing the two
restricted-edge equivalences and keeping its vertex list unchanged.
-/

noncomputable section

namespace Erdos1016.Proof.ComponentCorridorReindexing

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.ComponentMarginalData
open Erdos1016.Proof.SelectedComponentRoutes
open Erdos1016.Proof.PartitionRouteDecomposition

open Erdos1016.Proof.SingleCorridorRoute

def componentCorridorEdgeToOriginal (G : PhysicalGraph)
    (c : ActiveComponent G)
    (p : ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge) : G.Edge :=
  (G.restrictedEdgeEquiv (activeEdges G)
    (((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) p).1)).1

theorem componentCorridorEdgeToOriginal_injective (G : PhysicalGraph)
    (c : ActiveComponent G) :
    Function.Injective (componentCorridorEdgeToOriginal G c) := by
  intro p q hpq
  apply (activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) |>.injective
  apply Subtype.ext
  apply (G.restrictedEdgeEquiv (activeEdges G)).injective
  apply Subtype.ext
  exact hpq

theorem src_componentCorridorEdgeToOriginal (G : PhysicalGraph)
    (c : ActiveComponent G)
    (p : ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge) :
    G.src (componentCorridorEdgeToOriginal G c p) =
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).src p := by
  rfl

theorem dst_componentCorridorEdgeToOriginal (G : PhysicalGraph)
    (c : ActiveComponent G)
    (p : ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge) :
    G.dst (componentCorridorEdgeToOriginal G c p) =
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).dst p := by
  rfl

/-- Reindex a component corridor to a corridor in the original graph. -/
def componentCorridorToOriginal (G : PhysicalGraph)
    (c : ActiveComponent G)
    (C : PhysicalCorridor
      ((activeSubgraph G).restrictPhysical (componentEdges G c))) :
    PhysicalCorridor G where
  edges := C.edges.map (componentCorridorEdgeToOriginal G c)
  vertices := C.vertices
  vertices_length := by simpa using C.vertices_length
  edges_nodup := C.edges_nodup.map_on (fun p _ q _ hpq =>
    componentCorridorEdgeToOriginal_injective G c hpq)
  step := by
    intro i
    let i' : Fin C.edges.length := ⟨i.val, by simpa using i.isLt⟩
    have hi := C.step i'
    dsimp
    simpa [i', List.get_eq_getElem, List.getElem_map,
      src_componentCorridorEdgeToOriginal,
      dst_componentCorridorEdgeToOriginal] using hi

/-- The component corridor support maps exactly to the original support. -/
theorem componentCorridorToOriginal_support (G : PhysicalGraph)
    (c : ActiveComponent G)
    (C : PhysicalCorridor
      ((activeSubgraph G).restrictPhysical (componentEdges G c))) :
    (componentCorridorToOriginal G c C).support =
      C.support.image (componentCorridorEdgeToOriginal G c) := by
  classical
  ext e
  simp [PhysicalCorridor.support, componentCorridorToOriginal,
    Finset.mem_image, List.mem_toFinset, List.mem_map]

/-- Support membership transfers under the corridor reindexing. -/
theorem componentCorridor_support_mem_transfer (G : PhysicalGraph)
    (c : ActiveComponent G)
    (C : PhysicalCorridor
      ((activeSubgraph G).restrictPhysical (componentEdges G c)))
    {p : ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge}
    (hp : p ∈ C.support) :
    componentCorridorEdgeToOriginal G c p ∈
      (componentCorridorToOriginal G c C).support := by
  rw [componentCorridorToOriginal_support]
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

















end Erdos1016.Proof.ComponentCorridorReindexing

end
