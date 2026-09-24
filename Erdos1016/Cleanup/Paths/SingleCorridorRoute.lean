import Erdos1016.Graph.PathExpansion.RouteConstancy
import Erdos1016.Cleanup.Corridors.PhysicalPartition

set_option autoImplicit false

/-!
# Scratch adapter: one physical corridor as a path-bearing route

This file intentionally stays isolated from the umbrella.  It records the
remaining local incidence obligations as hypotheses, so a later construction
can replace those hypotheses with a proof from ambient degree-two data.
-/

noncomputable section

namespace Erdos1016.Proof.SingleCorridorRoute

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition

variable {G : PhysicalGraph}

/-- The physical graph viewed as a finite labelled multigraph. -/
def routeGraph (G : PhysicalGraph) : FiniteMultiGraph where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount
  src := G.src
  dst := G.dst

/-- A one-edge auxiliary multigraph, with two possibly identified images in
its physical vertex map. -/
def oneEdgeGraph : FiniteMultiGraph where
  vertexCount := 2
  edgeCount := 1
  src := fun _ => 0
  dst := fun _ => 1




def corridorStart (C : PhysicalCorridor G) : G.Vertex :=
  C.vertices.head (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))

def corridorFinish (C : PhysicalCorridor G) : G.Vertex :=
  C.vertices.getLast (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))

theorem corridorStart_head? (C : PhysicalCorridor G) :
    C.vertices.head? = some (corridorStart C) := by
  exact (List.head_eq_iff_head?_eq_some
    (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))).1 rfl

theorem corridorFinish_getLast? (C : PhysicalCorridor G) :
    C.vertices.getLast? = some (corridorFinish C) := by
  exact List.getLast?_eq_getLast_of_ne_nil
    (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))

/-- The indexed corridor edge/vertex pairs, converted to oriented path steps.
The proof in each item is exactly the corridor's recorded `step` field. -/
def corridorSteps (C : PhysicalCorridor G) :
    List (PathStep (routeGraph G)) :=
  List.ofFn fun i : Fin C.edges.length =>
    let e : G.Edge := C.edges.get i
    let u : G.Vertex := C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩
    let v : G.Vertex := C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩
    { startVertex := u
      edge := e
      endVertex := v
      endpoints := C.step i }

@[simp] theorem corridorSteps_length (C : PhysicalCorridor G) :
    (corridorSteps C).length = C.edges.length := by
  simp [corridorSteps]

/-- The edge list of the generated step sequence is the recorded corridor
edge list, so its finite support is exactly the corridor support. -/
theorem corridorSteps_edges (C : PhysicalCorridor G) :
    (corridorSteps C).map PathStep.edge = C.edges := by
  rw [corridorSteps, List.map_ofFn]
  change List.ofFn (C.edges.get) = C.edges
  exact List.ofFn_get _

/-- An explicitly supplied incidence certificate for the corridor support.
It is the endpoint-boundary condition needed to install this support as a
route in `EdgeDisjointRouteSystem`. -/
def CorridorEndpointBoundary (C : PhysicalCorridor G) (s t : G.Vertex) : Prop :=
  (routeGraph G).boundary (edgeSetWord (routeGraph G) C.support) =
    endpointDemand oneEdgeGraph (routeGraph G) (fun v : oneEdgeGraph.Vertex =>
      if v.val = 0 then s else t) ⟨0, by decide⟩





end Erdos1016.Proof.SingleCorridorRoute
