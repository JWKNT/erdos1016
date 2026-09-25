import Erdos1016.Cleanup.Paths.CorridorTerminalEdges
import Erdos1016.Cleanup.Transport.CorridorRouteEquivalence

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ReducedRouteEndpointLabels

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.CorridorTerminalEdges
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.CorridorRouteEquivalence

open Erdos1016.Proof.SingleCorridorRoute

/-- Corridor head/last options determine the source and target endpoint
labels needed by reduced cleanup event transport. In the reversed orientation
the endpoint labels are swapped. The only construction inputs are nonempty
corridors and endpoint-option alignment to the mapped auxiliary endpoints. -/
theorem endpoint_edges_of_corridor_endpoint_options
    {G : PhysicalGraph} {Γ : FiniteMultiGraph}
    (vertexMap : Γ.Vertex → G.Vertex)
    (edgePath : Γ.Edge → PhysicalCorridor G)
    (hnonempty : ∀ e, (edgePath e).edges ≠ [])
    (hpathEndpoints : ∀ e,
      (((edgePath e).vertices.head? = some (vertexMap (Γ.src e)) ∧
        (edgePath e).vertices.getLast? = some (vertexMap (Γ.dst e))) ∨
       ((edgePath e).vertices.head? = some (vertexMap (Γ.dst e)) ∧
        (edgePath e).vertices.getLast? = some (vertexMap (Γ.src e))))) :
    ∀ e, ∃ p q : G.Edge,
      p ∈ (edgePath e).support ∧ q ∈ (edgePath e).support ∧
      G.incident p (vertexMap (Γ.src e)) ∧
      G.incident q (vertexMap (Γ.dst e)) := by
  intro e
  rcases hpathEndpoints e with hforward | hreverse
  · obtain ⟨p, q, hp, hq, hpi, hqi⟩ :=
      endpoint_edges (edgePath e) (hnonempty e)
        (vertexMap (Γ.src e)) (vertexMap (Γ.dst e)) hforward.1 hforward.2
    exact ⟨p, q, hp, hq, hpi, hqi⟩
  · obtain ⟨p, q, hp, hq, hpi, hqi⟩ :=
      endpoint_edges (edgePath e) (hnonempty e)
        (vertexMap (Γ.dst e)) (vertexMap (Γ.src e)) hreverse.1 hreverse.2
    exact ⟨q, p, hq, hp, hqi, hpi⟩







end Erdos1016.Proof.ReducedRouteEndpointLabels

end
