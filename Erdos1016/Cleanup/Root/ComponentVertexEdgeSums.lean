import Erdos1016.Cleanup.Root.OutsideComponentPartitions

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ComponentVertexEdgeSums

open Erdos1016
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.OutsideComponentPartitions
open Erdos1016.Proof.CleanupSpecification

/-- The sizes of the outside components partition the complement of the
protected vertices. -/
theorem outsideComponentVertices_card_sum
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (∑ c : OutsideComponent Γ P,
      (outsideComponentVertices Γ P c).card) = Pᶜ.card :=
  sum_outside_component_vertex_card Γ P

/-- The internal edge sets of the outside components partition all edges
whose two endpoints lie outside the protected vertices. -/
theorem outsideComponent_internalEdges_card_sum
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (∑ c : OutsideComponent Γ P,
      (internalEdges Γ (outsideComponentVertices Γ P c)).card) =
        (internalEdges Γ Pᶜ).card :=
  sum_outside_component_internal_edge_card Γ P

end Erdos1016.Proof.ComponentVertexEdgeSums

end
