import Erdos1016.Graph.Basic

set_option autoImplicit false

/-!
# Finite physical corridor partition certificates

This module gives the concrete *certificate* shape needed for a physical
corridor decomposition.  Unlike `FiniteSeriesRouteDecomposition`, it has no
auxiliary multigraph or pre-existing route-system as input: a corridor is
given directly as an ordered physical edge/vertex chain, and the partition is
stated directly on the physical edge labels.  Endpoints are deliberately not
required to be distinct, so the certificate permits a corridor returning to
its initial protected vertex.

The existence of such a certificate for an arbitrary connected graph is not
proved here.  In particular, `maximal` below is part of the data and the
global finite construction from local degree-two components is still a
separate obligation.  The results here establish the exact edge-accounting
and path-length consequences of any supplied maximal certificate.
-/

noncomputable section

namespace Erdos1016.Proof.PhysicalPartition

open Erdos1016

variable {G : PhysicalGraph}

/-- A recorded physical edge path.  The `vertices` list has one more entry
than the edge list.  Each step uses its physical edge in either stored
orientation.  No endpoint-distinctness requirement is imposed. -/
structure PhysicalCorridor (G : PhysicalGraph) where
  edges : List G.Edge
  vertices : List G.Vertex
  vertices_length : vertices.length = edges.length + 1
  edges_nodup : edges.Nodup
  step : ∀ (i : Fin edges.length),
    let e := edges.get ⟨i.val, i.isLt⟩
    let u := vertices.get ⟨i.val, by rw [vertices_length]; omega⟩
    let v := vertices.get ⟨i.val + 1, by rw [vertices_length]; omega⟩
    (G.src e = u ∧ G.dst e = v) ∨ (G.dst e = u ∧ G.src e = v)

namespace PhysicalCorridor

def support (C : PhysicalCorridor G) : Finset G.Edge := C.edges.toFinset

/-- Number of physical edges on the corridor, equivalently its path length. -/
def length (C : PhysicalCorridor G) : ℕ := C.edges.length

theorem support_card_eq_length (C : PhysicalCorridor G) :
    C.support.card = C.length := by
  exact List.toFinset_card_of_nodup C.edges_nodup





end PhysicalCorridor

/-- A finite family of corridor certificates partitioning the physical edge
labels.  `maximal` says each path cannot be extended at either end through an
unprotected degree-two vertex.  Witness edges are required to appear as
singleton corridors; `witness_singleton` does not identify their endpoint
vertices, so a witness can coexist with a returning corridor elsewhere. -/
structure CorridorPartition (G : PhysicalGraph) (P₀ : Finset G.Vertex)
    (W : Finset G.Edge) where
  corridors : List (PhysicalCorridor G)
  edge_cover : ∀ e : G.Edge, ∃ C ∈ corridors, e ∈ C.support
  edge_disjoint : ∀ C ∈ corridors, ∀ D ∈ corridors,
    C ≠ D → Disjoint C.support D.support
  witness_singleton : ∀ e, e ∈ W → ∃ C ∈ corridors, C.support = {e}
  internal_unprotected_degree_two : ∀ C ∈ corridors,
    ∀ i : Fin (C.vertices.length - 2),
      let v := C.vertices.get ⟨i.val + 1, by
        have h := C.vertices_length
        omega⟩
      v ∉ P₀ ∧ G.degree v = 2
  maximal : ∀ C ∈ corridors,
    ∀ e : G.Edge, e ∉ C.support →
      (∃ v, v ∉ P₀ ∧ G.degree v = 2 ∧
        ((G.src e = v ∧ (∃ f ∈ C.support, G.dst f = v ∨ G.src f = v)) ∨
         (G.dst e = v ∧ (∃ f ∈ C.support, G.dst f = v ∨ G.src f = v)))) →
      False

namespace CorridorPartition

variable {P₀ : Finset G.Vertex} {W : Finset G.Edge}







end CorridorPartition

end Erdos1016.Proof.PhysicalPartition
