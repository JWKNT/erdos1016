import Erdos1016.CycleSpace.Parity

set_option autoImplicit false

/-!
# Finite labelled multigraphs over `F₂`

An edge is a label, not an unordered pair of vertices. Thus distinct labels may
have the same endpoints, and an edge may have equal endpoints (a loop).
The boundary records both endpoints, so a loop contributes twice and hence
vanishes over `F₂`, as required for the usual mod-two cycle space.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016

/-- A finite multigraph with explicitly labelled vertices and edges.
`src` and `dst` are only an orientation convention for storing endpoints. -/
structure FiniteMultiGraph where
  vertexCount : ℕ
  edgeCount : ℕ
  src : Fin edgeCount → Fin vertexCount
  dst : Fin edgeCount → Fin vertexCount

namespace FiniteMultiGraph

abbrev Vertex (G : FiniteMultiGraph) := Fin G.vertexCount
abbrev Edge (G : FiniteMultiGraph) := Fin G.edgeCount
abbrev EdgeWord (G : FiniteMultiGraph) := G.Edge → F₂
abbrev Demand (G : FiniteMultiGraph) := G.Vertex → F₂

/-- Binary incidence boundary. Loops occur in both summands at the same
vertex, and therefore cancel in characteristic two. -/
def boundary (G : FiniteMultiGraph) : G.EdgeWord →ₗ[F₂] G.Demand where
  toFun x v := ∑ e,
    ((if G.src e = v then x e else 0) +
     (if G.dst e = v then x e else 0))
  map_add' x y := by
    funext v
    change (∑ e, ((if G.src e = v then x e + y e else 0) +
      (if G.dst e = v then x e + y e else 0))) = _ + _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
      simp [hs, ht] <;> ring
  map_smul' a x := by
    funext v
    change (∑ e, ((if G.src e = v then a * x e else 0) +
      (if G.dst e = v then a * x e else 0))) =
      a * ∑ e, ((if G.src e = v then x e else 0) +
      (if G.dst e = v then x e else 0))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
      simp [hs, ht] <;> ring

/-- The mod-two cycle space is the kernel of the incidence boundary. -/
abbrev CycleSpace (G : FiniteMultiGraph) := LinearMap.ker G.boundary

/-- First Betti number, defined as the dimension of the binary cycle space. -/
def cycleRank (G : FiniteMultiGraph) : ℕ :=
  Module.finrank F₂ G.CycleSpace

/-- Rank of the boundary image. -/
def boundaryRank (G : FiniteMultiGraph) : ℕ :=
  Module.finrank F₂ (LinearMap.range G.boundary)

/-- Rank-nullity for the edge boundary: cycle rank plus boundary rank equals
the number of labelled edges, counting loops and parallel copies. -/
theorem cycleRank_add_boundaryRank (G : FiniteMultiGraph) :
    G.cycleRank + G.boundaryRank = G.edgeCount := by
  have h := G.boundary.finrank_range_add_finrank_ker
  have he : Module.finrank F₂ (G.Edge → F₂) = G.edgeCount := by simp
  simpa [cycleRank, boundaryRank, EdgeWord, he, add_comm] using h

noncomputable instance cycleSpaceFintype (G : FiniteMultiGraph) :
    Fintype G.CycleSpace := Fintype.ofFinite _

@[simp] theorem cycleSpace_card (G : FiniteMultiGraph) :
    Fintype.card G.CycleSpace = 2 ^ G.cycleRank := by
  have h := Module.card_eq_pow_finrank (K := F₂) (V := G.CycleSpace)
  simpa [F₂, cycleRank] using h







end FiniteMultiGraph
end Erdos1016
