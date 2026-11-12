import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false

/-!
# The local structure of a cycle in a pole: two statements

The count of Theorem 5.4 of the paper "The maximum number of cycles in a graph of large rank"
uses two local facts about a bridgeless pole with the two ports `s`, `t`. This file has the
definitions and the statements. It proves nothing.

* `IsLayerEdge`: the edge joins the layers `l` and `l + 1`.
* `IsLayerMatching`: a word within these edges in which every vertex of the two layers has
  exactly one edge. For two thin layers this is a perfect matching between them.
* `TwoStrandsStatement` (the paragraph "Two strands"): let the cycle `Z` have a vertex before
  the thin layer `l` and a vertex after it. Then `Z` has no edge inside the layer, and each of
  the two vertices of the layer has exactly one edge of `Z` to the layer `l - 1` and exactly one
  to the layer `l + 1`.
* `LayerMatchingStatement` (the paragraph "Matchings"): two consecutive ordinary layers have at
  most two perfect matchings, and for three consecutive ordinary layers the two numbers of
  perfect matchings have sum at most three.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance poleMatchingsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The edge joins a vertex at distance `l` and a vertex at distance `l + 1` from `s`. -/
def IsLayerEdge (N : Network V E) (s : V) (l : ℕ) (g : E) : Prop :=
  (N.graph.dist s (N.src g) = l ∧ N.graph.dist s (N.dst g) = l + 1) ∨
    (N.graph.dist s (N.src g) = l + 1 ∧ N.graph.dist s (N.dst g) = l)

/-- A word within the edges between the layers `l` and `l + 1` in which every vertex of these
two layers has exactly one edge. -/
def IsLayerMatching (N : Network V E) (s : V) (l : ℕ) (m : N.Word) : Prop :=
  Within m (N.IsLayerEdge s l) ∧
    ∀ v, N.graph.dist s v = l ∨ N.graph.dist s v = l + 1 → N.deg m v = 1

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleMatchingsDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Two strands.** Let `N` be a bridgeless pole with the two ports `s`, `t`, let the layer `l`
be thin, and let the cycle `Z` have a vertex at a smaller distance from `s` and a vertex at a
larger distance. Then `Z` has no edge inside the layer `l`, and each vertex of the layer has
exactly one edge of `Z` to the layer `l - 1` and exactly one edge of `Z` to the layer `l + 1`.
Not proved in this file. -/
def TwoStrandsStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.IsBridgelessTwoPole s t → ∀ (Z : N.Word) (l : ℕ), N.IsCycleWord Z →
    N.IsThinLayer s t l → (∃ u, 0 < N.deg Z u ∧ N.graph.dist s u < l) →
    (∃ w, 0 < N.deg Z w ∧ l < N.graph.dist s w) →
    (∀ g, N.graph.dist s (N.src g) = l → N.graph.dist s (N.dst g) = l → Z g = 0) ∧
      ∀ v, N.graph.dist s v = l →
        N.deg (restrict Z (N.IsLayerEdge s (l - 1))) v = 1 ∧
          N.deg (restrict Z (N.IsLayerEdge s l)) v = 1

/-- **Matchings.** Let `N` be a bridgeless pole with the two ports `s`, `t`, and let the layers
`l` and `l + 1` be ordinary. Then there are at most two perfect matchings between them. If the
layer `l + 2` is ordinary too, then the numbers of perfect matchings between `l`, `l + 1` and
between `l + 1`, `l + 2` have sum at most three. Not proved in this file. -/
def LayerMatchingStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.IsBridgelessTwoPole s t → ∀ l : ℕ, N.IsOrdinaryLayer s t l →
    N.IsOrdinaryLayer s t (l + 1) →
    Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2 ∧
      (N.IsOrdinaryLayer s t (l + 2) →
        Nat.card {m : N.Word // N.IsLayerMatching s l m} +
          Nat.card {m : N.Word // N.IsLayerMatching s (l + 1) m} ≤ 3)

end Erdos1016.ExactMaximum
