import Mathlib.Combinatorics.SimpleGraph.Metric
import Erdos1016.ExactMaximum.TwoCut

set_option autoImplicit false

/-!
# The two inputs of Theorem 5.4 from the forest estimate

Theorem 5.4 of the paper "The maximum number of cycles in a graph of large rank"
(`FewCyclesStatement`, for `ε = 1/1000`) uses the forest estimate at two places, both in the
proof of Proposition 5.3. This file states the two facts for a connected subcubic network with a
path `A` from `s` to `t` and with at least `0.501 · 2^b` paths from `s` to `t`. They are not
proved here.

* `PoleLayerBoundStatement` (Step 1): every distance layer from `s` has at most `Θ` vertices.
  In the paper this is Lemma 4.1 for the marked set `V(A)` of a shortest path `A`. The map
  `Q ↦ Q + A` sends the paths from `s` to `t` to even words whose edges outside `V(A)` form a
  forest, so more than half of the even words have this property.
* `PoleCyclePackingStatement` (Step 3): there are at most `k(d)` pairwise vertex-disjoint cycles
  with at most `d` edges that do not meet `A`. In the paper this is Lemma 2.5 for the vertex sets
  of the cycles, with the same map.

Steps 2 and 3 of that proof derive from these two facts that the part of the network outside a
shortest path has bounded rank. `PoleOutsideRankStatement` states this conclusion. It is the only
fact about forests that the rest of the proof of Theorem 5.4 uses: Lemma 5.2, Step 4 of
Proposition 5.3 and the count of Theorem 5.4 are about distance layers and count edges and
vertices.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Step 1 of the proof of Proposition 5.3.** There is a number `Θ` with this property. Let `N`
be a connected network in which `s` and `t` have degree at most three and every other vertex has
degree three. If at least `0.501 · 2^b` paths join `s` and `t`, then at most `Θ` vertices have
any given distance from `s`. Not proved in this file. -/
def PoleLayerBoundStatement : Prop :=
  ∃ Θ : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.graph.Connected → (∀ v, N.deg (fun _ => 1) v ≤ 3) →
    (∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3) → s ≠ t →
    501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
    ∀ j : ℕ, Nat.card {v : V // N.graph.dist s v = j} ≤ Θ

/-- **Step 3 of the proof of Proposition 5.3.** For every `d` there is a number `k` with this
property. Let `N` be a connected network with all degrees at most three, let `A` be a path from
`s` to `t`, and let at least `0.501 · 2^b` paths join `s` and `t`. Then every family of pairwise
vertex-disjoint cycles with at most `d` edges that do not meet `A` has at most `k` members. Not
proved in this file. -/
def PoleCyclePackingStatement : Prop :=
  ∀ d : ℕ, ∃ k : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V)
    (A : N.Word), N.graph.Connected → (∀ v, N.deg (fun _ => 1) v ≤ 3) → N.IsPathWord s t A →
    501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
    ∀ (ι : Type) [Fintype ι] (Z : ι → N.Word), (∀ i, N.IsCycleWord (Z i)) →
      (∀ i, N.VertexDisjoint (Z i) A) → (∀ i j, i ≠ j → N.VertexDisjoint (Z i) (Z j)) →
      (∀ i, size (Z i) ≤ d) → Fintype.card ι ≤ k

/-- **Steps 1 to 3 of the proof of Proposition 5.3.** There is a number `C` with this property.
Let `N` be a connected network in which `s` and `t` have degree at most two and every other
vertex has degree three. Let `A` be a shortest path from `s` to `t`, and let at least
`0.501 · 2^b` paths join `s` and `t`. Then the edges that have no end on `A` form a network of
rank at most `C`. Not proved in this file. -/
def PoleOutsideRankStatement : Prop :=
  ∃ C : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V) (A : N.Word),
    N.graph.Connected → N.deg (fun _ => 1) s ≤ 2 → N.deg (fun _ => 1) t ≤ 2 →
    (∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3) →
    N.IsPathWord s t A → size A = N.graph.dist s t →
    501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
    networkRank (N.sub fun e => N.deg A (N.src e) = 0 ∧ N.deg A (N.dst e) = 0) ≤ C

end Erdos1016.ExactMaximum
