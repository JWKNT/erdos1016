import Erdos1016.ExactMaximum.Poles

set_option autoImplicit false

/-!
# A cubic cyclic shore in a pole with many paths: a statement

Corollary 5.6 of the paper "The maximum number of cycles in a graph of large rank" is about a
pole `K` inside a cubic multigraph `G` without a cyclic cut of size at most four: if `K` has few
ports and large rank, then fewer than `(1/2 + ε) 2^b` paths join two of its ports. The proof finds
a cyclic cut of `G` of size at most four inside `K`.

This file states the part of the corollary that is about the pole alone. It proves nothing. A
*cubic cyclic shore* of `K` is a set `S` of vertices of degree three such that at most four edges
leave `S` and both sides contain a cycle. The statement says that a pole with few ports, large
rank and many paths between two ports has a cubic cyclic shore. In a cubic multigraph `G` that
contains `K`, all edges of `G` at a vertex of `S` are edges of `K`, so `S` is a cyclic cut of `G`
of size at most four.

The margin is `ε = 2^(-m)`: the hypothesis `(2^m + 2) 2^b ≤ 2^(m+1) P` says
`P ≥ (1/2 + 2^(-m)) 2^b`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance cyclicShoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Corollary 5.6 of the paper, for the pole alone.** For all numbers `m` and `g` there is a
number `B` with this property. Let `K` be a pole of rank `b ≥ B` with at most `g + 2` ports, and
let at least `(1/2 + 2^(-m)) 2^b` paths join two different ports. Then some set `S` of vertices of
degree three is a cyclic cut of `K` with at most four crossing edges. Not proved in this file. -/
def CyclicShoreStatement : Prop :=
  ∀ m g : ℕ, ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
    Nat.card {v : V // K.IsPort v} ≤ g + 2 → B ≤ networkRank K →
    ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
      (2 ^ m + 2) * 2 ^ networkRank K ≤ 2 ^ (m + 1) * K.numPaths s t →
      ∃ S : V → Prop, K.IsCyclicCut S ∧ K.cutSize S ≤ 4 ∧
        ∀ v, S v → K.deg (fun _ => 1) v = 3

end Erdos1016.ExactMaximum
