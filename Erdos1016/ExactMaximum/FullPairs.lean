import Erdos1016.ExactMaximum.Poles
import Erdos1016.ExactMaximum.HorakKim

set_option autoImplicit false

/-!
# Full pairs: two statements

A pair `s`, `t` of ports of a pole of rank `b` is full if `2^b` paths join them
(`Network.IsFullPair`). Section 5.3 of the paper "The maximum number of cycles in a graph of
large rank" describes the poles with full pairs (Lemma 5.8 and Corollary 5.11), and Section 6.1
counts the cycles of the rings. This file states the two results that the case of a cyclic cut
of size four uses. It proves nothing.

* `GapStatement` (Theorem 5.10): a pair of ports is full, or at most `15/16` of the possible
  paths join it.
* `RingCaseStatement` (Case 4 of Theorem 6.8 with Corollary 6.2): let a connected cubic network
  of large rank `r` have no cyclic cut of size at most three, and let a cut of size four have
  two sides in which the four pairs between the ports `1, 2` and the ports `3, 4` are full. Then
  the network has at most `H(r)` cycles. In the paper the two sides are chains of tiles, so the
  network is a ring.

The ports are numbered by `Fin 4`: the cut edge `e i` joins the port `x i` of the first side and
the port `y i` of the second side, and the pairs in question are those of an index in `{0, 1}`
and an index in `{2, 3}`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance fullPairsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Theorem 5.10 of the paper (the gap).** In a pole of rank `b`, the number of paths between
two ports is `2^b` or at most `(15/16) 2^b`. Not proved in this file. -/
def GapStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.IsWeakPole →
    ∀ s t : V, N.IsPort s → N.IsPort t → s ≠ t →
      N.numPaths s t = 2 ^ networkRank N ∨ 16 * N.numPaths s t ≤ 15 * 2 ^ networkRank N

/-- **The ring case.** There is a number `R` with this property. Let `N` be a connected cubic
network of rank `r ≥ R` without a cyclic cut of size at most three. Let the cut `S` have exactly
the four crossing edges `e i`, where `e i` joins `x i ∈ S` and `y i ∉ S`, with four different
vertices `x i` and four different vertices `y i`. Let the two sides be poles, and let the pairs
`x i, x j` and `y i, y j` be full in their sides for `i ∈ {0, 1}` and `j ∈ {2, 3}`. Then `N` has
at most `H(r)` cycles. Not proved in this file. -/
def RingCaseStatement : Prop :=
  ∃ R : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.graph.Connected →
    N.IsCubic → (∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) → R ≤ networkRank N →
    ∀ (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V),
      (∀ g, N.crosses S g → ∃ i, g = e i) → (∀ i, N.Joins (e i) (x i) (y i)) →
      (∀ i, S (x i)) → (∀ i, ¬ S (y i)) → Function.Injective x → Function.Injective y →
      (N.sub (N.inside S)).IsWeakPole → (N.sub (N.outside S)).IsWeakPole →
      (∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
        (N.sub (N.inside S)).IsFullPair (x i) (x j) ∧
          (N.sub (N.outside S)).IsFullPair (y i) (y j)) →
      N.numCycles ≤ horakKim (networkRank N)

end Erdos1016.ExactMaximum
