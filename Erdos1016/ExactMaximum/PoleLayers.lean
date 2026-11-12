import Mathlib.Combinatorics.SimpleGraph.Metric
import Erdos1016.ExactMaximum.PoleInputs

set_option autoImplicit false

/-!
# Distance layers of a pole: definitions and two statements

Section 5.2 of the paper "The maximum number of cycles in a graph of large rank" studies a
bridgeless pole `N` with exactly two ports `s`, `t` through its distance layers: the layer `j`
is the set of the vertices at distance `j` from `s`. This file has the definitions and states two
results. It proves nothing.

* `IsBridgelessTwoPole`: `N` is connected, `s` and `t` have degree two, every other vertex has
  degree three, and every edge is on a cycle.
* `IsThinLayer`: the layer lies strictly between `s` and `t` and has exactly two vertices.
* `IsOrdinaryLayer`: a thin layer in which at most one vertex is on a pair of parallel edges.
  The paper calls a thin layer ordinary if its vertex outside a fixed shortest path is on no
  pair of parallel edges. Such a layer is ordinary in the sense of this file, and this file does
  not need the shortest path.
* `ThinLayersStatement`: Proposition 5.3 (ii) and (iii). If at least `0.501 · 2^b` paths join `s`
  and `t`, then every distance from `s` is at most `b + C`, and at most `C` vertices lie outside
  the ordinary layers.
* `FourThinLayersStatement`: Lemma 5.5. Four consecutive thin layers contain a cycle with at
  most four edges.

The count of Theorem 5.4 uses `ThinLayersStatement` only.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance poleLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The vertex is on two different edges with the same two ends. -/
def OnParallel (N : Network V E) (v : V) : Prop :=
  ∃ (e f : E) (w : V), e ≠ f ∧ N.Joins e v w ∧ N.Joins f v w

/-- Every edge is on a cycle. -/
def IsBridgeless (N : Network V E) : Prop := ∀ e, ∃ Z : N.Word, N.IsCycleWord Z ∧ Z e ≠ 0

/-- A connected pole without a bridge whose ports are `s` and `t`. -/
structure IsBridgelessTwoPole (N : Network V E) (s t : V) : Prop where
  connected : N.graph.Connected
  ne : s ≠ t
  deg_s : N.deg (fun _ => 1) s = 2
  deg_t : N.deg (fun _ => 1) t = 2
  deg_other : ∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3
  bridgeless : N.IsBridgeless

/-- The layer `j` is thin: it lies strictly between `s` and `t`, and it has two vertices. -/
def IsThinLayer (N : Network V E) (s t : V) (j : ℕ) : Prop :=
  0 < j ∧ j < N.graph.dist s t ∧ Nat.card {v : V // N.graph.dist s v = j} = 2

/-- The layer `j` is ordinary: it is thin, and at most one of its vertices is on a pair of
parallel edges. -/
def IsOrdinaryLayer (N : Network V E) (s t : V) (j : ℕ) : Prop :=
  N.IsThinLayer s t j ∧ ∀ x y, N.graph.dist s x = j → N.graph.dist s y = j →
    N.OnParallel x → N.OnParallel y → x = y

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleLayersDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Proposition 5.3 (ii) and (iii) of the paper for `ε = 1/1000`.** There is a number `C` with
this property. Let `N` be a bridgeless pole with the two ports `s`, `t`, and let at least
`0.501 · 2^b` paths join `s` and `t`. Then every vertex has distance at most `b + C` from `s`,
and at most `C` vertices lie outside the ordinary layers. Not proved in this file. -/
def ThinLayersStatement : Prop :=
  ∃ C : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.IsBridgelessTwoPole s t → 501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
    (∀ v, N.graph.dist s v ≤ networkRank N + C) ∧
      Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C

/-- **Lemma 5.5 of the paper.** Let `N` be a bridgeless pole with the two ports `s`, `t`. If the
four consecutive layers `j, …, j + 3` are thin, then some cycle with at most four edges has all
its vertices in these layers. Not proved in this file. -/
def FourThinLayersStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.IsBridgelessTwoPole s t → ∀ j : ℕ, N.IsThinLayer s t j → N.IsThinLayer s t (j + 1) →
    N.IsThinLayer s t (j + 2) → N.IsThinLayer s t (j + 3) →
    ∃ Z : N.Word, N.IsCycleWord Z ∧ size Z ≤ 4 ∧
      ∀ v, 0 < N.deg Z v → j ≤ N.graph.dist s v ∧ N.graph.dist s v ≤ j + 3

end Erdos1016.ExactMaximum
