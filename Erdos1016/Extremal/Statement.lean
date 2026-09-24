import Erdos1016.Extremal.Recurrence.LogStarTowers
import Mathlib.Combinatorics.SimpleGraph.Path

set_option autoImplicit false

/-!
# Project target statement for Erdős problem 1016

Cycles are Mathlib `SimpleGraph.Walk.IsCycle` objects. The extremal function
is restricted to vertex type `Fin n`, which is equivalent up to relabeling to
the paper's definition over all finite simple graphs on `n` vertices.
This file records the full two-sided asymptotic target in Mathlib's finite
simple-graph language; it does not assert its proof. I found no corresponding
Erdős 1016 file in the current Google DeepMind Formal Conjectures tree, so this
is the project's explicit target statement rather than an imported community
formalization.
-/

namespace Erdos1016.Problem1016

/-- A finite simple graph contains a cycle of a specified edge length. -/
def HasCycleLength {V : Type*} [Fintype V] (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = ℓ

/-- Pancyclicity in the usual simple-graph sense. -/
def IsPancyclic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ Fintype.card V → HasCycleLength G ℓ

/-- The excess over `n` edges of a graph on the labeled vertex set `Fin n`. -/
noncomputable def excess (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ := by
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact Fintype.card G.edgeSet - n

/-- Candidate excess values for pancyclic graphs on `n` vertices. -/
def candidateExcesses (n : ℕ) : Set ℕ :=
  {z | ∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ excess n G = z}

/-- The extremal pancyclic excess `h(n)` from the paper. -/
noncomputable def h (n : ℕ) : ℕ := sInf (candidateExcesses n)

/-- Every pancyclic graph on `Fin n` is a candidate in the defining set, so
its excess bounds the extremal infimum from above. -/
theorem h_le_excess_of_isPancyclic (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : IsPancyclic G) : h n ≤ excess n G := by
  classical
  have hmem : excess n G ∈ candidateExcesses n := by
    exact ⟨G, hG, rfl⟩
  let hex : ∃ z : ℕ, z ∈ candidateExcesses n := ⟨excess n G, hmem⟩
  unfold h
  change (if h : ∃ z, z ∈ candidateExcesses n then Nat.find h else 0) ≤ _
  rw [dif_pos hex]
  exact Nat.find_min' hex hmem

/-- The exact two-sided asymptotic assertion of the paper, with absolute
additive constants and the paper's bottom-one tower convention for `log_*`. -/
def MainTheorem : Prop :=
  ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
    Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) - Aminus ≤ (h n : ℝ) ∧
    (h n : ℝ) ≤ Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) + Aplus

end Erdos1016.Problem1016
