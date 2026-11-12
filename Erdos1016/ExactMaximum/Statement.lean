import Erdos1016.CycleCount.Asymptotic
import Erdos1016.ExactMaximum.HorakKim

set_option autoImplicit false

/-!
# The exact maximum: the statement

`CycleCount.maxCycles r` is the largest number of cycles of a simple graph with cyclomatic
number `r`. The theorem of the paper "The maximum number of cycles in a graph of large rank" says
that `maxCycles r = horakKim r` for all sufficiently large `r`.

This file states the theorem in Mathlib's language of simple graphs and splits it into an upper
bound and a lower bound. It proves the split. It does not prove the two bounds.
-/

noncomputable section

namespace Erdos1016.ExactMaximum
open CycleCount

/-- **Theorem 1.1 of the paper.** There is `R` such that, for every `r ≥ R`, the largest number
of cycles of a simple graph with cyclomatic number `r` is the number `H(r)` of Horak and Kim. -/
def ExactMaximumStatement : Prop :=
  ∃ R : ℕ, ∀ r, R ≤ r → maxCycles r = horakKim r

/-- The upper bound: every simple graph of large cyclomatic number `r` has at most `H(r)`
cycles. -/
def UpperBoundStatement : Prop :=
  ∃ R : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → R ≤ r →
    numCycles G ≤ horakKim r

/-- The lower bound: for every large `r` some simple graph of cyclomatic number `r` has at least
`H(r)` cycles. -/
def LowerBoundStatement : Prop :=
  ∃ R : ℕ, ∀ r, R ≤ r → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent ∧ horakKim r ≤ numCycles G

/-- The two bounds give the theorem. -/
theorem exactMaximumStatement_of_bounds (hU : UpperBoundStatement) (hL : LowerBoundStatement) :
    ExactMaximumStatement := by
  obtain ⟨R₁, h₁⟩ := hU
  obtain ⟨R₂, h₂⟩ := hL
  refine ⟨max (max R₁ R₂) 3, fun r hr => ?_⟩
  have hr1 : R₁ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr2 : R₂ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr3 : 3 ≤ r := le_trans (le_max_right _ _) hr
  apply le_antisymm
  · obtain ⟨n, G, hG, hc⟩ := maxCycles_mem r hr3
    rw [← hc]
    exact h₁ n G r hG hr1
  · obtain ⟨n, G, hG, hc⟩ := h₂ r hr2
    exact hc.trans (numCycles_le_maxCycles G r hG)

/-- The theorem implies the asymptotic formula of Entringer and Slater in this form:
`2^(r-1) ≤ maxCycles r` for all large `r`, with equality of `maxCycles r` and `H(r)`. -/
theorem two_pow_le_maxCycles_of_exact (h : ExactMaximumStatement) :
    ∃ R : ℕ, ∀ r, R ≤ r → 2 ^ (r - 1) ≤ maxCycles r := by
  obtain ⟨R, hR⟩ := h
  refine ⟨max R 3, fun r hr => ?_⟩
  rw [hR r (le_trans (le_max_left _ _) hr)]
  exact two_pow_le_horakKim r (le_trans (le_max_right _ _) hr)

end Erdos1016.ExactMaximum
