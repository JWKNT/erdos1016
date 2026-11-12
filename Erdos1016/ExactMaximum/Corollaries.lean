import Erdos1016.ExactMaximum.Statement
import Erdos1016.ExactMaximumSupport.SecondOrder

set_option autoImplicit false

/-!
# Forms of the exact maximum

`ExactMaximumStatement` says that `maxCycles r = horakKim r` for all large `r`. This file derives
the forms of this statement that the paper "The maximum number of cycles in a graph of large
rank" prints. Every theorem here is an implication from `ExactMaximumStatement`; no theorem here
proves it.

* `parity_of_exactMaximum`: the two parities of equation (1.1), in natural numbers and without
  subtraction.
* `formula_of_exactMaximum`: equation (1.1) as printed, in real numbers:
  `ψ(2q+1) = 2^(2q) + (2q + 1/2) 2^q - 3q` and
  `ψ(2q+2) = 2^(2q+1) + (2q + 9/2) 2^q - 3q - 4`.
* `secondOrder_of_exactMaximum`, `secondOrder_explicit_of_exactMaximum`: the second term,
  `ψ(r) - 2^(r-1) = Θ(r 2^(r/2))`, with the explicit constants `1/8` and `2`. The proofs are in
  `ExactMaximumSupport/SecondOrder.lean` (by Astra).
-/

noncomputable section

namespace Erdos1016.ExactMaximum

open CycleCount Filter Asymptotics

/-- **Equation (1.1) of the paper, without subtraction.** If the exact maximum holds, then for
all large `q` the two parities are `ψ(2q+1) + 3q = 2^(2q) + (4q+1) 2^(q-1)` and
`ψ(2q+2) + 3q + 4 = 2^(2q+1) + (4q+9) 2^(q-1)`. -/
theorem parity_of_exactMaximum (h : ExactMaximumStatement) :
    ∃ Q : ℕ, ∀ q, Q ≤ q →
      maxCycles (2 * q + 1) + 3 * q = 2 ^ (2 * q) + (4 * q + 1) * 2 ^ (q - 1) ∧
      maxCycles (2 * q + 2) + 3 * q + 4 = 2 ^ (2 * q + 1) + (4 * q + 9) * 2 ^ (q - 1) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨max R 1, fun q hq => ?_⟩
  have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : R ≤ q := le_trans (le_max_left _ _) hq
  rw [hR (2 * q + 1) (by omega), hR (2 * q + 2) (by omega)]
  exact ⟨horakKim_odd q hq1, horakKim_even q hq1⟩

/-- **Equation (1.1) of the paper, as printed.** If the exact maximum holds, then for all large
`q`: `ψ(2q+1) = 2^(2q) + (2q + 1/2) 2^q - 3q` and
`ψ(2q+2) = 2^(2q+1) + (2q + 9/2) 2^q - 3q - 4`, in real numbers. -/
theorem formula_of_exactMaximum (h : ExactMaximumStatement) :
    ∃ Q : ℕ, ∀ q, Q ≤ q →
      (maxCycles (2 * q + 1) : ℝ) =
          2 ^ (2 * q) + (2 * (q : ℝ) + 1 / 2) * 2 ^ q - 3 * (q : ℝ) ∧
      (maxCycles (2 * q + 2) : ℝ) =
          2 ^ (2 * q + 1) + (2 * (q : ℝ) + 9 / 2) * 2 ^ q - 3 * (q : ℝ) - 4 := by
  obtain ⟨Q, hQ⟩ := parity_of_exactMaximum h
  refine ⟨max Q 1, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hQ q (le_trans (le_max_left _ _) hq)
  have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hq
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  have h1' : (maxCycles (2 * (k + 1) + 1) : ℝ) + 3 * ((k + 1 : ℕ) : ℝ) =
      2 ^ (2 * (k + 1)) + (4 * ((k + 1 : ℕ) : ℝ) + 1) * 2 ^ k := by exact_mod_cast h1
  have h2' : (maxCycles (2 * (k + 1) + 2) : ℝ) + 3 * ((k + 1 : ℕ) : ℝ) + 4 =
      2 ^ (2 * (k + 1) + 1) + (4 * ((k + 1 : ℕ) : ℝ) + 9) * 2 ^ k := by exact_mod_cast h2
  constructor
  · rw [pow_succ (2 : ℝ) k]
    linear_combination h1'
  · rw [pow_succ (2 : ℝ) k]
    linear_combination h2'

/-- **The second term.** If the exact maximum holds, then `ψ(r) - 2^(r-1) = Θ(r 2^(r/2))`. -/
theorem secondOrder_of_exactMaximum (h : ExactMaximumStatement) :
    (fun r : ℕ => (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) :=
  ExactMaximumSupport.sharpSecondOrder_rpow_of_exactMaximum h

/-- **The second term with explicit constants.** If the exact maximum holds, then for all large
`r`: `r 2^(r/2) / 8 ≤ ψ(r) - 2^(r-1) ≤ 2 r 2^(r/2)`. -/
theorem secondOrder_explicit_of_exactMaximum (h : ExactMaximumStatement) :
    ∃ R : ℕ, ∀ r, R ≤ r →
      (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2) / 8 ≤ (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1) ∧
      (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1) ≤ 2 * ((r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) :=
  ExactMaximumSupport.sharpSecondOrder_explicit_of_exactMaximum h

end Erdos1016.ExactMaximum
