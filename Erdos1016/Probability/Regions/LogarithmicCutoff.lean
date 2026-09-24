import Erdos1016.Cleanup.Degree.LinearBadVertexBound
import Erdos1016.Probability.Conditional.UniformReveal
import Mathlib.Data.Nat.Log

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ManyRegionsLogCutoff


open Erdos1016.Proof.GraphicalThreshold

/-- The logarithmic cutoff used to make the residual product error at most
`1/(4R)`. -/
def cutoff (R : ℕ) : ℕ := Nat.log 2 (4 * R) + 1

private theorem four_mul_lt_two_pow (R : ℕ) (hR : 5 ≤ R) :
    4 * R < 2 ^ R := by
  have h : ∀ n : ℕ, 5 ≤ n → 4 * n < 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        calc
          4 * (n + 1) ≤ 2 * (4 * n) := by omega
          _ < 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
  exact h R hR

theorem cutoff_le (R : ℕ) (hR : 5 ≤ R) : cutoff R ≤ R := by
  have hlog : Nat.log 2 (4 * R) < R :=
    Nat.log_lt_of_lt_pow (by omega) (four_mul_lt_two_pow R hR)
  dsimp [cutoff]
  omega





end Erdos1016.Proof.ManyRegionsLogCutoff
