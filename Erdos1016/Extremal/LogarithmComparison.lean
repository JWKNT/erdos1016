import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
# Integer to real logarithm bridge

Convert the floor base-two logarithm used in integer graph budgets to the
real logarithm used in the statement of Erdős problem 1016.
-/
namespace Erdos1016.Problem1016

/-- For positive `n`, its integer base-two logarithm lies within one below
its real base-two logarithm. -/
theorem log2_real_logb_bounds (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log2 n : ℝ) ≤ Real.logb 2 (n : ℝ) ∧
      Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hn0 : n ≠ 0 := by omega
  have hpow_le_nat : 2 ^ Nat.log2 n ≤ n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hn0
  have hpow_lt_nat : n < 2 ^ (Nat.log2 n + 1) := by
    rw [Nat.log2_eq_log_two]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hpow_le_real : (2 : ℝ) ^ (Nat.log2 n : ℝ) ≤ (n : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hpow_le_nat
  have hpow_lt_real : (n : ℝ) < (2 : ℝ) ^ ((Nat.log2 n : ℝ) + 1) := by
    rw [show ((Nat.log2 n : ℝ) + 1) = ((Nat.log2 n + 1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    exact_mod_cast hpow_lt_nat
  constructor
  · exact (Real.le_logb_iff_rpow_le (by norm_num : 1 < (2 : ℝ))
      (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)).2 hpow_le_real
  · exact (Real.logb_lt_iff_lt_rpow (by norm_num : 1 < (2 : ℝ))
      (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)).2 hpow_lt_real

end Erdos1016.Problem1016
