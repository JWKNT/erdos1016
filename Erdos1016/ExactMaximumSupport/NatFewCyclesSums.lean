import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Natural floor-exponent sums for the cycle count

The real half-exponent sum has constant twelve. Rounding both exponents
down changes that statement. The natural version below uses constant sixteen.
-/

open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.NatFewCyclesSums

/-- The natural floor-exponent geometric sum has a uniform factor-four bound. -/
theorem sum_two_pow_half_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (2 : ℕ) ^ (i / 2)) ≤ 4 * 2 ^ (n / 2) := by
  have hall : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1), (2 : ℕ) ^ (i / 2)) ≤ 4 * 2 ^ (n / 2) := by
    apply Nat.twoStepInduction
    · norm_num
    · norm_num [Finset.sum_range_succ]
    · intro n ih _
      have h1 : (2 : ℕ) ^ ((n + 1) / 2) ≤ 2 ^ (n / 2) * 2 := by
        calc
          _ ≤ 2 ^ (n / 2 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
          _ = _ := pow_succ _ _
      have h2 : (2 : ℕ) ^ ((n + 2) / 2) = 2 ^ (n / 2) * 2 := by
        rw [show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h2]
      omega
  exact hall n

/-- Translating an integer interval preserves its physical length exponent. -/
theorem sum_Icc_two_pow_half_le (i n : ℕ) (hi : i ≤ n) :
    (∑ j ∈ Finset.Icc i n, (2 : ℕ) ^ ((j - i) / 2)) ≤ 4 * 2 ^ ((n - i) / 2) := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  have he : n + 1 - i = n - i + 1 := by omega
  simp only [he, Nat.add_sub_cancel_left]
  exact sum_two_pow_half_le (n - i)

/-- The double sum with natural floor exponents, as needed by the integer cycle count. -/
theorem double_sum_two_pow_half_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc i n,
      (2 : ℕ) ^ ((j - i) / 2)) ≤ 16 * 2 ^ (n / 2) := by
  have href := Finset.sum_range_reflect (fun i : ℕ => (2 : ℕ) ^ (i / 2)) (n + 1)
  simp only [Nat.add_sub_cancel] at href
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), 4 * 2 ^ ((n - i) / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_Icc_two_pow_half_le i n (by have h := Finset.mem_range.mp hi; omega)
    _ = 4 * (∑ i ∈ Finset.range (n + 1), 2 ^ ((n - i) / 2)) := by rw [Finset.mul_sum]
    _ = 4 * (∑ i ∈ Finset.range (n + 1), 2 ^ (i / 2)) := by rw [href]
    _ ≤ 4 * (4 * 2 ^ (n / 2)) := Nat.mul_le_mul_left 4 (sum_two_pow_half_le n)
    _ = _ := by ring

/-- The constant twelve cannot be reused when both exponents are rounded down. -/
theorem twelve_fails_at_nine :
    ¬ (∑ i ∈ Finset.range 10, ∑ j ∈ Finset.Icc i 9,
      (2 : ℕ) ^ ((j - i) / 2)) ≤ 12 * 2 ^ (9 / 2) := by
  decide

end Erdos1016.ExactMaximumSupport.NatFewCyclesSums
