import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Numerical bounds for the fixed-probability packing argument

A product of independent zero-star penalties drops below two fifths once
the number of selected spaces reaches two to the boundary budget.
-/

namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingProbabilityBounds

theorem exp_neg_one_lt_two_fifths : Real.exp (-1) < (2 / 5 : ℝ) := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
  nlinarith [Real.exp_one_gt_d9]

/-- The probability threshold bounds the number of independent selected spaces. -/
theorem selected_card_lt_two_pow (d t : ℕ)
    (hprob : (2 / 5 : ℝ) ≤ (1 - 1 / (2 : ℝ)^d)^t) : t < 2^d := by
  by_contra hn
  have ht : 2^d ≤ t := by omega
  have hN : (1 : ℝ) ≤ (2^d : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hbase : 0 ≤ 1 - 1 / (2 : ℝ)^d := by
    have hh : (1 : ℝ) ≤ (2 : ℝ)^d := by exact_mod_cast Nat.one_le_two_pow
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hh)
  have hle : 1 - 1 / (2 : ℝ)^d ≤ 1 := by
    have hh : 0 ≤ 1 / (2 : ℝ)^d := by positivity
    linarith
  have hp := pow_le_pow_of_le_one hbase hle ht
  have he := Real.one_sub_div_pow_le_exp_neg hN
  have he' : (1 - 1 / (2 : ℝ)^d)^(2^d : ℕ) ≤ Real.exp (-1) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using he
  exact not_le_of_gt exp_neg_one_lt_two_fifths (hprob.trans (hp.trans he'))

/-- Two zero-dimensional local spaces would already contradict the threshold. -/
theorem zero_space_count_le_one (z : ℕ) (hprob : (2 / 5 : ℝ) ≤ (1 / 2 : ℝ)^z) :
    z ≤ 1 := by
  by_contra hn
  have hz : 2 ≤ z := by omega
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hz
  norm_num at hp
  linarith

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingProbabilityBounds
