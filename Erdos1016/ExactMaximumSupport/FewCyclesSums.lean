import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Numerical sums for the few-cycle decomposition

These are numerical inequalities only. They supply the double geometric sum
and the aggregation of positive component ranks used in the few-cycle argument.
The difference `j-i` is natural subtraction, always summed with `i ≤ j`.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.FewCyclesSums

private theorem sqrt_two_sq : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

private theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have hs := sqrt_two_sq
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- Ordinary powers of sqrt(2) equal the real half-exponent scale. -/
theorem sqrt_two_pow_eq (n : ℕ) :
    (Real.sqrt 2)^n = (2 : ℝ)^((n : ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- A finite geometric sum, with its exact uniform envelope. -/
theorem sum_sqrt_two_pow_le (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), (Real.sqrt 2)^i) ≤
      (2+Real.sqrt 2)*(Real.sqrt 2)^n := by
  have ha := one_lt_sqrt_two
  have hc : (2+Real.sqrt 2)*(Real.sqrt 2-1) = Real.sqrt 2 := by
    nlinarith [sqrt_two_sq]
  apply (mul_le_mul_right (sub_pos.mpr ha)).mp
  calc
    _ = (Real.sqrt 2)^(n+1)-1 := geom_sum_mul _ _
    _ ≤ (Real.sqrt 2)^(n+1) := by linarith
    _ = ((2+Real.sqrt 2)*(Real.sqrt 2)^n)*(Real.sqrt 2-1) := by
      rw [pow_succ]
      calc
        _ = (Real.sqrt 2)^n*((2+Real.sqrt 2)*(Real.sqrt 2-1)) := by rw [hc]
        _ = _ := by ring

/-- The interval sum is an ordinary geometric sum after translating its lower endpoint. -/
theorem sum_Icc_sqrt_two_pow_le (i n : ℕ) (hi : i ≤ n) :
    (∑ j ∈ Finset.Icc i n, (Real.sqrt 2)^(j-i)) ≤
      (2+Real.sqrt 2)*(Real.sqrt 2)^(n-i) := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  have he : n+1-i = n-i+1 := by omega
  simp only [he, Nat.add_sub_cancel_left]
  exact sum_sqrt_two_pow_le (n-i)

/-- The double geometric sum in the few-cycle decomposition, in ordinary powers. -/
theorem double_sum_sqrt_two_pow_le (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.Icc i n,
      (Real.sqrt 2)^(j-i)) ≤ 12*(Real.sqrt 2)^n := by
  have ha := Real.sqrt_nonneg (2 : ℝ)
  have hcoeff : (2+Real.sqrt 2)*(2+Real.sqrt 2) ≤ (12 : ℝ) := by
    have hs := sqrt_two_sq
    have hu : Real.sqrt 2 ≤ (3/2 : ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    nlinarith
  have href := Finset.sum_range_reflect (fun i : ℕ => (Real.sqrt 2)^i) (n+1)
  simp only [Nat.add_sub_cancel] at href
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (2+Real.sqrt 2)*(Real.sqrt 2)^(n-i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_Icc_sqrt_two_pow_le i n (by have h := Finset.mem_range.mp hi; omega)
    _ = (2+Real.sqrt 2)*(∑ i ∈ Finset.range (n+1), (Real.sqrt 2)^(n-i)) := by
      rw [Finset.mul_sum]
    _ = (2+Real.sqrt 2)*(∑ i ∈ Finset.range (n+1), (Real.sqrt 2)^i) := by rw [href]
    _ ≤ (2+Real.sqrt 2)*((2+Real.sqrt 2)*(Real.sqrt 2)^n) :=
      mul_le_mul_of_nonneg_left (sum_sqrt_two_pow_le n) (by positivity)
    _ = ((2+Real.sqrt 2)*(2+Real.sqrt 2))*(Real.sqrt 2)^n := by ring
    _ ≤ 12*(Real.sqrt 2)^n := mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- The requested real-power double sum; natural subtraction is explicit. -/
theorem double_sum_two_rpow_half_le (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.Icc i n,
      (2 : ℝ)^((↑(j-i) : ℝ)/2)) ≤ 12*(2 : ℝ)^((n : ℝ)/2) := by
  simpa only [sqrt_two_pow_eq] using double_sum_sqrt_two_pow_le n

/-- An elementary sum/product inequality in a form that also handles an empty family. -/
theorem sum_powers_add_one_le {ι : Type*} (s : Finset ι) (b : ι → ℕ) :
    (∑ i ∈ s, (Real.sqrt 2)^(b i))+1 ≤
      (Real.sqrt 2)^(∑ i ∈ s, b i)+(s.card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_not_mem ha, pow_add]
    push_cast
    have h1 : (1 : ℝ) ≤ (Real.sqrt 2)^(b a) := one_le_pow₀ one_lt_sqrt_two.le
    have h2 : (1 : ℝ) ≤ (Real.sqrt 2)^(∑ i ∈ s, b i) := one_le_pow₀ one_lt_sqrt_two.le
    have hm := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
    nlinarith

/-- The family-size correction is no larger than the geometric scale. -/
theorem nat_le_sqrt_two_pow_add_one (n : ℕ) :
    (n : ℝ) ≤ (Real.sqrt 2)^n+1 := by
  apply Nat.twoStepInduction (P := fun n => (n : ℝ) ≤ (Real.sqrt 2)^n+1) ?_ ?_ ?_ n
  · norm_num
  · norm_num
  · intro k ih _
    rw [pow_add, sqrt_two_sq]
    push_cast
    by_cases hk : k ≤ 2
    · interval_cases k <;> norm_num [sqrt_two_sq]
      have ha := one_lt_sqrt_two
      linarith
    · have hkR : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
      nlinarith

/-- Positive integral ranks aggregate with the uniform factor two. -/
theorem sum_sqrt_two_pow_ranks_le {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    (hb : ∀ i ∈ s, 1 ≤ b i) :
    (∑ i ∈ s, (Real.sqrt 2)^(b i)) ≤ 2*(Real.sqrt 2)^(∑ i ∈ s, b i) := by
  have hcard : s.card ≤ ∑ i ∈ s, b i := by
    calc
      s.card = ∑ _i ∈ s, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum hb
  have hp := pow_le_pow_right₀ one_lt_sqrt_two.le hcard
  have hn := nat_le_sqrt_two_pow_add_one s.card
  have hs := sum_powers_add_one_le s b
  linarith

/-- The component-rank sum in the usual real half-exponent notation. -/
theorem sum_two_rpow_half_ranks_le {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    (hb : ∀ i ∈ s, 1 ≤ b i) :
    (∑ i ∈ s, (2 : ℝ)^((b i : ℝ)/2)) ≤
      2*(2 : ℝ)^((↑(∑ i ∈ s, b i) : ℝ)/2) := by
  simpa only [sqrt_two_pow_eq] using sum_sqrt_two_pow_ranks_le s b hb

end Erdos1016.ExactMaximumSupport.FewCyclesSums
