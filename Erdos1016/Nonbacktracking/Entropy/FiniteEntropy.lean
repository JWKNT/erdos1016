import Mathlib

set_option autoImplicit false

/-!
# Finite logarithmic averaging

All sums in this file are finite. The weighted logarithm inequality is proved
from `log x ≤ x - 1`; no entropy or Markov-chain theorem is an input.
Zero weights are permitted, but logarithm arguments are positive.

This is the finite Jensen step in the stationary entropy argument of
`ANALYTIC_CUBIC_INVERSE_PROOF.md`, §§5 and 7.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking.FiniteEntropy
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Finite weighted Jensen inequality for the logarithm, including zero weights. -/
theorem sum_mul_log_le_log_sum (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hx : ∀ i, 0 < x i) :
    (∑ i, p i * Real.log (x i)) ≤ Real.log (∑ i, p i * x i) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < p i := by
    by_contra hn
    push_neg at hn
    have hle : ∑ i, p i ≤ (0 : ℝ) :=
      Finset.sum_nonpos (fun i _ => hn i)
    linarith
  let m : ℝ := ∑ i, p i * x i
  have hm : 0 < m := by
    dsimp [m]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hp i) (hx i).le)
      ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (hx i₀)⟩
  have hpoint (i : ι) :
      p i * (Real.log (x i) - Real.log m) ≤ p i * (x i / m - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hx i) hm)
    rw [Real.log_div (hx i).ne' hm.ne'] at h
    exact mul_le_mul_of_nonneg_left h (hp i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hleft : (∑ i, p i * (Real.log (x i) - Real.log m)) =
      (∑ i, p i * Real.log (x i)) - Real.log m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  have hscale : (∑ i, p i * (x i / m)) = (∑ i, p i * x i) / m := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i, p i * (x i / m - 1)) = 0 := by
    calc
      _ = (∑ i, p i * (x i / m)) - ∑ i, p i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i * x i) / m - 1 := by rw [hscale, hs]
      _ = m / m - 1 := by dsimp [m]
      _ = 0 := by rw [div_self hm.ne']; ring
  rw [hleft, hright] at hsum
  dsimp [m] at hsum
  linarith

/-- Uniform logarithmic averaging, with no positivity requirement on a zero
cardinality denominator hidden in the statement. -/
theorem average_log_le_log_average [Nonempty ι] (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) :
    (∑ i, Real.log (x i)) / (Fintype.card ι : ℝ) ≤
      Real.log ((∑ i, x i) / (Fintype.card ι : ℝ)) := by
  have hm : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hs : (∑ _ : ι, (1 / (Fintype.card ι : ℝ))) = 1 := by
    simp [hm.ne']
  have h := sum_mul_log_le_log_sum
    (fun _ : ι => 1 / (Fintype.card ι : ℝ)) x
    (fun _ => (div_pos zero_lt_one hm).le) hs hx
  simpa only [one_div, ← Finset.mul_sum, ← div_eq_inv_mul, Finset.sum_div] using h





/-- A column-stochastic finite kernel preserves unnormalized uniform sums. -/
theorem sum_transition_average (P : ι → ι → ℝ)
    (hcol : ∀ j, ∑ i, P i j = 1) (f : ι → ℝ) :
    (∑ i, ∑ j, P i j * f j) = ∑ j, f j := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hcol, one_mul]

end Erdos1016.Nonbacktracking.FiniteEntropy
