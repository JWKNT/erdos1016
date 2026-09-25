import Erdos1016.Probability.Avoidance.StretchedExponentialAbsorption
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Relative error bounds for finite cycle avoidance

The Taylor error is bounded using a single nonnegative term of the exponential
series at twice the mean. This avoids a separate Stirling estimate. Both error
terms below are controlled relative to `exp (-lam)`, as required in Section 6 of
the standalone manuscript.
-/

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.QuantitativeAvoidance

/-- A moment cutoff at least eight times the mean makes the factorial Taylor
remainder exponentially smaller than the main Poisson term. -/
theorem factorial_tail_le_exp_neg_two_mul {lam : ℝ} (hlam : 0 ≤ lam)
    (k : ℕ) (hk : 8 * lam ≤ (k : ℝ)) :
    lam ^ k / (k.factorial : ℝ) ≤ Real.exp (-2 * lam) := by
  have hseries := Real.pow_div_factorial_le_exp (2 * lam) (show 0 ≤ 2 * lam by positivity) k
  have htwo : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    lam ^ k / (k.factorial : ℝ) =
        ((2 * lam) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ k := by
      rw [mul_pow]
      field_simp
      ring
    _ ≤ Real.exp (2 * lam) / (2 : ℝ) ^ k :=
      div_le_div_of_nonneg_right hseries htwo.le
    _ = Real.exp (2 * lam - (k : ℝ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-2 * lam) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The conditional-moment error is at most the Poisson term exactly when its
relative error is at most one. All exponential normalization is explicit. -/
theorem conditional_error_le_exp_neg {lam d a : ℝ}
    (hrelative : d * lam * Real.exp (2 * lam + a) ≤ 1) :
    d * lam * Real.exp (lam + a) ≤ Real.exp (-lam) := by
  have h := mul_le_mul_of_nonneg_right hrelative (Real.exp_nonneg (-lam))
  have heq : d * lam * Real.exp (2 * lam + a) * Real.exp (-lam) =
      d * lam * Real.exp (lam + a) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simpa only [heq, one_mul] using h

/-- A finite Bonferroni/Poisson bound has a constant relative error once its
actual moment cutoff and conditional load satisfy the displayed numerical
conditions. This statement does not assume decay of the avoidance probability. -/
theorem poisson_bound_le_three_exp_neg {μ lam d : ℝ} (K : ℕ)
    (hlam : 0 ≤ lam) (hK : 8 * lam ≤ (K + 1 : ℕ))
    (hrelative : d * lam *
      Real.exp (2 * lam + (K.choose 2 : ℝ) * d / lam) ≤ 1)
    (hfinite : μ ≤ Real.exp (-lam) + lam ^ (K + 1) / ((K + 1).factorial : ℝ) +
      d * lam * Real.exp (lam + (K.choose 2 : ℝ) * d / lam)) :
    μ ≤ 3 * Real.exp (-lam) := by
  have htail := factorial_tail_le_exp_neg_two_mul hlam (K + 1) hK
  have htail' : Real.exp (-2 * lam) ≤ Real.exp (-lam) :=
    Real.exp_le_exp.mpr (by linarith)
  have herr := conditional_error_le_exp_neg hrelative
  linarith

/-- Uniform control of the relative conditional error by an explicit
square-root threshold. The inputs are only a decaying load bound and scalar
size bounds; the desired relative error is proved here. -/
theorem relative_error_le_one_of_exp_decay {x c lam d : ℝ} (K : ℕ)
    (hx : 0 ≤ x) (hc : 0 < c) (hs : 1 ≤ Real.sqrt x)
    (hcs : 8 ≤ c * Real.sqrt x)
    (hlam : 1 ≤ lam) (hlamUpper : lam ≤ Real.sqrt x)
    (hK : (K : ℝ) ≤ Real.sqrt x)
    (hd : 0 ≤ d) (hdUpper : d ≤ Real.exp (-c * x)) :
    d * lam * Real.exp (2 * lam + (K.choose 2 : ℝ) * d / lam) ≤ 1 := by
  have hs0 := Real.sqrt_nonneg x
  have hlam0 : 0 < lam := by linarith
  have hcx : 8 * Real.sqrt x ≤ c * x := by
    calc
      _ ≤ (c * Real.sqrt x) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hcs hs0
      _ = c * x := by rw [mul_assoc, Real.mul_self_sqrt hx]
  have hcx0 : 0 ≤ c * x := mul_nonneg hc.le hx
  have hsq : (8 * Real.sqrt x) ^ 2 ≤ (c * x) ^ 2 :=
    (sq_le_sq₀ (by positivity) hcx0).mpr hcx
  have hexp : x ≤ Real.exp (c * x) := by
    have hquad := Real.quadratic_le_exp_of_nonneg hcx0
    nlinarith [Real.sq_sqrt hx]
  have hxd : x * d ≤ 1 := by
    calc
      _ ≤ x * Real.exp (-c * x) := mul_le_mul_of_nonneg_left hdUpper hx
      _ ≤ Real.exp (c * x) * Real.exp (-c * x) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hchoose : (K.choose 2 : ℝ) ≤ x := by
    have hchoose' : (K.choose 2 : ℝ) ≤ (K : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow K 2
    have hKsq : (K : ℝ) ^ 2 ≤ (Real.sqrt x) ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg _) hs0).mpr hK
    nlinarith [Real.sq_sqrt hx]
  have ha : (K.choose 2 : ℝ) * d / lam ≤ 1 := by
    calc
      _ ≤ (x * d) / lam :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose hd) hlam0.le
      _ ≤ x * d := div_le_self (mul_nonneg hx hd) hlam
      _ ≤ 1 := hxd
  have hsExp : Real.sqrt x ≤ Real.exp (Real.sqrt x) := by
    linarith [Real.add_one_le_exp (Real.sqrt x)]
  calc
    _ ≤ Real.exp (-c * x) * Real.sqrt x *
        Real.exp (2 * Real.sqrt x + 1) := by
      apply mul_le_mul
      · exact mul_le_mul hdUpper hlamUpper hlam0.le (Real.exp_nonneg _)
      · exact Real.exp_le_exp.mpr (by linarith)
      · exact Real.exp_nonneg _
      · positivity
    _ ≤ Real.exp (-c * x) * Real.exp (Real.sqrt x) *
        Real.exp (2 * Real.sqrt x + 1) := by
      gcongr
    _ = Real.exp (-c * x + 3 * Real.sqrt x + 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- The fixed factor three in the quantitative avoidance estimate is absorbed
while retaining the manuscript's absolute coefficient `σ/4`. -/
theorem three_exp_neg_le_base_two_stretched
    (x mean : ℕ → ℝ) (σ C : ℝ)
    (hx : Tendsto x atTop atTop) (hσ : 0 < σ)
    (hmean : ∀ᶠ j in atTop,
      (σ * Real.log 2 / 2) * Real.sqrt (x j) -
        (1 / 2 : ℝ) * Real.log (x j) - C ≤ mean j) :
    ∀ᶠ j in atTop,
      3 * Real.exp (-mean j) ≤ (2 : ℝ) ^ (-(σ / 4) * Real.sqrt (x j)) := by
  have hlower : ∀ᶠ j in atTop,
      (σ * Real.log 2 / 2) * Real.sqrt (x j) -
        (1 / 2 : ℝ) * Real.log (x j) - (C + Real.log 3) ≤ mean j - Real.log 3 := by
    filter_upwards [hmean] with j hj
    linarith
  have h := StretchedExponentialAbsorption.exp_neg_le_base_two_stretched_of_mean_lower_bound
    x (fun j => mean j - Real.log 3) σ (C + Real.log 3) hx hσ hlower
  filter_upwards [h] with j hj
  have heq : Real.exp (-(mean j - Real.log 3)) = 3 * Real.exp (-mean j) := by
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  rwa [heq] at hj

end Erdos1016.Proof.QuantitativeAvoidance
