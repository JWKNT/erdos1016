import Erdos1016.ExactMaximum.Statement
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# The sharp second-order consequence of eventual exactness

This file proves the parity arithmetic and asymptotic comparison needed to deduce
`maxCycles r - 2^(r-1) = Θ(r * sqrt (2^r))` from `ExactMaximumStatement`.
It does **not** prove eventual exactness, and hence does not independently close
the sharp second-order graph theorem. No graph-theoretic hypothesis is hidden in
the arithmetic lemmas about `horakKim`.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport

open Erdos1016.ExactMaximum Erdos1016.CycleCount Filter Asymptotics

/-- Integer bounds for the positive Horak--Kim excess, uniform in both parities. -/
theorem horakKim_excess_nat_bounds (r : ℕ) (hr : 6 ≤ r) :
    r * 2 ^ (r / 2) ≤ 4 * (horakKim r - 2 ^ (r - 1)) ∧
    horakKim r - 2 ^ (r - 1) ≤ 2 * r * 2 ^ (r / 2) := by
  have hbase := two_pow_le_horakKim r (by omega)
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨q, hq⟩
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    have hq : 2 ≤ q := by omega
    have he : r = 2 * q + 2 := by omega
    rw [he] at hbase ⊢
    have hH := horakKim_even q (by omega)
    have hexp : 2 * q + 2 - 1 = 2 * q + 1 := by omega
    have hdiv : (2 * q + 2) / 2 = q - 1 + 2 := by omega
    have hp : 2 ^ (q - 1 + 2) = 4 * 2 ^ (q - 1) := by rw [pow_add]; ring
    have hP : 2 ≤ 2 ^ (q - 1) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hexp] at hbase ⊢
    rw [hdiv, hp]
    have hE : horakKim (2 * q + 2) - 2 ^ (2 * q + 1) + 3 * q + 4 =
        (4 * q + 9) * 2 ^ (q - 1) := by omega
    have hmul := Nat.mul_le_mul_left q hP
    constructor <;> nlinarith
  · have hq1 : 1 ≤ q := by omega
    subst r
    have hH := horakKim_odd q hq1
    have hexp : 2 * q + 1 - 1 = 2 * q := by omega
    have hdiv : (2 * q + 1) / 2 = q - 1 + 1 := by omega
    have hp : 2 ^ (q - 1 + 1) = 2 * 2 ^ (q - 1) := by rw [pow_add]; ring
    have hP : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
    rw [hexp] at hbase ⊢
    rw [hdiv, hp]
    have hE : horakKim (2 * q + 1) - 2 ^ (2 * q) + 3 * q =
        (4 * q + 1) * 2 ^ (q - 1) := by omega
    have hmul := Nat.mul_le_mul_left q hP
    constructor <;> nlinarith

/-- The integer half-exponent and the real square-root scale differ by at most two. -/
theorem two_pow_half_sqrt_bounds (r : ℕ) :
    (2 : ℝ) ^ (r / 2) ≤ Real.sqrt ((2 : ℝ) ^ r) ∧
    Real.sqrt ((2 : ℝ) ^ r) ≤ 2 * (2 : ℝ) ^ (r / 2) := by
  have hlow : 2 * (r / 2) ≤ r := by omega
  have hupp : r ≤ 2 * (r / 2) + 2 := by omega
  constructor
  · apply Real.le_sqrt_of_sq_le
    calc
      ((2 : ℝ) ^ (r / 2)) ^ 2 = (2 : ℝ) ^ (2 * (r / 2)) := by
        rw [← pow_mul, Nat.mul_comm]
      _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hlow
  · apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    calc
      (2 : ℝ) ^ r ≤ (2 : ℝ) ^ (2 * (r / 2) + 2) :=
        pow_le_pow_right₀ (by norm_num) hupp
      _ = (2 * (2 : ℝ) ^ (r / 2)) ^ 2 := by
        rw [Nat.mul_comm 2 (r / 2), pow_add, pow_mul]
        ring

/-- Explicit real bounds: the constants are absolute and the threshold is six. -/
theorem horakKim_excess_real_bounds (r : ℕ) (hr : 6 ≤ r) :
    (r : ℝ) * Real.sqrt ((2 : ℝ) ^ r) / 8 ≤
        (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1) ∧
    (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1) ≤
        2 * ((r : ℝ) * Real.sqrt ((2 : ℝ) ^ r)) := by
  have hb := two_pow_le_horakKim r (by omega)
  have he : (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1) =
      ((horakKim r - 2 ^ (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hb]
    norm_cast
  have hn := horakKim_excess_nat_bounds r hr
  have hlow : (r : ℝ) * (2 : ℝ) ^ (r / 2) ≤
      4 * ((horakKim r - 2 ^ (r - 1) : ℕ) : ℝ) := by exact_mod_cast hn.1
  have hupp : ((horakKim r - 2 ^ (r - 1) : ℕ) : ℝ) ≤
      2 * (r : ℝ) * (2 : ℝ) ^ (r / 2) := by exact_mod_cast hn.2
  have hs := two_pow_half_sqrt_bounds r
  have hs₁ := mul_le_mul_of_nonneg_left hs.1 (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hs₂ := mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  rw [he]
  constructor <;> nlinarith

/-- Horak--Kim's excess is of sharp second order, with both parity cases proved above. -/
theorem horakKim_excess_isTheta :
    (fun r : ℕ => (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) * Real.sqrt ((2 : ℝ) ^ r)) := by
  constructor
  · refine isBigO_iff.2 ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop 6] with r hr
    have h := horakKim_excess_real_bounds r hr
    have he : 0 ≤ (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1) :=
      le_trans (by positivity) h.1
    have hg : 0 ≤ (r : ℝ) * Real.sqrt ((2 : ℝ) ^ r) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg he, abs_of_nonneg hg] using h.2
  · refine isBigO_iff.2 ⟨8, ?_⟩
    filter_upwards [eventually_ge_atTop 6] with r hr
    have h := horakKim_excess_real_bounds r hr
    have he : 0 ≤ (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1) :=
      le_trans (by positivity) h.1
    have hg : 0 ≤ (r : ℝ) * Real.sqrt ((2 : ℝ) ^ r) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg he, abs_of_nonneg hg]
    nlinarith [h.1]

/-- The sharp second-order maximum-cycle assertion, with a real square-root scale. -/
def SharpSecondOrderStatement : Prop :=
  (fun r : ℕ => (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1)) =Θ[atTop]
    (fun r : ℕ => (r : ℝ) * Real.sqrt ((2 : ℝ) ^ r))

/-- Conditional implication only: eventual exactness supplies the missing graph theorem. -/
theorem sharpSecondOrder_of_exactMaximum (h : ExactMaximumStatement) :
    SharpSecondOrderStatement := by
  obtain ⟨R, hR⟩ := h
  have he : (fun r : ℕ => (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1)) =ᶠ[atTop]
      (fun r : ℕ => (horakKim r : ℝ) - (2 : ℝ) ^ (r - 1)) := by
    filter_upwards [eventually_ge_atTop R] with r hr
    rw [hR r hr]
  exact he.trans_isTheta horakKim_excess_isTheta

/-- The square-root scale is exactly the usual real half-exponent scale. -/
theorem sqrt_two_pow_eq_rpow (r : ℕ) :
    Real.sqrt ((2 : ℝ) ^ r) = (2 : ℝ) ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) r,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The standard `r * 2^(r/2)` formulation, conditional only on eventual exactness. -/
theorem sharpSecondOrder_rpow_of_exactMaximum (h : ExactMaximumStatement) :
    (fun r : ℕ => (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) := by
  simpa only [SharpSecondOrderStatement, sqrt_two_pow_eq_rpow] using
    sharpSecondOrder_of_exactMaximum h

/-- Eventual exactness also gives explicit two-sided bounds, not just asymptotic notation. -/
theorem sharpSecondOrder_explicit_of_exactMaximum (h : ExactMaximumStatement) :
    ∃ R : ℕ, ∀ r, R ≤ r →
      (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2) / 8 ≤
          (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1) ∧
      (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1) ≤
          2 * ((r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨max R 6, fun r hr => ?_⟩
  rw [hR r (le_trans (le_max_left _ _) hr)]
  simpa only [sqrt_two_pow_eq_rpow] using
    horakKim_excess_real_bounds r (le_trans (le_max_right _ _) hr)

end Erdos1016.ExactMaximumSupport
