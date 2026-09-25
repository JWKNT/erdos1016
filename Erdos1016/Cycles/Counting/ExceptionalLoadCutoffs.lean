import Erdos1016.Cycles.Counting.DeficitCutoffParameters

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! The actual exceptional-pair load tends uniformly to zero under the
 explicit three-term exterior-link bound from the shorter proof. -/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.ExceptionalLoadCutoffs
open DeficitCutoffParameters

def linkEnvelope (x : ℝ) : ℝ :=
  Real.logb 2 x + x / Real.sqrt (Real.logb 2 x) +
    Real.logb 2 x * Real.sqrt x * Real.logb 2 (Real.logb 2 x)

private theorem logb_square_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => (Real.logb 2 x) ^ 2 / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hraw : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h
  have h' := hraw.div_const ((Real.log 2) ^ 2)
  convert h' using 1
  · ext x
    simp only [Real.logb]
    ring
  · simp

/-- Every fixed multiple of the explicit link error is at most x/100
 eventually. This replaces the manuscript's o(x) with a quantified bound. -/
theorem eventually_linkEnvelope_le (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, A * linkEnvelope x ≤ x / 100 := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.logb 2 x)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hy
  have hinv := hsqrt.inv_tendsto_atTop
  have hsum := ((logb_div_self_tendsto_zero.add hinv).add
    logb_square_div_sqrt_tendsto_zero).const_mul A
  have hsmall : ∀ᶠ x : ℝ in atTop,
      A * (Real.logb 2 x / x + (Real.sqrt (Real.logb 2 x))⁻¹ +
        (Real.logb 2 x) ^ 2 / Real.sqrt x) < 1 / 100 := by
    exact hsum.eventually_lt_const (by norm_num : A * (0 + 0 + 0) < (1 / 100 : ℝ))
  have hzy := hy.eventually
    (logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hy.eventually_ge_atTop 1, hzy, hsmall]
    with x hx hy1 hzy hsmallx
  have hypos : 0 < Real.logb 2 x := by linarith
  have hzle : Real.logb 2 (Real.logb 2 x) ≤ Real.logb 2 x :=
    ((div_lt_one hypos).mp hzy).le
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsqrty : 0 < Real.sqrt (Real.logb 2 x) := Real.sqrt_pos.mpr hypos
  have hterm : Real.logb 2 x * Real.sqrt x * Real.logb 2 (Real.logb 2 x) ≤
      (Real.logb 2 x) ^ 2 * Real.sqrt x := by
    nlinarith [mul_le_mul_of_nonneg_left hzle (mul_nonneg hypos.le hsqrtx.le)]
  have hratio : linkEnvelope x / x ≤
      Real.logb 2 x / x + (Real.sqrt (Real.logb 2 x))⁻¹ +
        (Real.logb 2 x) ^ 2 / Real.sqrt x := by
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    have heq : (Real.logb 2 x + x / Real.sqrt (Real.logb 2 x) +
        (Real.logb 2 x) ^ 2 * Real.sqrt x) / x =
        Real.logb 2 x / x + (Real.sqrt (Real.logb 2 x))⁻¹ +
          (Real.logb 2 x) ^ 2 / Real.sqrt x := by
      have hmiddle : (x / Real.sqrt (Real.logb 2 x)) / x =
          (Real.sqrt (Real.logb 2 x))⁻¹ := by
        field_simp [hx.ne', hsqrty.ne']
        ring
      have hlast : (Real.logb 2 x) ^ 2 * Real.sqrt x / x =
          (Real.logb 2 x) ^ 2 / Real.sqrt x := by
        apply (div_eq_div_iff hx.ne' hsqrtx.ne').mpr
        linear_combination (Real.logb 2 x) ^ 2 * hsq
      rw [add_div, add_div, hmiddle, hlast]
    rw [← heq]
    exact div_le_div_of_nonneg_right (by unfold linkEnvelope; linarith) hx.le
  have htotal : A * linkEnvelope x / x ≤ 1 / 100 := by
    calc
      _ = A * (linkEnvelope x / x) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hratio hA).trans hsmallx.le
  nlinarith [(div_le_iff₀ hx).mp htotal]

/-- Uniform numerical form of equation (10). The constants A and B are
 fixed; c is the witness-component count and e is the excess link count.
 The theorem assumes the displayed explicit envelope, not an o(1) premise. -/
theorem eventually_exceptional_load_le_quarter (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in atTop, ∀ (c e : ℝ) (L s : ℕ),
      c ≤ x / 100 → e ≤ A * linkEnvelope x →
      (L : ℝ) ≤ x * Real.sqrt (Real.logb 2 x) →
      x / 20 - 2 ≤ (s : ℝ) →
      (2 : ℝ) ^ (c + e) * (B * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) ≤ 1 / 4 := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hdecay := (polynomial_dyadic_decay 6 (3 / 100) (by norm_num)).const_mul (4 * B)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hy.eventually_ge_atTop 1,
    logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_linkEnvelope_le A hA,
    hdecay.eventually_lt_const (by norm_num : (4 * B) * 0 < (1 / 4 : ℝ))] with
    x hx hy1 hyx henv hdec
  intro c e L s hc he hL hs
  have hxpos : 0 < x := by linarith
  have hy0 : 0 ≤ Real.logb 2 x := by linarith
  have hyle : Real.logb 2 x ≤ x := ((div_lt_one hxpos).mp hyx).le
  have hroot : Real.sqrt (Real.logb 2 x) ≤ x := by
    nlinarith [Real.sq_sqrt hy0, Real.sqrt_nonneg (Real.logb 2 x)]
  have hLx : (L : ℝ) ≤ x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hroot hxpos.le]
  have hL3 : (L : ℝ) ^ 3 ≤ x ^ 6 := by
    calc
      _ ≤ (x ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hLx 3
      _ = _ := by ring
  have hexponent : c + e - (s : ℝ) ≤ -(3 / 100 : ℝ) * x + 2 := by
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent
  have hinv : (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ (-(s : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, div_pow, one_pow]
    simp only [one_div]
  have hfactor : (2 : ℝ) ^ (c + e) * (1 / 2 : ℝ) ^ s =
      (2 : ℝ) ^ (c + e - (s : ℝ)) := by
    rw [hinv, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
  have hupper : (2 : ℝ) ^ (-(3 / 100 : ℝ) * x + 2) =
      4 * (2 : ℝ) ^ (-(3 / 100 : ℝ) * x) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  calc
    _ = B * (L : ℝ) ^ 3 * ((2 : ℝ) ^ (c + e) * (1 / 2 : ℝ) ^ s) := by ring
    _ ≤ B * x ^ 6 * (4 * (2 : ℝ) ^ (-(3 / 100 : ℝ) * x)) := by
      rw [hfactor]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hL3 hB)
        (hpow.trans_eq hupper) (by positivity) (by positivity)
    _ = (4 * B) * (x ^ 6 * (2 : ℝ) ^ (-(3 / 100 : ℝ) * x)) := by ring
    _ ≤ _ := hdec.le

/-- Specialization to the actual integer cutoffs used for the cycle supply. -/
theorem eventually_cutoff_exceptional_load_le_quarter (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in atTop, ∀ c e : ℝ,
      c ≤ x / 100 → e ≤ A * linkEnvelope x →
      (2 : ℝ) ^ (c + e) *
        (B * ((2 * upperHalfLength x : ℕ) : ℝ) ^ 3 *
          (1 / 2 : ℝ) ^ suffixCutoff x) ≤ 1 / 4 := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hy.comp hy
  filter_upwards [eventually_exceptional_load_le_quarter A B hA hB,
    eventually_ge_atTop (100 : ℝ), hy.eventually_ge_atTop 4,
    hz.eventually_ge_atTop 32,
    logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with
    x hload hx hY hZ hYX
  intro c e hc he
  have hyx : Real.logb 2 x ≤ x := ((div_lt_one (by linarith : 0 < x)).mp hYX).le
  obtain ⟨hM, hK, hMK, hKhi, hs, hsD, hslo, hlog⟩ := cutoff_bounds x hx hY hyx hZ
  apply hload c e (2 * upperHalfLength x) (suffixCutoff x) hc he ?_ hslo
  have hfloor := Nat.floor_le
    (show 0 ≤ x * Real.sqrt (Real.logb 2 x) / 2 by positivity)
  change (upperHalfLength x : ℝ) ≤ x * Real.sqrt (Real.logb 2 x) / 2 at hfloor
  push_cast
  linarith

end Erdos1016.Proof.ExceptionalLoadCutoffs
