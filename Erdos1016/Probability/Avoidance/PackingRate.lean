import Erdos1016.Cycles.Selection.ProtectedCoreDichotomy

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.ManyCycleRate
open CycleSupply ProtectorCoreDichotomy
open ConnectorCutoffLimits
open CutoffLimits

/-- Substitution of the exact logarithmic length and polynomial packing
cutoffs into the already proved finite MANY estimate. -/
theorem manyBound_le_polynomial {c n : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (hx : 2 ≤ Real.logb 2 n) (hh1 : c * n ^ (-(1 / 8 : ℝ)) ≤ 1) :
    manyBound c n ≤ (11 * (2 / c) * (1 / (2 * Real.log 2)) ^ 2) *
      (Real.log n) ^ 2 / n ^ (1 / 8 : ℝ) := by
  have hnpos : 0 < n := by linarith
  let D := logarithmicGirthCutoff n
  let h := c * n ^ (-(1 / 8 : ℝ))
  have hh : 0 < h := by dsimp [h]; positivity
  have hD : 1 ≤ D := by apply Nat.le_floor; linarith
  have hDf : (D : ℝ) ≤ Real.logb 2 n / 2 := Nat.floor_le (by linarith)
  have hrecip : 1 / (h / 2) ≤ (2 / c) * n ^ (1 / 8 : ℝ) := by
    dsimp [h]
    rw [Real.rpow_neg hnpos.le]
    field_simp
    ring_nf
    exact le_rfl
  have hlog : (D : ℝ) ≤ (1 / (2 * Real.log 2)) * Real.log n := by
    convert hDf using 1
    rw [Real.logb]
    ring
  have hbinary : (2 : ℝ) ^ D ≤ n ^ (1 / 2 : ℝ) := by
    calc
      _ = (2 : ℝ) ^ (D : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (Real.logb 2 n / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hDf
      _ = n ^ (1 / 2 : ℝ) := by
        rw [show Real.logb 2 n / 2 = Real.logb 2 n * (1 / 2) by ring,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hnpos]
  have ht := many_bound_power_majorant n (h / 2) (1 / 8) (2 / c)
    (1 / (2 * Real.log 2)) D (polynomialPackingCutoff n) hn (by positivity)
    (by dsimp [h]; linarith) hD (by positivity) (by positivity)
    hrecip hlog hbinary (Nat.le_ceil _)
  norm_num at ht
  simpa [manyBound, D, h, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using ht

/-- Every fixed polynomial saving, including its logarithmic-square factor,
beats every fixed stretched-exponential target of this square-root scale. -/
theorem polynomial_le_stretched_eventually (C γ : ℝ) (hγ : 0 < γ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, C * (Real.log (n j)) ^ 2 / (n j) ^ (1 / 8 : ℝ) ≤
      (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (n j))) := by
  have ht := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 16)).tendsto_div_nhds_zero.comp hn).const_mul C
  simp only [mul_zero, Real.rpow_two] at ht
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  have hs := CutoffAvoidance.sqrt_tendsto_atTop _ hx
  filter_upwards [hn.eventually_gt_atTop 1, hx.eventually_ge_atTop 0,
      hs.eventually_ge_atTop (16 * γ), ht.eventually_lt_const (zero_lt_one : (0 : ℝ) < 1)]
    with j hnj hxj hsj htj
  have hnpos : 0 < n j := by linarith
  have hnum : C * Real.log (n j) ^ 2 ≤ (n j) ^ (1 / 16 : ℝ) := by
    have hh : C * Real.log (n j) ^ 2 / (n j) ^ (1 / 16 : ℝ) ≤ 1 := by
      simpa only [mul_div_assoc, Function.comp_apply] using htj.le
    exact (div_le_one (Real.rpow_pos_of_pos hnpos _)).mp hh
  have hs2 := Real.sq_sqrt hxj
  simp only [Function.comp_apply] at hxj hsj hs2
  have hpower : -(Real.logb 2 (n j)) / 16 ≤ -γ * Real.sqrt (Real.logb 2 (n j)) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (Real.logb 2 (n j)))
      (sub_nonneg.mpr hsj)]
  calc
    _ ≤ (n j) ^ (1 / 16 : ℝ) / (n j) ^ (1 / 8 : ℝ) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (n j) ^ (-(1 / 16 : ℝ)) := by rw [← Real.rpow_sub hnpos]; norm_num
    _ = ((2 : ℝ) ^ Real.logb 2 (n j)) ^ (-(1 / 16 : ℝ)) := by
      rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hnpos]
    _ = (2 : ℝ) ^ (-(Real.logb 2 (n j)) / 16) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hpower

theorem manyBound_le_stretched_eventually (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, manyBound c (n j) ≤
      (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (n j))) := by
  have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hn).const_mul c
  simp only [mul_zero] at hh
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  filter_upwards [hn.eventually_ge_atTop 1, hx.eventually_ge_atTop 2,
      hh.eventually_lt_const (zero_lt_one : (0 : ℝ) < 1),
      polynomial_le_stretched_eventually (11 * (2 / c) * (1 / (2 * Real.log 2)) ^ 2) γ hγ n hn]
    with j hnj hxj hhj hr
  exact (manyBound_le_polynomial hc hnj hxj hhj.le).trans hr

end Erdos1016.Proof.ManyCycleRate
