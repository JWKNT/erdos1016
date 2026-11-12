import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Link and exponential decay budgets

These estimates use the actual rounded choices from `ParameterBudget`.
The link envelope includes the constants in the proved multigraph link theorem.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

theorem polynomial_rpow_decay (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x^n * (2 : ℝ)^(-b*x)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ)
    (Real.log 2 * b) (mul_pos (Real.log_pos (by norm_num)) hb)
  convert h using 1
  funext x
  rw [Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

theorem parallelDepth_div_x :
    Tendsto (fun x => (parallelDepth x : ℝ) / x) atTop (𝓝 0) := by
  have h := parallelDepth_ratio.mul logScale_ratio
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [logScale_atTop.eventually (eventually_gt_atTop 0)] with x hx
  exact div_mul_div_cancel₀ hx.ne'

theorem parallel_power_bound : ∀ᶠ x in atTop,
    (2 : ℝ) ^ parallelDepth x ≤ x / (logScale x)^2 := by
  have hr := parallelDepth_ratio
  have hraw : Tendsto
      (fun x => (logScale x - 2 * Real.logb 2 (logScale x)) / logScale x)
      atTop (𝓝 (1 : ℝ)) := by
    have h := logScale_ratio.comp logScale_atTop
    have hid : Tendsto (fun x => logScale x / logScale x) atTop (𝓝 (1 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [logScale_atTop.eventually (eventually_gt_atTop 0)] with x hx
      simp [hx.ne']
    simpa only [sub_div, mul_div_assoc, mul_zero, sub_zero, logScale] using hid.sub (h.const_mul 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    logScale_atTop.eventually (eventually_gt_atTop 0),
    hraw.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with x hx hz hrawx
  have hp : 0 ≤ logScale x - 2 * Real.logb 2 (logScale x) := by
    simpa only [zero_mul] using ((lt_div_iff₀ hz).mp hrawx).le
  calc
    (2 : ℝ)^parallelDepth x = (2 : ℝ)^(parallelDepth x : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ)^(logScale x - 2 * Real.logb 2 (logScale x)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hp)
    _ = x / (logScale x)^2 := by
      rw [Real.rpow_sub (by norm_num),
        show 2 * Real.logb 2 (logScale x) = Real.logb 2 (logScale x) * 2 by ring,
        Real.rpow_mul (by norm_num), Real.rpow_two,
        Real.rpow_logb (by norm_num) (by norm_num) hz]
      rw [show (2 : ℝ)^logScale x = x from
        Real.rpow_logb (by norm_num) (by norm_num) hx]

/-- A convenient upper envelope for every large-scale link count. -/
def linkCeiling (x : ℝ) : ℝ :=
  2 + 2 * cutoff x / (parallelDepth x + 1) +
    3 * x / (logScale x)^2 + 578 * (32 * amplitude)^2

theorem linkCeiling_div_x : Tendsto (fun x => linkCeiling x / x) atTop (𝓝 0) := by
  have hc : Tendsto (fun x : ℝ => (2 + 578 * (32 * amplitude)^2) / x)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hd : Tendsto (fun x => ((parallelDepth x : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      (tendsto_natCast_atTop_iff.mpr parallelDepth_atTop)
  have hm : Tendsto (fun x => (2 * ((cutoff x : ℝ) / x)) /
      ((parallelDepth x : ℝ) + 1)) atTop (𝓝 0) :=
    (cutoff_ratio.const_mul 2).div_atTop hd
  have hs : Tendsto (fun x => (3 : ℝ) / (logScale x)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp logScale_atTop)
  have hh := (hc.add hm).add hs
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp [linkCeiling]
  field_simp
  ring

theorem eventually_cutoff_bounds : ∀ᶠ x in atTop,
    4 ≤ cutoff x ∧ (cutoff x : ℝ) ≤ 2 * amplitude * x ∧ x ≤ cutoff x := by
  have hupper := cutoff_ratio.eventually_lt_const (show amplitude < 2 * amplitude by
    linarith [amplitude_pos])
  have hlower := cutoff_ratio.eventually_const_lt (show (1 : ℝ) < amplitude by
    linarith [amplitude_gt_six])
  filter_upwards [hupper, hlower, eventually_ge_atTop (4 : ℝ)] with x hu hl hx
  have hx0 : 0 < x := by linarith
  have hL := (lt_div_iff₀ hx0).mp hl
  refine ⟨?_, ?_, by simpa using hL.le⟩
  · exact_mod_cast (show (4 : ℝ) ≤ cutoff x by linarith)
  · simpa [mul_assoc] using ((div_lt_iff₀ hx0).mp hu).le

/-- The link exponent is sublinear, uniformly over the permitted upper scale. -/
theorem eventually_link_budget : ∀ᶠ (x : ℝ) in atTop, ∀ D : ℕ,
    x / 16 ≤ D →
    1 + 2 * (cutoff x : ℝ) / (parallelDepth x + 1) +
      (3 * (2 : ℝ)^parallelDepth x + 1) + 578 * ((cutoff x : ℝ) / D)^2 ≤ x / 64 := by
  have hb := linkCeiling_div_x.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 64)
  filter_upwards [eventually_cutoff_bounds, parallel_power_bound, hb,
    eventually_gt_atTop (0 : ℝ)] with x hL hp hb hx
  intro D hD
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (div_pos hx (by norm_num)) hD
  have hratio : (cutoff x : ℝ) / D ≤ 32 * amplitude := by
    apply (div_le_iff₀ hD0).mpr
    have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ 32 * amplitude by have := amplitude_pos; positivity)
    nlinarith only [hh, hL.2.1]
  have hs := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hD0.le) hratio 2
  have hbc : linkCeiling x ≤ x / 64 := by
    have hh := ((div_lt_iff₀ hx).mp hb).le
    nlinarith only [hh]
  dsimp [linkCeiling] at hbc
  simp only [mul_div_assoc] at hbc ⊢
  linarith only [hbc, hp, hs]

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget
