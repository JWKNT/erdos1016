import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Dyadic choices and deletion-size exponents

The same initial dyadic scale supplies both girth thresholds.
The bounds include the integer logarithms in the proved packing recurrence.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

def scaleIndex (D : ℕ) (y : ℝ) : ℕ := ⌈Real.logb 2 (y / D)⌉₊

theorem chosen_scale_bounds (D : ℕ) (hD : 0 < D) (y : ℝ) (hy : D ≤ y) :
    y ≤ (GirthRaiseBounds.scale D (scaleIndex D y) : ℝ) ∧
      (GirthRaiseBounds.scale D (scaleIndex D y) : ℝ) < 2*y := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hy0 : 0 < y := lt_of_lt_of_le hD0 hy
  have hratio : 1 ≤ y / D := (le_div_iff₀ hD0).mpr (by simpa using hy)
  have hlog : 0 ≤ Real.logb 2 (y / D) :=
    Real.logb_nonneg (by norm_num) hratio
  have heq : (GirthRaiseBounds.scale D (scaleIndex D y) : ℝ) =
      (2 : ℝ)^(scaleIndex D y : ℝ) * D := by
    simp [GirthRaiseBounds.scale, Real.rpow_natCast]
  rw [heq]
  constructor
  · have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.le_ceil (Real.logb 2 (y / D)))
    rw [Real.rpow_logb (by norm_num) (by norm_num) (div_pos hy0 hD0)] at h
    exact (div_le_iff₀ hD0).mp h
  · have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (Nat.ceil_lt_add_one hlog)
    rw [Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_logb (by norm_num) (by norm_num) (div_pos hy0 hD0)] at h
    have hh := mul_lt_mul_of_pos_right h hD0
    convert hh using 1
    field_simp
    ring

def deletionExponent (D : ℕ) : ℕ := 2*D + 6*(Nat.clog 2 D)^2

theorem clog_le_logScale_add_one (D : ℕ) (hD : 0 < D) (x : ℝ) (hDx : D ≤ x) :
    (Nat.clog 2 D : ℝ) ≤ logScale x + 1 := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hl : 0 ≤ Real.logb 2 (D : ℝ) := Real.logb_nonneg (by norm_num) hD1
  rw [← Real.natCeil_logb_natCast 2 D]
  exact (Nat.ceil_lt_add_one hl).le.trans
    (add_le_add_right (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hD) hDx) 1)

theorem log_square_div_x :
    Tendsto (fun x => (logScale x + 1)^2 / x) atTop (𝓝 0) := by
  have hsq := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hsq' : Tendsto (fun x => (logScale x)^2 / x) atTop (𝓝 0) := by
    convert hsq.div_const ((Real.log 2)^2) using 1
    · funext x
      dsimp [logScale, Real.logb]
      ring
    · simp
  have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  convert (hsq'.add (logScale_ratio.const_mul 2)).add hi using 1
  · funext x
    ring
  · norm_num

theorem sqrt_div_x : Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)
  have hi : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs0 := Real.sqrt_pos.mpr hx
  have heq := Real.sq_sqrt hx.le
  apply (div_eq_div_iff hs0.ne' hx.ne').mpr
  nlinarith

/-- The smaller deleted set has a sublinear base-two exponent. -/
theorem small_exponent_ratio :
    Tendsto (fun x => (4*Real.sqrt x + 6*(logScale x+1)^2)/x) atTop (𝓝 0) := by
  simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
    (sqrt_div_x.const_mul 4).add (log_square_div_x.const_mul 6)

/-- The larger deleted set has exponent asymptotic to one quarter of `x`. -/
theorem large_exponent_ratio :
    Tendsto (fun x => (x/4 + 6*(logScale x+1)^2)/x) atTop (𝓝 (1/4 : ℝ)) := by
  have hc : Tendsto (fun x : ℝ => (x/4)/x) atTop (𝓝 (1/4 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
    hc.add (log_square_div_x.const_mul 6)

/-- Both proved packing exponents admit fixed eventual margins. -/
theorem eventually_deletion_exponents : ∀ᶠ x in atTop,
    (∀ D : ℕ, 0 < D → (D : ℝ) ≤ 2*Real.sqrt x →
      (deletionExponent D : ℝ) ≤ x/128) ∧
    (∀ D : ℕ, 0 < D → (D : ℝ) ≤ x/8 →
      (deletionExponent D : ℝ) ≤ x/3) := by
  have hs := small_exponent_ratio.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1/128)
  have hl := large_exponent_ratio.eventually_lt_const
    (by norm_num : (1/4 : ℝ) < 1/3)
  filter_upwards [hs, hl, eventually_ge_atTop (4 : ℝ)] with x hs hl hx
  have hx0 : 0 < x := by linarith
  have hz : 0 ≤ logScale x := Real.logb_nonneg (by norm_num) (by linarith)
  have hsx : 2*Real.sqrt x ≤ x := by
    have hh := Real.sq_sqrt hx0.le
    have hn := Real.sqrt_nonneg x
    nlinarith
  constructor
  · intro D hD hDs
    have hcl := clog_le_logScale_add_one D hD x (hDs.trans hsx)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.clog 2 D)) hcl 2
    have hh := (div_lt_iff₀ hx0).mp hs
    dsimp [deletionExponent]
    push_cast
    nlinarith
  · intro D hD hDl
    have hcl := clog_le_logScale_add_one D hD x (by linarith)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.clog 2 D)) hcl 2
    have hh := (div_lt_iff₀ hx0).mp hl
    dsimp [deletionExponent]
    push_cast
    nlinarith

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget
