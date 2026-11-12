import Erdos1016.ExactMaximumSupport.LargeGirth.GirthRaiseBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Scalar choices for the large-girth argument

The variable `x` is the base-two logarithm of the ambient rank.
The cycle cutoff is even, so it matches the finite trace theorem exactly.
All limits below are proved for these choices, before any graph is supplied.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

def amplitude : ℝ := 6 * Real.exp 124
def traceStart (x : ℝ) : ℕ := ⌈3 * x⌉₊
def halfCutoff (x : ℝ) : ℕ := ⌈amplitude * x / 2⌉₊
def cutoff (x : ℝ) : ℕ := 2 * halfCutoff x
def logScale (x : ℝ) : ℝ := Real.logb 2 x
def parallelDepth (x : ℝ) : ℕ :=
  ⌊logScale x - 2 * Real.logb 2 (logScale x)⌋₊

theorem amplitude_pos : 0 < amplitude := by
  unfold amplitude
  positivity

theorem amplitude_gt_six : 6 < amplitude := by
  have h := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 124)
  dsimp [amplitude]
  linarith

/-- Rounding a numerator changes its ratio by at most the reciprocal denominator. -/
theorem ceil_div_tendsto {f g : ℝ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop atTop)
    (hf : Tendsto (fun x => f x / g x) atTop (𝓝 c))
    (hf0 : ∀ᶠ x in atTop, 0 ≤ f x) :
    Tendsto (fun x => (⌈f x⌉₊ : ℝ) / g x) atTop (𝓝 c) := by
  have hi : Tendsto (fun x => (1 : ℝ) / g x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hf
    (show Tendsto (fun x => f x / g x + 1 / g x) atTop (𝓝 c) by
      simpa using hf.add hi)
  · filter_upwards [hg.eventually (eventually_gt_atTop 0)] with x hx
    exact div_le_div_of_nonneg_right (Nat.le_ceil _) hx.le
  · filter_upwards [hf0, hg.eventually (eventually_gt_atTop 0)] with x hx hgx
    have h := (div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hx).le hgx.le)
    simpa only [add_div, one_div] using h

theorem floor_div_tendsto {f g : ℝ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop atTop)
    (hf : Tendsto (fun x => f x / g x) atTop (𝓝 c))
    (hf0 : ∀ᶠ x in atTop, 0 ≤ f x) :
    Tendsto (fun x => (⌊f x⌋₊ : ℝ) / g x) atTop (𝓝 c) := by
  have hi : Tendsto (fun x => (1 : ℝ) / g x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun x => f x / g x - 1 / g x) atTop (𝓝 c) by
      simpa using hf.sub hi) hf
  · filter_upwards [hg.eventually (eventually_gt_atTop 0)] with x hx
    have h : f x - 1 ≤ (⌊f x⌋₊ : ℝ) := by
      have hh := Nat.lt_floor_add_one (f x)
      linarith
    simpa only [sub_div, one_div] using div_le_div_of_nonneg_right h hx.le
  · filter_upwards [hf0, hg.eventually (eventually_gt_atTop 0)] with x hx hgx
    exact div_le_div_of_nonneg_right (Nat.floor_le hx) hgx.le

theorem traceStart_ratio :
    Tendsto (fun x => (traceStart x : ℝ) / x) atTop (𝓝 3) := by
  apply ceil_div_tendsto tendsto_id
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [hx.ne']
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    positivity

theorem halfCutoff_ratio :
    Tendsto (fun x => (halfCutoff x : ℝ) / x) atTop (𝓝 (amplitude / 2)) := by
  apply ceil_div_tendsto tendsto_id
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
    ring
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_nonneg (mul_nonneg amplitude_pos.le hx) (by norm_num)

theorem cutoff_ratio :
    Tendsto (fun x => (cutoff x : ℝ) / x) atTop (𝓝 amplitude) := by
  convert halfCutoff_ratio.const_mul 2 using 1 <;>
    simp [cutoff, mul_div_assoc]
  ring

theorem logScale_atTop : Tendsto logScale atTop atTop :=
  Real.tendsto_logb_atTop (by norm_num)

theorem logScale_ratio : Tendsto (fun x => logScale x / x) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.div_const (Real.log 2)
  simpa only [logScale, Real.logb, div_right_comm, zero_div] using h

theorem parallelDepth_ratio :
    Tendsto (fun x => (parallelDepth x : ℝ) / logScale x) atTop (𝓝 1) := by
  have hlog := logScale_ratio.comp logScale_atTop
  have hid : Tendsto (fun x => logScale x / logScale x) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [logScale_atTop.eventually (eventually_gt_atTop 0)] with x hx
    simp [hx.ne']
  have hr : Tendsto
      (fun x => (logScale x - 2 * Real.logb 2 (logScale x)) / logScale x)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_div, mul_div_assoc, mul_zero, sub_zero, logScale] using
      hid.sub (hlog.const_mul 2)
  apply floor_div_tendsto logScale_atTop hr
  filter_upwards [hr.eventually_const_lt (by norm_num : (0 : ℝ) < 1),
    logScale_atTop.eventually (eventually_gt_atTop 0)] with x hx hz
  simpa only [zero_mul] using ((lt_div_iff₀ hz).mp hx).le

theorem parallelDepth_atTop : Tendsto parallelDepth atTop atTop := by
  have hr := parallelDepth_ratio.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hg : Tendsto (fun x => (parallelDepth x : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' _ _
      (logScale_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hr, logScale_atTop.eventually (eventually_gt_atTop 0)] with x hx hz
    exact ((lt_div_iff₀ hz).mp hx).le
  exact tendsto_natCast_atTop_iff.mp hg

/-- The trace interval has more logarithmic mass than the finite supply theorem needs. -/
theorem trace_log_ratio :
    Tendsto (fun x => Real.log (((halfCutoff x + 1 : ℕ) : ℝ) / traceStart x))
      atTop (𝓝 124) := by
  have hi : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hnum : Tendsto (fun x => ((halfCutoff x + 1 : ℕ) : ℝ) / x)
      atTop (𝓝 (amplitude / 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using halfCutoff_ratio.add hi
  have hrat : Tendsto (fun x => ((halfCutoff x + 1 : ℕ) : ℝ) / traceStart x)
      atTop (𝓝 (amplitude / 6)) := by
    have hh := hnum.div traceStart_ratio (by norm_num : (3 : ℝ) ≠ 0)
    rw [show amplitude/2/3=amplitude/6 by ring] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_div_div_cancel_right₀ hx.ne' _ _
  have heq : amplitude / 6 = Real.exp 124 := by dsimp [amplitude]; ring
  have hp : amplitude / 6 ≠ 0 := ne_of_gt (div_pos amplitude_pos (by norm_num))
  simpa only [heq, Real.log_exp] using hrat.log hp

theorem eventually_trace_log_budget :
    ∀ᶠ x in atTop, 123 ≤ Real.log (((halfCutoff x + 1 : ℕ) : ℝ) / traceStart x) :=
  (trace_log_ratio.eventually_const_lt (by norm_num : (123 : ℝ) < 124)).mono
    fun _ h => h.le

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget
