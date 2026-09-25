import Erdos1016.Probability.Avoidance.PoissonErrorBounds
import Erdos1016.Cycles.Selection.CutoffLimits

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Uniform scalar parameter assembly for manuscript Section 6

All cutoffs and the selected-family target here are deterministic functions of
`x = log₂ n`. The eventual bounds quantify over every mean in the selection
interval and every load below the actual cutoff load. Thus the onset does not
depend on which graph or selected family realizes these scalar data.
-/

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.CutoffAvoidance

open CutoffLimits
open ConditionalLoadDecay

/-- Least even natural number at least `6x` on the natural domain `x≥0`. -/
def traceStart (x : ℝ) : ℕ := 2 * Nat.ceil (3 * x)

/-- Deterministic retained-family selection target from equation (6.7). -/
def selectionTarget (σ x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((cutoffL σ x : ℝ) / (traceStart x : ℝ)) - 1

/-- The selected mean has this uniform elementary lower bound. -/
def meanFloor (σ x : ℝ) : ℝ :=
  (σ * Real.log 2 / 2) * Real.sqrt x - (1 / 2 : ℝ) * Real.log x - 3

/-- Exact ceiling-bearing conditional load in the manuscript. -/
def cutoffLoad (σ x : ℝ) : ℝ := Real.exp
  (exactDstarLogScale (cutoffQ σ x) (cutoffS x) (momentK σ x)
    (cutoffRc σ x) (cutoffDelta σ x) (cutoffL σ x))

theorem traceStart_bounds {x : ℝ} (hx : 1 ≤ x) :
    6 * x ≤ (traceStart x : ℝ) ∧ (traceStart x : ℝ) ≤ 8 * x := by
  have hlo := Nat.le_ceil (3 * x)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 3 * x by linarith)
  dsimp [traceStart]
  push_cast
  constructor <;> linarith

/-- Rounding errors in both cutoffs cost only a fixed additive constant. -/
theorem selectionTarget_bounds {σ x : ℝ} (hσ : 0 < σ) (hx : 1 ≤ x)
    (hlarge : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt x)) :
    meanFloor σ x ≤ selectionTarget σ x ∧
      selectionTarget σ x + 1 ≤ σ * Real.sqrt x := by
  have hs := Real.sqrt_nonneg x
  have hM := traceStart_bounds hx
  have hMpos : 0 < (traceStart x : ℝ) := by linarith [hM.1]
  have hMone : 1 ≤ (traceStart x : ℝ) := by linarith [hM.1]
  have hL := largestOddCutoff_bounds ((2 : ℝ) ^ (σ * Real.sqrt x)) hlarge
  change _ < (cutoffL σ x : ℝ) ∧ (cutoffL σ x : ℝ) ≤ _ at hL
  have hLpos : 0 < (cutoffL σ x : ℝ) := by linarith [hL.1]
  have hLhalf : (2 : ℝ) ^ (σ * Real.sqrt x) / 2 ≤ (cutoffL σ x : ℝ) := by
    linarith [hL.1]
  have hlogLlow := Real.log_le_log (show 0 < (2 : ℝ) ^ (σ * Real.sqrt x) / 2 by positivity) hLhalf
  have hlogLhigh := Real.log_le_log hLpos hL.2
  have hpowlog : Real.log ((2 : ℝ) ^ (σ * Real.sqrt x)) =
      (σ * Real.sqrt x) * Real.log 2 := Real.log_rpow (by norm_num) _
  rw [Real.log_div (by positivity) (by norm_num), hpowlog] at hlogLlow
  rw [hpowlog] at hlogLhigh
  have hlogM := Real.log_le_log hMpos hM.2
  have hxpos : 0 < x := by linarith
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hxpos.ne'] at hlogM
  have hlogMnonneg := Real.log_nonneg hMone
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  dsimp [selectionTarget, meanFloor]
  rw [Real.log_div hLpos.ne' hMpos.ne']
  constructor
  · rw [hlog8] at hlogM
    nlinarith
  · have hprod := mul_nonneg (show 0 ≤ σ * Real.sqrt x by positivity)
      (show 0 ≤ 2 - Real.log 2 by linarith)
    nlinarith



/-- The square-root scale tends to infinity along every diverging size sequence. -/
theorem sqrt_tendsto_atTop (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
  simpa only [Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx

/-- The deterministic lower mean diverges; the logarithmic correction is
strictly smaller than its square-root leading term. -/
theorem meanFloor_tendsto_atTop (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => meanFloor σ (x j)) atTop atTop := by
  have hsqrt := sqrt_tendsto_atTop x hx
  have hinv := hsqrt.inv_tendsto_atTop
  have hlog : Tendsto (fun j => Real.log (x j) / Real.sqrt (x j)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have h' : Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using h
    exact h'.comp hx
  let a := σ * Real.log 2 / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hratio : Tendsto (fun j => meanFloor σ (x j) / Real.sqrt (x j))
      atTop (𝓝 a) := by
    have h := ((tendsto_const_nhds (x := a)).sub (hlog.const_mul (1 / 2 : ℝ))).sub
      (hinv.const_mul (3 : ℝ))
    have h' : Tendsto (fun j => a - (1 / 2 : ℝ) * (Real.log (x j) / Real.sqrt (x j)) -
        3 * (Real.sqrt (x j))⁻¹) atTop (𝓝 a) := by simpa using h
    apply h'.congr'
    filter_upwards [hx.eventually_gt_atTop 0] with j hj
    dsimp [meanFloor, a]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hj)]
    ring
  have hbound : ∀ᶠ j in atTop, (a / 2) * Real.sqrt (x j) ≤ meanFloor σ (x j) := by
    filter_upwards [hratio.eventually (Ioi_mem_nhds (show a / 2 < a by linarith)),
      hx.eventually_gt_atTop 0] with j hj hxj
    exact ((lt_div_iff₀ (Real.sqrt_pos.2 hxj)).mp hj).le
  exact tendsto_atTop_mono' atTop hbound
    ((tendsto_const_mul_atTop_of_pos (by positivity : 0 < a / 2)).mpr hsqrt)

/-- The exact ceiling penalty is bounded by the existing simplified load
expression on the positive logarithmic domain. -/
theorem cutoffLoad_le_majorant {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    cutoffLoad σ x ≤ Real.exp
      (loadLogScale (cutoffQ σ x) (cutoffS x) (momentK σ x)
        (cutoffRc σ x) (cutoffL σ x)) := by
  have hK : 1 ≤ momentK σ x := by
    have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt x) :=
      Nat.one_le_ceil_iff.mpr (by positivity)
    dsimp [momentK]
    omega
  have hL : 1 ≤ cutoffL σ x := by dsimp [cutoffL, largestOddCutoff]; omega
  have hr : 1 ≤ cutoffRc σ x := by
    apply Nat.one_le_ceil_iff.mpr
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    have hKr : (1 : ℝ) ≤ momentK σ x := by exact_mod_cast hK
    have hLr : (1 : ℝ) ≤ cutoffL σ x := by exact_mod_cast hL
    nlinarith [mul_nonneg (sub_nonneg.mpr hKr) (sub_nonneg.mpr hLr)]
  have hΔ : momentK σ x * (2 * cutoffRc σ x - 1) ≤ cutoffDelta σ x := by
    simpa [cutoffDelta, cutoffQ] using
      ConditionalPenaltyBounds.separation_denominator_lower_bound
        (momentK σ x) (cutoffRc σ x) hK hr
  exact Real.exp_le_exp.mpr (exactDstarLogScale_le_loadLogScale _ _ _ _ _ _ hK hr hΔ)

/-- Equation (6.6), with the fixed negative power retained. This is stronger
than the previously available assertion that the load merely tends to zero. -/
theorem cutoffLoad_le_exp_power_eventually
    (σ : ℝ) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    ∀ᶠ j in atTop, cutoffLoad σ (x j) ≤
      Real.exp (-(Real.log 2 / 5) * x j) := by
  have hscale := normalized_loadLogScale_tendsto x
    (fun j => cutoffQ σ (x j)) (fun j => cutoffS (x j))
    (fun j => momentK σ (x j)) (fun j => cutoffRc σ (x j))
    (fun j => cutoffL σ (x j)) (20 * σ ^ 2) (1 / 4) hx
    (cutoffQ_ratio_tendsto σ hσ x hx) (cutoffS_ratio_tendsto x hx)
    (momentK_ratio_tendsto_zero σ hσ.le x hx)
    (cutoffPenalty_tendsto_zero σ hσ x hx)
    (cutoffL_log_over_x_tendsto_zero σ hσ x hx)
  have hcoeff : (20 * σ ^ 2 - 1 / 4) * Real.log 2 < -(Real.log 2 / 5) := by
    have hsq : σ ^ 2 < (1 / 20 : ℝ) ^ 2 := by nlinarith
    have hgap : 20 * σ ^ 2 - 1 / 4 < -(1 / 5 : ℝ) := by nlinarith
    have h := mul_lt_mul_of_pos_right hgap (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    nlinarith
  filter_upwards [hscale.eventually_lt_const hcoeff, hx.eventually_gt_atTop 0]
    with j hj hxj
  apply (cutoffLoad_le_majorant hσ hxj).trans
  exact Real.exp_le_exp.mpr ((div_lt_iff₀ hxj).mp hj).le

/-- With the manuscript's fixed small `σ`, the actual ceiling-rounded moment
order lies between `10σ√x` and `√x` once `√x≥4`. -/
theorem momentK_bounds {σ x : ℝ} (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (hs : 4 ≤ Real.sqrt x) :
    10 * σ * Real.sqrt x ≤ (momentK σ x : ℝ) ∧
      (momentK σ x : ℝ) ≤ Real.sqrt x := by
  have hnonneg : 0 ≤ 5 * σ * Real.sqrt x := by positivity
  have hlo := Nat.le_ceil (5 * σ * Real.sqrt x)
  have hhi := Nat.ceil_lt_add_one hnonneg
  have hσmul := mul_le_mul_of_nonneg_right hσ20.le (Real.sqrt_nonneg x)
  dsimp [momentK]
  push_cast
  constructor <;> nlinarith



end Erdos1016.Proof.CutoffAvoidance
