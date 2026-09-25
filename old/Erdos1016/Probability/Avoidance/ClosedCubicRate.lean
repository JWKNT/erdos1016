import Erdos1016.Probability.Avoidance.ClosedCubicBound

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.ClosedCubicDecay
open BoundaryDecay ConnectorCutoffLimits

/-- The exponentially small closed cubic bound satisfies every fixed
square-root logarithmic decay rate uniformly in the order. -/
theorem closed_cubic_stretched_eventually (γ : ℝ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph), IsEmpty (CorePin H) →
      (H.vertexCount : ℝ) = n j → H.IsConnected →
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      coreBoundaryAverage H ≤ (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (n j))) := by
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  have hs := CutoffAvoidance.sqrt_tendsto_atTop _ hx
  have hlog : Tendsto (fun j => Real.logb 2 (n j) / n j) atTop (𝓝 0) := by
    have ht := (log_div_rpow_tendsto_zero n hn 1 (by norm_num)).div_const (Real.log 2)
    simp only [Real.rpow_one, zero_div] at ht
    convert ht using 1
    ext j
    rw [Real.logb]
    ring
  filter_upwards [hn.eventually_gt_atTop 1, hx.eventually_ge_atTop 0,
    hs.eventually_ge_atTop γ, hlog.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with j hnj hxj hsj hlogj
  intro H hnone horder hconn hmin hmax
  letI := hnone
  have h := closed_cubic_bound H hconn hmin hmax
  rw [horder] at h
  apply h.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hsq := Real.sq_sqrt hxj
  have hlogle : Real.logb 2 (n j) ≤ n j / 2 := by
    have hh := (div_le_iff₀ (by linarith : 0 < n j)).mp hlogj.le
    linarith
  simp only [Function.comp_apply] at hsj hsq
  nlinarith [mul_nonneg (Real.sqrt_nonneg (Real.logb 2 (n j))) (sub_nonneg.mpr hsj)]

end Erdos1016.Proof.ClosedCubicDecay
