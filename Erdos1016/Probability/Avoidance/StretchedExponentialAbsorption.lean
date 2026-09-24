import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.StretchedExponentialAbsorption

/-- The logarithmic correction in the §8–9 mean estimate is absorbed by a
fixed fraction of its square-root-log main term. This isolates the final
stretched-exponential parameter calculation from the graph and moment
arguments that supply `hmean`. -/
theorem exp_neg_le_stretched_of_mean_lower_bound
    (x mean : ℕ → ℝ) (σ C : ℝ)
    (hx : Tendsto x atTop atTop) (hσ : 0 < σ)
    (hmean : ∀ᶠ j in atTop,
      (σ * Real.log 2 / 2) * Real.sqrt (x j) -
          (1 / 2 : ℝ) * Real.log (x j) - C ≤ mean j) :
    ∀ᶠ j in atTop,
      Real.exp (-mean j) ≤
        Real.exp (-(σ * Real.log 2 / 4) * Real.sqrt (x j)) := by
  have hsqrt : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
    simpa only [Real.sqrt_eq_rpow] using hpow
  have hinvsqrt : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hsqrt.inv_tendsto_atTop
  have hlog := (Real.tendsto_log_atTop.comp hx)
  have hlogratio0 : Tendsto (fun j => Real.log (x j) / Real.sqrt (x j))
      atTop (𝓝 0) := by
    have hsmall :=
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hsmall' : Tendsto (fun y : ℝ => Real.log y / Real.sqrt y)
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using hsmall
    exact hsmall'.comp hx
  have hcorrection : Tendsto
      (fun j => ((1 / 2 : ℝ) * Real.log (x j) + C) / Real.sqrt (x j))
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun j => (1 / 2 : ℝ) * (Real.log (x j) / Real.sqrt (x j)) +
          C * (Real.sqrt (x j))⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using
        (tendsto_const_nhds.mul hlogratio0).add
          (tendsto_const_nhds.mul hinvsqrt)
    convert hsum using 1
    ext j
    field_simp
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htarget : 0 < σ * Real.log 2 / 4 := by positivity
  have hsmallEventually : ∀ᶠ j in atTop,
      ((1 / 2 : ℝ) * Real.log (x j) + C) / Real.sqrt (x j) <
        σ * Real.log 2 / 4 := hcorrection.eventually_lt_const htarget
  filter_upwards [hmean, hsmallEventually, hx.eventually_gt_atTop 0] with
    j hjMean hjSmall hxj
  have hsqrtpos : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hxj
  have hcorr : (1 / 2 : ℝ) * Real.log (x j) + C <
      (σ * Real.log 2 / 4) * Real.sqrt (x j) :=
    (div_lt_iff₀ hsqrtpos).1 hjSmall
  have hmean' : (σ * Real.log 2 / 4) * Real.sqrt (x j) ≤ mean j := by
    nlinarith [hjMean, hcorr]
  apply Real.exp_le_exp.mpr
  nlinarith [hmean']

/-- The same tail estimate in the base-two form used by the paper. -/
theorem exp_neg_le_base_two_stretched_of_mean_lower_bound
    (x mean : ℕ → ℝ) (σ C : ℝ)
    (hx : Tendsto x atTop atTop) (hσ : 0 < σ)
    (hmean : ∀ᶠ j in atTop,
      (σ * Real.log 2 / 2) * Real.sqrt (x j) -
          (1 / 2 : ℝ) * Real.log (x j) - C ≤ mean j) :
    ∀ᶠ j in atTop,
      Real.exp (-mean j) ≤ (2 : ℝ) ^ (-(σ / 4) * Real.sqrt (x j)) := by
  have h := exp_neg_le_stretched_of_mean_lower_bound x mean σ C hx hσ hmean
  filter_upwards [h] with j hj
  have hpow : (2 : ℝ) ^ (-(σ / 4) * Real.sqrt (x j)) =
      Real.exp (-(σ * Real.log 2 / 4) * Real.sqrt (x j)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hpow]
  exact hj

end Erdos1016.Proof.StretchedExponentialAbsorption

end
