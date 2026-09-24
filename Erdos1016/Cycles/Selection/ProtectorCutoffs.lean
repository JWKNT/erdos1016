import Erdos1016.Cycles.Selection.ProtectedCoreRealization
import Erdos1016.Expansion.ConnectorCutoffLimits

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.ProtectorParameterBounds
open CutoffAvoidance CutoffLimits
open ConnectorCutoffLimits
open FewBranchCoreRealization

/-- The cycle horizon is negligible compared with every positive power of
the ambient order, with its exact odd rounding retained. -/
theorem cutoffL_power_ratio (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun j => (cutoffL σ (Real.logb 2 (n j)) : ℝ) / (n j) ^ α)
      atTop (𝓝 0) := by
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  have hlog := cutoffL_log_over_x_tendsto_zero σ hσ _ hx
  have hupper : ∀ᶠ j in atTop,
      (cutoffL σ (Real.logb 2 (n j)) : ℝ) ≤ (n j) ^ (α / 2) := by
    filter_upwards [hn.eventually_gt_atTop 1,
      hlog.eventually_lt_const (by positivity : (0 : ℝ) < (α / 2) * Real.log 2)]
      with j hnj hj
    have hxj : 0 < Real.logb 2 (n j) := Real.logb_pos (by norm_num) hnj
    have hl := (div_lt_iff₀ hxj).mp hj
    have hLpos : (0 : ℝ) < cutoffL σ (Real.logb 2 (n j)) := by
      have h : 0 < cutoffL σ (Real.logb 2 (n j)) := by dsimp [cutoffL, largestOddCutoff]; omega
      exact_mod_cast h
    apply (Real.log_le_log_iff hLpos (Real.rpow_pos_of_pos (by linarith) _)).mp
    rw [Real.log_rpow (by linarith : 0 < n j)]
    have heq : (α / 2) * Real.log 2 * Real.logb 2 (n j) = (α / 2) * Real.log (n j) := by
      rw [Real.logb]
      field_simp
      ring
    simp only [Function.comp_apply] at hl
    rw [heq] at hl
    exact hl.le
  have hsmall := (tendsto_rpow_neg_atTop (by positivity : 0 < α / 2)).comp hn
  apply squeeze_zero' _ _ hsmall
  · filter_upwards [hn.eventually_gt_atTop 0] with j hj
    positivity
  · filter_upwards [hn.eventually_gt_atTop 0, hupper] with j hj hu
    calc
      _ ≤ (n j) ^ (α / 2) / (n j) ^ α :=
        div_le_div_of_nonneg_right hu (by positivity)
      _ = (n j) ^ (-(α / 2)) := by
        rw [← Real.rpow_sub hj]
        congr 1
        ring

theorem momentK_power_ratio (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun j => (momentK σ (Real.logb 2 (n j)) : ℝ) / (n j) ^ α)
      atTop (𝓝 0) := by
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  have hk := momentK_ratio_tendsto_zero σ hσ.le _ hx
  have hlog := log_div_rpow_tendsto_zero n hn α hα
  have hb : Tendsto (fun j => Real.logb 2 (n j) / (n j) ^ α) atTop (𝓝 0) := by
    convert hlog.div_const (Real.log 2) using 1
    · ext j
      rw [Real.logb]
      ring
    · simp
  apply squeeze_zero' _ _ hb
  · filter_upwards [hn.eventually_gt_atTop 0] with j hj
    positivity
  · filter_upwards [hn.eventually_gt_atTop 1,
      hk.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with j hnj hkj
    have hxj := Real.logb_pos (by norm_num : (1 : ℝ) < 2) hnj
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (div_le_one hxj).mp hkj.le

/-- Strictly more anchors than the moment-family component threshold. -/
def anchorCount (c σ n : ℝ) : ℕ :=
  Nat.floor (2 * (momentK σ (Real.logb 2 n) : ℝ) *
    (cutoffL σ (Real.logb 2 n) : ℝ) / (c * n ^ (-(1 / 8 : ℝ)))) + 1

theorem anchorCount_power_ratio (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (α : ℝ) (hα : 1 / 8 < α) :
    Tendsto (fun j => (anchorCount c σ (n j) : ℝ) / (n j) ^ α)
      atTop (𝓝 0) := by
  let β := (α - 1 / 8) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hkl := (momentK_power_ratio σ hσ n hn β hβ).mul
    (cutoffL_power_ratio σ hσ n hn β hβ)
  have harg : Tendsto (fun j =>
      (2 * (momentK σ (Real.logb 2 (n j)) : ℝ) *
        (cutoffL σ (Real.logb 2 (n j)) : ℝ) / (c * (n j) ^ (-(1 / 8 : ℝ)))) /
        (n j) ^ α) atTop (𝓝 0) := by
    have ht := hkl.const_mul (2 / c)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hn.eventually_gt_atTop 0] with j hj
    have hp : (c * (n j) ^ (-(1 / 8 : ℝ))) * (n j) ^ α =
        c * ((n j) ^ β * (n j) ^ β) := by
      rw [mul_assoc, ← Real.rpow_add hj, ← Real.rpow_add hj]
      congr 2
      dsimp [β]
      ring
    rw [div_div, hp]
    ring
  have hi := (tendsto_rpow_neg_atTop (by linarith : 0 < α)).comp hn
  have hi' : Tendsto (fun j => 1 / (n j) ^ α) atTop (𝓝 0) := by
    apply hi.congr'
    filter_upwards [hn.eventually_gt_atTop 0] with j hj
    simp only [Function.comp_apply]
    rw [Real.rpow_neg hj.le]
    simp only [one_div]
  have ht := harg.add hi'
  simp only [add_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [hn.eventually_gt_atTop 0] with j hj
    positivity
  · filter_upwards [hn.eventually_gt_atTop 0] with j hj
    dsimp [anchorCount]
    push_cast
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add_right (Nat.floor_le (by positivity)) 1

/-- The entire connected protector, including its initial anchors, is
`o(n^(31/32))`. This preserves a fixed power saving for the trace deficit. -/
theorem protectorBudget_power_ratio (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hnge : ∀ j, 1 ≤ n j) :
    Tendsto (fun j =>
      (protectorBudget (anchorCount c σ (n j)) (logarithmicGirthCutoff (n j))
        (polynomialPackingCutoff (n j)) (logarithmicConnectorRadius c (n j)) : ℝ) /
        (n j) ^ (31 / 32 : ℝ)) atTop (𝓝 0) := by
  let a := fun j => (anchorCount c σ (n j) : ℝ)
  let D := fun j => (logarithmicGirthCutoff (n j) : ℝ)
  let K := fun j => (polynomialPackingCutoff (n j) : ℝ)
  let R := fun j => (logarithmicConnectorRadius c (n j) : ℝ)
  have ha := anchorCount_power_ratio c σ hc hσ n hn (26 / 32) (by norm_num)
  have hD := logarithmicGirthCutoff_ratio_tendsto_zero n hn (1 / 32) (by norm_num)
  have hK := polynomialPackingCutoff_ratio_tendsto_zero n hn
  have hR := logarithmicConnectorRadius_ratio_tendsto_zero n hn c hc hnge
  have hi (α : ℝ) (hα : 0 < α) :
      Tendsto (fun j => 1 / (n j) ^ α) atTop (𝓝 0) := by
    have ht := ((tendsto_rpow_atTop hα).comp hn).inv_tendsto_atTop
    simpa only [one_div] using ht
  have hsum : Tendsto (fun j => a j / (n j) ^ (26 / 32 : ℝ) +
      (D j / (n j) ^ (1 / 32 : ℝ)) * (K j / (n j) ^ (25 / 32 : ℝ)))
      atTop (𝓝 0) := by simpa [a, D, K] using ha.add (hD.mul hK)
  have hrad : Tendsto (fun j => 2 * (R j / (n j) ^ (5 / 32 : ℝ)) +
      1 / (n j) ^ (5 / 32 : ℝ)) atTop (𝓝 0) := by
    simpa [R] using (hR.const_mul 2).add (hi (5 / 32) (by norm_num))
  have ht := (hi (31 / 32) (by norm_num)).add (hsum.mul hrad)
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [hn.eventually_gt_atTop 0] with j hj
    positivity
  · filter_upwards [hn.eventually_gt_atTop 0] with j hj
    have hp1 : (n j) ^ (1 / 32 : ℝ) * (n j) ^ (25 / 32 : ℝ) =
        (n j) ^ (26 / 32 : ℝ) := by rw [← Real.rpow_add hj]; norm_num
    have hp2 : (n j) ^ (26 / 32 : ℝ) * (n j) ^ (5 / 32 : ℝ) =
        (n j) ^ (31 / 32 : ℝ) := by rw [← Real.rpow_add hj]; norm_num
    have heq : 1 / (n j) ^ (31 / 32 : ℝ) +
        (a j / (n j) ^ (26 / 32 : ℝ) +
          (D j / (n j) ^ (1 / 32 : ℝ)) * (K j / (n j) ^ (25 / 32 : ℝ))) *
        (2 * (R j / (n j) ^ (5 / 32 : ℝ)) + 1 / (n j) ^ (5 / 32 : ℝ)) =
        (1 + (a j + D j * K j) * (2 * R j + 1)) / (n j) ^ (31 / 32 : ℝ) := by
      rw [div_mul_div_comm, hp1]
      rw [← add_div]
      have hh : 2 * (R j / (n j) ^ (5 / 32 : ℝ)) + 1 / (n j) ^ (5 / 32 : ℝ) =
          (2 * R j + 1) / (n j) ^ (5 / 32 : ℝ) := by ring
      rw [hh, div_mul_div_comm, hp2, ← add_div]
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hKm : ((polynomialPackingCutoff (n j) - 1 : ℕ) : ℝ) ≤ K j := by
      dsimp [K]
      exact_mod_cast Nat.sub_le (polynomialPackingCutoff (n j)) 1
    dsimp [protectorBudget]
    push_cast
    dsimp [a, D, R, K] at *
    nlinarith [mul_nonneg (Nat.cast_nonneg (logarithmicGirthCutoff (n j)))
      (sub_nonneg.mpr hKm)]

/-- The exact deletion budget remains negligible after multiplying by the
growing cycle horizon. This is the quantitative core-defect condition that
plain sublinearity of the protector would not supply. -/
theorem weighted_protectorBudget_tendsto_zero (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hnge : ∀ j, 1 ≤ n j) :
    Tendsto (fun j =>
      (protectorBudget (anchorCount c σ (n j)) (logarithmicGirthCutoff (n j))
        (polynomialPackingCutoff (n j)) (logarithmicConnectorRadius c (n j)) : ℝ) *
        (cutoffL σ (Real.logb 2 (n j)) : ℝ) / n j) atTop (𝓝 0) := by
  have ht := (protectorBudget_power_ratio c σ hc hσ n hn hnge).mul
    (cutoffL_power_ratio σ hσ n hn (1 / 32) (by norm_num))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_gt_atTop 0] with j hj
  rw [div_mul_div_comm, ← Real.rpow_add hj]
  norm_num

/-- Every actual graph with boundary deficit at most `B n^(7/8)` and the
constructed protector budget eventually meets both finite core inequalities. -/
theorem weighted_total_defect_tendsto_zero (c B σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hnge : ∀ j, 1 ≤ n j) :
    Tendsto (fun j =>
      (B * (n j) ^ (7 / 8 : ℝ) + 4 *
        (protectorBudget (anchorCount c σ (n j)) (logarithmicGirthCutoff (n j))
          (polynomialPackingCutoff (n j)) (logarithmicConnectorRadius c (n j)) : ℝ)) *
        (cutoffL σ (Real.logb 2 (n j)) : ℝ) / n j) atTop (𝓝 0) := by
  have hb := (cutoffL_power_ratio σ hσ n hn (1 / 8) (by norm_num)).const_mul B
  have hw := (weighted_protectorBudget_tendsto_zero c σ hc hσ n hn hnge).const_mul 4
  have ht := hb.add hw
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_gt_atTop 0] with j hj
  have hp : (n j) ^ (7 / 8 : ℝ) * (n j) ^ (1 / 8 : ℝ) = n j := by
    rw [← Real.rpow_add hj]
    norm_num
  have hcalc : B * ((cutoffL σ (Real.logb 2 (n j)) : ℝ) / (n j) ^ (1 / 8 : ℝ)) =
      B * (n j) ^ (7 / 8 : ℝ) * (cutoffL σ (Real.logb 2 (n j)) : ℝ) / n j := by
    apply (eq_div_iff hj.ne').mpr
    calc
      _ = B * ((cutoffL σ (Real.logb 2 (n j)) : ℝ) / (n j) ^ (1 / 8 : ℝ)) *
          ((n j) ^ (7 / 8 : ℝ) * (n j) ^ (1 / 8 : ℝ)) := by rw [hp]
      _ = _ := by field_simp; ring
  rw [hcalc]
  ring

end Erdos1016.Proof.ProtectorParameterBounds
