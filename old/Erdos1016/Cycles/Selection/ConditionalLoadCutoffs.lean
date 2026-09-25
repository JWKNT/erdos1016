import Erdos1016.Cycles.Selection.EvenTraceCutoffs

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Erdos1016.Proof.SelectedLoadParameters
open CutoffLimits CutoffAvoidance
open ConditionalLoadDecay

/-- The logarithmic quantity used in the scalar avoidance estimate is
exactly the conditional-neighbor load produced by weighted path counting. -/
theorem cutoffLoad_eq (σ x : ℝ) :
    cutoffLoad σ x = 18 * (2 : ℝ) ^ cutoffQ σ x * (cutoffL σ x : ℝ) ^ 2 *
      ((2 : ℝ) ^ (momentK σ x * Nat.ceil (((cutoffS x - 1 : ℕ) : ℝ) / cutoffDelta σ x)) /
        2 ^ cutoffS x) := by
  have hL : (0 : ℝ) < cutoffL σ x := by
    have h : 0 < cutoffL σ x := by dsimp [cutoffL, largestOddCutoff]; omega
    exact_mod_cast h
  unfold cutoffLoad exactDstarLogScale
  rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 18)]
  have hmain : Real.exp (((cutoffQ σ x : ℝ) - cutoffS x +
      (momentK σ x * Nat.ceil (((cutoffS x - 1 : ℕ) : ℝ) / cutoffDelta σ x) : ℕ)) * Real.log 2) =
      (2 : ℝ) ^ cutoffQ σ x *
      (2 : ℝ) ^ (momentK σ x * Nat.ceil (((cutoffS x - 1 : ℕ) : ℝ) / cutoffDelta σ x)) /
      (2 : ℝ) ^ cutoffS x := by
    rw [mul_comm _ (Real.log 2), ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    simp only [Real.rpow_natCast]
    ring
  have hlast : Real.exp (2 * Real.log (cutoffL σ x : ℝ)) = (cutoffL σ x : ℝ) ^ 2 := by
    rw [show 2 * Real.log (cutoffL σ x : ℝ) = Real.log (cutoffL σ x : ℝ) + Real.log (cutoffL σ x : ℝ) by ring,
      Real.exp_add, Real.exp_log hL]
    ring
  rw [hmain, hlast]
  ring

/-- The exact moment order is even and its separation denominator is
positive throughout the positive logarithmic domain. -/
theorem cutoff_load_discrete_conditions {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    Even (momentK σ x) ∧ 2 ≤ momentK σ x ∧ 0 < cutoffDelta σ x ∧
      cutoffDelta σ x ≤ cutoffQ σ x - 2 * momentK σ x + 1 := by
  have hK : 2 ≤ momentK σ x := by
    have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt x) := Nat.one_le_ceil_iff.mpr (by positivity)
    dsimp [momentK]
    omega
  have hL : 1 ≤ cutoffL σ x := by dsimp [cutoffL, largestOddCutoff]; omega
  have hr : 1 ≤ cutoffRc σ x := by
    apply Nat.one_le_ceil_iff.mpr
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    have hKr : (2 : ℝ) ≤ momentK σ x := by exact_mod_cast hK
    have hLr : (1 : ℝ) ≤ cutoffL σ x := by exact_mod_cast hL
    nlinarith [mul_nonneg (sub_nonneg.mpr hKr) (sub_nonneg.mpr hLr)]
  have hΔ : momentK σ x * (2 * cutoffRc σ x - 1) ≤ cutoffDelta σ x := by
    simpa [cutoffDelta, cutoffQ] using
      ConditionalPenaltyBounds.separation_denominator_lower_bound
        (momentK σ x) (cutoffRc σ x) (by omega) hr
  refine ⟨⟨Nat.ceil (5 * σ * Real.sqrt x), by dsimp [momentK]; omega⟩, hK, ?_, le_rfl⟩
  exact lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hΔ

/-- Replacing the actual conditioning tuple size by the maximum moment
order preserves the conditional-neighbor majorant used by avoidance. -/
theorem conditional_neighbor_bound_le_cutoffLoad (σ x : ℝ) (k : ℕ)
    (hk : k ≤ momentK σ x) :
    18 * (2 : ℝ) ^ cutoffQ σ x * (cutoffL σ x : ℝ) ^ 2 *
      ((2 : ℝ) ^ (k * Nat.ceil (((cutoffS x - 1 : ℕ) : ℝ) / cutoffDelta σ x)) /
        2 ^ cutoffS x) ≤ cutoffLoad σ x := by
  rw [cutoffLoad_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hk)

open Filter
open scoped Topology

/-- The actual even-trace target grows without bound, so the selected family
has strictly positive mean uniformly beyond one onset. -/
theorem evenTraceTarget_tendsto_atTop (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => EvenTraceParameters.evenTraceTarget σ (x j)) atTop atTop := by
  have hm := meanFloor_tendsto_atTop (σ / 32) (by positivity) x hx
  have hs := sqrt_tendsto_atTop x hx
  apply tendsto_atTop_mono' atTop _ hm
  filter_upwards [hx.eventually_ge_atTop 1, hs.eventually_ge_atTop (2 / σ)] with j hxj hsj
  have hσs : 2 ≤ σ * Real.sqrt (x j) := by
    have ht := (div_le_iff₀ hσ).mp hsj
    nlinarith
  have hlarge : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt (x j)) := by
    have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσs
    norm_num at ht ⊢
    exact ht
  exact (EvenTraceParameters.evenTraceTarget_bounds hσ hxj hlarge).1

end Erdos1016.Proof.SelectedLoadParameters
