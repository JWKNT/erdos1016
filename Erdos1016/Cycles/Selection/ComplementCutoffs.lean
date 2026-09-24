import Erdos1016.Cycles.Geometry.SelectedComplementGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.SelectedComplementParameters
open CutoffLimits ProtectorParameterBounds CutoffAvoidance

/-- A natural upper bound for a small complementary component. -/
def componentOrderBound (c σ n : ℝ) : ℕ := anchorCount c σ n + 2

/-- The radius cutoff always covers four times the complete moment-family cut. -/
theorem cutoff_radius_bound (σ x : ℝ) :
    (4 * (momentK σ x : ℝ) * (cutoffL σ x : ℝ)) < 2 ^ cutoffRc σ x := by
  have hp : 0 < 4 * (momentK σ x : ℝ) * (cutoffL σ x : ℝ) + 1 := by positivity
  have h := Nat.le_ceil (Real.logb 2 (4 * (momentK σ x : ℝ) * (cutoffL σ x : ℝ) + 1))
  have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h
  rw [Real.rpow_logb (by norm_num) (by norm_num) hp, Real.rpow_natCast] at hr
  exact lt_of_lt_of_le (by linarith) hr

/-- All numerical hypotheses in the small-component tree argument hold
uniformly for the actual manuscript cutoffs. -/
theorem eventually_component_budgets (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (hσ20 : σ < 1 / 20) (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop,
      0 < c * (n j) ^ (-(1 / 8 : ℝ)) ∧ c * (n j) ^ (-(1 / 8 : ℝ)) ≤ 2 ∧
      2 ≤ componentOrderBound c σ (n j) ∧
      ((momentK σ (Real.logb 2 (n j)) * cutoffL σ (Real.logb 2 (n j)) : ℕ) : ℝ) /
        ((c * (n j) ^ (-(1 / 8 : ℝ))) / 2) ≤ componentOrderBound c σ (n j) ∧
      2 * cutoffRc σ (Real.logb 2 (n j)) + 1 ≤ cutoffD (Real.logb 2 (n j)) ∧
      (((cutoffD (Real.logb 2 (n j)) / 2 - 1 : ℕ) : ℝ) *
        (1 - 1 / ((4 : ℝ) - 1))) > Real.logb 2 ((componentOrderBound c σ (n j) : ℝ) / 2) ∧
      4 * momentK σ (Real.logb 2 (n j)) ≤ cutoffD (Real.logb 2 (n j)) := by
  let x := fun j => Real.logb 2 (n j)
  have hx : Tendsto x atTop atTop := (Real.tendsto_logb_atTop (by norm_num)).comp hn
  have hs := sqrt_tendsto_atTop x hx
  have hr := cutoffRc_sqrt_ratio_tendsto σ hσ x hx
  have ha := anchorCount_power_ratio c σ hc hσ n hn (5 / 32) (by norm_num)
  have hi : Tendsto (fun j => (2 : ℝ) / (n j) ^ (5 / 32 : ℝ)) atTop (𝓝 0) := by
    have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 32)).comp hn).inv_tendsto_atTop
    simpa only [mul_zero, div_eq_mul_inv] using ht.const_mul 2
  have hM : Tendsto (fun j => (componentOrderBound c σ (n j) : ℝ) /
      (n j) ^ (5 / 32 : ℝ)) atTop (𝓝 0) := by
    convert ha.add hi using 1
    · ext j
      simp only [componentOrderBound, Nat.cast_add, Nat.cast_ofNat, add_div]
    · simp
  have hh : Tendsto (fun j => c * (n j) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hn).const_mul c
  filter_upwards [hn.eventually_gt_atTop 1, hx.eventually_ge_atTop 1000,
    hs.eventually_ge_atTop 10, hr.eventually_lt_const (by linarith : σ < 1),
    hM.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hh.eventually_lt_const (by norm_num : (0 : ℝ) < 2)] with j hnj hxj hsj hrj hMj hhj
  have hnpos : 0 < n j := by linarith
  have hxpos : 0 < x j := by linarith
  have hspos : 0 < Real.sqrt (x j) := by positivity
  have hsq := Real.sq_sqrt hxpos.le
  have hRc : (cutoffRc σ (x j) : ℝ) ≤ Real.sqrt (x j) :=
    (div_le_one hspos).mp hrj.le
  have hK : (momentK σ (x j) : ℝ) ≤ Real.sqrt (x j) :=
    (momentK_bounds hσ hσ20 (by linarith : 4 ≤ Real.sqrt (x j))).2
  have hD : x j / 2 - 1 < (cutoffD (x j) : ℝ) := by
    have ht := Nat.lt_floor_add_one (x j / 2)
    dsimp [cutoffD]
    linarith
  have hrcD : 2 * cutoffRc σ (x j) + 1 ≤ cutoffD (x j) := by
    have hh : 2 * (cutoffRc σ (x j) : ℝ) + 1 ≤ (cutoffD (x j) : ℝ) := by nlinarith
    exact_mod_cast hh
  have hkD : 4 * momentK σ (x j) ≤ cutoffD (x j) := by
    have hh : 4 * (momentK σ (x j) : ℝ) ≤ (cutoffD (x j) : ℝ) := by nlinarith
    exact_mod_cast hh
  have hhalfNat : cutoffD (x j) ≤ 2 * (cutoffD (x j) / 2 - 1) + 3 := by omega
  have hhalf : (cutoffD (x j) : ℝ) ≤ 2 * ((cutoffD (x j) / 2 - 1 : ℕ) : ℝ) + 3 := by
    exact_mod_cast hhalfNat
  have hMpow : (componentOrderBound c σ (n j) : ℝ) ≤ (n j) ^ (5 / 32 : ℝ) :=
    (div_le_one (by positivity)).mp hMj.le
  have hMpos : (0 : ℝ) < componentOrderBound c σ (n j) := by
    dsimp [componentOrderBound]; positivity
  have hlog : Real.logb 2 ((componentOrderBound c σ (n j) : ℝ) / 2) ≤ (5 / 32 : ℝ) * x j := by
    calc
      _ ≤ Real.logb 2 ((n j) ^ (5 / 32 : ℝ)) :=
        (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).2 (by linarith)
      _ = _ := Real.logb_rpow_eq_mul_logb_of_pos hnpos
  have hbound : ((momentK σ (x j) * cutoffL σ (x j) : ℕ) : ℝ) /
      ((c * (n j) ^ (-(1 / 8 : ℝ))) / 2) ≤ componentOrderBound c σ (n j) := by
    have ht := Nat.lt_floor_add_one (2 * (momentK σ (x j) : ℝ) *
      (cutoffL σ (x j) : ℝ) / (c * (n j) ^ (-(1 / 8 : ℝ))))
    dsimp [componentOrderBound, anchorCount]
    push_cast
    simp only [x] at ht
    push_cast at ht ⊢
    convert (le_of_lt ht).trans (by linarith :
      (Nat.floor (2 * (momentK σ (x j) : ℝ) * (cutoffL σ (x j) : ℝ) /
        (c * (n j) ^ (-(1 / 8 : ℝ)))) : ℝ) + 1 ≤
      (Nat.floor (2 * (momentK σ (x j) : ℝ) * (cutoffL σ (x j) : ℝ) /
        (c * (n j) ^ (-(1 / 8 : ℝ)))) : ℝ) + 1 + 2) using 1 <;> dsimp [x] <;> ring
  exact ⟨by positivity, hhj.le, by dsimp [componentOrderBound]; omega,
    hbound, hrcD, by norm_num at *; nlinarith, hkD⟩

end Erdos1016.Proof.SelectedComplementParameters
