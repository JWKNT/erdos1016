import Erdos1016.Cycles.Counting.ExceptionalLoadCutoffs

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! Numerical cutoffs for the short-cycle packing and the exterior-link count. -/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.ForestCutoffParameters
open DeficitCutoffParameters ExceptionalLoadCutoffs

def packingCutoff (x : ℝ) : ℕ := Nat.ceil ((2 : ℝ) ^ (x / 2))
def smallCutCutoff (x : ℝ) : ℕ := Nat.floor (Real.logb 2 x / 2)

theorem packingCutoff_pos (x : ℝ) : 0 < packingCutoff x := by
  exact Nat.ceil_pos.mpr (by positivity)

theorem packingCutoff_le (x : ℝ) (hx : 0 ≤ x) :
    (packingCutoff x : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (x / 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have h := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ (x / 2) by positivity)
  change (packingCutoff x : ℝ) < _ at h
  linarith

/-- Integer block lengths satisfy the actual short-path uniqueness budget,
both for direct edges and for exterior trees with small cut. -/
theorem eventually_geometry_cutoffs :
    ∀ᶠ x : ℝ in atTop,
      8 ≤ girthCutoff x ∧ girthCutoff x ≤ 2 * upperHalfLength x ∧
      0 < girthCutoff x / 8 ∧ 1 ≤ smallCutCutoff x ∧
      2 * (smallCutCutoff x + 2 * (girthCutoff x / 8)) ≤ girthCutoff x := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (200 : ℝ), hy.eventually_ge_atTop 4,
    logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 100)]
    with x hx hy hratio
  have hxpos : 0 < x := by linarith
  have hyle : Real.logb 2 x ≤ x / 100 := by
    have h := (div_lt_iff₀ hxpos).mp hratio
    linarith
  have ht : (smallCutCutoff x : ℝ) ≤ Real.logb 2 x / 2 := Nat.floor_le (by positivity)
  have hDlo := Nat.lt_floor_add_one (x / 10)
  change x / 10 < (girthCutoff x : ℝ) + 1 at hDlo
  have hDhi : (girthCutoff x : ℝ) ≤ x / 10 := Nat.floor_le (by positivity)
  have hD8 : 8 ≤ girthCutoff x := by
    have h : (8 : ℝ) ≤ girthCutoff x := by linarith
    exact_mod_cast h
  have htD : 4 * smallCutCutoff x ≤ girthCutoff x := by
    have h : (4 : ℝ) * smallCutCutoff x ≤ girthCutoff x := by linarith
    exact_mod_cast h
  have ht1 : 1 ≤ smallCutCutoff x := by
    apply (Nat.one_le_floor_iff _).mpr
    linarith
  have hsqrt : 2 ≤ Real.sqrt (Real.logb 2 x) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.logb 2 x),
      Real.sqrt_nonneg (Real.logb 2 x)]
  have hKlo := Nat.lt_floor_add_one (x * Real.sqrt (Real.logb 2 x) / 2)
  change x * Real.sqrt (Real.logb 2 x) / 2 < (upperHalfLength x : ℝ) + 1 at hKlo
  have hDL : girthCutoff x ≤ 2 * upperHalfLength x := by
    have h : (girthCutoff x : ℝ) ≤ 2 * upperHalfLength x := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt hxpos.le]
    exact_mod_cast h
  refine ⟨hD8, hDL, by omega, ht1, ?_⟩
  omega

/-- The small-cut corollary rules out a square-root-sized packing for all
sufficiently large rank parameters. -/
theorem eventually_packing_threshold :
    ∀ᶠ x : ℝ in atTop,
      ((girthCutoff x : ℝ) + 1) * (2 : ℝ) ^ girthCutoff x /
        (2 * (packingCutoff x : ℝ)) ≤ 20 / Real.logb 2 (Real.logb 2 x) := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hy.comp hy
  have hdec := polynomial_dyadic_decay 2 (2 / 5) (by norm_num)
  have hlog := logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hy.eventually_gt_atTop 0,
    hz.eventually_gt_atTop 0, hlog, hy.eventually hlog,
    hdec.eventually_lt_const (by norm_num : (0 : ℝ) < 20)] with x hx hypos hzpos hyle hzle hdec
  have hxpos : 0 < x := by linarith
  have hyx : Real.logb 2 x ≤ x := ((div_lt_one hxpos).mp hyle).le
  have hzy : Real.logb 2 (Real.logb 2 x) ≤ Real.logb 2 x := ((div_lt_one hypos).mp hzle).le
  have hD : (girthCutoff x : ℝ) ≤ x / 10 := Nat.floor_le (by positivity)
  have hD' : (girthCutoff x : ℝ) + 1 ≤ 2 * x := by linarith
  have hpow : (2 : ℝ) ^ girthCutoff x ≤ (2 : ℝ) ^ (x / 10) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
  have hB : (2 : ℝ) ^ (x / 2) ≤ (packingCutoff x : ℝ) := Nat.le_ceil _
  have hquot : (2 : ℝ) ^ (x / 10) / (2 : ℝ) ^ (x / 2) =
      (2 : ℝ) ^ (-(2 / 5 : ℝ) * x) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ ≤ (2 * x * (2 : ℝ) ^ (x / 10)) / (2 * (packingCutoff x : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul hD' hpow (by positivity) (by positivity)) (by positivity)
    _ ≤ (2 * x * (2 : ℝ) ^ (x / 10)) / (2 * (2 : ℝ) ^ (x / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = x * (2 : ℝ) ^ (-(2 / 5 : ℝ) * x) := by
      rw [← hquot]
      ring
    _ ≤ 20 / x := by
      apply (le_div_iff₀ hxpos).mpr
      nlinarith only [hdec]
    _ ≤ 20 / Real.logb 2 (Real.logb 2 x) :=
      div_le_div_of_nonneg_left (by norm_num) hzpos (hzy.trans hyx)

/-- A direct numerical bound for the three link-error terms. The generous
fixed constant absorbs integer blocks without changing the final theorem. -/
theorem link_error_le_envelope (x : ℝ) (hx : 100 ≤ x)
    (hy : 2 ≤ Real.logb 2 x) (hz : 0 ≤ Real.logb 2 (Real.logb 2 x))
    (L : ℕ) (hL : (L : ℝ) ≤ x * Real.sqrt (Real.logb 2 x)) :
    578 * ((L : ℝ) / girthCutoff x) ^ 2 +
      2 * L / ((smallCutCutoff x : ℝ) + 1) +
      ((smallCutCutoff x : ℝ) + 1) * (2 : ℝ) ^ smallCutCutoff x *
        Real.logb 2 (Real.logb 2 x) / 40 ≤ 300000 * linkEnvelope x := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < Real.logb 2 x := by linarith
  have hspos : 0 < Real.sqrt (Real.logb 2 x) := Real.sqrt_pos.mpr hypos
  have hsquare : Real.sqrt (Real.logb 2 x) ^ 2 = Real.logb 2 x := Real.sq_sqrt hypos.le
  have hDlo := Nat.lt_floor_add_one (x / 10)
  change x / 10 < (girthCutoff x : ℝ) + 1 at hDlo
  have hD : x / 20 ≤ (girthCutoff x : ℝ) := by linarith
  have hDpos : (0 : ℝ) < girthCutoff x := by linarith
  have htlo := Nat.lt_floor_add_one (Real.logb 2 x / 2)
  change Real.logb 2 x / 2 < (smallCutCutoff x : ℝ) + 1 at htlo
  have hthi : (smallCutCutoff x : ℝ) ≤ Real.logb 2 x / 2 := Nat.floor_le (by positivity)
  have htpos : (0 : ℝ) < (smallCutCutoff x : ℝ) + 1 := by positivity
  have htr : (smallCutCutoff x : ℝ) + 1 ≤ Real.logb 2 x := by linarith
  have hpow : (2 : ℝ) ^ smallCutCutoff x ≤ Real.sqrt x := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hthi
    rw [Real.rpow_natCast] at h
    have heq : (2 : ℝ) ^ (Real.logb 2 x / 2) = Real.sqrt x := by
      rw [show Real.logb 2 x / 2 = Real.logb 2 x * (1 / 2) by ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) hxpos, Real.sqrt_eq_rpow]
    exact heq ▸ h
  have hratio : (L : ℝ) / girthCutoff x ≤ 20 * Real.sqrt (Real.logb 2 x) := by
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hD hspos.le]
  have hblock : 578 * ((L : ℝ) / girthCutoff x) ^ 2 ≤ 231200 * Real.logb 2 x := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (L : ℝ) / girthCutoff x) hratio 2
    nlinarith only [h, hsquare]
  have hlarge : 2 * (L : ℝ) / ((smallCutCutoff x : ℝ) + 1) ≤
      4 * x / Real.sqrt (Real.logb 2 x) := by
    apply (div_le_iff₀ htpos).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hspos).mpr
    have ht := mul_le_mul_of_nonneg_left htlo.le (show 0 ≤ 4 * x by positivity)
    have hl := mul_le_mul_of_nonneg_right hL hspos.le
    nlinarith [hsquare]
  have hsmall : ((smallCutCutoff x : ℝ) + 1) * (2 : ℝ) ^ smallCutCutoff x *
      Real.logb 2 (Real.logb 2 x) / 40 ≤
      Real.logb 2 x * Real.sqrt x * Real.logb 2 (Real.logb 2 x) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul htr hpow (by positivity) hypos.le) hz
    have hn : 0 ≤ Real.logb 2 x * Real.sqrt x * Real.logb 2 (Real.logb 2 x) := by positivity
    linarith
  unfold linkEnvelope
  have hmid : 0 ≤ x / Real.sqrt (Real.logb 2 x) := by positivity
  have hlast : 0 ≤ Real.logb 2 x * Real.sqrt x * Real.logb 2 (Real.logb 2 x) := by positivity
  simp only [div_eq_mul_inv] at hblock hlarge hsmall hmid hlast ⊢
  nlinarith only [hblock, hlarge, hsmall, hmid, hlast, hy]

end Erdos1016.Proof.ForestCutoffParameters
