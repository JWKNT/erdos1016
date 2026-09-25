import Erdos1016.Cycles.Counting.LowDegreeTraceCycles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Complex.ExponentialBounds

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! Logarithmic cutoffs for the shorter proof. The parameter x is log₂ r.
We use an even upper length 2K and s=floor(D/2); both satisfy the same
high-girth counting conditions as the manuscript's rounding convention. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos1016.Proof.DeficitCutoffParameters
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.LowDegreeTraceCycles
open Erdos1016.Proof.SimpleRunWeight

def lowerHalfLength (x : ℝ) : ℕ := Nat.ceil (3 * x)
def upperHalfLength (x : ℝ) : ℕ := Nat.floor (x * Real.sqrt (Real.logb 2 x) / 2)
def girthCutoff (x : ℝ) : ℕ := Nat.floor (x / 10)
def suffixCutoff (x : ℝ) : ℕ := girthCutoff x / 2

theorem polynomial_dyadic_decay (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ k * (2 : ℝ) ^ (-a * x)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (k : ℝ) (a * Real.log 2) (mul_pos ha (Real.log_pos (by norm_num)))
  convert h using 1
  ext x
  rw [Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

theorem logb_div_self_tendsto_zero :
    Tendsto (fun x : ℝ => Real.logb 2 x / x) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h' := h.div_const (Real.log 2)
  convert h' using 1
  · ext x
    simp only [Real.logb, id_eq]
    ring
  · simp

theorem cutoff_bounds (x : ℝ) (hx : 100 ≤ x)
    (hy : 4 ≤ Real.logb 2 x) (hyx : Real.logb 2 x ≤ x)
    (hz : 32 ≤ Real.logb 2 (Real.logb 2 x)) :
    0 < lowerHalfLength x ∧ 1 ≤ upperHalfLength x ∧
    lowerHalfLength x ≤ upperHalfLength x + 1 ∧
    (upperHalfLength x : ℝ) ≤ x ^ 2 / 2 ∧
    0 < suffixCutoff x ∧ 2 * suffixCutoff x ≤ girthCutoff x ∧
    x / 20 - 2 ≤ (suffixCutoff x : ℝ) ∧
    Real.logb 2 (Real.logb 2 x) / 4 ≤
      Real.log ((upperHalfLength x + 1 : ℕ) / (lowerHalfLength x : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < Real.logb 2 x := by linarith
  have hrootpos : 0 < Real.sqrt (Real.logb 2 x) := Real.sqrt_pos.mpr hypos
  have hrootlower : 2 ≤ Real.sqrt (Real.logb 2 x) := by
    nlinarith [Real.sq_sqrt hypos.le, Real.sqrt_nonneg (Real.logb 2 x)]
  have hrootupper : Real.sqrt (Real.logb 2 x) ≤ x := by
    nlinarith [Real.sq_sqrt hypos.le, Real.sqrt_nonneg (Real.logb 2 x)]
  have hMlo : 3 * x ≤ (lowerHalfLength x : ℝ) := Nat.le_ceil _
  have hMhi : (lowerHalfLength x : ℝ) ≤ 4 * x := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 3 * x by positivity)
    change (lowerHalfLength x : ℝ) < 3 * x + 1 at h
    linarith
  have hM : 0 < lowerHalfLength x := by
    have : (0 : ℝ) < lowerHalfLength x := by linarith
    exact_mod_cast this
  have hK : 1 ≤ upperHalfLength x := by
    apply (Nat.one_le_floor_iff _).mpr
    nlinarith
  have hKhi : (upperHalfLength x : ℝ) ≤ x ^ 2 / 2 := by
    have h := Nat.floor_le (show 0 ≤ x * Real.sqrt (Real.logb 2 x) / 2 by positivity)
    change (upperHalfLength x : ℝ) ≤ x * Real.sqrt (Real.logb 2 x) / 2 at h
    nlinarith
  have hKlo : x * Real.sqrt (Real.logb 2 x) / 2 <
      ((upperHalfLength x + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (x * Real.sqrt (Real.logb 2 x) / 2)
  have hDlo : x / 10 < (girthCutoff x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsD : 2 * suffixCutoff x ≤ girthCutoff x := by
    unfold suffixCutoff
    omega
  have hDhi : girthCutoff x ≤ 2 * suffixCutoff x + 1 := by
    unfold suffixCutoff
    omega
  have hDhiR : (girthCutoff x : ℝ) ≤ 2 * suffixCutoff x + 1 := by exact_mod_cast hDhi
  have hslo : x / 20 - 2 ≤ (suffixCutoff x : ℝ) := by linarith
  have hs : 0 < suffixCutoff x := by
    have : (0 : ℝ) < suffixCutoff x := by linarith
    exact_mod_cast this
  have hrat : Real.sqrt (Real.logb 2 x) / 8 ≤
      ((upperHalfLength x + 1 : ℕ) : ℝ) / (lowerHalfLength x : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hM)).mpr
    nlinarith
  have hlograt : Real.log (Real.sqrt (Real.logb 2 x) / 8) ≤
      Real.log ((upperHalfLength x + 1 : ℕ) / (lowerHalfLength x : ℝ)) :=
    Real.log_le_log (by positivity) hrat
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  have hlogy : Real.log (Real.logb 2 x) =
      Real.logb 2 (Real.logb 2 x) * Real.log 2 := by
    rw [Real.logb]
    exact (div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne').symm
  have hlogsmall : Real.logb 2 (Real.logb 2 x) / 4 ≤
      Real.log (Real.sqrt (Real.logb 2 x) / 8) := by
    rw [Real.log_div hrootpos.ne' (by norm_num), Real.log_sqrt hypos.le, hlog8, hlogy]
    have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hprod := mul_nonneg
      (show 0 ≤ Real.logb 2 (Real.logb 2 x) / 2 - 3 by linarith)
      (show 0 ≤ Real.log 2 - 2 / 3 by linarith)
    nlinarith
  have hlog : Real.logb 2 (Real.logb 2 x) / 4 ≤
      Real.log ((upperHalfLength x + 1 : ℕ) / (lowerHalfLength x : ℝ)) :=
    hlogsmall.trans hlograt
  have hMK : lowerHalfLength x ≤ upperHalfLength x + 1 := by
    by_contra h
    have hlt : ((upperHalfLength x + 1 : ℕ) : ℝ) < (lowerHalfLength x : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge h
    have hratio : ((upperHalfLength x + 1 : ℕ) : ℝ) / (lowerHalfLength x : ℝ) < 1 :=
      (div_lt_one (by exact_mod_cast hM)).mpr hlt
    have hneg := Real.log_neg (by positivity :
      (0 : ℝ) < ((upperHalfLength x + 1 : ℕ) : ℝ) / (lowerHalfLength x : ℝ)) hratio
    linarith
  exact ⟨hM, hK, hMK, hKhi, hs, hsD, hslo, hlog⟩

/-- Uniform eventual cycle supply at the v8 scale. Here x=log₂ r,
 n is between r and 3r, and the full degree deficit is at most
 C*sqrt(r)*log₂ r. All finite numerical errors are discharged in the proof. -/
theorem eventually_cycleWordMass_ge_loglog (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ G : PhysicalGraph,
      (∀ v, G.degree v ≤ 3) →
      (2 : ℝ) ^ x ≤ G.vertexCount → G.vertexCount ≤ 3 * (2 : ℝ) ^ x →
      degreeDeficit G ≤ C * x * (2 : ℝ) ^ (x / 2) →
      ShortWalks.GirthGreater G.toSimpleGraph (girthCutoff x) →
      Real.logb 2 (Real.logb 2 x) / 64 ≤
        ∑ ell ∈ Finset.Icc 1 (2 * upperHalfLength x), cycleWordMassAtLength G ell := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hy.comp hy
  have hm := (polynomial_dyadic_decay 3 (1 / 2) (by norm_num)).const_mul C
  have he := (polynomial_dyadic_decay 0 2 (by norm_num)).const_mul 9
  have hc := (polynomial_dyadic_decay 4 (1 / 20) (by norm_num)).const_mul 9
  filter_upwards [eventually_ge_atTop (100 : ℝ), hy.eventually_ge_atTop 4,
    hz.eventually_ge_atTop 32,
    logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hm.eventually_lt_const (by norm_num : C * 0 < (1 / 4 : ℝ)),
    he.eventually_lt_const (by norm_num : (9 : ℝ) * 0 < 1 / 4),
    hc.eventually_lt_const (by norm_num : (9 : ℝ) * 0 < 1 / 2)] with
    x hx hY hZ hYX hMain hError hCollision
  intro G hmax hnlo hnhi hdg hg
  have hxpos : 0 < x := by linarith
  have hyx : Real.logb 2 x ≤ x := ((div_lt_one hxpos).mp hYX).le
  obtain ⟨hM, hK, hMK, hKhi, hs, hsD, hslo, hlog⟩ := cutoff_bounds x hx hY hyx hZ
  have hnR : (0 : ℝ) < G.vertexCount := (Real.rpow_pos_of_pos (by norm_num) x).trans_le hnlo
  have hn : 0 < G.vertexCount := by exact_mod_cast hnR
  have hd0 := degreeDeficit_nonneg G hmax
  have hK0 : (0 : ℝ) ≤ upperHalfLength x := Nat.cast_nonneg _
  have hpower : (2 : ℝ) ^ x = (2 : ℝ) ^ (x / 2) * (2 : ℝ) ^ (x / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hMain' : C * x ^ 3 / (2 : ℝ) ^ (x / 2) ≤ 1 / 4 := by
    have hExp : -(1 / 2 : ℝ) * x = -(x / 2) := by ring
    rw [hExp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hMain
    simpa only [div_eq_mul_inv, mul_assoc] using hMain.le
  have hmain : degreeDeficit G * (upperHalfLength x : ℝ) / G.vertexCount ≤ 1 / 4 := by
    have hKx : (upperHalfLength x : ℝ) ≤ x ^ 2 := by nlinarith [sq_nonneg x]
    have hnum : degreeDeficit G * (upperHalfLength x : ℝ) ≤
        C * x ^ 3 * (2 : ℝ) ^ (x / 2) := by
      calc
        _ ≤ (C * x * (2 : ℝ) ^ (x / 2)) * (x ^ 2) :=
          mul_le_mul hdg hKx hK0 (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (C * x ^ 3 * (2 : ℝ) ^ (x / 2)) / G.vertexCount :=
        div_le_div_of_nonneg_right hnum hnR.le
      _ ≤ (C * x ^ 3 * (2 : ℝ) ^ (x / 2)) / (2 : ℝ) ^ x :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hnlo
      _ = C * x ^ 3 / (2 : ℝ) ^ (x / 2) := by
        rw [hpower]
        field_simp
        ring
      _ ≤ _ := hMain'
  have hd : degreeDeficit G < G.vertexCount := by
    have hK1 : (1 : ℝ) ≤ upperHalfLength x := by exact_mod_cast hK
    have hdk : degreeDeficit G ≤ degreeDeficit G * (upperHalfLength x : ℝ) := by nlinarith
    have hbound := (div_le_iff₀ hnR).mp hmain
    linarith
  have hError' : (9 : ℝ) / (2 : ℝ) ^ (2 * x) ≤ 1 / 4 := by
    rw [show -(2 : ℝ) * x = -(2 * x) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hError
    simpa only [pow_zero, one_mul, div_eq_mul_inv] using hError.le
  have hMpower : (2 : ℝ) ^ (3 * x) ≤ (2 : ℝ) ^ lowerHalfLength x := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ lowerHalfLength x ≤ 1 / 4 := by
    calc
      _ ≤ (9 * (2 : ℝ) ^ x) / (2 : ℝ) ^ lowerHalfLength x := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ (9 * (2 : ℝ) ^ x) / (2 : ℝ) ^ (3 * x) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hMpower
      _ = 9 / (2 : ℝ) ^ (2 * x) := by
        have hpow : (2 : ℝ) ^ (3 * x) = (2 : ℝ) ^ x * (2 : ℝ) ^ (2 * x) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        rw [hpow]
        field_simp
        ring
      _ ≤ _ := hError'
  have hCollision' : 9 * x ^ 4 / (2 : ℝ) ^ (x / 20) ≤ 1 / 2 := by
    rw [show -(1 / 20 : ℝ) * x = -(x / 20) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hCollision
    simpa only [div_eq_mul_inv, mul_assoc] using hCollision.le
  have hsPow : (1 / 2 : ℝ) ^ suffixCutoff x ≤ 4 / (2 : ℝ) ^ (x / 20) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hslo
    have hlow : (2 : ℝ) ^ (x / 20 - 2) = (2 : ℝ) ^ (x / 20) / 4 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hlow, Real.rpow_natCast] at h
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (x / 20) := by positivity
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ suffixCutoff x := by positivity
    have hrecip : (1 / 2 : ℝ) ^ suffixCutoff x = 1 / (2 : ℝ) ^ suffixCutoff x := by
      rw [div_pow, one_pow]
    rw [hrecip, div_le_div_iff₀ hpowpos hpos]
    linarith
  have hcollision : (9 / 4 : ℝ) * ((2 * upperHalfLength x : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ suffixCutoff x ≤ 1 / 2 := by
    have hlen : ((2 * upperHalfLength x : ℕ) : ℝ) ≤ x ^ 2 := by
      push_cast
      linarith
    have hsq : (((2 * upperHalfLength x : ℕ) : ℝ)) ^ 2 ≤ x ^ 4 := by
      calc
        _ ≤ (x ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hlen 2
        _ = _ := by ring
    calc
      _ ≤ (9 / 4 : ℝ) * x ^ 4 * (4 / (2 : ℝ) ^ (x / 20)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hsPow
          (by positivity) (by positivity)
      _ = 9 * x ^ 4 / (2 : ℝ) ^ (x / 20) := by ring
      _ ≤ _ := hCollision'
  have hmass := cycleWordMass_ge_log_ratio G hmax hn hd
    (lowerHalfLength x) (upperHalfLength x) (suffixCutoff x) (girthCutoff x)
    hM hMK hmain herr hg hsD hs hcollision
  linarith

/-- The same uniform theorem in the manuscript's rank parameter r. -/
theorem eventually_rank_cycleWordMass_ge (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ r : ℝ in atTop, ∀ G : PhysicalGraph,
      (∀ v, G.degree v ≤ 3) →
      r ≤ G.vertexCount → G.vertexCount ≤ 3 * r →
      degreeDeficit G ≤ C * Real.sqrt r * Real.logb 2 r →
      ShortWalks.GirthGreater G.toSimpleGraph (girthCutoff (Real.logb 2 r)) →
      Real.logb 2 (Real.logb 2 (Real.logb 2 r)) / 64 ≤
        ∑ ell ∈ Finset.Icc 1 (2 * upperHalfLength (Real.logb 2 r)),
          cycleWordMassAtLength G ell := by
  have hlog : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  filter_upwards [hlog.eventually (eventually_cycleWordMass_ge_loglog C hC),
    eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  intro G hmax hnlo hnhi hd hg
  have hpow : (2 : ℝ) ^ Real.logb 2 r = r :=
    Real.rpow_logb (by norm_num) (by norm_num) hrpos
  have hhalf : (2 : ℝ) ^ (Real.logb 2 r / 2) = Real.sqrt r := by
    rw [show Real.logb 2 r / 2 = Real.logb 2 r * (1 / 2) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hpow, Real.sqrt_eq_rpow]
  apply hr G hmax (by simpa [hpow] using hnlo) (by simpa [hpow] using hnhi) ?_ hg
  rw [hhalf]
  nlinarith [hd]

end Erdos1016.Proof.DeficitCutoffParameters
