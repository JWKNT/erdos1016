import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false

/-!
# The explicit analytic stopping threshold

Section 7.3 of the supplied manuscript uses
`T₀(c) = ceil ((16/15) * max N₀ (2 ^ ((c/γ)^2)))` for `c ≥ 1`.
The unused value at zero is defined to be one. This monotone extension
allows the quadratic-exponential estimate to hold for every natural `c`,
as required by the existing root-comparison interface. The literal formula
at zero would exceed one and could not satisfy that interface.

The exponent coefficient below is deliberately loose but explicit and fixed
once `N₀` and `γ` are fixed. No analytic forest estimate is assumed or proved
in this arithmetic module.
-/

noncomputable section

namespace Erdos1016.Proof.AnalyticStoppingThreshold

/-- The manuscript's cutoff at positive exterior counts, with value one at
zero to make its natural-number extension compatible with `2^(A₀ c²)`. -/
def stoppingThreshold (N₀ : ℕ) (γ : ℝ) (c : ℕ) : ℕ :=
  if c = 0 then 1 else
    Nat.ceil ((16 / 15 : ℝ) *
      max (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2)))

/-- A natural, graph-independent coefficient for the quadratic exponent. -/
def quadraticExponent (N₀ : ℕ) (γ : ℝ) : ℕ :=
  N₀ + Nat.ceil ((γ⁻¹) ^ 2) + 1

@[simp] theorem stoppingThreshold_zero (N₀ : ℕ) (γ : ℝ) :
    stoppingThreshold N₀ γ 0 = 1 := by
  simp [stoppingThreshold]

theorem stoppingThreshold_of_pos (N₀ : ℕ) (γ : ℝ) {c : ℕ} (hc : 0 < c) :
    stoppingThreshold N₀ γ c =
      Nat.ceil ((16 / 15 : ℝ) *
        max (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2))) := by
  simp [stoppingThreshold, Nat.ne_of_gt hc]

theorem stoppingThreshold_pos (N₀ : ℕ) (γ : ℝ) (c : ℕ) :
    0 < stoppingThreshold N₀ γ c := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [stoppingThreshold_of_pos N₀ γ (Nat.pos_of_ne_zero hc)]
    apply Nat.ceil_pos.mpr
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (((c : ℝ) / γ) ^ 2) := by positivity
    have hmax := le_max_right (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2))
    positivity

theorem stoppingThreshold_monotone (N₀ : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Monotone (stoppingThreshold N₀ γ) := by
  intro a b hab
  by_cases ha : a = 0
  · rw [ha, stoppingThreshold_zero]
    exact stoppingThreshold_pos N₀ γ b
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    have hbpos : 0 < b := hapos.trans_le hab
    rw [stoppingThreshold_of_pos N₀ γ hapos,
      stoppingThreshold_of_pos N₀ γ hbpos]
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16 / 15)
    apply max_le_max_left
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hnonneg : 0 ≤ (a : ℝ) / γ := div_nonneg (Nat.cast_nonneg _) hγ.le
    have hle : (a : ℝ) / γ ≤ (b : ℝ) / γ := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hγ.le
    nlinarith

/-- The stopping size grows at most quadratically in the base-two exponent.
The coefficient is chosen once, independently of the exterior count. -/
theorem stoppingThreshold_le_two_pow (N₀ : ℕ) (γ : ℝ) (c : ℕ) :
    stoppingThreshold N₀ γ c ≤ 2 ^ (quadraticExponent N₀ γ * c ^ 2) := by
  by_cases hc : c = 0
  · simp [hc]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    rw [stoppingThreshold_of_pos N₀ γ hcpos]
    apply Nat.ceil_le.mpr
    let a := Nat.ceil ((γ⁻¹) ^ 2)
    have hinv : (γ⁻¹) ^ 2 ≤ (a : ℝ) := Nat.le_ceil _
    have hexponent : ((c : ℝ) / γ) ^ 2 ≤ ((a * c ^ 2 : ℕ) : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hinv (sq_nonneg (c : ℝ))
      simpa [div_eq_mul_inv, mul_pow, mul_comm, a] using hmul
    have hpower : (2 : ℝ) ^ (((c : ℝ) / γ) ^ 2) ≤
        (2 : ℝ) ^ (a * c ^ 2 : ℕ) := by
      rw [← Real.rpow_natCast (2 : ℝ) (a * c ^ 2)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    have hN : (N₀ : ℝ) ≤ (2 : ℝ) ^ N₀ := by
      exact_mod_cast (Nat.lt_two_pow_self (n := N₀)).le
    have hNOne : (1 : ℝ) ≤ (2 : ℝ) ^ N₀ := one_le_pow₀ (by norm_num)
    have haOne : (1 : ℝ) ≤ (2 : ℝ) ^ (a * c ^ 2 : ℕ) :=
      one_le_pow₀ (by norm_num)
    have hmax : max (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2)) ≤
        (2 : ℝ) ^ N₀ * (2 : ℝ) ^ (a * c ^ 2 : ℕ) := by
      apply max_le
      · exact hN.trans (le_mul_of_one_le_right (by positivity) haOne)
      · exact hpower.trans (le_mul_of_one_le_left (by positivity) hNOne)
    have hscaled : (16 / 15 : ℝ) *
        max (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2)) ≤
        (2 : ℝ) ^ (N₀ + a * c ^ 2 + 1) := by
      calc
        _ ≤ 2 * ((2 : ℝ) ^ N₀ * (2 : ℝ) ^ (a * c ^ 2 : ℕ)) := by
          exact mul_le_mul (by norm_num) hmax (by positivity) (by norm_num)
        _ = (2 : ℝ) ^ (N₀ + a * c ^ 2 + 1) := by
          rw [pow_add, pow_add, pow_one]
          ring
    have hcOne : 1 ≤ c ^ 2 := by nlinarith
    have hle : N₀ + a * c ^ 2 + 1 ≤ quadraticExponent N₀ γ * c ^ 2 := by
      change N₀ + a * c ^ 2 + 1 ≤ (N₀ + a + 1) * c ^ 2
      nlinarith
    have hmono : (2 : ℝ) ^ (N₀ + a * c ^ 2 + 1) ≤
        (2 : ℝ) ^ (quadraticExponent N₀ γ * c ^ 2) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hle
    exact_mod_cast hscaled.trans hmono

/-- A region above this cutoff has a core above both analytic onsets whenever
the core retains at least `15/16` of the region's vertices. This is the exact
arithmetic transfer used in Lemma 7.4. -/
theorem core_onsets_le (N₀ : ℕ) (γ : ℝ) {c n k : ℕ}
    (hc : 0 < c) (hregion : stoppingThreshold N₀ γ c ≤ n)
    (hcore : (15 / 16 : ℝ) * (n : ℝ) ≤ (k : ℝ)) :
    N₀ ≤ k ∧ (2 : ℝ) ^ (((c : ℝ) / γ) ^ 2) ≤ (k : ℝ) := by
  have hceil : (16 / 15 : ℝ) *
      max (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2)) ≤
      (stoppingThreshold N₀ γ c : ℝ) := by
    rw [stoppingThreshold_of_pos N₀ γ hc]
    exact Nat.le_ceil _
  have hregionReal : (stoppingThreshold N₀ γ c : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hregion
  have hmax : max (N₀ : ℝ) ((2 : ℝ) ^ (((c : ℝ) / γ) ^ 2)) ≤ (k : ℝ) := by
    nlinarith
  have hparts := max_le_iff.mp hmax
  exact ⟨by exact_mod_cast hparts.1, hparts.2⟩

/-- At the core cutoff, the stretched-exponential term pays the entire
`2^(c-1)` cost of conditioning on the actual exterior components. -/
theorem exterior_conditioning_factor_le_half
    {γ : ℝ} (hγ : 0 < γ) {c k : ℕ} (hc : 0 < c)
    (hcutoff : (2 : ℝ) ^ (((c : ℝ) / γ) ^ 2) ≤ (k : ℝ)) :
    (2 : ℝ) ^ (c - 1) *
      (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (k : ℝ))) ≤ 1 / 2 := by
  have hk : (0 : ℝ) < k :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hcutoff
  have hsquare : ((c : ℝ) / γ) ^ 2 ≤ Real.logb 2 (k : ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hk).mpr hcutoff
  have hsqrt := Real.le_sqrt_of_sq_le hsquare
  have hpaid : (c : ℝ) ≤ γ * Real.sqrt (Real.logb 2 (k : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hγ.le
    have hcancel : γ * ((c : ℝ) / γ) = c := by field_simp
    rwa [hcancel] at hmul
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (by omega : 1 ≤ c) (R := ℝ)
  rw [← Real.rpow_natCast (2 : ℝ) (c - 1),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  calc
    (2 : ℝ) ^ (((c - 1 : ℕ) : ℝ) +
        -γ * Real.sqrt (Real.logb 2 (k : ℝ))) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      rw [hcast]
      linarith
    _ = 1 / 2 := by norm_num

end Erdos1016.Proof.AnalyticStoppingThreshold

end
