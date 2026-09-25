import Erdos1016.Extremal.Recurrence.LogStarTowers
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-!
# Iteration at the shorter proof's linear exponential rank scale

The scale is exactly `R ↦ 2^(256R)`. The reciprocal double logarithm in
the multiplicative error becomes a reciprocal earlier rank after two steps.
The comparison with an ordinary tower uses the square of the current rank.
-/

noncomputable section
namespace Erdos1016.Extremal.LinearExponentialDecay

def scale (Rmin : ℕ) : ℕ → ℕ
  | 0 => max Rmin 512
  | j + 1 => 2 ^ (256 * scale Rmin j)

theorem scale_zero (Rmin : ℕ) : scale Rmin 0 = max Rmin 512 := rfl
theorem scale_succ (Rmin j : ℕ) :
    scale Rmin (j + 1) = 2 ^ (256 * scale Rmin j) := rfl
attribute [irreducible] scale

private lemma four_pow_lower (j : ℕ) : 2 * j + 4 ≤ 4 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      nlinarith [Nat.one_le_pow (j + 1) 4]

theorem scale_ge_four_pow (Rmin j : ℕ) : 4 ^ (j + 1) ≤ scale Rmin j := by
  induction j with
  | zero =>
      rw [scale_zero]
      exact (by norm_num : 4 ^ (0 + 1) ≤ 512).trans (Nat.le_max_right _ _)
  | succ j ih =>
      have hlin := (four_pow_lower j).trans ih
      have hexp : 2 * (j + 2) ≤ 256 * scale Rmin j := by omega
      have hp : 2 ^ (2 * (j + 2)) ≤ 2 ^ (256 * scale Rmin j) :=
        Nat.pow_le_pow_right (by omega) hexp
      simpa [scale_succ, pow_mul] using hp

theorem scale_ge_start (Rmin j : ℕ) : max Rmin 512 ≤ scale Rmin j := by
  induction j with
  | zero => rw [scale_zero]
  | succ j ih =>
      apply ih.trans
      rw [scale_succ]
      exact (Nat.lt_two_pow_self (n := scale Rmin j)).le.trans
        (Nat.pow_le_pow_right (by omega) (by omega))

theorem scale_linear_lower (Rmin j : ℕ) : 2 * j + 4 ≤ scale Rmin j :=
  (four_pow_lower j).trans (scale_ge_four_pow Rmin j)

/-- This is the squared form of the paper's square-root tower comparison. -/
theorem scale_sq_le_tower (Rmin m j : ℕ)
    (hinit : (scale Rmin 0) ^ 2 ≤ expTower m) :
    (scale Rmin j) ^ 2 ≤ expTower (m + j) := by
  induction j with
  | zero => simpa using hinit
  | succ j ih =>
      have hlarge : 512 ≤ scale Rmin j := (Nat.le_max_right _ _).trans (scale_ge_start Rmin j)
      have hexp : 512 * scale Rmin j ≤ expTower (m + j) := by
        have hmul := Nat.mul_le_mul_right (scale Rmin j) hlarge
        nlinarith
      rw [scale_succ]
      calc
        (2 ^ (256 * scale Rmin j)) ^ 2 = 2 ^ (512 * scale Rmin j) := by
          rw [← pow_mul]
          congr 1
          omega
        _ ≤ 2 ^ expTower (m + j) := Nat.pow_le_pow_right (by omega) hexp
        _ = expTower (m + (j + 1)) := by simp [expTower, Nat.add_assoc]

theorem tower_le_scale (Rmin j : ℕ) : expTower j ≤ scale Rmin j := by
  induction j with
  | zero => simp only [expTower, scale_zero]; omega
  | succ j ih =>
      rw [expTower, scale_succ]
      apply Nat.pow_le_pow_right (by omega)
      omega

/-- One recurrence step adds one log-star level, up to a fixed initial shift. -/
theorem logStar_scale_bounds (Rmin j : ℕ) :
    j ≤ logStar (scale Rmin j) ∧
      logStar (scale Rmin j) ≤ logStar ((max Rmin 512) ^ 2) + j := by
  constructor
  · simpa only [logStar_expTower] using logStar_mono (tower_le_scale Rmin j)
  · apply logStar_min_le
    have htower := scale_sq_le_tower Rmin (logStar ((max Rmin 512) ^ 2)) j
      (by simpa only [scale_zero] using le_expTower_logStar ((max Rmin 512) ^ 2))
    have hlarge : 512 ≤ scale Rmin j := (Nat.le_max_right _ _).trans (scale_ge_start Rmin j)
    nlinarith

def doubleLog (R : ℕ) : ℝ := Real.logb 2 (Real.logb 2 (R : ℝ))

/-- After two steps the double logarithm is an affine function of the earlier rank. -/
theorem doubleLog_scale_add_two (Rmin j : ℕ) :
    doubleLog (scale Rmin (j + 2)) = 8 + 256 * (scale Rmin j : ℝ) := by
  have hpos : (0 : ℝ) < scale Rmin (j + 1) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 512)
      ((Nat.le_max_right _ _).trans (scale_ge_start Rmin (j + 1))))
  have hlog : Real.logb 2 (256 : ℝ) = 8 := by
    have h := Real.logb_pow (2 : ℝ) 2 8
    norm_num at h
    exact h
  change Real.logb 2 (Real.logb 2 (scale Rmin ((j + 1) + 1) : ℝ)) = _
  rw [scale_succ, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow]
  norm_num only [Real.logb_self_eq_one, Nat.cast_mul, Nat.cast_ofNat, mul_one]
  rw [Real.logb_mul (by norm_num) (ne_of_gt hpos), hlog, scale_succ,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow]
  norm_num

private lemma geometric_half_sum_le (j : ℕ) :
    (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  have heq : (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i) =
      2 * (1 - (1 / 2 : ℝ) ^ j) := by
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  have : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
  linarith

/-- Both errors become summable after rescaling, starting at the third scale. -/
theorem scaled_error_le (Rmin j : ℕ) :
    (2 : ℝ) ^ (j + 3) * (20 / doubleLog (scale Rmin (j + 2))) +
      (2 : ℝ) ^ (j + 3) * (2 : ℝ) ^ (2 - (scale Rmin (j + 2) : ℝ)) ≤
        (1 / 2 : ℝ) ^ j := by
  have hR4 : (4 : ℝ) ^ (j + 1) ≤ (scale Rmin j : ℝ) := by
    exact_mod_cast scale_ge_four_pow Rmin j
  have hden : 80 * (4 : ℝ) ^ (j + 1) ≤ doubleLog (scale Rmin (j + 2)) := by
    rw [doubleLog_scale_add_two]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (j + 1)]
  have hfirst : (2 : ℝ) ^ (j + 3) * (20 / doubleLog (scale Rmin (j + 2))) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
    calc
      (2 : ℝ) ^ (j + 3) * (20 / doubleLog (scale Rmin (j + 2))) ≤
          (2 : ℝ) ^ (j + 3) * (20 / (80 * (4 : ℝ) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden) (by positivity)
      _ = (1 / 2 : ℝ) ^ (j + 1) := by
        have hfour : (4 : ℝ) ^ (j + 1) = (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1) := by
          rw [← mul_pow]; norm_num
        rw [hfour, show j + 3 = (j + 1) + 2 by omega, pow_add]
        norm_num [one_div_pow]
        field_simp
        ring
  have hRlin : (2 : ℝ) * j + 8 ≤ (scale Rmin (j + 2) : ℝ) := by
    have h := scale_linear_lower Rmin (j + 2)
    exact_mod_cast (show 2 * j + 8 ≤ scale Rmin (j + 2) by omega)
  have hexp : ((j + 3 : ℕ) : ℝ) + (2 - (scale Rmin (j + 2) : ℝ)) ≤
      -((j + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hsecond : (2 : ℝ) ^ (j + 3) * (2 : ℝ) ^ (2 - (scale Rmin (j + 2) : ℝ)) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
    rw [← Real.rpow_natCast (2 : ℝ) (j + 3), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      (2 : ℝ) ^ (((j + 3 : ℕ) : ℝ) + (2 - (scale Rmin (j + 2) : ℝ))) ≤
          (2 : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (1 / 2 : ℝ) ^ (j + 1) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        norm_num [one_div_pow]
  calc
    _ ≤ (1 / 2 : ℝ) ^ (j + 1) + (1 / 2 : ℝ) ^ (j + 1) := add_le_add hfirst hsecond
    _ = (1 / 2 : ℝ) ^ j := by rw [pow_succ]; ring

/-- The first two scales are absorbed using `Φ ≤ 1`; subsequent errors have
the geometric bound above. No hypothesis about convergence is assumed. -/
theorem phi_scale_bound (Rmin : ℕ) (Φ : ℕ → ℝ)
    (hΦ : ∀ n, 0 ≤ Φ n ∧ Φ n ≤ 1)
    (hrec : ∀ R, Rmin ≤ R →
      Φ (2 ^ (256 * R)) ≤
        ((1 / 2 : ℝ) + 20 / doubleLog R) * Φ R + (2 : ℝ) ^ (2 - (R : ℝ))) :
    ∀ j, Φ (scale Rmin j) ≤ 6 / (2 : ℝ) ^ j := by
  let B : ℕ → ℝ := fun j => (2 : ℝ) ^ j * Φ (scale Rmin j)
  have hstep : ∀ j, B (j + 3) ≤ B (j + 2) + (1 / 2 : ℝ) ^ j := by
    intro j
    let R := scale Rmin (j + 2)
    have hRmin : Rmin ≤ R := (Nat.le_max_left _ _).trans (scale_ge_start Rmin (j + 2))
    have hden : 0 < doubleLog R := by
      dsimp [R]
      rw [doubleLog_scale_add_two]
      positivity
    have herror : 0 ≤ 20 / doubleLog R := by positivity
    have hrec' := hrec R hRmin
    have hmul := mul_le_mul_of_nonneg_left (hΦ R).2 herror
    have hb : Φ (2 ^ (256 * R)) ≤
        (1 / 2 : ℝ) * Φ R + 20 / doubleLog R + (2 : ℝ) ^ (2 - (R : ℝ)) := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 : ℝ) ^ (j + 3))
    have hid : (2 : ℝ) ^ (j + 3) *
        ((1 / 2 : ℝ) * Φ R + 20 / doubleLog R + (2 : ℝ) ^ (2 - (R : ℝ))) =
        B (j + 2) + ((2 : ℝ) ^ (j + 3) * (20 / doubleLog R) +
          (2 : ℝ) ^ (j + 3) * (2 : ℝ) ^ (2 - (R : ℝ))) := by
      dsimp [B, R]
      rw [show j + 3 = (j + 2) + 1 by omega, pow_succ]
      ring
    rw [hid] at hscaled
    have hnext : scale Rmin (j + 3) = 2 ^ (256 * R) := by
      change scale Rmin ((j + 2) + 1) = _
      exact scale_succ Rmin (j + 2)
    change (2 : ℝ) ^ (j + 3) * Φ (scale Rmin (j + 3)) ≤ _
    rw [hnext]
    exact hscaled.trans (add_le_add_left (scaled_error_le Rmin j) _)
  have hsum : ∀ j, B (j + 2) ≤ 4 + ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := by
    intro j
    induction j with
    | zero =>
        have hb := mul_le_mul_of_nonneg_left (hΦ (scale Rmin 2)).2 (by norm_num : (0 : ℝ) ≤ 4)
        simpa only [B, Nat.zero_add, Finset.range_zero, Finset.sum_empty, add_zero, mul_one,
          show (2 : ℝ) ^ 2 = 4 by norm_num] using hb
    | succ j ih =>
        have hs := hstep j
        rw [Finset.sum_range_succ]
        convert hs.trans (add_le_add_right ih ((1 / 2 : ℝ) ^ j)) using 1
        ring
  intro j
  have hB6 : B j ≤ 6 := by
    rcases j with _ | _ | j
    · have h := (hΦ (scale Rmin 0)).2
      dsimp [B]
      norm_num
      linarith
    · have h := (hΦ (scale Rmin 1)).2
      dsimp [B]
      norm_num
      linarith
    · have h := hsum j
      have hg := geometric_half_sum_le j
      linarith
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)).2
  simpa [B, mul_comm] using hB6

/-- The shorter proof's recurrence implies uniform log-star decay. The only
mathematical input is the displayed recurrence for a bounded antitone sequence. -/
theorem recurrence_logStar_bound (Rmin : ℕ) (Φ : ℕ → ℝ)
    (hΦ : ∀ n, 0 ≤ Φ n ∧ Φ n ≤ 1)
    (hmono : ∀ ⦃a b⦄, a ≤ b → Φ b ≤ Φ a)
    (hrec : ∀ R, Rmin ≤ R →
      Φ (2 ^ (256 * R)) ≤
        ((1 / 2 : ℝ) + 20 / doubleLog R) * Φ R + (2 : ℝ) ^ (2 - (R : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ,
      Φ r ≤ K / (2 : ℝ) ^ logStar r := by
  let K0 := max Rmin 512
  let m := logStar (K0 ^ 2)
  let K : ℝ := 6 * (2 : ℝ) ^ (m + 1)
  have hinit : K0 ^ 2 ≤ expTower m := le_expTower_logStar (K0 ^ 2)
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, ?_⟩
  intro r
  by_cases hr : r < K0
  · have hk : logStar r ≤ m := by
      apply logStar_min_le
      have hK0 : 1 ≤ K0 := by dsimp [K0]; omega
      have hpow : K0 ≤ K0 ^ 2 := by nlinarith
      exact (show r ≤ K0 ^ 2 by omega).trans hinit
    have h2k : (2 : ℝ) ^ logStar r ≤ (2 : ℝ) ^ m := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) hk
    have hKbig : (2 : ℝ) ^ logStar r ≤ K := by
      have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) (Nat.le_succ m)
      have hpos : 0 ≤ (2 : ℝ) ^ (m + 1) := by positivity
      dsimp [K]
      nlinarith
    have hratio : 1 ≤ K / (2 : ℝ) ^ logStar r := by
      rw [le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ logStar r)]
      simpa using hKbig
    exact (hΦ r).2.trans hratio
  · have hrK0 : K0 ≤ r := le_of_not_gt hr
    let P : ℕ → Prop := fun j => r < scale Rmin (j + 1)
    have hex : ∃ j, P j := by
      refine ⟨r, ?_⟩
      have hlarge := scale_linear_lower Rmin (r + 1)
      dsimp [P]
      omega
    let j := Nat.find hex
    have hjP : r < scale Rmin (j + 1) := Nat.find_spec hex
    have hRjle : scale Rmin j ≤ r := by
      by_cases hj0 : j = 0
      · rw [hj0, scale_zero]
        exact hrK0
      · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        have hnot : ¬ r < scale Rmin j := by
          intro hlt
          have hprev : P (j - 1) := by
            dsimp [P]
            simpa [Nat.sub_add_cancel hjpos] using hlt
          have hmin := Nat.find_min' hex hprev
          omega
        exact le_of_not_gt hnot
    have hphi : Φ r ≤ 6 / (2 : ℝ) ^ j :=
      (hmono hRjle).trans (phi_scale_bound Rmin Φ hΦ hrec j)
    have hinit' : (scale Rmin 0) ^ 2 ≤ expTower m := by
      simpa only [scale_zero, K0] using hinit
    have htower := scale_sq_le_tower Rmin m (j + 1) hinit'
    have hRnext : scale Rmin (j + 1) ≤ expTower (m + (j + 1)) := by
      have hp := (Nat.le_max_right _ _).trans (scale_ge_start Rmin (j + 1))
      nlinarith
    have hlog : logStar r ≤ m + (j + 1) :=
      logStar_min_le ((le_of_lt hjP).trans hRnext)
    have hden : (2 : ℝ) ^ logStar r ≤ (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ j := by
      calc
        (2 : ℝ) ^ logStar r ≤ (2 : ℝ) ^ (m + (j + 1)) := by
          exact_mod_cast Nat.pow_le_pow_right (by omega) hlog
        _ = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ j := by
          rw [pow_add, pow_succ, pow_succ]
          ring
    have hratio : 6 / (2 : ℝ) ^ j ≤ K / (2 : ℝ) ^ logStar r := by
      rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)
        (by positivity : 0 < (2 : ℝ) ^ logStar r)]
      dsimp [K]
      nlinarith
    exact hphi.trans hratio

end Erdos1016.Extremal.LinearExponentialDecay
