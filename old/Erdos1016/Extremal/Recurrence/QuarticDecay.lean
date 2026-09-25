import Erdos1016.Extremal.Recurrence.LogStarTowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Extremal

def recurrenceScaleStep (C R : ℕ) : ℕ := 2 ^ (C * R ^ 4)

/-- The scale reached after `j` applications of the paper's recurrence. -/
def recurrenceScale (C Rmin : ℕ) (j : ℕ) : ℕ :=
  (recurrenceScaleStep C)^[j] (max Rmin (max 4 (5 * C)))
attribute [irreducible] recurrenceScale

lemma recurrenceScale_zero (C Rmin : ℕ) :
    recurrenceScale C Rmin 0 = max Rmin (max 4 (5 * C)) := by
  simp [recurrenceScale]

lemma recurrenceScale_succ (C Rmin j : ℕ) :
    recurrenceScale C Rmin (j + 1) =
      2 ^ (C * (recurrenceScale C Rmin j) ^ 4) := by
  simp [recurrenceScale, recurrenceScaleStep, Function.iterate_succ_apply']

lemma four_pow_succ_ge (j : ℕ) : 2 * j + 4 ≤ 4 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      nlinarith [ih, Nat.one_le_pow (j + 1) 4]

lemma recurrenceScale_ge (C Rmin j : ℕ) (hC : 1 ≤ C) :
    4 ^ (j + 1) ≤ recurrenceScale C Rmin j := by
  induction j with
  | zero =>
      rw [recurrenceScale_zero]
      exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  | succ j ih =>
      rw [recurrenceScale_succ]
      have hlin : 2 * j + 4 ≤ recurrenceScale C Rmin j := by
        calc
          2 * j + 4 ≤ 4 ^ (j + 1) := four_pow_succ_ge j
          _ ≤ recurrenceScale C Rmin j := ih
      have hexp : 2 * (j + 2) ≤ C * (recurrenceScale C Rmin j) ^ 4 := by
        have hpow : recurrenceScale C Rmin j ≤ (recurrenceScale C Rmin j) ^ 4 := by
          have hpos : 1 ≤ recurrenceScale C Rmin j := by omega
          calc
            recurrenceScale C Rmin j = recurrenceScale C Rmin j ^ 1 := by simp
            _ ≤ recurrenceScale C Rmin j ^ 4 := Nat.pow_le_pow_right hpos (by omega)
        have hmul := Nat.mul_le_mul_right ((recurrenceScale C Rmin j) ^ 4) hC
        nlinarith
      have htwo : 2 ^ (2 * (j + 2)) ≤
          2 ^ (C * (recurrenceScale C Rmin j) ^ 4) :=
        Nat.pow_le_pow_right (by omega) hexp
      simpa [pow_mul] using htwo

lemma recurrenceScale_ge_start (C Rmin j : ℕ) (hC : 1 ≤ C) :
    max Rmin (max 4 (5 * C)) ≤ recurrenceScale C Rmin j := by
  induction j with
  | zero => rw [recurrenceScale_zero]
  | succ j ih =>
      rw [recurrenceScale_succ]
      have hle : recurrenceScale C Rmin j ≤ 2 ^ (C * (recurrenceScale C Rmin j) ^ 4) := by
        have hR : 1 ≤ recurrenceScale C Rmin j := by
          have := recurrenceScale_ge C Rmin j hC
          omega
        have hpow : recurrenceScale C Rmin j ≤ (recurrenceScale C Rmin j) ^ 4 := by
          calc
            recurrenceScale C Rmin j = recurrenceScale C Rmin j ^ 1 := by simp
            _ ≤ recurrenceScale C Rmin j ^ 4 := Nat.pow_le_pow_right hR (by omega)
        have hmul := Nat.mul_le_mul_right ((recurrenceScale C Rmin j) ^ 4) hC
        have hexp : recurrenceScale C Rmin j ≤ C * (recurrenceScale C Rmin j) ^ 4 := by
          nlinarith
        calc
          recurrenceScale C Rmin j ≤ 2 ^ (recurrenceScale C Rmin j) := by
            exact (Nat.lt_two_pow_self (n := recurrenceScale C Rmin j)).le
          _ ≤ 2 ^ (C * (recurrenceScale C Rmin j) ^ 4) := Nat.pow_le_pow_right (by omega) hexp
      exact ih.trans hle

lemma recurrenceScale_pow_five_le_tower (C Rmin m j : ℕ) (hC : 1 ≤ C)
    (hinit : (recurrenceScale C Rmin 0) ^ 5 ≤ expTower m) :
    (recurrenceScale C Rmin j) ^ 5 ≤
      expTower (m + j) := by
  induction j with
  | zero =>
      simpa using hinit
  | succ j ih =>
      have hlarge : 5 * C ≤ recurrenceScale C Rmin j := by
        have hst := recurrenceScale_ge_start C Rmin j hC
        omega
      have hpow : 5 * C * (recurrenceScale C Rmin j) ^ 4 ≤
          (recurrenceScale C Rmin j) ^ 5 := by
        have hmul := Nat.mul_le_mul_right ((recurrenceScale C Rmin j) ^ 4) hlarge
        nlinarith
      have hexp : 5 * (C * (recurrenceScale C Rmin j) ^ 4) ≤
          expTower (m + j) := by
        calc
          5 * (C * (recurrenceScale C Rmin j) ^ 4) =
              5 * C * (recurrenceScale C Rmin j) ^ 4 := by ring
          _ ≤ (recurrenceScale C Rmin j) ^ 5 := hpow
          _ ≤ expTower (m + j) := ih
      rw [recurrenceScale_succ]
      calc
        (2 ^ (C * (recurrenceScale C Rmin j) ^ 4)) ^ 5 =
            2 ^ (5 * (C * (recurrenceScale C Rmin j) ^ 4)) := by
              rw [← Nat.pow_mul]
              congr 1
              omega
        _ ≤ 2 ^ expTower (m + j) := Nat.pow_le_pow_right (by omega) hexp
        _ = expTower (m + j + 1) := by simp [expTower, Nat.add_assoc]

lemma recurrenceScale_linear_lower (C Rmin j : ℕ) (hC : 1 ≤ C) :
    2 * j + 4 ≤ recurrenceScale C Rmin j := by
  calc
    2 * j + 4 ≤ 4 ^ (j + 1) := four_pow_succ_ge j
    _ ≤ recurrenceScale C Rmin j := recurrenceScale_ge C Rmin j hC

lemma recurrenceScale_start_lower (C Rmin j : ℕ) (hC : 1 ≤ C) :
    4 ^ (j + 1) ≤ recurrenceScale C Rmin j := recurrenceScale_ge C Rmin j hC

lemma geometric_half_sum (j : ℕ) :
    (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i) = 2 * (1 - (1 / 2 : ℝ) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma geometric_half_sum_le_two (j : ℕ) :
    (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  rw [geometric_half_sum]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
  linarith

lemma recurrenceScale_error_le (C Rmin j : ℕ) (hC : 1 ≤ C) :
    (2 : ℝ) ^ (j + 1) / (recurrenceScale C Rmin j : ℝ) +
      (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (2 - (recurrenceScale C Rmin j : ℝ)) ≤
        (1 / 2 : ℝ) ^ j := by
  let R := recurrenceScale C Rmin j
  have hR4 : (4 : ℝ) ^ (j + 1) ≤ (R : ℝ) := by
    exact_mod_cast recurrenceScale_start_lower C Rmin j hC
  have hRlin : (2 : ℝ) * j + 4 ≤ (R : ℝ) := by
    exact_mod_cast recurrenceScale_linear_lower C Rmin j hC
  have hfirst : (2 : ℝ) ^ (j + 1) / (R : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 1) := by
    have hden : (4 : ℝ) ^ (j + 1) = (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1) := by
      rw [← mul_pow]
      norm_num
    calc
      (2 : ℝ) ^ (j + 1) / (R : ℝ) ≤
          (2 : ℝ) ^ (j + 1) / (4 : ℝ) ^ (j + 1) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hR4
      _ = (1 / 2 : ℝ) ^ (j + 1) := by rw [hden]; field_simp
  have hexp : ((j + 1 : ℕ) : ℝ) + (2 - (R : ℝ)) ≤ -((j + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hpow : (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) + (2 - (R : ℝ))) ≤
      (2 : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : 1 < (2 : ℝ))).2 hexp
  have hterm : (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (2 - (R : ℝ)) =
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) + (2 - (R : ℝ))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (j + 1), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hneg : (2 : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      (1 / 2 : ℝ) ^ (j + 1) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    norm_num [one_div_pow]
  have hsecond : (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (2 - (R : ℝ)) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
    rw [hterm]
    exact hpow.trans_eq hneg
  calc
    (2 : ℝ) ^ (j + 1) / (R : ℝ) +
        (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (2 - (R : ℝ)) ≤
        (1 / 2 : ℝ) ^ (j + 1) + (1 / 2 : ℝ) ^ (j + 1) := add_le_add hfirst hsecond
    _ = (1 / 2 : ℝ) ^ j := by rw [pow_succ]; ring

lemma recurrenceScale_phi_bound (C Rmin : ℕ) (hC : 1 ≤ C) (Φ : ℕ → ℝ)
    (hΦ : ∀ n, 0 ≤ Φ n ∧ Φ n ≤ 1)
    (hrec : ∀ R, Rmin ≤ R →
      Φ (2 ^ (C * R ^ 4)) ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * Φ R + (2 : ℝ) ^ (2 - (R : ℝ))) :
    ∀ j, Φ (recurrenceScale C Rmin j) ≤ 3 / (2 : ℝ) ^ j := by
  let B : ℕ → ℝ := fun j => (2 : ℝ) ^ j * Φ (recurrenceScale C Rmin j)
  have hBstep : ∀ j, B (j + 1) ≤ B j + (1 / 2 : ℝ) ^ j := by
    intro j
    let R := recurrenceScale C Rmin j
    have hRmin : Rmin ≤ R :=
      (Nat.le_max_left Rmin _).trans (recurrenceScale_ge_start C Rmin j hC)
    have hRposNat : 0 < R := by
      have h := recurrenceScale_start_lower C Rmin j hC
      exact lt_of_lt_of_le (by positivity) h
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRposNat
    have hRrec := hrec R hRmin
    have hΦbounds := hΦ R
    have hrec' : Φ (2 ^ (C * R ^ 4)) ≤
        (1 / 2 : ℝ) * Φ R + 1 / (R : ℝ) + (2 : ℝ) ^ (2 - (R : ℝ)) := by
      have hinv : 0 ≤ 1 / (R : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hΦbounds.2 hinv
      nlinarith [hRrec]
    have hscaleErr := recurrenceScale_error_le C Rmin j hC
    have hstep : Φ (recurrenceScale C Rmin (j + 1)) ≤
        (1 / 2 : ℝ) * Φ R + 1 / (R : ℝ) + (2 : ℝ) ^ (2 - (R : ℝ)) := by
      simpa [R, recurrenceScale_succ] using hrec'
    have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ (2 : ℝ) ^ (j + 1))
    have hidentity : (2 : ℝ) ^ (j + 1) *
          ((1 / 2 : ℝ) * Φ R + 1 / (R : ℝ) + (2 : ℝ) ^ (2 - (R : ℝ))) =
        (2 : ℝ) ^ j * Φ R +
          ((2 : ℝ) ^ (j + 1) / (R : ℝ) +
            (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (2 - (R : ℝ))) := by
      rw [pow_succ]
      ring
    change (2 : ℝ) ^ (j + 1) * Φ (recurrenceScale C Rmin (j + 1)) ≤ _
    rw [hidentity] at hmul
    change B (j + 1) ≤ B j + (1 / 2 : ℝ) ^ j
    simpa [B, R] using hmul.trans (add_le_add_left hscaleErr _)
  have hBbound : ∀ j, B j ≤ 1 + ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := by
    intro j
    induction j with
    | zero =>
        have h := hΦ (recurrenceScale C Rmin 0)
        simpa [B] using h.2
    | succ j ih =>
        have hs := hBstep j
        rw [Finset.sum_range_succ]
        calc
          B (j + 1) ≤ B j + (1 / 2 : ℝ) ^ j := hs
          _ ≤ 1 + (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i) + (1 / 2 : ℝ) ^ j :=
            add_le_add_right ih _
          _ = 1 + ((∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i) + (1 / 2 : ℝ) ^ j) := by ring
  intro j
  have hB3 : B j ≤ 3 := by
    calc
      B j ≤ 1 + ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := hBbound j
      _ ≤ 3 := by linarith [geometric_half_sum_le_two j]
  have hpowpos : 0 < (2 : ℝ) ^ j := by positivity
  have hdivide := div_le_div_of_nonneg_right hB3 (le_of_lt hpowpos)
  calc
    Φ (recurrenceScale C Rmin j) = B j / (2 : ℝ) ^ j := by
      simp [B]
    _ ≤ 3 / (2 : ℝ) ^ j := hdivide

/-- Iterate the paper's quartic-exponential recurrence. Monotonicity fills
the gaps between recurrence scales; the tower majorant shows that each scale
index accounts for one log-star level up to a fixed initial offset. -/
theorem quartic_exponential_recurrence_logStar_bound
    (C Rmin : ℕ) (hC : 1 ≤ C) (Φ : ℕ → ℝ)
    (hΦ : ∀ n, 0 ≤ Φ n ∧ Φ n ≤ 1)
    (hmono : ∀ ⦃a b⦄, a ≤ b → Φ b ≤ Φ a)
    (hrec : ∀ R, Rmin ≤ R →
      Φ (2 ^ (C * R ^ 4)) ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * Φ R + (2 : ℝ) ^ (2 - (R : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ,
      Φ r ≤ K / (2 : ℝ) ^ logStar r := by
  let K0 := max Rmin (max 4 (5 * C))
  let m := logStar (K0 ^ 5)
  let K : ℝ := 3 * (2 : ℝ) ^ (m + 1)
  have hCpos : 1 ≤ C := hC
  have hinit : K0 ^ 5 ≤ expTower m := le_expTower_logStar (K0 ^ 5)
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, ?_⟩
  intro r
  by_cases hr : r < K0
  · have hk : logStar r ≤ m := by
      apply logStar_min_le
      have hle : r ≤ K0 ^ 5 := by
        have hK0 : 1 ≤ K0 := by dsimp [K0]; omega
        have hpow : K0 ≤ K0 ^ 5 := by
          calc
            K0 = K0 ^ 1 := by simp
            _ ≤ K0 ^ 5 := Nat.pow_le_pow_right hK0 (by omega)
        omega
      exact hle.trans (le_expTower_logStar (K0 ^ 5))
    have h2k : (2 : ℝ) ^ logStar r ≤ (2 : ℝ) ^ m := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) hk
    have hKbig : (2 : ℝ) ^ logStar r ≤ K := by
      have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) (Nat.le_succ m)
      have hpos : 0 ≤ (2 : ℝ) ^ (m + 1) := by positivity
      dsimp [K]
      nlinarith [h2k, hpow, hpos]
    have hratio : 1 ≤ K / (2 : ℝ) ^ logStar r := by
      rw [le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ logStar r)]
      simpa [one_mul] using hKbig
    exact (hΦ r).2.trans hratio
  · have hrK0 : K0 ≤ r := le_of_not_gt hr
    let P : ℕ → Prop := fun j => r < recurrenceScale C Rmin (j + 1)
    have hex : ∃ j, P j := by
      refine ⟨r, ?_⟩
      have hlarge : r < 4 ^ (r + 2) := by
        have hpow := four_pow_succ_ge (r + 1)
        have hpow' : 2 * (r + 1) + 4 ≤ 4 ^ (r + 2) := by
          simpa [Nat.add_assoc] using hpow
        have := hpow'
        omega
      exact hlarge.trans_le (recurrenceScale_ge C Rmin (r + 1) hC)
    let j := Nat.find hex
    have hjP : r < recurrenceScale C Rmin (j + 1) := Nat.find_spec hex
    have hRjle : recurrenceScale C Rmin j ≤ r := by
      by_cases hj0 : j = 0
      · rw [hj0]
        rw [recurrenceScale_zero]
        exact hrK0
      · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        have hnot : ¬ r < recurrenceScale C Rmin j := by
          intro hlt
          have hprev : P (j - 1) := by
            dsimp [P]
            simpa [Nat.sub_add_cancel hjpos] using hlt
          have hmin := Nat.find_min' hex hprev
          omega
        exact le_of_not_gt hnot
    have hphiScale := recurrenceScale_phi_bound C Rmin hC Φ hΦ hrec j
    have hphi : Φ r ≤ 3 / (2 : ℝ) ^ j :=
      (hmono hRjle).trans hphiScale
    have hinit' : (recurrenceScale C Rmin 0) ^ 5 ≤ expTower m := by
      simpa [recurrenceScale_zero, K0] using hinit
    have htower5 := recurrenceScale_pow_five_le_tower C Rmin m (j + 1) hC hinit'
    have hRnext : recurrenceScale C Rmin (j + 1) ≤ expTower (m + (j + 1)) := by
      have hRpos : 1 ≤ recurrenceScale C Rmin (j + 1) := by
        have := recurrenceScale_ge_start C Rmin (j + 1) hC
        omega
      have hpow : recurrenceScale C Rmin (j + 1) ≤
          (recurrenceScale C Rmin (j + 1)) ^ 5 := by
        calc
          recurrenceScale C Rmin (j + 1) =
              (recurrenceScale C Rmin (j + 1)) ^ 1 := by simp
          _ ≤ (recurrenceScale C Rmin (j + 1)) ^ 5 :=
            Nat.pow_le_pow_right hRpos (by omega)
      exact hpow.trans htower5
    have hlog : logStar r ≤ m + (j + 1) :=
      logStar_min_le (le_of_lt hjP |>.trans hRnext)
    have hden : (2 : ℝ) ^ logStar r ≤
        (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ j := by
      calc
        (2 : ℝ) ^ logStar r ≤ (2 : ℝ) ^ (m + (j + 1)) := by
          exact_mod_cast Nat.pow_le_pow_right (by omega) hlog
        _ = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ j := by
          rw [pow_add, pow_succ, pow_succ]
          ring
    have hratio : 3 / (2 : ℝ) ^ j ≤ K / (2 : ℝ) ^ logStar r := by
      rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)
        (by positivity : 0 < (2 : ℝ) ^ logStar r)]
      dsimp [K]
      nlinarith [hden]
    exact hphi.trans hratio

end Erdos1016.Extremal
