import Mathlib

set_option autoImplicit false

/-!
# Concave power budget for actual cut recursion

The constant is written as 4*(1/2)^p-2. For p=1-a this is exactly
2*(2^a-1), the constant used in manuscript equation (13.3).
-/

noncomputable section
namespace Erdos1016.SafeCore

def gapConstant (p : ℝ) : ℝ := 4 * (1 / 2 : ℝ) ^ p - 2

theorem gapConstant_pos {p : ℝ} (hp : p < 1) : 0 < gapConstant p := by
  have h := Real.self_lt_rpow_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hp
  unfold gapConstant
  linarith

theorem gapConstant_le_two {p : ℝ} (hp : 0 ≤ p) : gapConstant p ≤ 2 := by
  have h := Real.rpow_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hp
  unfold gapConstant
  linarith

/-- The two chord inequalities on [0,1/2] are proved separately. -/
theorem normalized_power_gap {p x : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    gapConstant p * x ≤ x ^ p + (1 - x) ^ p - 1 := by
  have hconc := Real.concaveOn_rpow hp0.le hp1
  rcases hconc with ⟨_, hconc⟩
  have h0 := hconc (x := (0 : ℝ)) (by norm_num) (y := (1 / 2 : ℝ))
    (by norm_num) (a := 1 - 2 * x) (b := 2 * x)
    (by linarith) (by linarith) (by ring)
  have h1 := hconc (x := (1 : ℝ)) (by norm_num) (y := (1 / 2 : ℝ))
    (by norm_num) (a := 1 - 2 * x) (b := 2 * x)
    (by linarith) (by linarith) (by ring)
  simp only [smul_eq_mul, Real.zero_rpow hp0.ne', Real.one_rpow, mul_zero,
    mul_one, zero_add] at h0 h1
  have ex0 : 2 * x * (1 / 2 : ℝ) = x := by ring
  have ex1 : 1 - 2 * x + 2 * x * (1 / 2 : ℝ) = 1 - x := by ring
  rw [ex0] at h0
  rw [ex1] at h1
  unfold gapConstant
  nlinarith

theorem power_gap_of_le {p s t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    gapConstant p * s * (s + t) ^ (p - 1) ≤
      s ^ p + t ^ p - (s + t) ^ p := by
  let n := s + t
  let x := s / n
  have hn : 0 < n := add_pos hs ht
  have hx0 : 0 ≤ x := (div_pos hs hn).le
  have hx1 : x ≤ 1 / 2 := by
    apply (div_le_iff₀ hn).2
    dsimp [n]
    linarith
  have hy : 0 ≤ 1 - x := by linarith
  have eqs : n * x = s := by dsimp [x]; field_simp [hn.ne']
  have eqt : n * (1 - x) = t := by
    dsimp [x, n]
    field_simp [show s + t ≠ 0 from hn.ne']
  have hpow := mul_le_mul_of_nonneg_left
    (normalized_power_gap hp0 hp1 hx0 hx1) (Real.rpow_nonneg hn.le p)
  have es : n ^ p * x ^ p = s ^ p := by
    rw [← Real.mul_rpow hn.le hx0, eqs]
  have et : n ^ p * (1 - x) ^ p = t ^ p := by
    rw [← Real.mul_rpow hn.le hy, eqt]
  have ex : n ^ p * x = s * n ^ (p - 1) := by
    rw [Real.rpow_sub hn, Real.rpow_one]
    dsimp [x]
    ring
  have er : n ^ p * (x ^ p + (1 - x) ^ p - 1) =
      s ^ p + t ^ p - n ^ p := by
    rw [mul_sub, mul_add, mul_one, es, et]
  rw [er] at hpow
  have el : n ^ p * (gapConstant p * x) = gapConstant p * s * n ^ (p - 1) := by
    calc
      _ = gapConstant p * (n ^ p * x) := by ring
      _ = _ := by rw [ex]; ring
  rw [el] at hpow
  exact hpow

/-- The manuscript's concavity estimate, with a symmetric minimum. -/
theorem power_gap {p s t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hs : 0 < s) (ht : 0 < t) :
    gapConstant p * min s t * (s + t) ^ (p - 1) ≤
      s ^ p + t ^ p - (s + t) ^ p := by
  rcases le_total s t with h | h
  · simpa only [min_eq_left h] using power_gap_of_le hp0 hp1 hs ht h
  · simpa only [min_eq_right h, add_comm, mul_comm, mul_left_comm] using
      power_gap_of_le hp0 hp1 ht hs h

/-- This exact package has a proved concrete instance below, not an
untranslated analytic input. -/
structure CutParameters where
  p : ℝ
  B : ℝ
  epsilon : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  B_pos : 0 < B
  B_lt_one : B < 1
  epsilon_pos : 0 < epsilon
  epsilon_le_B : epsilon ≤ B
  pays_split : 2 * epsilon ≤ B * gapConstant p

/-- Same parameters as the source: a=1/8, B=1/16, epsilon=c_a/32. -/
def canonicalParameters : CutParameters where
  p := 7 / 8
  B := 1 / 16
  epsilon := gapConstant (7 / 8) / 32
  p_pos := by norm_num
  p_lt_one := by norm_num
  B_pos := by norm_num
  B_lt_one := by norm_num
  epsilon_pos := div_pos (gapConstant_pos (by norm_num)) (by norm_num)
  epsilon_le_B := by
    have h := gapConstant_le_two (p := (7 / 8 : ℝ)) (by norm_num)
    linarith
  pays_split := by
    change 2 * (gapConstant (7 / 8) / 32) ≤ (1 / 16) * gapConstant (7 / 8)
    exact le_of_eq (by ring)

end Erdos1016.SafeCore
