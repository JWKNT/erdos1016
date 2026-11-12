import Erdos1016.ExactMaximumSupport.LargeGirth.MooreGrowth

set_option autoImplicit false

/-!
# The size recurrence for raising the girth

This is the numerical step of the dyadic construction. The input is the
explicit recurrence supplied by the packing bound. The graph packing theorem
and the nested deleted sets are not assumed to have been proved here.
-/

namespace Erdos1016.ExactMaximumSupport.LargeGirth.GirthRaiseBounds

open scoped BigOperators

def scale (D j : ℕ) : ℕ := 2 ^ j * D

theorem scale_mono (D : ℕ) : Monotone (scale D) := by
  intro i j hij
  exact Nat.mul_le_mul_right D (Nat.pow_le_pow_right (by decide) hij)

theorem sum_scale_le (D j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), scale D i ≤ 2 * scale D j := by
  induction j with
  | zero => simp [scale]; omega
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hs : scale D (j + 1) = 2 * scale D j := by
      simp only [scale, pow_succ]
      ring
    rw [hs]
    omega

theorem stages_le_clog (D j : ℕ) (hD : 2 ≤ D) :
    j + 1 ≤ Nat.clog 2 (scale D j) := by
  have hp : 0 < 2 ^ j := by positivity
  have hs : 2 ^ j < scale D j := by dsimp [scale]; nlinarith
  have h := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hs
  omega

theorem three_le_clog (D j : ℕ) (hD : 7 ≤ D) :
    3 ≤ Nat.clog 2 (scale D j) := by
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hs : 2 ^ 2 < scale D j := by dsimp [scale]; nlinarith
  have h := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hs
  omega

/-- Each packing step costs at most this many binary exponent units. -/
theorem packing_multiplier_le (b : ℕ) :
    1552 * b ^ 2 * 2 ^ b ≤ 2 ^ (b + 2 * Nat.clog 2 b + 11) := by
  have hb := Nat.le_pow_clog (by decide : 1 < 2) b
  have hb2 := Nat.pow_le_pow_left hb 2
  have hc : 1552 ≤ 2 ^ 11 := by norm_num
  have hm := Nat.mul_le_mul_right (2 ^ b) (Nat.mul_le_mul hc hb2)
  calc
    1552 * b ^ 2 * 2 ^ b ≤ 2 ^ 11 * (2 ^ Nat.clog 2 b) ^ 2 * 2 ^ b := hm
    _ = 2 ^ (b + 2 * Nat.clog 2 b + 11) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

/-- Iterating multiplicative size estimates adds their binary exponents. -/
theorem recurrence_le_pow_sum (S a : ℕ → ℕ) (hzero : S 0 = 0)
    (hstep : ∀ j, S (j + 1) + 1 ≤ 2 ^ a j * (S j + 1)) (n : ℕ) :
    S n + 1 ≤ 2 ^ (∑ i ∈ Finset.range n, a i) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    calc
      S (n + 1) + 1 ≤ 2 ^ a n * (S n + 1) := hstep n
      _ ≤ 2 ^ a n * 2 ^ (∑ i ∈ Finset.range n, a i) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (∑ i ∈ Finset.range (n + 1), a i) := by
        rw [← pow_add, Finset.sum_range_succ, Nat.add_comm]

/-- The cumulative logarithmic loss is quadratic in the final binary logarithm. -/
theorem sum_exponents_le (D j : ℕ) (hD : 7 ≤ D) :
    (∑ i ∈ Finset.range (j + 1),
      (scale D i + 2 * Nat.clog 2 (scale D i) + 11)) ≤
        2 * scale D j + 6 * (Nat.clog 2 (scale D j)) ^ 2 := by
  let L := Nat.clog 2 (scale D j)
  have hL : 3 ≤ L := three_le_clog D j hD
  have hj : j + 1 ≤ L := stages_le_clog D j (by omega)
  have hsum : (∑ i ∈ Finset.range (j + 1),
      (scale D i + 2 * Nat.clog 2 (scale D i) + 11)) ≤
      (∑ i ∈ Finset.range (j + 1), scale D i) + (j + 1) * (2 * L + 11) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (scale D i + (2 * L + 11)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
        have hc := Nat.clog_mono_right 2 (scale_mono D hij)
        dsimp [L]
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hsmall : (j + 1) * (2 * L + 11) ≤ 6 * L ^ 2 := by
    have hm := Nat.mul_le_mul_right (2 * L + 11) hj
    nlinarith
  exact hsum.trans (Nat.add_le_add (sum_scale_le D j) hsmall)

/-- The actual packing recurrence gives a uniform size bound at every stage.
`S 0` is the empty initial deletion set; `S (j+1)` follows scale `2^j D`. -/
theorem size_bound (D : ℕ) (hD : 7 ≤ D) (S : ℕ → ℕ) (hzero : S 0 = 0)
    (hstep : ∀ j, S (j + 1) + 1 ≤
      1552 * (scale D j) ^ 2 * 2 ^ scale D j * (S j + 1)) (j : ℕ) :
    S (j + 1) + 1 ≤ 2 ^ (2 * scale D j + 6 * (Nat.clog 2 (scale D j)) ^ 2) := by
  have hrec := recurrence_le_pow_sum S
    (fun i => scale D i + 2 * Nat.clog 2 (scale D i) + 11) hzero
    (fun i => (hstep i).trans (Nat.mul_le_mul_right _ (packing_multiplier_le _))) (j + 1)
  exact hrec.trans (Nat.pow_le_pow_right (by decide) (sum_exponents_le D j hD))

end Erdos1016.ExactMaximumSupport.LargeGirth.GirthRaiseBounds
