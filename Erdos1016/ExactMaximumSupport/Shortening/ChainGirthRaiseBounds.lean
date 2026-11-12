import Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence

set_option autoImplicit false

/-!
# The chain-packing girth-raising budget

The packing bound150*b^3*(s+1)*2^b gives the deletion multiplier151*b^4*2^b.
Its logarithmic loss still fits the previous coefficient6 once the initial
scale is at least9. The actual selected-region recurrence is retained.
-/
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainGirthRaiseBounds
open scoped BigOperators
open FiniteMultiGraph LargeGirth GirthRaiseBounds RegionPackingSequence

theorem four_le_clog (D j : ℕ) (hD : 9 ≤ D) :
    4 ≤ Nat.clog 2 (scale D j) := by
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hs : 2 ^ 3 < scale D j := by dsimp [scale]; nlinarith
  have h := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hs
  omega

/-- Each packing step costs at most this many binary exponent units. -/
theorem packing_multiplier_le (b : ℕ) :
    151 * b ^ 4 * 2 ^ b ≤ 2 ^ (b + 4 * Nat.clog 2 b + 8) := by
  have hb := Nat.le_pow_clog (by decide : 1 < 2) b
  have hb2 := Nat.pow_le_pow_left hb 4
  have hc : 151 ≤ 2 ^ 8 := by norm_num
  have hm := Nat.mul_le_mul_right (2 ^ b) (Nat.mul_le_mul hc hb2)
  calc
    151 * b ^ 4 * 2 ^ b ≤ 2 ^ 8 * (2 ^ Nat.clog 2 b) ^ 4 * 2 ^ b := hm
    _ = 2 ^ (b + 4 * Nat.clog 2 b + 8) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

/-- The cumulative logarithmic loss is quadratic in the final binary logarithm. -/
theorem sum_exponents_le (D j : ℕ) (hD : 9 ≤ D) :
    (∑ i ∈ Finset.range (j + 1),
      (scale D i + 4 * Nat.clog 2 (scale D i) + 8)) ≤
        2 * scale D j + 6 * (Nat.clog 2 (scale D j)) ^ 2 := by
  let L := Nat.clog 2 (scale D j)
  have hL : 4 ≤ L := four_le_clog D j hD
  have hj : j + 1 ≤ L := stages_le_clog D j (by omega)
  have hsum : (∑ i ∈ Finset.range (j + 1),
      (scale D i + 4 * Nat.clog 2 (scale D i) + 8)) ≤
      (∑ i ∈ Finset.range (j + 1), scale D i) + (j + 1) * (4 * L + 8) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (scale D i + (4 * L + 8)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
        have hc := Nat.clog_mono_right 2 (scale_mono D hij)
        dsimp [L]
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hsmall : (j + 1) * (4 * L + 8) ≤ 6 * L ^ 2 := by
    have hm := Nat.mul_le_mul_right (4 * L + 8) hj
    nlinarith
  exact hsum.trans (Nat.add_le_add (sum_scale_le D j) hsmall)

/-- The actual packing recurrence gives a uniform size bound at every stage.
`S 0` is the empty initial deletion set; `S (j+1)` follows scale `2^j D`. -/
theorem size_bound (D : ℕ) (hD : 9 ≤ D) (S : ℕ → ℕ) (hzero : S 0 = 0)
    (hstep : ∀ j, S (j + 1) + 1 ≤
      151 * (scale D j) ^ 4 * 2 ^ scale D j * (S j + 1)) (j : ℕ) :
    S (j + 1) + 1 ≤ 2 ^ (2 * scale D j + 6 * (Nat.clog 2 (scale D j)) ^ 2) := by
  have hrec := recurrence_le_pow_sum S
    (fun i => scale D i + 4 * Nat.clog 2 (scale D i) + 8) hzero
    (fun i => (hstep i).trans (Nat.mul_le_mul_right _ (packing_multiplier_le _))) (j + 1)
  exact hrec.trans (Nat.pow_le_pow_right (by decide) (sum_exponents_le D j hD))

/-- A single quantitative packing estimate gives the deletion-size recurrence. -/
theorem vertices_step_bound (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ)
    (n : ℕ) (hD : 1 ≤ D n)
    (hpack : (selected G (P ∪ vertices G P D n) (D n)).card ≤
      150 * (D n)^3 * ((vertices G P D n).card + 1) * 2 ^ D n) :
    (vertices G P D (n + 1)).card + 1 ≤
      151 * (D n) ^ 4 * 2 ^ D n * ((vertices G P D n).card + 1) := by
  have hc := vertices_step_card G P D n
  have hm := Nat.mul_le_mul_right (D n) hpack
  have ht : 1 ≤ (D n) ^ 4 * 2 ^ D n := by
    apply Nat.one_le_iff_ne_zero.mpr
    have hp : 0 < D n := by omega
    positivity
  have hs := Nat.mul_le_mul_right ((vertices G P D n).card + 1) ht
  nlinarith

/-- Conditional only on the explicit cardinality bound for each newly selected
family, the actual nested sets satisfy the dyadic deletion budget. -/
theorem vertices_size_bound (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ) (hD : 9 ≤ D)
    (hpack : ∀ n,
      (selected G (P ∪ vertices G P (GirthRaiseBounds.scale D) n)
        (GirthRaiseBounds.scale D n)).card ≤
      150 * (GirthRaiseBounds.scale D n)^3 *
        ((vertices G P (GirthRaiseBounds.scale D) n).card + 1) *
          2 ^ GirthRaiseBounds.scale D n) (j : ℕ) :
    (vertices G P (GirthRaiseBounds.scale D) (j + 1)).card + 1 ≤
      2 ^ (2 * GirthRaiseBounds.scale D j +
        6 * (Nat.clog 2 (GirthRaiseBounds.scale D j)) ^ 2) := by
  apply size_bound D hD
    (fun n => (vertices G P (GirthRaiseBounds.scale D) n).card) (by simp)
  intro n
  apply vertices_step_bound G P (GirthRaiseBounds.scale D) n ?_ (hpack n)
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  dsimp [GirthRaiseBounds.scale]
  nlinarith


end Erdos1016.ExactMaximumSupport.Shortening.ChainGirthRaiseBounds
