import Erdos1016.ExactMaximum.HorakKim

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Arithmetic for the ring upper bound

The doubled excess uses integers, so subtraction never truncates.
The graph-theoretic count remains an explicit premise of the final adapters.
-/

namespace Erdos1016.ExactMaximumSupport.RingUpperArithmetic
open ExactMaximum

/-- Twice the excess from the ring count with `a` squares and `s` single rungs. -/
def doubledExcess (a s : ℕ) : ℤ :=
  (2 : ℤ)^a * (4*(a : ℤ) + 8*(s : ℤ) + (s : ℤ)*((s : ℤ)-1) + 1) -
    6*(a : ℤ) - 8*(s : ℤ) + (s : ℤ)*((s : ℤ)-1)

/-- The exact change when one square becomes two single rungs. -/
theorem replacement_identity (a s : ℕ) :
    doubledExcess a (s+2) - doubledExcess (a+1) s =
      -(2 : ℤ)^a * (4*(a : ℤ) + (s : ℤ)^2 + 3*(s : ℤ) - 9) + 4*(s : ℤ)-8 := by
  simp only [doubledExcess, Nat.cast_add, Nat.cast_ofNat, pow_succ]
  ring

/-- At weight at least seven, replacing a square strictly lowers the upper bound. -/
theorem replacement_lt (a s : ℕ) (ha : 2 ≤ a) (hW : 7 ≤ 2*a+s) :
    doubledExcess (a-1) (s+2) < doubledExcess a s := by
  have h := replacement_identity (a-1) s
  have he : a-1+1=a := by omega
  have hc : ((a-1 : ℕ) : ℤ) = (a : ℤ)-1 := by omega
  rw [he,hc] at h
  have hpow : (2 : ℤ) ≤ 2^(a-1) := by
    calc
      (2 : ℤ) = 2^1 := by norm_num
      _ ≤ 2^(a-1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hW' : (7 : ℤ) ≤ 2*(a : ℤ)+(s : ℤ) := by exact_mod_cast hW
  have hs : (0 : ℤ) ≤ (s : ℤ)*((s : ℤ)-1) := by
    by_cases hz : s=0
    · simp [hz]
    · have hp : (1 : ℤ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      exact mul_nonneg (Int.natCast_nonneg s) (by omega)
  have hcoef : (0 : ℤ) ≤ 4*((a : ℤ)-1)+(s : ℤ)^2+3*(s : ℤ)-9 := by
    nlinarith [Int.natCast_nonneg s]
  have hmul := mul_le_mul_of_nonneg_right hpow hcoef
  nlinarith

/-- Among rings with a square and fixed weight, the parity representative maximizes the excess. -/
theorem excess_le_parity (a s : ℕ) (ha : 1 ≤ a) (hW : 7 ≤ 2*a+s) :
    doubledExcess a s ≤ doubledExcess ((2*a+s)/2) ((2*a+s)%2) := by
  have hall : ∀ s a : ℕ, 1 ≤ a → 7 ≤ 2*a+s →
      doubledExcess a s ≤ doubledExcess ((2*a+s)/2) ((2*a+s)%2) := by
    intro s
    induction s using Nat.twoStepInduction with
    | zero =>
        intro a ha hW
        have hd : (2*a+0)/2=a := by omega
        have hm : (2*a+0)%2=0 := by omega
        rw [hd,hm]
    | one =>
        intro a ha hW
        have hd : (2*a+1)/2=a := by omega
        have hm : (2*a+1)%2=1 := by omega
        rw [hd,hm]
    | more s ih _ =>
        intro a ha hW
        have hr := replacement_lt (a+1) s (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hr
        have hh := ih (a+1) (by omega) (by omega)
        have he : 2*(a+1)+s=2*a+(s+2) := by omega
        rw [he] at hh
        exact (le_of_lt hr).trans hh
  exact hall s a ha hW

/-- The maximal parity excess is exactly the Horak--Kim excess, without natural subtraction. -/
theorem parity_horakKim (W : ℕ) (hW : 7 ≤ W) :
    2*(horakKim (W+1) : ℤ) = (2 : ℤ)^(W+1)+doubledExcess (W/2) (W%2) := by
  rcases Nat.even_or_odd W with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hq : 1 ≤ k := by omega
    have he : W=2*k := by omega
    rw [he]
    have hH : (horakKim (2*k+1) : ℤ)+3*(k : ℤ) =
        (2 : ℤ)^(2*k)+(4*(k : ℤ)+1)*2^(k-1) := by
      exact_mod_cast horakKim_odd k hq
    have hp : (2 : ℤ)^k=2*2^(k-1) := by
      have he : k=k-1+1 := by omega
      conv_lhs => rw [he]
      rw [pow_succ]
      ring
    have hd : (2*k)/2=k := by omega
    have hm : (2*k)%2=0 := by omega
    rw [hd,hm]
    simp only [doubledExcess, Nat.cast_zero, mul_zero, add_zero, sub_zero, pow_succ]
    rw [hp]
    nlinarith
  · have hq : 1 ≤ k := by omega
    have he : W=2*k+1 := by omega
    rw [he]
    have hH : (horakKim (2*k+2) : ℤ)+3*(k : ℤ)+4 =
        (2 : ℤ)^(2*k+1)+(4*(k : ℤ)+9)*2^(k-1) := by
      exact_mod_cast horakKim_even k hq
    have hp : (2 : ℤ)^k=2*2^(k-1) := by
      have he : k=k-1+1 := by omega
      conv_lhs => rw [he]
      rw [pow_succ]
      ring
    have hd : (2*k+1)/2=k := by omega
    have hm : (2*k+1)%2=1 := by omega
    rw [hd,hm]
    have he : 2*k+1+1=2*k+2 := by omega
    rw [he]
    simp only [doubledExcess, Nat.cast_one, sub_self, mul_zero, add_zero]
    have hp2 : (2 : ℤ)^(2*k+2)=2*2^(2*k+1) := by ring
    rw [hp,hp2]
    nlinarith

/-- The ring sector upper bound implies the Horak--Kim bound. -/
theorem cycle_bound_of_doubled (c a s : ℕ) (ha : 1 ≤ a) (hW : 7 ≤ 2*a+s)
    (hc : 2*(c : ℤ) ≤ (2 : ℤ)^(2*a+s+1)+doubledExcess a s) :
    c ≤ horakKim (2*a+s+1) := by
  have hopt := excess_le_parity a s ha hW
  have hH := parity_horakKim (2*a+s) hW
  have hh : (c : ℤ) ≤ (horakKim (2*a+s+1) : ℤ) := by omega
  exact_mod_cast hh

/-- Adding one square more than doubles either parity excess. -/
theorem excess_succ_gt_twice (a s : ℕ) (ha : 1 ≤ a) (hs : s ≤ 1) :
    2*doubledExcess a s < doubledExcess (a+1) s := by
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hp : (0 : ℤ) < 2^a := by positivity
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with rfl | rfl <;>
    simp only [doubledExcess, Nat.cast_add, Nat.cast_zero, Nat.cast_one, mul_zero,
      add_zero, sub_zero, sub_self, pow_succ] <;> nlinarith

/-- The parity excess strictly exceeds the all-singleton quadratic bound. -/
theorem double_square_lt_parity (W : ℕ) (hW : 7 ≤ W) :
    2*(W : ℤ)^2 < doubledExcess (W/2) (W%2) := by
  have hall : ∀ n : ℕ, 2*((n+7 : ℕ) : ℤ)^2 <
      doubledExcess ((n+7)/2) ((n+7)%2) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => norm_num [doubledExcess]
    | one => norm_num [doubledExcess]
    | more n ih _ =>
        have hd : (n+2+7)/2=(n+7)/2+1 := by omega
        have hm : (n+2+7)%2=(n+7)%2 := by omega
        rw [hd,hm]
        have hh := excess_succ_gt_twice ((n+7)/2) ((n+7)%2) (by omega) (by omega)
        push_cast at ih ⊢
        have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
        nlinarith
  obtain ⟨n,rfl⟩ : ∃ n, W=n+7 := ⟨W-7,by omega⟩
  exact hall n

/-- A ring without squares is strictly below the Horak--Kim number. -/
theorem singleton_cycle_bound (c W : ℕ) (hW : 7 ≤ W) (hc : c ≤ 2^W+W^2) :
    c < horakKim (W+1) := by
  have hD := double_square_lt_parity W hW
  have hH := parity_horakKim W hW
  have hc' : (c : ℤ) ≤ (2 : ℤ)^W+(W : ℤ)^2 := by exact_mod_cast hc
  rw [pow_succ] at hH
  have hh : (c : ℤ) < (horakKim (W+1) : ℤ) := by nlinarith
  exact_mod_cast hh

end Erdos1016.ExactMaximumSupport.RingUpperArithmetic
