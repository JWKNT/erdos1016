import Mathlib.Tactic

set_option autoImplicit false

/-!
# The numbers of Horak and Kim

For a rank `r ≥ 3` put

* `H(2q+1) = 2^(2q) + (2q + 1/2) 2^q - 3q`,
* `H(2q+2) = 2^(2q+1) + (2q + 9/2) 2^q - 3q - 4`.

Horak and Kim found cubic graphs of rank `r` with `H(r)` cycles. This file defines `H` as a
function on the natural numbers and proves the arithmetic facts that the proof of the exact
maximum needs. The definition is meant for `r ≥ 3`; its values at `r ≤ 2` have no meaning.

The file is part of the formalisation of the paper
"The maximum number of cycles in a graph of large rank" (`paper/minimal/exact-maximum`).
-/

namespace Erdos1016.ExactMaximum

/-- The number `H(r)` of Horak and Kim. For odd `r = 2q+1` it is
`2^(r-1) + (4q+1) 2^(q-1) - 3q`, and for even `r = 2q+2` it is
`2^(r-1) + (4q+9) 2^(q-1) - 3q - 4`. -/
def horakKim (r : ℕ) : ℕ :=
  if r % 2 = 1 then
    2 ^ (r - 1) + (2 * r - 1) * 2 ^ ((r - 1) / 2 - 1) - 3 * ((r - 1) / 2)
  else
    2 ^ (r - 1) + (2 * r + 5) * 2 ^ ((r - 2) / 2 - 1) - 3 * ((r - 2) / 2) - 4

/-! ### Values that the paper states -/

example : horakKim 3 = 6 := by decide
example : horakKim 4 = 14 := by decide
example : horakKim 8 = 199 := by decide
example : horakKim 9 = 380 := by decide
example : horakKim 10 = 696 := by decide
example : horakKim 13 = 4878 := by decide
example : horakKim 27 = 67325913 := by norm_num [horakKim]

/-! ### Forms without subtraction -/

/-- For `q ≥ 1`, a power of two is at least its exponent plus one, in this shifted form. -/
theorem le_two_pow_pred (q : ℕ) (hq : 1 ≤ q) : q ≤ 2 ^ (q - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.lt_two_pow_self

/-- The odd case without subtraction. -/
theorem horakKim_odd (q : ℕ) (hq : 1 ≤ q) :
    horakKim (2 * q + 1) + 3 * q = 2 ^ (2 * q) + (4 * q + 1) * 2 ^ (q - 1) := by
  have h1 : (2 * q + 1) % 2 = 1 := by omega
  have h2 : (2 * q + 1 - 1) / 2 = q := by omega
  have h3 : 2 * q + 1 - 1 = 2 * q := by omega
  have h4 : 2 * (2 * q + 1) - 1 = 4 * q + 1 := by omega
  have hle : 3 * q ≤ 2 ^ (2 * q) + (4 * q + 1) * 2 ^ (q - 1) := by
    have := le_two_pow_pred q hq
    nlinarith [Nat.zero_le (2 ^ (2 * q)), Nat.one_le_two_pow (n := q - 1)]
  unfold horakKim
  rw [if_pos h1, h2, h3, h4]
  omega

/-- The even case without subtraction. -/
theorem horakKim_even (q : ℕ) (hq : 1 ≤ q) :
    horakKim (2 * q + 2) + 3 * q + 4 = 2 ^ (2 * q + 1) + (4 * q + 9) * 2 ^ (q - 1) := by
  have h1 : ¬ (2 * q + 2) % 2 = 1 := by omega
  have h2 : (2 * q + 2 - 2) / 2 = q := by omega
  have h3 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
  have h4 : 2 * (2 * q + 2) + 5 = 4 * q + 9 := by omega
  have hle : 3 * q + 4 ≤ 2 ^ (2 * q + 1) + (4 * q + 9) * 2 ^ (q - 1) := by
    have := le_two_pow_pred q hq
    nlinarith [Nat.zero_le (2 ^ (2 * q + 1)), Nat.one_le_two_pow (n := q - 1)]
  unfold horakKim
  rw [if_neg h1, h2, h3, h4]
  omega

/-! ### Lower bounds -/

/-- `H(r) ≥ 2^(r-1)` for `r ≥ 3`. -/
theorem two_pow_le_horakKim (r : ℕ) (hr : 3 ≤ r) : 2 ^ (r - 1) ≤ horakKim r := by
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- r = 2k = 2(k-1)+2
    obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hr' : r = 2 * q + 2 := by omega
    subst hr'
    have h := horakKim_even q hq
    have h3 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
    rw [h3]
    have := le_two_pow_pred q hq
    have hpos := Nat.one_le_two_pow (n := q - 1)
    nlinarith
  · have hq : 1 ≤ k := by omega
    subst hk
    have h := horakKim_odd k hq
    have h3 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [h3]
    have := le_two_pow_pred k hq
    have hpos := Nat.one_le_two_pow (n := k - 1)
    nlinarith

/-- The second term of `H(r)` beats every multiple of `2^(r/2)`: for every `K` and every
`r ≥ 2K + 6`, `2^(r-1) + K * 2^((r+1)/2) < H(r)`. This is the form of the inequality
`H(r) ≥ 2^(r-1) + (r-2) 2^(r/2-1)` that the last step of the proof uses. -/
theorem add_mul_two_pow_lt_horakKim (K r : ℕ) (hr : 2 * K + 6 ≤ r) :
    2 ^ (r - 1) + K * 2 ^ ((r + 1) / 2) < horakKim r := by
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hr' : r = 2 * q + 2 := by omega
    subst hr'
    have h := horakKim_even q hq
    have h3 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
    have h5 : (2 * q + 2 + 1) / 2 = (q - 1) + 2 := by omega
    have e1 : 2 ^ (q - 1 + 2) = 4 * 2 ^ (q - 1) := by rw [pow_add]; ring
    rw [h3, h5, e1]
    have hpow := le_two_pow_pred q hq
    have h6 : 4 * (K + 2) * 2 ^ (q - 1) ≤ 4 * q * 2 ^ (q - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize 2 ^ (q - 1) = P at *
    generalize 2 ^ (2 * q + 1) = A at *
    nlinarith
  · have hq : 1 ≤ k := by omega
    subst hk
    have h := horakKim_odd k hq
    have h3 : 2 * k + 1 - 1 = 2 * k := by omega
    have h5 : (2 * k + 1 + 1) / 2 = (k - 1) + 2 := by omega
    have e1 : 2 ^ (k - 1 + 2) = 4 * 2 ^ (k - 1) := by rw [pow_add]; ring
    rw [h3, h5, e1]
    have hpow := le_two_pow_pred k hq
    have h6 : 4 * (K + 3) * 2 ^ (k - 1) ≤ 4 * k * 2 ^ (k - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize 2 ^ (k - 1) = P at *
    generalize 2 ^ (2 * k) = A at *
    nlinarith

end Erdos1016.ExactMaximum
