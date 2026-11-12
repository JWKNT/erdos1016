import Mathlib.Tactic

set_option autoImplicit false

/-!
# Arithmetic for the third-port and gap arguments

The path-count formulas are explicit inputs here.
These lemmas do not assert the physical ladder decomposition or its counts.
-/
namespace Erdos1016.ExactMaximumSupport.ThirdPortArithmetic

/-- An interface with positive preceding weight loses at least one quarter. -/
theorem interface_quarter (p q A : ℕ) (hp : 1 ≤ p) (hA : A ≤ 2^p) :
    4*((1+A)*2^q) ≤ 3*2^(p+q+1) := by
  have hpow : 2 ≤ 2^p := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^p := Nat.pow_le_pow_right (by decide) hp
  have hh : 4*(1+A) ≤ 6*2^p := by omega
  have hm := Nat.mul_le_mul_right (2^q) hh
  simp only [pow_add, pow_one]
  nlinarith

/-- An interface gives a full pair or the required seven-eighths bound. -/
theorem interface_gap (p q A : ℕ) (hA : A ≤ 2^p) :
    (1+A)*2^q = 2^(p+q+1) ∨ 8*((1+A)*2^q) ≤ 7*2^(p+q+1) := by
  by_cases hp : p = 0
  · subst p
    have hA' : A = 0 ∨ A = 1 := by norm_num at hA; omega
    rcases hA' with rfl | rfl
    · right
      simp only [zero_add, add_zero, one_mul, pow_add, pow_one]
      omega
    · left
      simp only [zero_add, Nat.reduceAdd, pow_add, pow_one]
      omega
  · have hh := interface_quarter p q A (by omega) hA
    right
    omega

/-- Subdividing a single rung doubles the interface count and its capacity. -/
theorem rung_gap (p q A : ℕ) (hA : A ≤ 2^p) :
    2*(1+A)*2^q = 2^(p+q+2) ∨ 8*(2*(1+A)*2^q) ≤ 7*2^(p+q+2) := by
  have he : 2^(p+q+2) = 2*2^(p+q+1) := by
    have hs : p+q+2 = (p+q+1)+1 := by omega
    rw [hs,pow_succ]
    omega
  rcases interface_gap p q A hA with h | h
  · left
    rw [he,← h]
    ring
  · right
    rw [he]
    nlinarith

/-- A subdivided square always loses at least one eighth. -/
theorem square_eighth (p q A : ℕ) (hA : A ≤ 2^p) :
    8*((4+3*A)*2^q) ≤ 7*2^(p+q+3) := by
  have hpow : 1 ≤ 2^p := Nat.one_le_two_pow
  have hh : 8*(4+3*A) ≤ 56*2^p := by omega
  have hm := Nat.mul_le_mul_right (2^q) hh
  simp only [pow_add] at ⊢
  norm_num
  nlinarith

/-- Positive weight before a square strengthens its bound to five eighths. -/
theorem square_five_eighths (p q A : ℕ) (hp : 1 ≤ p) (hA : A ≤ 2^p) :
    8*((4+3*A)*2^q) ≤ 5*2^(p+q+3) := by
  have hpow : 2 ≤ 2^p := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^p := Nat.pow_le_pow_right (by decide) hp
  have hh : 8*(4+3*A) ≤ 40*2^p := by omega
  have hm := Nat.mul_le_mul_right (2^q) hh
  simp only [pow_add] at ⊢
  norm_num
  nlinarith

/-- The two smaller-pole counts give the gap after deleting the first port. -/
theorem sum_gap (x y B : ℕ)
    (hx : x = B ∨ 16*x ≤ 15*B) (hy : y = B ∨ 16*y ≤ 15*B)
    (hxy : x = B → y = B ∨ 8*y ≤ 7*B)
    (hyx : y = B → x = B ∨ 8*x ≤ 7*B) :
    x+y = 2*B ∨ 16*(x+y) ≤ 15*(2*B) := by
  rcases hx with hx | hx
  · rcases hxy hx with hy | hy
    · left; omega
    · right; omega
  · rcases hy with hy | hy
    · rcases hyx hy with hx | hx
      · left; omega
      · right; omega
    · right; omega

/-- The adjacent-port path estimate gives a quarter loss above rank one. -/
theorem adjacent_port_quarter (p P : ℕ) (hp : 1 ≤ p) (hP : P ≤ 1+2^p) :
    4*P ≤ 3*2^(p+1) := by
  have hpow : 2 ≤ 2^p := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^p := Nat.pow_le_pow_right (by decide) hp
  rw [pow_succ]
  omega

end Erdos1016.ExactMaximumSupport.ThirdPortArithmetic
