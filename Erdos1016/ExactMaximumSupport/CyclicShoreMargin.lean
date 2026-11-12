import Mathlib.Tactic

set_option autoImplicit false

/-!
# The rational path-density margin for cyclic shores

The natural-number inequality implies a strict half bound.
Its margin survives either factor of an exact bridge path product.
-/
namespace Erdos1016.ExactMaximumSupport.CyclicShoreMargin

/-- The stated margin is strictly above one half. -/
theorem strict_half (m r P : ℕ)
    (h : (2^m+2)*2^r≤2^(m+1)*P) : 2^r<2*P := by
  have hp : 0<2^m := Nat.two_pow_pos _
  have hr : 0<2^r := Nat.two_pow_pos _
  rw [pow_succ] at h
  nlinarith

/-- The integer margin is the real margin used by the layer theorem. -/
theorem real_margin (m r P : ℕ)
    (h : (2^m+2)*2^r≤2^(m+1)*P) :
    (1/2+1/(2:ℝ)^m)*(2:ℝ)^r≤P := by
  have hp : 0<(2:ℝ)^m := by positivity
  have hh : ((2:ℝ)^m+2)*(2:ℝ)^r≤(2:ℝ)^(m+1)*P := by exact_mod_cast h
  rw [pow_succ] at hh
  have he : (1/2+1/(2:ℝ)^m)=((2:ℝ)^m+2)/((2:ℝ)^m*2) := by
    field_simp
    left
    ring
  rw [he,div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos hp (by norm_num))).mpr
  nlinarith

/-- Either bridge factor retains the original integer margin. -/
theorem left_factor (m a b P Q : ℕ) (hQ : Q≤2^b)
    (h : (2^m+2)*2^(a+b)≤2^(m+1)*(P*Q)) :
    (2^m+2)*2^a≤2^(m+1)*P := by
  apply (mul_le_mul_right (Nat.two_pow_pos b)).mp
  calc
    ((2^m+2)*2^a)*2^b = (2^m+2)*2^(a+b) := by rw [pow_add]; ring
    _ ≤ 2^(m+1)*(P*Q) := h
    _ ≤ (2^(m+1)*P)*2^b := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2^(m+1)*P) hQ

/-- The other bridge factor has the same bound. -/
theorem right_factor (m a b P Q : ℕ) (hP : P≤2^a)
    (h : (2^m+2)*2^(a+b)≤2^(m+1)*(P*Q)) :
    (2^m+2)*2^b≤2^(m+1)*Q := by
  apply left_factor m b a Q P hP
  simpa only [Nat.add_comm,Nat.mul_comm] using h

end Erdos1016.ExactMaximumSupport.CyclicShoreMargin
