import Mathlib.Tactic

set_option autoImplicit false

/-!
# Matching counts across two-vertex layers

The number of physical perfect matchings of a two-by-two interface is its
permanent `a*d+b*c`. Ordinariness excludes parallel labels at both vertices
of the relevant layer. These bounds use physical multiplicities, not simple
adjacency indicators, and follow by bounding a product with a factor at most one.
-/
namespace Erdos1016.ExactMaximumSupport.InterfaceMatchings

private theorem mul_le_right_of_le_one (a b : ℕ) (ha : a ≤ 1) : a*b ≤ b := by
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right b ha

private theorem mul_le_left_of_le_one (a b : ℕ) (hb : b ≤ 1) : a*b ≤ a := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb

/-- Row degree at most two and an ordinary first layer allow at most two
physical perfect matchings across the interface. -/
theorem matching_count_le_two (a b c d : ℕ)
    (hrow₁ : a+b ≤ 2) (hrow₂ : c+d ≤ 2)
    (hordinary : ¬ ((2 ≤ a ∨ 2 ≤ b) ∧ (2 ≤ c ∨ 2 ≤ d))) :
    a*d+b*c ≤ 2 := by
  rcases not_and_or.mp hordinary with hfirst | hsecond
  · have ha : a ≤ 1 := by omega
    have hb : b ≤ 1 := by omega
    have h₁ := mul_le_right_of_le_one a d ha
    have h₂ := mul_le_right_of_le_one b c hb
    omega
  · have hc : c ≤ 1 := by omega
    have hd : d ≤ 1 := by omega
    have h₁ := mul_le_left_of_le_one a d hd
    have h₂ := mul_le_left_of_le_one b c hc
    omega

/-- For two adjacent interfaces, an ordinary subcubic middle layer bounds
 the sum of their physical matching counts by three. -/
theorem adjacent_matching_sum_le_three (a b c d e f g h : ℕ)
    (hmid₁ : a+c+e+f ≤ 3) (hmid₂ : b+d+g+h ≤ 3)
    (hordinary : ¬ ((2 ≤ a ∨ 2 ≤ c ∨ 2 ≤ e ∨ 2 ≤ f) ∧
      (2 ≤ b ∨ 2 ≤ d ∨ 2 ≤ g ∨ 2 ≤ h))) :
    (a*d+b*c)+(e*h+f*g) ≤ 3 := by
  rcases not_and_or.mp hordinary with hfirst | hsecond
  · have ha : a ≤ 1 := by omega
    have hc : c ≤ 1 := by omega
    have he : e ≤ 1 := by omega
    have hf : f ≤ 1 := by omega
    have h₁ := mul_le_right_of_le_one a d ha
    have h₂ := mul_le_left_of_le_one b c hc
    have h₃ := mul_le_right_of_le_one e h he
    have h₄ := mul_le_right_of_le_one f g hf
    omega
  · have hb : b ≤ 1 := by omega
    have hd : d ≤ 1 := by omega
    have hg : g ≤ 1 := by omega
    have hh : h ≤ 1 := by omega
    have h₁ := mul_le_left_of_le_one a d hd
    have h₂ := mul_le_right_of_le_one b c hb
    have h₃ := mul_le_left_of_le_one e h hh
    have h₄ := mul_le_left_of_le_one f g hg
    omega

/-- At least one of the adjacent interfaces admits at most one physical
perfect matching when their common layer is ordinary and subcubic. -/
theorem adjacent_matching_count_le_one (a b c d e f g h : ℕ)
    (hmid₁ : a+c+e+f ≤ 3) (hmid₂ : b+d+g+h ≤ 3)
    (hordinary : ¬ ((2 ≤ a ∨ 2 ≤ c ∨ 2 ≤ e ∨ 2 ≤ f) ∧
      (2 ≤ b ∨ 2 ≤ d ∨ 2 ≤ g ∨ 2 ≤ h))) :
    (a*d+b*c ≤ 1) ∨ (e*h+f*g ≤ 1) := by
  have hs := adjacent_matching_sum_le_three a b c d e f g h hmid₁ hmid₂ hordinary
  omega

end Erdos1016.ExactMaximumSupport.InterfaceMatchings
