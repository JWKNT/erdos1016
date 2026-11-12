import Erdos1016.ExactMaximumSupport.MixedTileMatchings

set_option autoImplicit false

/-!
# Finite products of two-rail permutations

The order follows traversal through the tiles: the new tile acts on the left.
Cancellation recovers one factor when every other factor is fixed.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles

/-- The rail transport through the first `n` tiles. -/
def railPrefix (f : ℕ → Equiv.Perm Bool) : ℕ → Equiv.Perm Bool
  | 0 => 1
  | n+1 => f n*railPrefix f n

@[simp] theorem railPrefix_zero (f : ℕ → Equiv.Perm Bool) : railPrefix f 0=1 := rfl
@[simp] theorem railPrefix_succ (f : ℕ → Equiv.Perm Bool) (n : ℕ) :
    railPrefix f (n+1)=f n*railPrefix f n := rfl

/-- Only factors before the endpoint enter the prefix. -/
theorem railPrefix_congr (f g : ℕ → Equiv.Perm Bool) (n : ℕ)
    (h : ∀ i,i<n → f i=g i) : railPrefix f n=railPrefix g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [railPrefix_succ,railPrefix_succ,h n (by omega),ih (fun i hi => h i (by omega))]

/-- One missing rail factor is determined by the total product and all other factors. -/
theorem railPrefix_cancel_one (f g : ℕ → Equiv.Perm Bool) (n i : ℕ) (hi : i<n)
    (hother : ∀ j,j<n → j≠i → f j=g j)
    (hprod : railPrefix f n=railPrefix g n) : f i=g i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases hin : i=n
    · subst i
      have hp := railPrefix_congr f g n (fun j hj => hother j (by omega) (by omega))
      rw [railPrefix_succ,railPrefix_succ,hp] at hprod
      exact mul_right_cancel hprod
    · have hlast := hother n (by omega) (by omega)
      rw [railPrefix_succ,railPrefix_succ,hlast] at hprod
      exact ih i (by omega) (fun j hj hji => hother j (by omega) hji)
        (mul_left_cancel hprod)

/-- The only nonidentity permutation of two rails exchanges them. -/
theorem bool_perm_apply_of_ne_one (p : Equiv.Perm Bool) (hp : p≠1) (b : Bool) : p b=!b := by
  have hf : p false=true := by
    cases h : p false
    · have ht : p true=true := by
        cases ht : p true
        · have he := p.injective (ht.trans h.symm)
          cases he
        · rfl
      apply False.elim
      apply hp
      ext b
      cases b
      · exact h
      · exact ht
    · rfl
  have ht : p true=false := by
    cases h : p true
    · rfl
    · have he := p.injective (h.trans hf.symm)
      cases he
  cases b
  · exact hf
  · exact ht

/-- Two nonidentity two-rail permutations are equal. -/
theorem bool_perm_eq_of_ne_one (p q : Equiv.Perm Bool) (hp : p≠1) (hq : q≠1) : p=q := by
  ext b
  exact (bool_perm_apply_of_ne_one p hp b).trans (bool_perm_apply_of_ne_one q hq b).symm

end Erdos1016.ExactMaximumSupport.MixedTiles
