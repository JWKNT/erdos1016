import Mathlib

set_option autoImplicit false

/-!
# Finite binary forest-descent bookkeeping

This module isolates the finite-tree argument from the graph construction.
Each split has potential and exterior data; the local hypotheses encode the
potential, exterior, and one-retained-child inequalities used in §9.
-/

namespace Erdos1016.Proof.ForestDescentTree



inductive SplitTree where
  | leaf (potential : ℤ) (exterior : ℕ)
  | fork (potential : ℤ) (exterior : ℕ) (left right : SplitTree)
  deriving DecidableEq

def potential : SplitTree → ℤ
  | .leaf p _ => p
  | .fork p _ _ _ => p

def exterior : SplitTree → ℕ
  | .leaf _ c => c
  | .fork _ c _ _ => c

def hasNegativeLeaf : SplitTree → Bool
  | .leaf p _ => decide (p < 0)
  | .fork _ _ l r => hasNegativeLeaf l || hasNegativeLeaf r

def negativeCredit : SplitTree → ℤ
  | .leaf p c => if p < 0 then (c : ℤ) - 2 else 0
  | .fork _ _ l r => negativeCredit l + negativeCredit r

/-- The local split facts: potential is subadditive, exterior counts have
total at most parent plus two, and an only-retained child cannot increase
the exterior count. -/
def LocallyValid : SplitTree → Prop
  | .leaf _ _ => True
  | .fork p c l r =>
      LocallyValid l ∧ LocallyValid r ∧
      potential l + potential r ≤ p ∧
      exterior l + exterior r ≤ c + 2 ∧
      ((hasNegativeLeaf l = true ∧ hasNegativeLeaf r = false) → exterior l ≤ c) ∧
      ((hasNegativeLeaf l = false ∧ hasNegativeLeaf r = true) → exterior r ≤ c)



theorem negativeCredit_eq_zero_of_noNegative (t : SplitTree)
    (h : hasNegativeLeaf t = false) : negativeCredit t = 0 := by
  induction t with
  | leaf p c =>
      simp [hasNegativeLeaf, negativeCredit] at h ⊢
      omega
  | fork p c l r ihl ihr =>
      simp only [hasNegativeLeaf] at h
      have hl : hasNegativeLeaf l = false := by
        cases hx : hasNegativeLeaf l <;> simp_all
      have hr : hasNegativeLeaf r = false := by
        cases hx : hasNegativeLeaf r <;> simp_all
      simp [negativeCredit, ihl hl, ihr hr]

/-- The sum of `c-2` over negative-potential leaves is bounded by the root
credit. Credit may be negative for exterior count one; no positivity is used. -/
theorem negative_credit_le_root (t : SplitTree)
    (hvalid : LocallyValid t) (hnegative : hasNegativeLeaf t = true) :
    negativeCredit t ≤ (exterior t : ℤ) - 2 := by
  induction t with
  | leaf p c =>
      have hp : p < 0 := by simpa [hasNegativeLeaf] using hnegative
      simp [negativeCredit, exterior, hp]
  | fork p c l r ihl ihr =>
      rcases hvalid with ⟨hl, hr, _, hExterior, hLeftOnly, hRightOnly⟩
      simp only [hasNegativeLeaf] at hnegative
      cases hleft : hasNegativeLeaf l <;> cases hright : hasNegativeLeaf r
      · simp [hleft, hright] at hnegative
      · have hR := ihr hr hright
        have hMon := hRightOnly ⟨hleft, hright⟩
        change negativeCredit l + negativeCredit r ≤ (c : ℤ) - 2
        rw [negativeCredit_eq_zero_of_noNegative l hleft, zero_add]
        have hMonZ : (exterior r : ℤ) ≤ c := by exact_mod_cast hMon
        omega
      · have hL := ihl hl hleft
        have hMon := hLeftOnly ⟨hleft, hright⟩
        change negativeCredit l + negativeCredit r ≤ (c : ℤ) - 2
        rw [negativeCredit_eq_zero_of_noNegative r hright, add_zero]
        have hMonZ : (exterior l : ℤ) ≤ c := by exact_mod_cast hMon
        omega
      · have hL := ihl hl hleft
        have hR := ihr hr hright
        change negativeCredit l + negativeCredit r ≤ (c : ℤ) - 2
        have hExteriorZ : (exterior l : ℤ) + (exterior r : ℤ) ≤ (c : ℤ) + 2 := by
          exact_mod_cast hExterior
        omega
