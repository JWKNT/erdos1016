import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-! # The two physical orders of a two-port interface -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPortCodes

def pair {V : Type*} (a b : V) (q : Bool) : V := cond q b a

def flip : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- An actual unordered endpoint pair determines a Bool coordinate equivalence. -/
theorem exists_code {V : Type*} (f : Bool → V) (a b : V)
    (h : (f false=a ∧ f true=b) ∨ (f false=b ∧ f true=a)) :
    ∃p : Equiv.Perm Bool,∀q,f q=pair a b (p q) := by
  rcases h with ⟨hf,ht⟩ | ⟨hf,ht⟩
  · refine ⟨Equiv.refl Bool,?_⟩
    intro q
    cases q
    · exact hf
    · exact ht
  · refine ⟨flip,?_⟩
    intro q
    cases q
    · exact hf
    · exact ht

def lower (b : Bool) : Fin 4 := cond b 1 0
def upper (b : Bool) : Fin 4 := cond b 3 2

theorem pair_lower {V : Type*} (x : Fin 4 → V) (b : Bool) :
    pair (x 0) (x 1) b=x (lower b) := by cases b <;> rfl

theorem pair_upper {V : Type*} (x : Fin 4 → V) (b : Bool) :
    pair (x 2) (x 3) b=x (upper b) := by cases b <;> rfl

def index : (Bool ⊕ Bool) ≃ Fin 4 :=
  Equiv.ofBijective (Sum.elim lower upper) (by decide)

@[simp] theorem index_lower (b : Bool) : index (Sum.inl b)=lower b := rfl
@[simp] theorem index_upper (b : Bool) : index (Sum.inr b)=upper b := rfl

end Erdos1016.ExactMaximumSupport.FourPortCodes
