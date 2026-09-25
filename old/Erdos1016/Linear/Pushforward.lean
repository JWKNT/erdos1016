import Erdos1016.Probability.Finite.LinearImages

set_option autoImplicit false

/-!
# Binary pushforward along a map of finite labelled sets

`push f` adds the original coordinates over the fibers of f. All labels are
retained in the domain; repeated endpoints are added, never identified as
independent fair bits. This is the incidence arithmetic used by the graph law.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

def unitWord (a : A) : A → Bit := Pi.single a 1

@[simp] theorem unitWord_apply (a a' : A) :
    unitWord a a' = if a = a' then 1 else 0 := by
  classical
  simp [unitWord, Pi.single_apply, eq_comm]

/-- Pushforward of binary weights along a finite map. -/
def push (f : A → B) : (A → Bit) →ₗ[Bit] (B → Bit) where
  toFun x := ∑ a, x a • unitWord (f a)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_assoc, Finset.smul_sum]

@[simp] theorem push_apply (f : A → B) (x : A → Bit) (b : B) :
    push f x b = ∑ a, if f a = b then x a else 0 := by
  classical
  change (∑ a, x a • unitWord (f a)) b = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitWord_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

@[simp] theorem push_unit (f : A → B) (a : A) :
    push f (unitWord a) = unitWord (f a) := by
  classical
  change (∑ a', unitWord a a' • unitWord (f a')) = _
  simp [unitWord_apply]

@[simp] theorem push_id (x : A → Bit) : push (id : A → A) x = x := by
  classical
  funext a
  simp [push_apply, eq_comm]

/-- Composition counts every original coordinate exactly once. -/
theorem push_comp (f : A → B) (g : B → C) (x : A → Bit) :
    push g (push f x) = push (g ∘ f) x := by
  change push g (∑ a, x a • unitWord (f a)) = _
  simp only [map_sum, map_smul, push_unit]
  rfl

def total : (A → Bit) →ₗ[Bit] Bit where
  toFun x := ∑ a, x a
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem total_apply (x : A → Bit) : total x = ∑ a, x a := rfl

@[simp] theorem total_unit (a : A) : total (unitWord a) = 1 := by
  classical
  simp [total, unitWord_apply]

@[simp] theorem total_push (f : A → B) (x : A → Bit) :
    total (push f x) = total x := by
  classical
  change total (∑ a, x a • unitWord (f a)) = total x
  rw [map_sum]
  calc
    (∑ a, total (x a • unitWord (f a))) = ∑ a, x a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul, total_unit]
      simp only [smul_eq_mul, mul_one]
    _ = total x := rfl

/-- All but one component equation, together with total parity, imply the last. -/
theorem eq_zero_of_total_zero_of_off_eq_zero (c₀ : C) (x : C → Bit)
    (htotal : total x = 0) (hoff : ∀ c, c ≠ c₀ → x c = 0) : x = 0 := by
  have hsum : total x = x c₀ := by
    apply Finset.sum_eq_single c₀
    · intro c _ hc
      exact hoff c hc
    · intro hc
      exact False.elim (hc (Finset.mem_univ c₀))
  funext c
  by_cases hc : c = c₀
  · subst c
    exact hsum.symm.trans htotal
  · exact hoff c hc

/-- A pin injection really does determine every pin bit, not just its syndrome. -/
theorem push_injective (f : A → B) (hf : Function.Injective f) :
    Function.Injective (push f) := by
  intro x y hxy
  funext a
  have h := congrFun hxy (f a)
  have heq : ∀ a', f a' = f a ↔ a' = a := by
    intro a'
    exact ⟨fun h => hf h, fun h => congrArg f h⟩
  simpa [push_apply, heq] using h

end Erdos1016.BoundaryTrace
