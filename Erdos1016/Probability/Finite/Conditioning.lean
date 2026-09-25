import Erdos1016.Probability.Finite.LinearImages

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Erdos1016.Finite

local instance conditioningDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform conditioning on a nonempty subset factors its ambient probability. -/
theorem density_and_eq_density_subtype {X : Type*} [Fintype X]
    (P Q : X → Prop) [Nonempty {x // P x}] :
    density (fun x => P x ∧ Q x) = density P * density (fun x : {x // P x} => Q x.1) := by
  have hc : count (fun x => P x ∧ Q x) = count (fun x : {x // P x} => Q x.1) := by
    rw [BoundaryTrace.count_eq_subtype_card, BoundaryTrace.count_eq_subtype_card]
    congr 1
    exact Nat.card_congr {
      toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : count P = (Fintype.card {x // P x} : ℝ) := by
    rw [BoundaryTrace.count_eq_subtype_card, Nat.card_eq_fintype_card]
  have hn : (Fintype.card {x // P x} : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := {x // P x})
  letI : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty {x // P x})).1⟩
  have hx : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := X)
  simp only [density, hc, hp]
  field_simp [hn, hx]
  ring

/-- Two independent uniform coordinates have the product event law. -/
theorem density_prod_and {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Prop) (Q : Y → Prop) :
    density (fun z : X × Y => P z.1 ∧ Q z.2) = density P * density Q := by
  have hc : count (fun z : X × Y => P z.1 ∧ Q z.2) = count P * count Q := by
    simp only [count, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hp : P x <;> by_cases hq : Q y <;> simp [hp, hq]
  simp only [density, hc, Fintype.card_prod, Nat.cast_mul]
  ring

/-- Exactly one state is zero. -/
theorem density_ne_zero {X : Type*} [Fintype X] [Zero X] :
    density (fun x : X => x ≠ 0) = 1 - 1 / (Fintype.card X : ℝ) := by
  have hz : count (fun x : X => x = 0) = 1 := by simp [count]
  have hs : count (fun x : X => x ≠ 0) + count (fun x : X => x = 0) =
      Fintype.card X := by
    rw [count, count, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _x : X, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : x = 0 <;> simp [h]
      _ = _ := by simp
  have hn : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := X)
  rw [hz] at hs
  unfold density
  rw [eq_sub_of_add_eq hs]
  field_simp

end Erdos1016.Finite
