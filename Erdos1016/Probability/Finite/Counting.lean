import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite uniform counting

These are measure-free counting lemmas. `density` is always the uniform law on
an explicitly specified finite type. It is not an arbitrary historical law.
The convention on an empty space is zero.

Source role: the uniform outside-fiber averaging in the minimal manuscript,
and the finite counting behind S102 historical transport.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Finite

variable {α : Type*} {β : Type*} [Fintype α] [Fintype β]

/-- Number of states satisfying `P`, represented as a real number. -/
def count (P : α → Prop) : ℝ := by
  classical
  exact ∑ a, if P a then (1 : ℝ) else 0

/-- Probability under the uniform law on the full finite state space. -/
def density (P : α → Prop) : ℝ := count P / Fintype.card α



lemma count_nonneg (P : α → Prop) : 0 ≤ count P := by
  classical
  unfold count
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> norm_num

@[simp] lemma count_true : count (fun _ : α => True) = Fintype.card α := by
  classical
  simp [count]

@[simp] lemma count_false : count (fun _ : α => False) = 0 := by
  classical
  simp [count]

lemma count_mono {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    count P ≤ count Q := by
  classical
  unfold count
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a
  · simp [hp, h a hp]
  · simp only [if_neg hp]
    split_ifs <;> norm_num

lemma count_le_card (P : α → Prop) : count P ≤ Fintype.card α := by
  simpa using (count_mono (P := P) (Q := fun _ => True) (fun _ _ => trivial))

lemma count_eq_zero_of_card_eq_zero (P : α → Prop)
    (h : Fintype.card α = 0) : count P = 0 := by
  have hu := count_le_card P
  have hl := count_nonneg P
  rw [h] at hu
  norm_num at hu
  exact le_antisymm hu hl

lemma density_nonneg (P : α → Prop) : 0 ≤ density P := by
  exact div_nonneg (count_nonneg P) (Nat.cast_nonneg _)

lemma density_le_one (P : α → Prop) : density P ≤ 1 := by
  by_cases hz : Fintype.card α = 0
  · simp [density, hz]
  · have hc : (0 : ℝ) < Fintype.card α := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    exact (div_le_iff₀ hc).2 (by simpa using count_le_card P)



lemma count_le_mul_card_of_density_le {P : α → Prop} {ε : ℝ}
    (h : density P ≤ ε) : count P ≤ ε * Fintype.card α := by
  by_cases hz : Fintype.card α = 0
  · simp [count_eq_zero_of_card_eq_zero P hz, hz]
  · have hc : (0 : ℝ) < Fintype.card α := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    exact (div_le_iff₀ hc).1 h

lemma density_le_of_count_le_mul_card {P : α → Prop} {ε : ℝ}
    (hε : 0 ≤ ε) (h : count P ≤ ε * Fintype.card α) :
    density P ≤ ε := by
  by_cases hz : Fintype.card α = 0
  · simpa [density, hz] using hε
  · have hc : (0 : ℝ) < Fintype.card α := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    exact (div_le_iff₀ hc).2 h

/-- A bijection preserving the event preserves its count. -/
lemma count_equiv (e : α ≃ β) {P : α → Prop} {Q : β → Prop}
    (h : ∀ a, P a ↔ Q (e a)) : count P = count Q := by
  classical
  unfold count
  apply Fintype.sum_equiv e
  intro a
  simp only [h a]

lemma density_equiv (e : α ≃ β) {P : α → Prop} {Q : β → Prop}
    (h : ∀ a, P a ↔ Q (e a)) : density P = density Q := by
  unfold density
  rw [count_equiv e h, Fintype.card_congr e]

/-- Sum over the actual outside fibers, allowing different fiber sizes. -/
lemma count_sigma {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop) :
    count P = ∑ i, count (fun x : X i => P ⟨i, x⟩) := by
  classical
  simp only [count, Fintype.sum_sigma]











end Erdos1016.Finite
