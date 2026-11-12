import Erdos1016.ExactMaximum.FourCutArithmetic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# The numbering of four ports

The ports of a pole with four ports have the numbers `0, 1, 2, 3`, and the three pairings have
the numbers `0 = 01|23`, `1 = 02|13`, `2 = 03|12` (`pairingOf` in `FourCutArithmetic.lean`). This
file has the facts about these numbers that the case of a cyclic cut of size four uses. They are
finite checks.

* `quad_canon`: a function of four different ports that does not change when the two ports of a
  pair change places, or the two pairs change places, depends on the pairing only.
* `exists_pairing`: every port has a partner for every pairing.
* `renumber`: the numbering that puts four different ports `i, j, k, l` in the places
  `0, 1, 2, 3`.
-/

namespace Erdos1016.ExactMaximum

/-- The four ports are different. -/
theorem fin4_distinct : (0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2 ∧
    (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3 := by decide

/-- The pairing of `i, j` is the pairing of `j, i`. -/
theorem pairingOf_comm : ∀ i j : Fin 4, pairingOf i j = pairingOf j i := by decide

/-- Four different ports. -/
def Distinct4 (i j k l : Fin 4) : Prop := i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l

instance (i j k l : Fin 4) : Decidable (Distinct4 i j k l) := by
  unfold Distinct4
  infer_instance

theorem pairingOf_opposite_aux : ∀ i j k l : Fin 4, Distinct4 i j k l →
    pairingOf k l = pairingOf i j := by decide

/-- The two pairs of a pairing have the same pairing. -/
theorem pairingOf_opposite (i j k l : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : pairingOf k l = pairingOf i j :=
  pairingOf_opposite_aux i j k l ⟨hij, hik, hil, hjk, hjl, hkl⟩

/-- Every port has a partner for every pairing. -/
theorem exists_pairing : ∀ (i : Fin 4) (α : Fin 3), ∃ j k l : Fin 4,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ pairingOf i j = α := by decide

/-- **A symmetric function of two pairs depends on the pairing only.** Let `F i j k l` not change
when `i, j` change places, when `k, l` change places, and when the pairs `i, j` and `k, l` change
places. Then for four different ports its value is the value at `0 1 2 3`, at `0 2 1 3` or at
`0 3 1 2`, as the pairing of `i, j` says. -/
theorem quad_canon {α : Type*} (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → α)
    (hL : ∀ i j k l, F i j k l = F j i k l) (hR : ∀ i j k l, F i j k l = F i j l k)
    (hC : ∀ i j k l, F i j k l = F k l i j) (c : Fin 3 → α) (h0 : F 0 1 2 3 = c 0)
    (h1 : F 0 2 1 3 = c 1) (h2 : F 0 3 1 2 = c 2) :
    ∀ i j k l : Fin 4, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      F i j k l = c (pairingOf i j) := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    intro hij hik hil hjk hjl hkl <;>
    first
    | exact absurd rfl hij
    | exact absurd rfl hik
    | exact absurd rfl hil
    | exact absurd rfl hjk
    | exact absurd rfl hjl
    | exact absurd rfl hkl
    | exact h0
    | exact h1
    | exact h2
    | exact (hL _ _ _ _).trans h0
    | exact (hL _ _ _ _).trans h1
    | exact (hL _ _ _ _).trans h2
    | exact (hR _ _ _ _).trans h0
    | exact (hR _ _ _ _).trans h1
    | exact (hR _ _ _ _).trans h2
    | exact ((hL _ _ _ _).trans (hR _ _ _ _)).trans h0
    | exact ((hL _ _ _ _).trans (hR _ _ _ _)).trans h1
    | exact ((hL _ _ _ _).trans (hR _ _ _ _)).trans h2
    | exact (hC _ _ _ _).trans h0
    | exact (hC _ _ _ _).trans h1
    | exact (hC _ _ _ _).trans h2
    | exact ((hC _ _ _ _).trans (hL _ _ _ _)).trans h0
    | exact ((hC _ _ _ _).trans (hL _ _ _ _)).trans h1
    | exact ((hC _ _ _ _).trans (hL _ _ _ _)).trans h2
    | exact ((hC _ _ _ _).trans (hR _ _ _ _)).trans h0
    | exact ((hC _ _ _ _).trans (hR _ _ _ _)).trans h1
    | exact ((hC _ _ _ _).trans (hR _ _ _ _)).trans h2
    | exact (((hC _ _ _ _).trans (hL _ _ _ _)).trans (hR _ _ _ _)).trans h0
    | exact (((hC _ _ _ _).trans (hL _ _ _ _)).trans (hR _ _ _ _)).trans h1
    | exact (((hC _ _ _ _).trans (hL _ _ _ _)).trans (hR _ _ _ _)).trans h2

/-- The numbering that puts the ports `i, j, k, l` in the places `0, 1, 2, 3`. -/
def renumber (i j k l : Fin 4) : Fin 4 → Fin 4 := ![i, j, k, l]

theorem renumber_injective_aux : ∀ i j k l : Fin 4, Distinct4 i j k l →
    ∀ m n : Fin 4, renumber i j k l m = renumber i j k l n → m = n := by decide

theorem renumber_surjective_aux : ∀ i j k l : Fin 4, Distinct4 i j k l →
    ∀ m : Fin 4, ∃ n : Fin 4, renumber i j k l n = m := by decide

/-- The numbering of four different ports is injective. -/
theorem renumber_injective (i j k l : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : Function.Injective (renumber i j k l) :=
  fun m n h => renumber_injective_aux i j k l ⟨hij, hik, hil, hjk, hjl, hkl⟩ m n h

/-- The numbering of four different ports has all ports. -/
theorem renumber_surjective (i j k l : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∀ m : Fin 4, ∃ n : Fin 4, renumber i j k l n = m :=
  renumber_surjective_aux i j k l ⟨hij, hik, hil, hjk, hjl, hkl⟩

/-- The places `0, 1` have the ports `i, j`. -/
theorem renumber_low : ∀ i j k l m : Fin 4, m.val < 2 →
    renumber i j k l m = i ∨ renumber i j k l m = j := by decide

/-- The places `2, 3` have the ports `k, l`. -/
theorem renumber_high : ∀ i j k l m : Fin 4, 2 ≤ m.val →
    renumber i j k l m = k ∨ renumber i j k l m = l := by decide

end Erdos1016.ExactMaximum
