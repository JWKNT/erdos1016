import Mathlib.Order.SupIndep
import Mathlib.Order.ModularLattice
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Maximal direct-sum selection and the final packing count

Supremum independence is direct-sum independence for submodules. A maximal
finite independent subfamily makes every omitted subspace relevant to its sum.
The final arithmetic uses the explicit exception and string bounds.
-/

namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingSelection

variable {ι α : Type*} [DecidableEq ι] [Lattice α] [OrderBot α] [IsModularLattice α]

/-- Add one subspace that is disjoint from the entire previous sum. -/
theorem supIndep_insert {A : Finset ι} {L : ι → α} {i : ι}
    (hi : i ∉ A) (hA : A.SupIndep L) (hdis : Disjoint (L i) (A.sup L)) :
    (insert i A).SupIndep L := by
  rw [Finset.supIndep_iff_disjoint_erase]
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simpa [Finset.erase_insert, hi] using hdis
  · have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
    have hold := (Finset.supIndep_iff_disjoint_erase.mp hA) j hj
    have hle : L j ⊔ (A.erase j).sup L ≤ A.sup L :=
      sup_le (Finset.le_sup hj) (Finset.sup_mono (Finset.erase_subset j A))
    have hnew := hold.disjoint_sup_right_of_disjoint_sup_left (hdis.symm.mono_left hle)
    have heq : (insert i A).erase j = insert i (A.erase j) := by
      ext k
      simp only [Finset.mem_erase, Finset.mem_insert]
      aesop
    rw [heq, Finset.sup_insert, sup_comm]
    exact hnew

/-- Maximum-cardinality independent selection makes all omitted members intersect
the selected sum. This is stronger than pairwise maximality. -/
theorem exists_maximal_independent (s : Finset ι) (L : ι → α) :
    ∃ A ⊆ s, A.SupIndep L ∧
      ∀ i ∈ s, i ∉ A → ¬ Disjoint (L i) (A.sup L) := by
  classical
  let families := s.powerset.filter fun A => A.SupIndep L
  have hempty : ∅ ∈ families := by simp [families]
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image families Finset.card ⟨∅, hempty⟩
  have hAs : A ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hind : A.SupIndep L := (Finset.mem_filter.mp hA).2
  refine ⟨A, hAs, hind, ?_⟩
  intro i his hi hdis
  have hnew : insert i A ∈ families := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset his hAs),
      supIndep_insert hi hind hdis⟩
  have hh := hmax _ hnew
  rw [Finset.card_insert_of_not_mem hi] at hh
  omega

/-- A nonempty set of candidate indices gives a nonempty maximal family. -/
theorem exists_nonempty_maximal_independent (s : Finset ι) (hs : s.Nonempty) (L : ι → α) :
    ∃ A ⊆ s, A.Nonempty ∧ A.SupIndep L ∧
      ∀ i ∈ s, i ∉ A → ¬ Disjoint (L i) (A.sup L) := by
  obtain ⟨A, hAs, hind, hrel⟩ := exists_maximal_independent s L
  have hne : A.Nonempty := by
    by_contra hn
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨i, hi⟩ := hs
    have hh := hrel i hi (by simp [he])
    simp [he] at hh
  exact ⟨A, hAs, hne, hind, hrel⟩

/-- Count the one omitted zero space, selected spaces, exceptions and strings. -/
theorem packing_count (n t b d s : ℕ) (hd : 2 ≤ d) (ht : t < 2 ^ d)
    (hb : b ≤ d * t)
    (hn : n ≤ 1 + t + 2 * b + 2 * b * 258 * (s + 3)) :
    n ≤ 1551 * d * (s + 1) * 2 ^ d := by
  have ht' : t + 1 ≤ 2 ^ d := by omega
  have hb' : b ≤ d * 2 ^ d := hb.trans (Nat.mul_le_mul_left d ht.le)
  have hs : s + 3 ≤ 3 * (s + 1) := by omega
  have hlong : 2 * b * 258 * (s + 3) ≤ 1548 * d * (s + 1) * 2 ^ d := by
    have h₁ := Nat.mul_le_mul_left (2 * b * 258) hs
    have h₂ := Nat.mul_le_mul_right (1548 * (s + 1)) hb'
    nlinarith
  have hshort : 1 + t + 2 * b ≤ 3 * d * (s + 1) * 2 ^ d := by
    have h₁ : 1 + t + 2 * b ≤ (1 + 2 * d) * 2 ^ d := by nlinarith
    have h₂ : 1 + 2 * d ≤ 3 * d * (s + 1) := by nlinarith
    exact h₁.trans (Nat.mul_le_mul_right (2 ^ d) h₂)
  nlinarith

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingSelection
