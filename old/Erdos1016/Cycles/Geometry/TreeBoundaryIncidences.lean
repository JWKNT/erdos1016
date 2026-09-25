import Erdos1016.Cleanup.Corridors.TreeIncidenceCount
import Erdos1016.Decomposition.TwoCore.MaximalCore

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.TreeBoundaryInMinTwo

open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.Proof.TreeIncidenceCount

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A relation with at most one ordered incidence has total fiber size at
most one. This counts boundary adjacencies without reindexing edge labels. -/
theorem sum_fiber_card_le_one
    {V : Type*} [DecidableEq V] (A B : Finset V) (P : V → V → Prop)
    (hunique : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B,
      P a b → P c d → a = c ∧ b = d) :
    (∑ a ∈ A, (B.filter (P a)).card) ≤ 1 := by
  by_cases hex : ∃ a ∈ A, ∃ b ∈ B, P a b
  · obtain ⟨a, ha, b, hb, hab⟩ := hex
    have hzero : ∀ c ∈ A, c ≠ a → (B.filter (P c)).card = 0 := by
      intro c hc hca
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro d hd
      obtain ⟨hdB, hcd⟩ := Finset.mem_filter.mp hd
      exact hca (hunique c hc d hdB a ha b hb hcd hab).1
    rw [Finset.sum_eq_single a (fun c hc hca => hzero c hc hca) (by simp [ha])]
    apply Finset.card_le_one.mpr
    intro c hc d hd
    exact (hunique a ha c (Finset.mem_filter.mp hc).1
      a ha d (Finset.mem_filter.mp hd).1
      (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2).2
  · have hzero : ∀ a ∈ A, (B.filter (P a)).card = 0 := by
      intro a ha
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro b hb
      exact hex ⟨a, ha, b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
    rw [Finset.sum_eq_zero hzero]
    omega

/-- An induced tree inside a minimum-degree-two region has at least two
outgoing adjacency incidences within that region. -/
theorem tree_has_two_boundary_incidences
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) (A K : Finset V) (hAK : A ⊆ K)
    (hmin : MinTwo J K) (htree : (J.induce (↑A : Set V)).IsTree) :
    2 ≤ ∑ v ∈ A, ((K \ A).filter (J.Adj v)).card := by
  have hdeg (v : V) : degreeWithin J K v =
      degreeWithin J A v + ((K \ A).filter (J.Adj v)).card := by
    have hsets : K.filter (J.Adj v) =
        A.filter (J.Adj v) ∪ (K \ A).filter (J.Adj v) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hw
        by_cases hwA : w ∈ A
        · exact Or.inl ⟨hwA, hw.2⟩
        · exact Or.inr ⟨⟨hw.1, hwA⟩, hw.2⟩
      · rintro (hw | hw)
        · exact ⟨hAK hw.1, hw.2⟩
        · exact ⟨hw.1.1, hw.2⟩
    have hdisj : Disjoint (A.filter (J.Adj v)) ((K \ A).filter (J.Adj v)) := by
      apply Finset.disjoint_left.mpr
      intro w hw₁ hw₂
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw₂).1).2
        (Finset.mem_filter.mp hw₁).1
    change (K.filter (J.Adj v)).card = _
    rw [hsets, Finset.card_union_of_disjoint hdisj]
    rfl
  have hlow : 2 * A.card ≤ ∑ v ∈ A, degreeWithin J K v := by
    calc
      2 * A.card = ∑ _v ∈ A, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ A, degreeWithin J K v := Finset.sum_le_sum (fun v hv => hmin v (hAK hv))
  have hint := internal_incidence_sum_eq_tree_value J A htree.1 htree.2
  have hlocal (v : V) : (J.neighborFinset v ∩ A).card = degreeWithin J A v := by
    congr 1
    ext w
    simp [degreeWithin, Finset.mem_inter, and_comm]
  simp_rw [hlocal] at hint
  simp_rw [hdeg] at hlow
  rw [Finset.sum_add_distrib, hint] at hlow
  have hpos : 0 < A.card := by
    obtain ⟨v⟩ := htree.1.nonempty
    exact Finset.card_pos.mpr ⟨v.1, v.2⟩
  omega

end Erdos1016.Proof.TreeBoundaryInMinTwo

end
