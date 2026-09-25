import Mathlib

set_option autoImplicit false

/-!
# Capping the weight of a finite family

This is the deterministic selection step used in the paper after the cycle
family has been shown to have large total weight. It is independent of the
graph geometry and of the probability estimates.
-/

namespace Erdos1016.BoundaryDecay

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- From a finite family of nonnegative weights, select a subfamily whose
total first reaches a prescribed threshold. The overshoot is at most the
largest individual weight. -/
theorem exists_subset_sum_between_threshold
    (s : Finset ι) (w : ι → ℝ) (τ δ : ℝ)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ δ)
    (hs : τ ≤ ∑ i ∈ s, w i) :
    ∃ t ⊆ s, τ ≤ (∑ i ∈ t, w i) ∧ (∑ i ∈ t, w i) ≤ τ + δ := by
  classical
  let good : Finset ι → Prop := fun t => τ ≤ ∑ i ∈ t, w i
  let candidates := s.powerset.filter good
  have hs_mem : s ∈ candidates := by
    simp [candidates, good, hs]
  obtain ⟨t, ht, hmin⟩ :=
    Finset.exists_min_image candidates Finset.card
      ⟨s, hs_mem⟩
  have htgood : good t := (Finset.mem_filter.1 ht).2
  have hts : t ⊆ s := Finset.mem_powerset.1 (Finset.mem_filter.1 ht).1
  refine ⟨t, hts, htgood, ?_⟩
  by_cases hempty : t = ∅
  · simp [hempty] at htgood ⊢
    linarith
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hempty
    have hsmall : ¬ good (t.erase i) := by
      intro hgood
      have herase_mem : t.erase i ∈ candidates := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_powerset.2 ?_, hgood⟩
        exact (Finset.erase_subset i t).trans hts
      have hcard := hmin (t.erase i) herase_mem
      have hless : (t.erase i).card < t.card := by
        rw [Finset.card_erase_of_mem hi]
        exact Nat.sub_lt (Finset.card_pos.mpr ⟨i, hi⟩) (by decide)
      omega
    have hbefore : (∑ j ∈ t.erase i, w j) < τ := by
      have hnot : ¬ τ ≤ ∑ j ∈ t.erase i, w j := hsmall
      exact lt_of_not_ge hnot
    have hiw := (hw i (hts hi)).2
    have hsum := Finset.sum_erase_add t w hi
    dsimp [good] at htgood
    rw [← hsum]
    linarith

end Erdos1016.BoundaryDecay
