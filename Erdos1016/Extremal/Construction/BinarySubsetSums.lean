import Erdos1016.Extremal.Statement

set_option autoImplicit false

/-!
# Arithmetic core of the binary-shortcut construction

This module formalizes the binary subset-sum fact used in the paper's §18
shortcut-chain lemma. The graph-theoretic realization still needs disjoint
arc interiors and is intentionally separated from this arithmetic lemma.
-/

namespace Erdos1016.Extremal

/-- Every integer below `2^j` is a sum of a subset of the first `j` powers of two. -/
theorem exists_subset_sum_powers (j m : ℕ) (hm : m < 2 ^ j) :
    ∃ s : Finset ℕ, s ⊆ Finset.range j ∧ (∑ i ∈ s, 2 ^ i) = m := by
  induction j generalizing m with
  | zero =>
      have : m = 0 := by simpa using hm
      subst m
      exact ⟨∅, by simp, by simp⟩
  | succ j ih =>
      by_cases hlo : m < 2 ^ j
      · obtain ⟨s, hs, hsum⟩ := ih m hlo
        exact ⟨s, hs.trans (Finset.range_mono (Nat.le_succ j)), hsum⟩
      · have hmlo : 2 ^ j ≤ m := by omega
        let r := m - 2 ^ j
        have htop : m < 2 ^ j * 2 := by
          simpa [pow_succ, Nat.mul_comm] using hm
        have hr : r < 2 ^ j := by
          dsimp [r]
          omega
        obtain ⟨s, hs, hsum⟩ := ih r hr
        have hjnot : j ∉ s := by
          intro hmem
          have := hs hmem
          simp at this
        refine ⟨insert j s, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · have hij : i < j := Finset.mem_range.mp (hs hi)
            exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hij)
        · rw [Finset.sum_insert hjnot, hsum]
          dsimp [r]
          omega





end Erdos1016.Extremal
